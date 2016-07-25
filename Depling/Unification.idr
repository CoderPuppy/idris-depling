module Depling.Unification

import Depling
import Data.Fin
import Data.Vect

UnificationGroup : Nat -> Nat -> Type
UnificationGroup l r = List (Either (DAST l) (DAST r))

total
find : Either (DAST l) (DAST r) -> List (UnificationGroup l r) -> (Maybe (UnificationGroup l r), List (UnificationGroup l r))
find e [] = (Nothing, [])
find e (g :: us) =
	if elem e g
	then (Just g, us)
	else
		let (g', us') = find e us
		in (g', g :: us')

mutual
	%assert_total
	do_merge : UnificationGroup l r -> (UnificationGroup l r, List (UnificationGroup l r)) -> (UnificationGroup l r, List (UnificationGroup l r))
	do_merge g1 (g2, us) = foldr add_to_group (g2, us) g1

	total
	try_merge1 : UnificationGroup l r -> UnificationGroup l r -> Maybe (UnificationGroup l r, List (UnificationGroup l r))
	try_merge1 g1 g2 =
		if or $ map (\e => elem e g2) g1
		then Just $ do_merge g1 (g2, [])
		else Nothing

	total
	merge : UnificationGroup l r -> List (UnificationGroup l r) -> List (UnificationGroup l r) -> List (UnificationGroup l r)
	merge g [] us' = g :: us'
	merge g (g' :: us) us' =
		case try_merge1 g g' of
			Just (g', us'') => g' :: assert_total (mergeMany us'' (us ++ us'))
			Nothing => merge g us (g' :: us')

	total
	mergeMany : List (UnificationGroup l r) -> List (UnificationGroup l r) -> List (UnificationGroup l r)
	mergeMany a b = foldr (\g, us => merge g us []) b a

	total
	add_to_group : Either (DAST l) (DAST r) -> (UnificationGroup l r, List (UnificationGroup l r)) -> (UnificationGroup l r, List (UnificationGroup l r))
	add_to_group e@(Left (ʌ _)) (g, us) = (e :: g, us)
	add_to_group e@(Right (ʌ _)) (g, us) = (e :: g, us)
	add_to_group e (g, us) = foldr merger (g, us) $ concatMap (unify_h e) g
		where
			merger : UnificationGroup l r -> (UnificationGroup l r, List (UnificationGroup l r)) -> (UnificationGroup l r, List (UnificationGroup l r))
			merger g' (g, us) =
				case try_merge1 g' g of
					Just (g, us') => (g, mergeMany us us')
					Nothing => (g, merge g' us [])

			%assert_total
			unify_h : Either (DAST l) (DAST r) -> Either (DAST l) (DAST r) -> List (UnificationGroup l r)
			unify_h (Left a) (Left b) = map (map $ Left . fromEither) $ unify a b []
			unify_h (Right a) (Right b) = map (map $ Right . fromEither) $ unify a b []
			unify_h (Left a) (Right b) = unify a b []
			unify_h (Right a) (Left b) = map (map mirror) $ unify a b []

	total
	add : DAST l -> DAST r -> List (UnificationGroup l r) -> List (UnificationGroup l r)
	add l r us =
		let
			(gl, us') = find (Left l) us
			(gr, us'') = find (Right r) us'
			f = assert_total $ case catMaybes $ the (List _) [gl, gr] of
				[g1, g2] => do_merge g1 (g2, us'')
				[g] => (g, us'')
				[] => ([], us'')
			(g, us''') = add_to_group (Left l) $ add_to_group (Right r) f
		in nub g :: us'''

	total
	unify : DAST l -> DAST r -> List (UnificationGroup l r) -> List (UnificationGroup l r)
	unify l@(ʌ v) r us = add l r us
	unify l r@(ʌ v) us = add l r us
	unify (λ lat lb) (λ rat rb) us = ?unify_λ
	unify (λT lat lrt) (λT rat rrt) us = ?unify_λT
	unify (lf =!= la) (rf =!= ra) us = unify lf rf $ unify la ra us
	unify 𝕋 𝕋 us = us
	unify (𝔽 lat lrt lb) (𝔽 rat rrt rb) us = ?unify_𝔽
	unify l@(𝕌 ln lt) r@(𝕌 rn rt) us =
		if ln == rn
		then unify lt rt us
		else add l r us
	unify l@(ℂ lc@(DConV {a=la} _ _ _) las) r@(ℂ rc@(DConV {a=ra} _ _ _) ras) us =
		if la == ra && lc == believe_me rc
		then assert_total $ foldr (\f, a => f a) us $ zipWith unify las (believe_me ras)
		else add l r us
	unify (ℙ lv lc lt lf) (ℙ rv rc rt rf) us = ?unify_ℙ
	unify (𝔹 lt) (𝔹 rt) us = unify lt rt us
	unify l r us = add l r us
