module Depling.Unification

import Depling
import Utils
import Data.Fin
import Data.Vect

public export
data UnificationGroup : Nat -> Nat -> Type where
	UnificationGroupV : (es : List (Either (DAST l) (DAST r))) -> {auto ne : NonEmpty es} -> UnificationGroup l r

total
export
map : (Either (DAST l1) (DAST r1) -> Either (DAST l2) (DAST r2)) -> UnificationGroup l1 r1 -> UnificationGroup l2 r2
map f (UnificationGroupV es {ne}) = UnificationGroupV (map f es) {ne = nonEmptyMap ne}

total
find : Either (DAST l) (DAST r) -> List (UnificationGroup l r) -> (Maybe (UnificationGroup l r), List (UnificationGroup l r))
find e [] = (Nothing, [])
find e (g@(UnificationGroupV es) :: us) =
	if elem e es
	then (Just g, us)
	else
		let (g', us') = find e us
		in (g', g :: us')

total
is_concrete : DAST n -> Bool
is_concrete (ʌ _) = False
is_concrete _ = True

total
export
is_similar : DAST l -> DAST r -> Bool
is_similar (ʌ _) _ = True
is_similar _ (ʌ _) = True
is_similar (_ =!= _) _ = True
is_similar _ (_ =!= _) = True
is_similar 𝕋 𝕋 = True
is_similar (𝕌 ln lt) (𝕌 rn rt) = ln == rn && is_similar lt rt
is_similar (ℂ {a=la} lc las) (ℂ {a=ra} rc ras) =
	la == ra &&
	lc == believe_me rc &&
	(assert_total $ and $ zipWith (\a, b => is_similar a b) (toList las) (toList ras))
is_similar (𝔹 lt) (𝔹 rt) = is_similar lt rt
is_similar l r = False

mutual
	%assert_total
	do_merge : UnificationGroup l r -> (UnificationGroup l r, List (UnificationGroup l r)) -> (UnificationGroup l r, List (UnificationGroup l r))
	do_merge (UnificationGroupV g1) (g2, us) = foldr add_to_group (g2, us) g1

	total
	try_merge1 : UnificationGroup l r -> UnificationGroup l r -> Maybe (UnificationGroup l r, List (UnificationGroup l r))
	try_merge1 g1@(UnificationGroupV es1) g2@(UnificationGroupV es2) =
		if or $ map (\e => elem e es2) es1
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
	add_to_group e@(Left (ʌ _)) (UnificationGroupV es, us) = (UnificationGroupV (e :: es), us)
	add_to_group e@(Right (ʌ _)) (UnificationGroupV es, us) = (UnificationGroupV (e :: es), us)
	add_to_group e (g, us) =
		let
			UnificationGroupV es = g
		in foldr merger (g, us) $ concatMap (unify_h e) es
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
	add {l=ln} {r=rn} l r us =
		let
			(gl, us') = find (Left l) us
			(gr, us'') = find (Right r) us'
			f = assert_total $ case catMaybes $ the (List _) [gl, gr] of
				[g1, g2] => add_to_group (Left l) $ add_to_group (Right r) $ do_merge g1 (g2, us'')
				[g] => add_to_group (Left l) $ add_to_group (Right r) $ (g, us'')
				[] => (UnificationGroupV [Left l, Right r], us'')
			(UnificationGroupV g {ne}, us''') = the (UnificationGroup ln rn, List (UnificationGroup ln rn)) f
		in (UnificationGroupV (nub g) {ne = nonEmptyNub ne}) :: us'''

	total
	export
	unify : DAST l -> DAST r -> List (UnificationGroup l r) -> List (UnificationGroup l r)
	unify l@(ʌ v) r us = add l r us
	unify l r@(ʌ v) us = add l r us
	unify (λ lat lb) (λ rat rb) us = ?unify_λ
	unify (λT lat lrt) (λT rat rrt) us = ?unify_λT $ unify lrt rrt []
	-- unify (lf =!= la) (rf =!= ra) us = unify lf rf $ unify la ra us
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

total
extract : Either (DAST l) (DAST r) -> (n : Nat ** DAST n)
extract (Left  l) = (_ ** l)
extract (Right r) = (_ ** r)

total
is_similar_h : (n : Nat ** DAST n) -> (n : Nat ** DAST n) -> Bool
is_similar_h (l ** la) (r ** ra) = is_similar la ra

total
export
primary : UnificationGroup l r -> Either (DAST l) (DAST r)
primary (UnificationGroupV es {ne}) =
	case find (either is_concrete is_concrete) $ nubBy (\a, b => is_similar_h (extract a) (extract b)) es of
		Just e => e
		Nothing => head (sortBy p_compare es) {ok = nonEmptySort ne}
	where
		total
		p_compare : Either (DAST l) (DAST r) -> Either (DAST l) (DAST r) -> Ordering
		p_compare (Left (ʌ a)) (Left (ʌ b)) = compare a b
		p_compare (Right (ʌ a)) (Right (ʌ b)) = compare a b
		p_compare (Left _) (Right _) = GT
		p_compare (Right _) (Left _) = LT
		p_compare _ _ = EQ
