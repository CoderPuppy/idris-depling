module Depling.Unification

import Depling
import Data.Fin
import Data.Vect

data UnificationGroup : Nat -> Nat -> Type where
	UnificationGroupV : List (Either (DAST l) (DAST r)) -> UnificationGroup l r

total
find_unification_group : Either (DAST l) (DAST r) -> List (UnificationGroup l r) -> (Maybe (UnificationGroup l r), List (UnificationGroup l r))
find_unification_group e [] = (Nothing, [])
find_unification_group e (g@(UnificationGroupV es) :: us) =
	if elem e es
	then (Just g, us)
	else
		let (g', us') = find_unification_group e us
		in (g', g :: us')

total
add_unification : DAST l -> DAST r -> List (UnificationGroup l r) -> List (UnificationGroup l r)
add_unification l r us =
	let
		(gl, us') = find_unification_group (Left l) us
		(gr, us'') = find_unification_group (Right r) us'
	in
		assert_total $ case catMaybes $ the (List _) [gl, gr] of
			[UnificationGroupV es1, UnificationGroupV es2] => UnificationGroupV (nub $ Left l :: Right r :: es1 ++ es2) :: us''
			[UnificationGroupV es] => UnificationGroupV (nub $ Left l :: Right r :: es) :: us''
			[] => UnificationGroupV [Left l, Right r] :: us''

total
unify : DAST l -> DAST r -> (List (UnificationGroup l r), List (DAST l, DAST r)) -> (List (UnificationGroup l r), List (DAST l, DAST r))
unify l@(ʌ v) r (us, es) = (add_unification l r us, es)
unify l r@(ʌ v) (us, es) = (add_unification l r us, es)
unify (λ lat lb) (λ rat rb) (us, es) = ?unify_λ
unify (λT lat lrt) (λT rat rrt) (us, es) = ?unify_λT
unify (lf =!= la) (rf =!= ra) (us, es) = unify lf rf $ unify la ra (us, es)
unify 𝕋 𝕋 (us, es) = (us, es)
unify (𝔽 lat lrt lb) (𝔽 rat rrt rb) (us, es) = ?unify_𝔽
unify l@(𝕌 ln lt) r@(𝕌 rn rt) (us, es) =
	if ln == rn
	then unify lt rt (us, es)
	else (us, (l, r) :: es)
unify l@(ℂ lc@(DConV {a=la} _ _ _) las) r@(ℂ rc@(DConV {a=ra} _ _ _) ras) (us, es) =
	if la == ra && lc == believe_me rc
	then assert_total $ foldr (\f, a => f a) (us, es) $ zipWith unify las (believe_me ras)
	else (us, (l, r) :: es)
unify (ℙ lv lc lt lf) (ℙ rv rc rt rf) (us, es) = ?unify_ℙ
unify (𝔹 lt) (𝔹 rt) (us, es) = unify lt rt (us, es)
unify l r (us, es) = (us, (l, r) :: es)
