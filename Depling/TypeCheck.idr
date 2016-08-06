module Depling.TypeCheck

import Depling
import Depling.Incr
import Depling.Elevate
import Depling.Reduce
import Depling.Replace
import Depling.Decr
import Depling.Unification
import Utils
import Data.Vect

total
export
dType : Vect n (DAST n) -> DAST n -> DAST n
dType c (ʌ v) = index v c
dType c (λ at b) = λT at $ dType (map (incr 0) $ at :: c) b
dType c (λT at rt) = 𝕋
dType c (f =!= a) = (dType c f) =!= a
dType c 𝕋 = 𝕋
dType c (𝔽 at rt b) = λT at rt
dType c (𝕌 n t) = t
dType c (ℂ {a} (DConV n ats rt) as) = dAppN (elevate $ dLamN ats $ replace (sym $ plusZeroRightNeutral a) $ rt) (toList as)
dType c (ℙ v cn t f) = dType c f
dType c (𝔹 t) = t

public export
data DTypeError : Type where
	DTypeErrorV : Maybe (DAST n) -> List (DAST n) -> DTypeError

total
check : Maybe (DAST n) -> UnificationGroup n n -> Maybe DTypeError
check a (UnificationGroupV es {ne}) with (nubBy is_similar $ map fromEither es)
	check a (UnificationGroupV _ {ne}) | [e] = Nothing
	check a (UnificationGroupV _ {ne}) | es' = Just $ DTypeErrorV a es'

total
ensureType : Vect n (DAST n) -> DAST n -> DAST n -> List DTypeError
ensureType {n} c a t = catMaybes $ map (check $ Just a) $ unify (dType c a) t []

reverse : DRCtx n m -> Vect m (DAST m) -> Vect (n + m) (DAST (n + m))
reverse [] c = c
reverse {n=S n} {m} (h :: t) c = rewrite plusSuccRightSucc n m in reverse t $ map (incr 0) $ h :: c

test : a -> b

total
export
typeCheck : Vect n (DAST n) -> DAST n -> List DTypeError
typeCheck c (ʌ v) = []
typeCheck c (λ at b) = typeCheck c at ++ ensureType c at 𝕋 ++ typeCheck (map (incr 0) $ at :: c) b
typeCheck c (λT at r) = typeCheck c at ++ ensureType c at 𝕋 ++ typeCheck (map (incr 0) $ at :: c) r ++ ensureType (map (incr 0) $ at :: c) r 𝕋
typeCheck {n} c ast@(f =!= a) =
	typeCheck c f ++
	typeCheck c a ++
	case lfreduce ft of
		λT fat b => ensureType c a fat
		_ => [DTypeErrorV (Just ast) [ft, λT at $ 𝕌 "result" 𝕋]]
	where
		ft : DAST n
		ft = dType c f
		at : DAST n
		at = dType c a
typeCheck c 𝕋 = []
typeCheck c (𝔽 at rt b) =
	typeCheck c at ++ ensureType c at 𝕋 ++
	typeCheck (map (incr 0) $ at :: c) rt ++ ensureType (map (incr 0) $ at :: c) rt 𝕋 ++
	typeCheck (map (incr 0 . incr 0) $ at :: (λT at rt) :: c) b ++ ensureType (map (incr 0 . incr 0) $ at :: (λT at rt) :: c) b (incr 1 rt)
typeCheck c (𝕌 n t) = typeCheck c t ++ ensureType c t 𝕋
typeCheck {n} c (ℂ (DConV {a} _ ats rt) as) = assert_total $ typeCheck c tca ++ ensureType c tca 𝕋
	where
		tca : DAST n
		tca = dAppN (elevate $ dLamN ats $ replace (sym $ plusZeroRightNeutral a) $ rt) (toList as)
typeCheck {n} c a@(ℙ v (DConV {a} _ ats rt) t f) =
	typeCheck c v ++
	typeCheck c f ++
	typeCheck (reverse (elevateRC {gte=LTEZero} ats) c) t ++
	(catMaybes $ map (check $ Just $ incr' a) groups) ++
	ensureType (map replace' $ reverse (elevateRC {gte=LTEZero} ats) c) (replace' t) (replace' $ incr' $ dType c f)
	where
		total
		groups : List (UnificationGroup (a + n) (a + n))
		groups =
			map (map $ either (Left . incr') (Right . elevate {gte = ltePlus'})) $
			unify (dType c v) rt []

		total
		replacements : List (DAST (a + n), DAST (a + n))
		replacements = do
			g <- groups
			let pr = primary g
			let UnificationGroupV es = g
			e <- es
			if e == pr
			then []
			else pure (fromEither pr, fromEither e)
		
		replace' : DAST (a + n) -> DAST (a + n)
		replace' a = foldl (\a, (p, r) => dReplace p r a) a replacements
typeCheck c (𝔹 t) = typeCheck c t ++ ensureType c t 𝕋
