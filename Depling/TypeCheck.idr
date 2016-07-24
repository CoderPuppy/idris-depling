module Depling.TypeCheck

import Depling
import Depling.Incr
import Depling.Elevate
import Depling.Reduce
import Depling.Decr
import Data.Vect

total
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

data DTypeError : Type where
	DExactTypeError : DAST n -> DAST n -> DAST n -> DTypeError
	DSimilarTypeError : DAST n -> DAST n -> DAST a -> DTypeError

total
ensureType : Vect n (DAST n) -> DAST n -> DAST n -> List DTypeError
ensureType {n} c a t =
	let
		at = fullReduce $ dType c a
	in
	if at == fullReduce t
	then []
	else [DExactTypeError a at t]

total
ensureSimilarType : Vect n (DAST n) -> DAST n -> DAST a -> List DTypeError
ensureSimilarType {n} c a t with (lfreduce $ dType c a)
	ensureSimilarType c a 𝕋 | 𝕋 = []
	ensureSimilarType {n} c a t@(ℂ (DConV nt _ _) _) | at@(ℂ (DConV na _ _) _) =
		if na == nt
		then []
		else [DSimilarTypeError a at t]
	ensureSimilarType {n} c a t | at = [DSimilarTypeError a at t]

-- reverse : DRCtx n m -> DCtx m -> DCtx (n + m)
-- reverse [] c = c
-- reverse {n=S n} {m} (h :: t) c = replace (sym $ plusSuccRightSucc n m) $ reverse t (h :-: c)

total
typeCheck : Vect n (DAST n) -> DAST n -> List DTypeError
typeCheck c (ʌ v) = []
typeCheck c (λ at b) = typeCheck c at ++ ensureType c at 𝕋 ++ typeCheck (map (incr 0) $ at :: c) b
typeCheck c (λT at r) = typeCheck c at ++ ensureType c at 𝕋 ++ typeCheck (map (incr 0) $ at :: c) r ++ ensureType (map (incr 0) $ at :: c) r 𝕋
typeCheck {n} c (f =!= a) =
	typeCheck c f ++
	typeCheck c a ++
	case fullReduce ft of
		λT fat b => ensureType c a fat
		_ => [DSimilarTypeError f ft $ λT at $ 𝕌 "result" 𝕋]
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
typeCheck {n} c (ℙ v (DConV {a} _ ats rt) t f) =
	?typeCheck_ℙ
	-- typeCheck c v ++
	-- ensureSimilarType {a=Z} (reverse ats DCNil) (replace (sym $ plusZeroRightNeutral a) $ rt) 𝕋 ++
	-- ensureSimilarType c v (lfreduce rt) ++
	-- typeCheck c f ++
	-- typeCheck (reverse (elevateRC {gte=LTEZero} ats) c) t ++
	-- ensureType (reverse (elevateRC {gte=LTEZero} ats) c) t (incr' $ dType c f)
typeCheck c (𝔹 t) = typeCheck c t ++ ensureType c t 𝕋
