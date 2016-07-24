module Depling.Incr

import Depling
import Data.Fin
import Data.Vect

total
incr_var : Fin (S n) -> Fin n -> Fin (S n)
incr_var FZ FZ = FS FZ
incr_var FZ (FS v) = FS $ incr_var FZ v
incr_var (FS i) FZ = FZ
incr_var (FS i) (FS v) = FS $ incr_var i v

mutual
	total
	export
	incr : Fin (S n) -> DAST n -> DAST (S n)
	incr {n = Z} i (ʌ v) = void $ FinZAbsurd v
	incr {n = S n} i (ʌ v) = ʌ $ incr_var i v
	incr i (λ at b) = λ (incr i at) (incr (FS i) b)
	incr i (λT at rt) = λT (incr i at) (incr (FS i) rt)
	incr i (f =!= a) = incr i f =!= incr i a
	incr i 𝕋 = 𝕋
	incr i (𝔽 at rt b) = 𝔽 (incr i at) (incr (FS i) rt) (incr (FS$ FS$ i) b)
	incr i (𝕌 n t) = 𝕌 n (incr i t)
	incr i (ℂ cn as) = assert_total $ ℂ cn $ map (incr i) as
	incr {n} i (ℙ {a} v cn t f) = ℙ (incr i v) cn (replace (plusSuccRightSucc a n) $ incr (replace (sym $ plusSuccRightSucc a n) $ shift a i) t) (incr i f)
	incr i (𝔹 t) = 𝔹 $ incr i t

	total
	export
	incr' : DAST n -> DAST (a + n)
	incr' {a = Z} ast = ast
	incr' {a = S a} ast = incr 0 $ incr' ast
