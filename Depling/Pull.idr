module Depling.Pull

import Depling
import Data.Fin
import Data.Vect
import Utils

mutual
	total
	pull_ℙ : Fin (S n) -> DAST (a + (S n)) -> Maybe (DAST (a + n))
	pull_ℙ {a=Z} pv ast = pull pv ast
	pull_ℙ {a=S a} {n} pv ast =
		assert_total $
		replace {P=Maybe . DAST} (sym $ plusSuccRightSucc _ _) $
		pull_ℙ (FS pv) $
		replace (plusSuccRightSucc _ _) $
		ast

	total
	export
	pull : Fin (S n) -> DAST (S n) -> Maybe (DAST n)
	pull pv (ʌ v) = case fcompare v pv of
		FLT lt => Just $ ʌ $ finDown v {lt}
		FEQ eq => Nothing
		FGT gt => Just $ ʌ $ finD v {gt}
	pull pv (λ at b) = do
		at' <- pull pv at
		b' <- pull (FS pv) b
		pure $ λ at' b'
	pull pv (λT at rt) = do
		at' <- pull pv at
		rt' <- pull (FS pv) rt
		pure $ λT at' rt'
	pull pv (f =!= a) = do
		f' <- pull pv f
		a' <- pull pv a
		pure $ f' =!= a'
	pull pv 𝕋 = Just 𝕋
	pull pv (𝔽 at rt b) = do
		at' <- pull          pv  at
		rt' <- pull (FS$     pv) rt
		b'  <- pull (FS$ FS$ pv) b
		pure $ 𝔽 at' rt' b'
	pull pv (𝕌 n t) = do
		t' <- pull pv t
		pure $ 𝕌 n t'
	pull pv (ℂ cn as) = do
		as' <- sequence $ map (assert_total $ pull pv) as
		pure $ ℂ cn as'
	pull pv (ℙ v cn t f) = do
		v' <- pull pv v
		t' <- pull_ℙ pv t
		f' <- pull pv f
		pure $ ℙ v' cn t' f'
	pull pv (𝔹 t) = do
		t' <- pull pv t
		pure $ 𝔹 t'
