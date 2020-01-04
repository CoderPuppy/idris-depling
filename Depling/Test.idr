module Main

import Depling
import Depling.TypeCheck
import Depling.PrettyPrint
import Depling.Incr
import Depling.Elevate
import Data.Vect
import Data.Fin
import Utils

lℕℂ : DCon 0
lℕℂ = DConV "ℕ" [] 𝕋

lℕ : DAST n
lℕ = ℂ lℕℂ []

lzℂ : DCon 0
lzℂ = DConV "z" [] lℕ

lz : DAST n
lz = ℂ lzℂ []

lsℂ : DCon 1
lsℂ = DConV "s" [lℕ] lℕ

ls : DAST n
ls = λ lℕ $ ℂ lsℂ [ʌ 0]

lp : DAST n
lp =
	𝔽 lℕ (λT lℕ lℕ) $
		ℙ (ʌ 0) lzℂ (λ lℕ $ ʌ 0) $
		ℙ (ʌ 0) lsℂ (λ lℕ $ ʌ 3 =!= ʌ 1 =!= (ls =!= ʌ 0)) $
		𝔹 (λT lℕ lℕ)

lco : DAST n
lco = λ 𝕋 $ λ (λT (ʌ 0) 𝕋) $ λ (λT (ʌ 1) (ʌ 1 =!= ʌ 0)) $ λ 𝕋 $ λ (λT (ʌ 0) (ʌ 4)) $ λ (ʌ 1) $ ʌ 3 =!= (ʌ 1 =!= ʌ 0)

llℂ : DCon 1
llℂ = DConV "l" [𝕋] 𝕋

ll : DAST n
ll = λ 𝕋 $ ℂ llℂ [ʌ 0]

lnℂ : DCon 1
lnℂ = DConV "n" [𝕋] $ ll =!= ʌ 0

ln : DAST n
ln = λ 𝕋 $ ℂ lnℂ [ʌ 0]

lcℂ : DCon 3
lcℂ = DConV "c" [𝕋, ʌ 0, ll =!= ʌ 1] $ ll =!= ʌ 2

lc : DAST n
lc = λ 𝕋 $ λ (ʌ 0) $ λ (ll =!= ʌ 1) $ ℂ lcℂ [ʌ 2, ʌ 1, ʌ 0]

lrepeat : DAST n
lrepeat = λ 𝕋 $ 𝔽 (ʌ 0) (ll =!= ʌ 1) $ lc =!= ʌ 2 =!= ʌ 0 =!= (ʌ 1 =!= ʌ 0)

lcycle : DAST n
lcycle =
	-- a : Type
	λ 𝕋 $
		-- orig : List a
		λ (ll =!= ʌ 0) $
			-- R : List a -> List a
			-- l : List a
			(𝔽 (ll =!= ʌ 1) (ll =!= ʌ 2) $
				-- a' : Type -- a' = a
				ℙ (ʌ 0) lnℂ (ʌ 2 =!= ʌ 3) $
				-- a' : Type -- a' = a
				-- h : a
				-- t : List a
				ℙ (ʌ 0) lcℂ (lc =!= ʌ 6 =!= ʌ 1 =!= (ʌ 4 =!= ʌ 0)) $
				𝔹 $ ll =!= ʌ 3
			) =!= ʌ 0

lhead : DAST n
lhead = λ 𝕋 $ λ (ll =!= ʌ 0) $ ℙ (ʌ 0) lcℂ (ʌ 1) $ 𝕌 "head of empty list" (ʌ 1)

ltail : DAST n
ltail = λ 𝕋 $ λ (ll =!= ʌ 0) $ ℙ (ʌ 0) lcℂ (ʌ 0) $ ʌ 0

leqℂ : DCon 4
leqℂ = DConV "=" [𝕋, ʌ 0, 𝕋, ʌ 0] 𝕋

leq : DAST n
leq = λ 𝕋 $ λ (ʌ 0) $ λ 𝕋 $ λ (ʌ 0) $ ℂ leqℂ [ʌ 3, ʌ 2, ʌ 1, ʌ 0]

lreflℂ : DCon 2
lreflℂ = DConV "Refl" [𝕋, ʌ 0] $ ℂ leqℂ [ʌ 1, ʌ 0, ʌ 1, ʌ 0]

lrefl : DAST n
lrefl = λ 𝕋 $ λ (ʌ 0) $ ℂ lreflℂ [ʌ 1, ʌ 0]

lThe : DAST n
lThe = λ 𝕋 $ λ (ʌ 0) $ ʌ 0

lPlusSuccRightSucc : DAST n
lPlusSuccRightSucc {n} =
	-- recurse : Nat -> Nat -> Nat
	-- left : Nat
	𝔽 lℕ (λT lℕ lℕ) $
		-- right : Nat
		λ lℕ $
			ℙ (ʌ 1) lzℂ (ℂ lreflℂ [lℕ, ℂ lsℂ [ʌ 0]]) $
			-- left : Nat
			-- ℙ (ʌ 1) lsℂ (
				-- lThe =!= t =!= ℂ lreflℂ [lℕ, ℂ lsℂ [ʌ 0]]
				𝕌 "wat" t
				-- ℙ (ʌ 3 =!= ʌ 0 =!= ʌ 1) lreflℂ (
					-- ℂ lreflℂ [lℕ, ℂ lsℂ [ʌ 0]]
				-- ) $
				-- 𝕌 "wat" $ elevate {gte=ltePlus'' {n=S$ S$ S$ n} {a=1}} t
			-- ) $
			-- 𝕌 "wat" t
	where
	t : DAST (S$ S$ S$ n)
	--  ℂ  =   [Nat, plus   left    ℂ succ [right], Nat, ℂ succ [plus   left    right]]
	t = ℂ leqℂ [lℕ , lp =!= ʌ 1 =!= ℂ lsℂ  [ʌ 0  ], lℕ , ℂ lsℂ  [lp =!= ʌ 1 =!= ʌ 0  ]]

ltest' : DAST n
ltest' = λ (ℂ leqℂ [lℕ, lz, lℕ, lz]) $ ʌ 0

ltest : DAST n
ltest = ltest' =!= ℂ lreflℂ [𝕋, 𝕋]

ppTypeError : DTypeError -> String
ppTypeError (DTypeErrorV e ts) =
	(pp_n DPOpen [] $ replace (sym $ plusZeroRightNeutral _) e) ++ ":\n"
	++ (unlines $ map (("  " ++) . pp_n DPOpen [] . replace (sym $ plusZeroRightNeutral _)) ts)

main : IO ()
main = putStrLn $ pp DPOpen [] $ lPlusSuccRightSucc
