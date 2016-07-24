module Depling

import Data.Vect
import Debug.Trace
import Utils

infixl 10 =!=
mutual
	public export
	data DAST : Nat -> Type where
		ʌ : Fin n -> DAST n
		λ : DAST n -> DAST (S n) -> DAST n
		λT : DAST n -> DAST (S n) -> DAST n
		(=!=) : DAST n -> DAST n -> DAST n
		𝕋 : DAST n
		𝔽 : DAST n -> DAST (S n) -> DAST (S$ S$ n) -> DAST n
		𝕌 : String -> DAST n -> DAST n
		ℂ : DCon a -> Vect a (DAST n) -> DAST n
		ℙ : DAST n -> DCon a -> DAST (a + n) -> DAST n -> DAST n
		𝔹 : DAST n -> DAST n
	
	public export
	data DCon : Nat -> Type where
		DConV : String -> DRCtx a 0 -> DAST a -> DCon a
	
	public export
	data DRCtx : Nat -> Nat -> Type where
		Nil : DRCtx Z n
		(::) : DAST n -> DRCtx l (S n) -> DRCtx (S l) n

Show (Fin n) where
	show = show . finToNat

Show (DAST n) where
	showPrec d (ʌ v) = show v
	showPrec d (λ at b) = showParens (d > Open) $ "λ" ++ showPrec Eq at ++ "=" ++ showPrec Open b
	showPrec d (λT at rt) = showParens (d > Open) $ "λ" ++ showPrec Eq at ++ ":" ++ showPrec Open rt
	showPrec d (f =!= a) = showParens (d >= App) $ showPrec Eq f ++ "!" ++ showPrec App a
	showPrec d 𝕋 = "Type"
	showPrec d (𝔽 at rt b) = showParens (d > Open) $ "𝔽" ++ showPrec Eq at ++ "=" ++ showPrec Open b
	showPrec d (𝕌 n t) = showParens (d > Open) $ "𝕌" ++ n ++ ":" ++ showPrec Open t
	showPrec d (ℂ (DConV n ats rt) as) = "ℂ" ++ n ++ "(" ++ (pack $ intercalate [',', ' '] $ toList $ map (unpack . showPrec Open) as) ++ ")"
	showPrec d (ℙ v (DConV n ats rt) t f) = "ℙ(" ++ showPrec Eq v ++ " of " ++ n ++ " then " ++ showPrec Eq t ++ " else " ++ showPrec Eq f ++ ")"
	showPrec d (𝔹 t) = "𝔹(" ++ showPrec Open t ++ ")"

mutual
	export Eq (DAST n) where
		(ʌ a) == (ʌ b) = a == b
		(λ aa ba) == (λ ab bb) = aa == ab && ba == bb
		(λT aa ra) == (λT ab rb) = aa == ab && ra == rb
		(fa =!= aa) == (fb =!= ab) = fa == fb && aa == ab
		𝕋 == 𝕋 = True
		(𝔽 aa ra fa) == (𝔽 ab rb fb) = aa == ab && ra == rb && fa == fb
		(𝕌 na ta) == (𝕌 nb tb) = na == nb && ta == tb
		(ℂ {a=aa} cna asa) == (ℂ {a=ab} cnb asb) = assert_total $ aa == ab && cna == believe_me cnb && asa == believe_me asb
		(ℙ {a=aa} va cna ta fa) == (ℙ {a=ab} vb cnb tb fb) = assert_total $ aa == ab && va == vb && cna == believe_me cnb && ta == believe_me tb && fa == fb
		(𝔹 ta) == (𝔹 tb) = ta == tb
		_ == _ = False

	export Eq (DCon a) where
		(DConV na atsa rta) == (DConV nb atsb rtb) = na == nb && atsa == atsb && rta == rtb
	
	export Eq (DRCtx l n) where
		Nil == Nil = True
		(ha :: ta) == (hb :: tb) = assert_total $ ha == hb && ta == tb
		_ == _ = False

total
export
dAppN : DAST n -> List (DAST n) -> DAST n
dAppN f [] = f
dAppN f (h :: t) = dAppN (f =!= h) t

total
export
dLamN : {a : Nat} -> {n : Nat} -> DRCtx a n -> DAST (a + n) -> DAST n
dLamN {a=Z} [] rt = rt
dLamN {a=S a} {n} (h :: t) rt = λ h $ dLamN t $ replace (plusSuccRightSucc a n) $ rt
