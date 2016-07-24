module Depling.Decr

import Depling
import Depling.Incr
import Utils
import Data.Fin
import Data.Vect

mutual
	total
	decr_ℙ : Fin (S n) -> DAST n -> DAST (a + (S n)) -> DAST (a + n)
	decr_ℙ {a = Z} rv ra ast = decr rv ra ast
	decr_ℙ {a = S a} {n} rv ra ast = assert_total $ replace (sym $ plusSuccRightSucc _ _) $ decr_ℙ (FS rv) (incr 0 ra) $ replace (plusSuccRightSucc _ _) ast

	total
	export
	decr : Fin (S n) -> DAST n -> DAST (S n) -> DAST n
	decr rv ra (ʌ v) = case fcompare v rv of
		FLT lt => ʌ $ finDown v {lt}
		FEQ eq => ra
		FGT gt => ʌ $ finD v {gt}
	decr rv ra (λ at b) = λ (decr rv ra at) (decr (FS rv) (incr FZ ra) b)
	decr rv ra (λT at rt) = λT (decr rv ra at) (decr (FS rv) (incr FZ ra) rt)
	decr rv ra (f =!= a) = decr rv ra f =!= decr rv ra a
	decr rv ra 𝕋 = 𝕋
	decr rv ra (𝔽 at rt b) =
		𝔽
			(decr (        rv) (                    ra) at)
			(decr (    FS$ rv) (          incr FZ $ ra) rt)
			(decr (FS$ FS$ rv) (incr FZ $ incr FZ $ ra) b )
	decr rv ra (𝕌 n t) = 𝕌 n $ decr rv ra t
	decr rv ra (ℂ cn as) = assert_total $ ℂ cn $ map (decr rv ra) as
	decr rv ra (ℙ v cn t f) = ℙ (decr rv ra v) cn (decr_ℙ rv ra t) (decr rv ra f)
	decr rv ra (𝔹 t) = 𝔹 $ decr rv ra t
