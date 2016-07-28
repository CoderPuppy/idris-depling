module Depling.Replace

import Depling
import Depling.Incr
import Utils
import Data.Fin
import Data.Vect

mutual
	total
	dReplace' : DAST n -> DAST n -> DAST n -> DAST n
	dReplace' rp ra (ʌ v) = ʌ v
	dReplace' rp ra (λ at b) = λ (dReplace rp ra at) (dReplace (incr FZ rp) (incr FZ ra) b)
	dReplace' rp ra (λT at rt) = λT (dReplace rp ra at) (dReplace (incr FZ rp) (incr FZ ra) rt)
	dReplace' rp ra (f =!= a) = dReplace rp ra f =!= dReplace rp ra a
	dReplace' rp ra 𝕋 = 𝕋
	dReplace' rp ra (𝔽 at rt b) =
		𝔽
			(dReplace (                    rp) (                    ra) at)
			(dReplace (          incr FZ $ rp) (          incr FZ $ ra) rt)
			(dReplace (incr FZ $ incr FZ $ rp) (incr FZ $ incr FZ $ ra) b )
	dReplace' rp ra (𝕌 n t) = 𝕌 n $ dReplace rp ra t
	dReplace' rp ra (ℂ cn as) = assert_total $ ℂ cn $ map (dReplace rp ra) as
	dReplace' rp ra (ℙ v cn t f) = ℙ (dReplace rp ra v) cn (dReplace (incr' rp) (incr' ra) t) (dReplace rp ra f)
	dReplace' rp ra (𝔹 t) = 𝔹 $ dReplace rp ra t
	
	total
	export
	dReplace : DAST n -> DAST n -> DAST n -> DAST n
	dReplace rp ra a = if a == rp then ra else dReplace' rp ra a
