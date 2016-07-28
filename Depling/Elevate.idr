module Depling.Elevate

import Depling
import Utils
import Data.Fin
import Data.Vect

total
export
elevate : {auto gte : GTE m n} -> DAST n -> DAST m
elevate (ʌ v) = ʌ $ finE v
elevate {gte} (λ at b) = λ (elevate at) (elevate {gte=LTESucc gte} b)
elevate {gte} (λT at rt) = λT (elevate at) (elevate {gte=LTESucc gte} rt)
elevate (f =!= a) = elevate f =!= elevate a
elevate 𝕋 = 𝕋
elevate {gte} (𝔽 at rt b) = 𝔽 (elevate at) (elevate rt) (elevate {gte=LTESucc$ LTESucc$ gte} b)
elevate (𝕌 n t) = 𝕌 n (elevate t)
elevate (ℂ cn as) = assert_total $ ℂ cn (map elevate as)
elevate {n} {m} {gte} (ℙ v cn t f) = ℙ (elevate v) cn (elevate {gte = ltePlus gte} t) (elevate f)
elevate (𝔹 t) = 𝔹 (elevate t)

total
export
elevateRC : {auto gte : GTE m n} -> DRCtx a n -> DRCtx a m
elevateRC [] = []
elevateRC {gte} (h :: t) = elevate h :: elevateRC {gte = LTESucc gte} t
