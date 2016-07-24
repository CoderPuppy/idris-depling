module Depling.Reduce

import Depling
import Depling.Decr
import Depling.Incr
import Data.Fin
import Data.Vect

total
reduce_ℙ : Vect a (DAST n) -> DAST (a + n) -> DAST n
reduce_ℙ [] ast = ast
reduce_ℙ (h :: t) ast = reduce_ℙ t $ decr 0 (incr' h) ast

total
reduce_to : DAST n -> DAST n -> DAST n
reduce_to p (𝔹 t) = p
reduce_to _ r = r

total
export
reduce : DAST n -> DAST n
reduce p@((λ at b) =!= a) = reduce_to p $ decr 0 a b
reduce p@((λT at rt) =!= a) = reduce_to p $ decr 0 a rt
reduce p@(f@(𝔽 at rt b) =!= a) = reduce_to p $ decr 0 f $ decr 0 (incr 0 a) b
reduce p@(ℙ {a=ap} (ℂ {a=ac} cnc as) cnp t f) =
	if ac == ap && cnc == believe_me cnp
	then reduce_to p $ reduce_ℙ (reverse as) $ believe_me t
	else reduce_to p f
reduce (ʌ v) = ʌ v
reduce (λ at b) = λ (reduce at) (reduce b)
reduce (λT at rt) = λT (reduce at) (reduce rt)
reduce (f =!= a) = reduce f =!= reduce a
reduce 𝕋 = 𝕋
reduce (𝔽 at rt b) = 𝔽 (reduce at) (reduce rt) (reduce b)
reduce (𝕌 n t) = 𝕌 n (reduce t)
reduce (ℂ cn as) = assert_total $ ℂ cn $ map reduce as
reduce (ℙ v cn t f) = ℙ (reduce v) cn (reduce t) (reduce f)
reduce (𝔹 t) = 𝔹 $ reduce t

%assert_total
export
fullReduce : DAST n -> DAST n
fullReduce a = tick (reduce a) [a]
	where
		tick : DAST n -> List (DAST n) -> DAST n
		tick r o = if elem r o then r else tick (reduce r) (r :: o)

export
fullReduce' : DAST n -> DAST n
fullReduce' a = tick (reduce a) a
	where
		tick : DAST n -> DAST n -> DAST n
		tick r o = if r == o then r else tick (reduce r) r

-- lazy reduce: reduces to weak head normal form
total
export
lreduce : DAST n -> DAST n
lreduce p@((λ at b) =!= a) = reduce_to p $ decr 0 a b
lreduce p@((λT at rt) =!= a) = reduce_to p $ decr 0 a rt
lreduce p@(f@(𝔽 at rt b) =!= a) = reduce_to p $ decr 0 f $ decr 0 (incr 0 a) b
lreduce p@(ℙ {a=ap} (ℂ {a=ac} cnc as) cnp t f) =
	 if ac == ap && cnc == believe_me cnp
	 then reduce_to p $ reduce_ℙ (reverse as) $ believe_me t
	 else reduce_to p f
lreduce (f =!= a) = lreduce f =!= a
lreduce (ℙ v cn t f) = ℙ (lreduce v) cn t f
lreduce a = a

%assert_total
export
lfreduce : DAST n -> DAST n
lfreduce a = tick (lreduce a) a
	where
		tick : DAST n -> DAST n -> DAST n
		tick r o = if r == o then r else tick (lreduce r) r
