module Utils

import Data.Fin
import Data.Vect

total
export
finE : Fin n -> {auto lte : LTE n m} -> Fin m
finE {n = Z} f = void $ FinZAbsurd f
finE {n = S Z} (FS f) = void $ FinZAbsurd f
finE {n = S n} {m = Z} f {lte} = void $ succNotLTEzero lte
finE {n = S n} {m = S m} FZ = FZ
finE {n = S$ S$ n} {m = S$ Z} (FS f) {lte = LTESucc lte} = void $ succNotLTEzero lte
finE {n = S$ S$ n} {m = S$ S$ m} (FS f) {lte = LTESucc lte} = FS $ finE f

total
fseq : (a = b) -> (FS a = FS b)
fseq Refl = Refl

public export
data FinOrd : Fin n -> Fin n -> Type where
	FLT : LT (finToNat a) (finToNat b) -> FinOrd a b
	FEQ : a = b -> FinOrd a b
	FGT : GT (finToNat a) (finToNat b) -> FinOrd a b

total
export
fcompare : (a : Fin n) -> (b : Fin n) -> FinOrd a b
fcompare {n=Z} a b = void $ FinZAbsurd a
fcompare {n=S n} FZ FZ = FEQ Refl
fcompare {n=S n} FZ (FS b) = FLT $ LTESucc LTEZero
fcompare {n=S n} (FS a) FZ = FGT $ LTESucc LTEZero
fcompare {n=S n} (FS a) (FS b) with (fcompare a b)
	| FLT lt = FLT $ LTESucc lt
	| FEQ eq = FEQ $ fseq eq
	| FGT gt = FGT $ LTESucc gt

total
export
finD : (f : Fin (S n)) -> {g : Fin (S n)} -> {gt : GT (finToNat f) (finToNat g)} -> Fin n
finD FZ {g} {gt} = void $ succNotLTEzero gt
finD (FS f) = f

total
export
finDown : {l : Fin (S n)} -> (f : Fin (S n)) -> {lt : LT (finToNat f) (finToNat l)} -> Fin n
finDown {l = FZ} _ {lt} = void $ succNotLTEzero lt
finDown {n = Z} {l = FS l} _ = void $ FinZAbsurd l
finDown {n = S n} {l = FS l} FZ = FZ
finDown {n = S n} {l = FS l} (FS f) {lt = LTESucc lt} = FS $ finDown f {lt}

total
export
ltePlus : LTE n m -> LTE (a + n) (a + m)
ltePlus {a=Z} lte = lte
ltePlus {a=S a} lte = LTESucc $ ltePlus lte

total
export
ltePlus' : LTE a (a + n)
ltePlus' {a=Z} = LTEZero
ltePlus' {a=S a} = LTESucc ltePlus'

total
export
nonEmptyNub : NonEmpty l -> NonEmpty (nubBy f l)
nonEmptyNub {l=[]} IsNonEmpty impossible
nonEmptyNub {l=h::t} IsNonEmpty = IsNonEmpty

total
export
nonEmptySort : NonEmpty l -> NonEmpty (sortBy f l)
nonEmptySort {l=[]} IsNonEmpty impossible
nonEmptySort {l=h::t} IsNonEmpty = believe_me $ the (NonEmpty [1, 2]) IsNonEmpty

total
export
nonEmptyMap : NonEmpty l -> NonEmpty (map f l)
nonEmptyMap {l=[]} IsNonEmpty impossible
nonEmptyMap {l=h::t} IsNonEmpty = IsNonEmpty
