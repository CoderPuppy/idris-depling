module Depling.PrettyPrint

import Depling
import Control.Monad.State
import Data.Vect

total
pp_pull : State (Stream String) String
pp_pull = do
	st <- get
	put $ Prelude.Stream.tail st
	pure $ head st

public export
data DPrec = DPOpen | DPApp | DPSingle
Eq DPrec where
	DPOpen == DPOpen = True
	DPApp == DPApp = True
	DPSingle == DPSingle = True
	_ == _ = True

Ord DPrec where
	compare DPOpen DPOpen = EQ
	compare DPApp DPApp = EQ
	compare DPSingle DPSingle = EQ
	compare DPOpen b = LT
	compare a DPOpen = GT
	compare a DPSingle = LT
	compare DPSingle b = GT

total
mapM : Monad m => (a -> m b) -> List a -> m (List b)
mapM f [] = pure []
mapM f (h :: t) = (::) <$> f h <*> mapM f t

total
vmapM : Monad m => (a -> m b) -> Vect n a -> m (Vect n b)
vmapM f [] = pure []
vmapM f (h :: t) = (::) <$> f h <*> vmapM f t

mutual
	total
	pp_ℙ : Vect n String -> DAST n -> DAST n -> State (Stream String) String
	pp_ℙ c ov p@(ℙ v (DConV {a} n ats rt) t f) =
		if ov == v
		then do
			names <- vmapM (const pp_pull) $ replicate a ()
			t' <- pp' DPOpen (reverse names ++ c) t
			f' <- pp_ℙ c ov f
			pure $ "ℂ" ++ n ++ "(" ++ (pack $ intercalate [',', ' '] $ map unpack $ toList names) ++ ") => " ++ t' ++ " ;; " ++ f'
		else do
			p' <- assert_total $ pp' DPOpen c p
			pure $ "_ => " ++ p'
	pp_ℙ c _ a = do
		a' <- assert_total $ pp' DPOpen c a
		pure $ "_ => " ++ a'

	total
	pp' : DPrec -> Vect n String -> DAST n -> State (Stream String) String
	pp' d c (ʌ v) = pure $ index v c
	pp' d c (λ at b) = do
		name <- pp_pull
		at' <- pp' DPOpen c at
		b <- pp' DPOpen (name :: c) b
		pure $ showParens (d > DPOpen) $ "\\(" ++ name ++ " : " ++ at' ++ ") => " ++ b
	pp' d c (λT at rt) = do
		name <- pp_pull
		at' <- pp' DPOpen c at
		rt' <- pp' DPOpen (name :: c) rt
		pure $ showParens (d > DPOpen) $ "(" ++ name ++ " : " ++ at' ++ ") -> " ++ rt'
	pp' d c (f =!= a) = do
		f' <- pp' DPApp c f
		a' <- pp' DPSingle c a
		pure $ showParens (d > DPApp) $ f' ++ " " ++ a'
	pp' d c 𝕋 = pure $ "Type"
	pp' d c (𝔽 at rt b) = do
		rName <- pp_pull
		aName' <- pp_pull
		at'' <- pp' DPOpen c at
		rt'' <- pp' DPOpen (aName' :: c) rt
		aName <- pp_pull
		at' <- pp' DPOpen c at
		b' <- pp' DPOpen (aName :: rName :: c) b
		pure $ showParens (d > DPOpen) $ "𝔽 (" ++ rName ++ " : (" ++ aName' ++ " : " ++ at'' ++ ") -> " ++ rt'' ++ ") (" ++ aName ++ " : " ++ at' ++ ") => " ++ b'
	pp' d c (𝕌 n t) = do
		t' <- pp' DPOpen c t
		pure $ showParens (d > DPOpen) $ "𝕌 " ++ n ++ " : " ++ t'
	pp' d c (ℂ (DConV n ats rt) as) = do
		as' <- assert_total $ mapM (pp' DPApp c) $ toList as
		pure $ "ℂ" ++ n ++ "(" ++ (pack $ intercalate [',', ' '] $ map unpack as') ++ ")"
	pp' d c p@(ℙ v (DConV {a} n ats rt) t f) = do
		v' <- pp' DPApp c v
		p' <- pp_ℙ c v p
		pure $ showParens (d > DPOpen) $ "case " ++ v' ++ " of " ++ p'
	pp' d c (𝔹 t) = do
		t' <- pp' DPOpen c t
		pure $ showParens (d > DPOpen) $ "𝔹 : " ++ t'

total
pp_next : String -> String
pp_next "" = "a"
pp_next p with (assert_total $ strHead p)
	| 'z' = assert_total $ strCons 'a' $ pp_next $ strTail p
	| c = assert_total $ strCons (succ c) $ strTail p

total
pp_names : Stream String
pp_names = map reverse $ iterate pp_next "a"

total
export
pp : DPrec -> Vect n String -> DAST n -> String
pp d c a = fst $ runState (pp' d c a) pp_names

total
pp_n' : DPrec -> Vect n String -> DAST (m + n) -> State (Stream String) String
pp_n' {m=Z} d c a = pp' d c a
pp_n' {m=S m} d c a = assert_total $ do
	name <- pp_pull
	pp_n' {m} d (name :: c) (replace (plusSuccRightSucc _ _) a)

total
export
pp_n : DPrec -> Vect n String -> DAST (m + n) -> String
pp_n d c a = fst $ runState (pp_n' d c a) pp_names
