-- simple universe hierarchy
module UnivPoly where

-- core language
type Ix = Int

data Proj = Fst | Snd
  deriving (Eq)

data Term
  = Var Ix
  | Abs Term
  | App Term Term
  | Pi Term Term
  | Let Term Term Term
  | Sigma Term Term
  | Pair Term Term
  | Proj Proj Term
  | U Ix
  | Void
  | Absurd Term
  | UnitType
  | Unit
  | Bool
  | BoolLit Bool
  | BoolInd Ix Term Term Term Term

instance Show Proj where
  show Fst = "fst"
  show Snd = "snd"

instance Show Term where
  show (Var i) = show i
  show (Abs b) = "(\\" ++ show b ++ ")"
  show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"
  show (Pi t b) = "(" ++ show t ++ " -> " ++ show b ++ ")"
  show (Let t v b) = "(let " ++ show t ++ " = " ++ show v ++ " in " ++ show b ++ ")"
  show (Sigma t b) = "(" ++ show t ++ " ** " ++ show b ++ ")"
  show (Pair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (Proj p t) = "(" ++ show p ++ " " ++ show t ++ ")"
  show (U l) = "U" ++ show l
  show Void = "Void"
  show (Absurd t) = "(absurd " ++ show t ++ ")"
  show UnitType = "()"
  show Unit = "[]"
  show Bool = "Bool"
  show (BoolLit b) = show b
  show (BoolInd u p t f b) = "(indBool " ++ show u ++ " " ++ show p ++ " " ++ show t ++ " " ++ show f ++ " " ++ show b ++ ")"

-- value domain
type Clos = Val -> Val
type Lvl = Int

type Spine = [Elim]

data Elim
  = EApp Val
  | EProj Proj
  | EAbsurd
  | EBoolInd Ix Val Val Val

data Val
  = VNe Lvl Spine
  | VAbs Clos
  | VPi Val Clos
  | VSigma Val Clos
  | VPair Val Val
  | VU Ix
  | VVoid
  | VUnitType
  | VUnit
  | VBool
  | VBoolLit Bool

type Env = [Val]

vvar :: Lvl -> Val
vvar k = VNe k []

-- evaluation
vapp :: Val -> Val -> Val
vapp (VAbs b) v = b v
vapp (VNe h sp) v = VNe h (EApp v : sp)

vproj :: Proj -> Val -> Val
vproj Fst (VPair a b) = a
vproj Snd (VPair a b) = b
vproj p (VNe h sp) = VNe h (EProj p : sp)

vabsurd :: Val -> Val
vabsurd (VNe h sp) = VNe h (EAbsurd : sp)

vboolind :: Ix -> Val -> Val -> Val -> Val -> Val
vboolind u p t f (VBoolLit True) = t
vboolind u p t f (VBoolLit False) = f
vboolind u p t f (VNe h sp) = VNe h (EBoolInd u p t f : sp)

eval :: Env -> Term -> Val
eval e (Var i) = e !! i
eval e (Abs b) = VAbs $ \v -> eval (v : e) b
eval e (App f a) = vapp (eval e f) (eval e a)
eval e (Pi t b) = VPi (eval e t) $ \v -> eval (v : e) b
eval e (Sigma t b) = VSigma (eval e t) $ \v -> eval (v : e) b
eval e (Pair a b) = VPair (eval e a) (eval e b)
eval e (Let t v b) = eval (eval e v : e) b
eval e (Proj p t) = vproj p (eval e t)
eval e (U l) = VU l
eval e Void = VVoid
eval e (Absurd t) = vabsurd (eval e t)
eval e UnitType = VUnitType
eval e Unit = VUnit
eval e Bool = VBool
eval e (BoolLit b) = VBoolLit b
eval e (BoolInd u p t f b) = vboolind u (eval e p) (eval e t) (eval e f) (eval e b)

quoteElim :: Lvl -> Elim -> Term -> Term
quoteElim k (EApp v) t = App t (quote k v)
quoteElim k (EProj p) t = Proj p t
quoteElim k EAbsurd t = Absurd t
quoteElim k (EBoolInd u p pt pf) t = BoolInd u (quote k p) (quote k pt) (quote k pf) t 

quote :: Lvl -> Val -> Term
quote k (VNe h sp) = foldr (quoteElim k) (Var (k - (h + 1))) sp
quote k (VAbs b) = Abs $ quote (k + 1) (b (vvar k))
quote k (VPi t b) = Pi (quote k t) $ quote (k + 1) (b (vvar k))
quote k (VSigma t b) = Sigma (quote k t) $ quote (k + 1) (b (vvar k))
quote k (VPair a b) = Pair (quote k a) (quote k b)
quote k (VU l) = U l
quote k VVoid = Void
quote k VUnitType = UnitType
quote k VUnit = Unit
quote k VBool = Bool
quote k (VBoolLit b) = BoolLit b

norm :: Term -> Term
norm = quote 0 . eval []

-- conversion checking
convElim :: Lvl -> Elim -> Elim -> Bool
convElim k (EApp v1) (EApp v2) = conv k v1 v2
convElim k (EProj p1) (EProj p2) = p1 == p2
convElim k EAbsurd EAbsurd = True
convElim k (EBoolInd u1 p1 pt1 pf1) (EBoolInd u2 p2 pt2 pf2) | u1 == u2 =
  conv k p1 p2 && conv k pt1 pt2 && conv k pf1 pf2
convElim _ _ _ = False

conv :: Lvl -> Val -> Val -> Bool
conv k (VU l1) (VU l2) = l1 == l2
conv k VVoid VVoid = True
conv k VUnitType VUnitType = True
conv k VBool VBool = True
conv k (VBoolLit b1) (VBoolLit b2) = b1 == b2
conv k VUnit _ = True
conv k _ VUnit = True
conv k (VPi t1 b1) (VPi t2 b2) =
  let v = vvar k in
  conv k t1 t2 && conv (k + 1) (b1 v) (b2 v)
conv k (VSigma t1 b1) (VSigma t2 b2) =
  let v = vvar k in
  conv k t1 t2 && conv (k + 1) (b1 v) (b2 v)
conv k (VAbs b1) (VAbs b2) =
  let v = vvar k in
  conv (k + 1) (b1 v) (b2 v)
conv k (VAbs b) o =
  let v = vvar k in
  conv (k + 1) (b v) (vapp o v)
conv k o (VAbs b) =
  let v = vvar k in
  conv (k + 1) (vapp o v) (b v)
conv k (VPair a1 b1) (VPair a2 b2) =
  conv k a1 a2 && conv k b1 b2
conv k (VPair a b) v =
  conv k a (vproj Fst v) && conv k b (vproj Snd v)
conv k v (VPair a b) =
  conv k (vproj Fst v) a && conv k (vproj Snd v) b
conv k (VNe h1 sp1) (VNe h2 sp2) | h1 == h2 =
  and $ zipWith (convElim k) sp1 sp2
conv _ _ _ = False

-- bidirectional typechecking
type Types = [Val]
type Ctx = (Lvl, Types, Env)

type TC t = Either String t

test :: Bool -> String -> TC ()
test True _ = return ()
test False msg = Left msg

check :: Ctx -> Term -> Val -> TC ()
check ctx@(k, ts, vs) (Abs b1) (VPi t b2) =
  let v = vvar k in
  check (k + 1, t : ts, v : vs) b1 (b2 v)
check ctx@(k, ts, vs) (Pair t1 t2) (VSigma ty b) = do
  check ctx t1 ty
  check ctx t2 (b (eval vs t1))
check ctx@(k, ts, vs) (Let t v b) ty = do
  _ <- synthU ctx t
  let ty = eval vs t
  check ctx v ty
  check (k + 1, ty : ts, eval vs v : vs) b ty
check ctx (U l1) (VU l2) | l1 < l2 = return ()
check ctx Void (VU _) = return ()
check ctx UnitType (VU _) = return ()
check ctx Bool (VU _) = return ()
check ctx (Absurd t) ty = check ctx t VVoid
check ctx@(k, _, _) c ty = do
  ty' <- synth ctx c
  _ <- test (conv k ty' ty) $ "check failed: " ++ show c ++ " : " ++ show (quote k ty) ++ ", got " ++ show (quote k ty')
  return ()

synthU :: Ctx -> Term -> TC Ix
synthU ctx@(k, _, _) t = do
  ty <- synth ctx t
  case ty of
    VU l -> return l
    _ -> Left $ "not a universe for " ++ show t ++ ": " ++ show (quote k ty)

synth :: Ctx -> Term -> TC Val
synth ctx@(_, ts, _) (Var i) = return $ ts !! i
synth ctx@(k, _, vs) c@(App f a) = do
  ft <- synth ctx f
  case ft of
    VPi t b -> do
      check ctx a t
      return $ b (eval vs a)
    _ -> Left $ "not a pi type in " ++ show c ++ ": " ++ show (quote k ft)
synth ctx@(k, ts, vs) (Pi t b) = do
  l1 <- synthU ctx t
  let v = vvar k
  l2 <- synthU (k + 1, eval vs t : ts, v : vs) b
  return $ VU (max l1 l2)
synth ctx@(k, ts, vs) (Sigma t b) = do
  l1 <- synthU ctx t
  let v = vvar k
  l2 <- synthU (k + 1, eval vs t : ts, v : vs) b
  return $ VU (max l1 l2)
synth ctx@(k, ts, vs) (Let t v b) = do
  _ <- synthU ctx t
  let ty = eval vs t
  check ctx v ty
  synth (k + 1, ty : ts, eval vs v : vs) b
synth ctx@(_, _, vs) (U l) = return $ VU (l + 1)
synth ctx Void = return $ VU 0
synth ctx UnitType = return $ VU 0
synth ctx Unit = return VUnitType
synth ctx Bool = return $ VU 0
synth ctx (BoolLit _) = return VBool
synth ctx@(_, _, vs) (BoolInd u p t f b) = do
  check ctx p (VPi VBool $ \_ -> VU u)
  let motive = eval vs p
  check ctx t (vapp motive $ VBoolLit True)
  check ctx f (vapp motive $ VBoolLit False)
  check ctx b VBool
  return $ vapp motive (eval vs b)
synth ctx@(k, _, vs) c@(Proj p t) = do
  ty <- synth ctx t
  case (ty, p) of
    (VSigma a _, Fst) -> return a
    (VSigma _ b, Snd) -> return $ b (vproj Fst (eval vs t))
    _ -> Left $ "not a sigma type in " ++ show c ++ ": " ++ show (quote k ty)
synth ctx c = Left $ "failed to synth: " ++ show c

infer :: Term -> TC Term
infer = fmap (quote 0) . synth (0, [], [])

-- testing
ann :: Term -> Term -> Term
ann c t = Let t c (Var 0)

idtype :: Term
idtype = Pi (U 0) $ Pi (Var 0) $ Var 1

idterm :: Term
idterm = ann (Abs $ Abs $ Var 0) idtype

nattype :: Term
nattype = Pi (U 0) $ Pi (Var 0) $ Pi (Pi (Var 1) (Var 2)) $ Var 2

natz :: Term
natz = ann (Abs $ Abs $ Abs $ Var 1) nattype

nats :: Term
nats = ann (Abs $ Abs $ Abs $ Abs $ App (Var 0) (App (App (App (Var 3) (Var 2)) (Var 1)) (Var 0))) (Pi nattype nattype)

unitindtype :: Ix -> Term
unitindtype u = Pi (Pi UnitType (U u)) $ Pi (App (Var 0) Unit) $ Pi UnitType $ App (Var 2) (Var 0)

unitind :: Ix -> Term
unitind u = ann (Abs $ Abs $ Abs $ Var 1) (unitindtype u)

cnot :: Term
cnot = ann (Abs $ BoolInd 1 (Abs Bool) (BoolLit False) (BoolLit True) (Var 0)) (Pi Bool Bool)

sumtype :: Term
sumtype = ann (Abs $ Abs $ Sigma Bool $ BoolInd 1 (Abs (U 0)) (Var 2) (Var 1) (Var 0)) (Pi (U 0) $ Pi (U 0) $ U 0)

inl :: Term
inl = ann (Abs $ Abs $ Abs $ Pair (BoolLit True) (Var 0)) (Pi (U 0) $ Pi (U 0) $ Pi (Var 1) $ App (App sumtype (Var 2)) (Var 1))

inr :: Term
inr = ann (Abs $ Abs $ Abs $ Pair (BoolLit False) (Var 0)) (Pi (U 0) $ Pi (U 0) $ Pi (Var 0) $ App (App sumtype (Var 2)) (Var 1))

main :: IO ()
main = do
  let c = Proj Snd (App (App (App inl UnitType) Bool) Unit)
  print c
  putStrLn $ either id show $ infer c
  print $ norm c
