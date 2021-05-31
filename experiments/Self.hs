-- self types, dependent elimination for lambda encodings
module Self where

-- core language
type Ix = Int

data Core
  = Var Ix
  | Abs Core
  | App Core Core
  | Pi Core Core
  | Let Core Core Core
  | Self Core
  | In Core
  | Out Core
  | Type

instance Show Core where
  show (Var i) = show i
  show (Abs b) = "(\\" ++ show b ++ ")"
  show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"
  show (Pi t b) = "(" ++ show t ++ " -> " ++ show b ++ ")"
  show (Let t v b) = "(let " ++ show t ++ " = " ++ show v ++ " in " ++ show b ++ ")"
  show (Self b) = "(self " ++ show b ++ ")"
  show (In t) = "(in " ++ show t ++ ")"
  show (Out t) = "(out " ++ show t ++ ")"
  show Type = "*"

-- value domain
type Clos = Val -> Val
type Clos2 = Val -> Val -> Val
type Lvl = Int

type Spine = [Elim]

data Elim
  = EApp Val
  | EOut

data Val
  = VNe Lvl Spine
  | VAbs Clos
  | VPi Val Clos
  | VSelf Clos2
  | VIn Val
  | VType

type Env = [Val]

vvar :: Lvl -> Val
vvar k = VNe k []

-- evaluation
vapp :: Val -> Val -> Val
vapp (VAbs b) v = b v
vapp (VNe h sp) v = VNe h (EApp v : sp)

vout :: Val -> Val
vout (VIn t2) = t2
vout (VNe h sp) = VNe h (EOut : sp)

eval :: Env -> Core -> Val
eval e (Var i) = e !! i
eval e (Abs b) = VAbs $ \v -> eval (v : e) b
eval e (App f a) = vapp (eval e f) (eval e a)
eval e (Pi t b) = VPi (eval e t) $ \v -> eval (v : e) b
eval e (Let t v b) = eval (eval e v : e) b
eval e (Self b) = VSelf $ \t v -> eval (v : t : e) b
eval e (In t2) = VIn (eval e t2)
eval e (Out t) = vout (eval e t)
eval e Type = VType

quoteElim :: Lvl -> Elim -> Core -> Core
quoteElim k (EApp a) t = App t (quote k a)
quoteElim k EOut t = Out t

quote :: Lvl -> Val -> Core
quote k (VNe h sp) = foldr (quoteElim k) (Var (k - (h + 1))) sp
quote k (VAbs b) = Abs $ quote (k + 1) (b (vvar k))
quote k (VPi t b) = Pi (quote k t) $ quote (k + 1) (b (vvar k))
quote k (VSelf b) = Self $ quote (k + 2) (b (vvar k) (vvar (k + 1)))
quote k (VIn t2) = In (quote k t2)
quote k VType = Type

norm :: Core -> Core
norm = quote 0 . eval []

-- conversion checking
convElim :: Lvl -> Elim -> Elim -> Bool
convElim k (EApp v1) (EApp v2) = conv k v1 v2
convElim k EOut EOut = True

conv :: Lvl -> Val -> Val -> Bool
conv k VType VType = True
conv k (VIn a) (VIn b) = conv k a b
conv k (VPi t1 b1) (VPi t2 b2) =
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
conv k (VSelf b1) (VSelf b2) =
  let v = vvar k in
  let w = vvar (k + 1) in
  conv (k + 2) (b1 v w) (b2 v w)
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

check :: Ctx -> Core -> Val -> TC ()
check ctx@(k, ts, vs) (Abs b1) (VPi t b2) =
  let v = vvar k in
  check (k + 1, t : ts, v : vs) b1 (b2 v)
check ctx@(_, _, vs) c@(In b1) ty@(VSelf b2) =
  check ctx b1 (b2 ty (eval vs c))
check ctx@(k, ts, vs) (Let t v b) ty = do
  check ctx t VType
  let ty = eval vs t
  check ctx v ty
  check (k + 1, ty : ts, eval vs v : vs) b ty
check ctx@(k, _, _) c ty = do
  ty' <- synth ctx c
  _ <- test (conv k ty' ty) $ "check failed: " ++ show c ++ " : " ++ show (quote k ty) ++ ", got " ++ show (quote k ty')
  return ()

synth :: Ctx -> Core -> TC Val
synth ctx@(_, ts, _) (Var i) = return $ ts !! i
synth ctx@(k, _, vs) c@(App f a) = do
  ft <- synth ctx f
  case ft of
    VPi t b -> do
      check ctx a t
      return $ b (eval vs a)
    _ -> Left $ "not a pi type in " ++ show c ++ ": " ++ show (quote k ft)
synth ctx@(k, ts, vs) (Pi t b) = do
  check ctx t VType
  let v = vvar k
  check (k + 1, eval vs t : ts, v : vs) b VType
  return VType
synth ctx@(k, ts, vs) (Let t v b) = do
  check ctx t VType
  let ty = eval vs t
  check ctx v ty
  synth (k + 1, ty : ts, eval vs v : vs) b
synth ctx@(k, ts, vs) c@(Self b) = do
  let ty = eval vs c
  check (k + 2, ty : VType : ts, vvar (k + 1) : ty : vs) b VType
  return VType
synth ctx@(k, ts, vs) c@(Out t) = do
  st <- synth ctx t
  case st of
    VSelf b -> return $ b st (eval vs t)
    _ -> Left $ "not a self type in " ++ show c ++ ": " ++ show (quote k st)
synth ctx Type = return VType
synth ctx c = Left $ "failed to synth: " ++ show c

infer :: Core -> TC Core
infer = fmap (quote 0) . synth (0, [], [])

-- testing
ann :: Core -> Core -> Core
ann c t = Let t c (Var 0)

example :: Core
example = Let (Pi Type $ Pi (Var 0) (Var 1)) (Abs $ Abs (Var 0)) (App (Var 0) Type)

-- unit = self (U u). (P : U -> *) -> P (In \P u. u) -> P u
-- unit = self. (1 -> *) -> 0 (In \\0) -> 1 2
unit :: Core
unit = Self $ Pi (Pi (Var 1) Type) $ Pi (App (Var 0) (In $ Abs $ Abs $ Var 0)) $ App (Var 1) (Var 2)

unitv :: Core
unitv = ann (In $ Abs $ Abs $ Var 0) unit

bool :: Core
bool = Self $ Pi (Pi (Var 1) Type) $ Pi (App (Var 0) (In $ Abs $ Abs $ Abs $ Var 1)) $ Pi (App (Var 1) (In $ Abs $ Abs $ Abs $ Var 0)) $ App (Var 2) (Var 3)

true :: Core
true = ann (In $ Abs $ Abs $ Abs $ Var 1) bool

false :: Core
false = ann (In $ Abs $ Abs $ Abs $ Var 0) bool

-- not : Bool -> Bool = \b. out b (\_. Bool) False True
cnot :: Core
cnot = ann (Abs $ App (App (App (Out $ Var 0) (Abs bool)) false) true) (Pi bool bool)

main :: IO ()
main = do
  let c = App cnot true
  print c
  putStrLn $ either id show $ infer c
  print $ norm c
