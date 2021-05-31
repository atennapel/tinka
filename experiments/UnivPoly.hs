-- universe polymorphism
-- WARNING: this implementation is completely wrong
module UnivPoly where

-- core language
type Ix = Int

data Term
  = Var Ix
  | Abs Term
  | App Term Term
  | Pi Term Term
  | Let Term Term Term
  | Level
  | L0
  | LS Term
  | LOmega
  | LMax Term Term
  | U Term

instance Show Term where
  show (Var i) = show i
  show (Abs b) = "(\\" ++ show b ++ ")"
  show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"
  show (Pi t b) = "(" ++ show t ++ " -> " ++ show b ++ ")"
  show (Let t v b) = "(let " ++ show t ++ " = " ++ show v ++ " in " ++ show b ++ ")"
  show Level = "Level"
  show L0 = "L0"
  show (LS l) = "(LS " ++ show l ++ ")"
  show LOmega = "LOmega"
  show (LMax a b) = "(LMax " ++ show a ++ " " ++ show b ++ ")"
  show (U l) = "(U " ++ show l ++ ")"

-- value domain
type Clos = Val -> Val
type Lvl = Int

type Spine = [Elim]

data Elim
  = EApp Val
  | ELMax Val

data Val
  = VNe Lvl Spine
  | VAbs Clos
  | VPi Val Clos
  | VLevel
  | VL0
  | VLS Val
  | VLOmega
  | VU Val

type Env = [Val]

vvar :: Lvl -> Val
vvar k = VNe k []

-- evaluation
vapp :: Val -> Val -> Val
vapp (VAbs b) v = b v
vapp (VNe h sp) v = VNe h (EApp v : sp)

vlmax :: Val -> Val -> Val
vlmax VL0 l = l
vlmax l VL0 = l
vlmax (VLS l1) (VLS l2) = VLS (vlmax l1 l2)
vlmax VLOmega _ = VLOmega
vlmax _ VLOmega = VLOmega
vlmax (VNe h sp) l = VNe h (ELMax l : sp)
vlmax l (VNe h sp) = VNe h (ELMax l : sp)

eval :: Env -> Term -> Val
eval e (Var i) = e !! i
eval e (Abs b) = VAbs $ \v -> eval (v : e) b
eval e (App f a) = vapp (eval e f) (eval e a)
eval e (Pi t b) = VPi (eval e t) $ \v -> eval (v : e) b
eval e (Let t v b) = eval (eval e v : e) b
eval e Level = VLevel
eval e L0 = VL0
eval e (LS l) = VLS (eval e l)
eval e LOmega = VLOmega
eval e (LMax a b) = vlmax (eval e a) (eval e b)
eval e (U l) = VU (eval e l)

quoteElim :: Lvl -> Elim -> Term -> Term
quoteElim k (EApp v) t = App t (quote k v)
quoteElim k (ELMax v) t = LMax t (quote k v)

quote :: Lvl -> Val -> Term
quote k (VNe h sp) = foldr (quoteElim k) (Var (k - (h + 1))) sp
quote k (VAbs b) = Abs $ quote (k + 1) (b (vvar k))
quote k (VPi t b) = Pi (quote k t) $ quote (k + 1) (b (vvar k))
quote k VLevel = Level
quote k VL0 = L0
quote k (VLS l) = LS (quote k l)
quote k VLOmega = LOmega
quote k (VU l) = U (quote k l)

norm :: Term -> Term
norm = quote 0 . eval []

-- conversion checking
convElim :: Lvl -> Elim -> Elim -> Bool
convElim k (EApp v1) (EApp v2) = conv k v1 v2
convElim k (ELMax v1) (ELMax v2) = conv k v1 v2

conv :: Lvl -> Val -> Val -> Bool
conv k VLevel VLevel = True
conv k VL0 VL0 = True
conv k (VLS l1) (VLS l2) = conv k l1 l2
conv k VLOmega VLOmega = True
conv k (VU l1) (VU l2) = conv k l1 l2
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
check ctx@(k, ts, vs) (Let t v b) ty = do
  _ <- synthU ctx t
  let ty = eval vs t
  check ctx v ty
  check (k + 1, ty : ts, eval vs v : vs) b ty
check ctx@(k, _, _) c ty = do
  ty' <- synth ctx c
  _ <- test (conv k ty' ty) $ "check failed: " ++ show c ++ " : " ++ show (quote k ty) ++ ", got " ++ show (quote k ty')
  return ()

synthU :: Ctx -> Term -> TC Val
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
  return $ VU (vlmax l1 l2)
synth ctx@(k, ts, vs) (Let t v b) = do
  _ <- synthU ctx t
  let ty = eval vs t
  check ctx v ty
  synth (k + 1, ty : ts, eval vs v : vs) b
synth ctx Level = return $ VU VLOmega
synth ctx L0 = return VLevel
synth ctx (LS l) = do
  check ctx l VLevel
  return VLevel
synth ctx LOmega = return VLevel
synth ctx (LMax l1 l2) = do
  check ctx l1 VLevel
  check ctx l2 VLevel
  return VLevel
synth ctx@(_, _, vs) (U l) = do
  check ctx l VLevel
  let vl = eval vs l
  case vl of
    VLOmega -> Left $ "U omega does not have a type"
    _ -> return $ VU (VLS $ eval vs l)
synth ctx c = Left $ "failed to synth: " ++ show c

infer :: Term -> TC Term
infer = fmap (quote 0) . synth (0, [], [])

-- testing
ann :: Term -> Term -> Term
ann c t = Let t c (Var 0)

idtype :: Term
idtype = Pi Level $ Pi (U (Var 0)) $ Pi (Var 0) $ Var 1

idterm :: Term
idterm = ann (Abs $ Abs $ Abs $ Var 0) idtype

main :: IO ()
main = do
  let c = App (App idterm (LS L0)) (U L0)
  print c
  putStrLn $ either id show $ infer c
  print $ norm c
