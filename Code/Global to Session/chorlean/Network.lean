import chorlean.Freer
import chorlean.GVal
import Test.my_utils

#check ReaderT

-- Effect Signature that allows sending and receiving Values of types that implement Serialize
inductive NetEffOld: Type -> Type 1
| send {μ: Type} [Serialize μ] : Socket -> μ -> NetEffOld Unit
| recv : Socket ->  (μ: Type) -> [Serialize μ] -> NetEffOld μ

inductive NetEff (δ:Type): Type -> Type 1
| send {μ: Type} [Serialize μ] : δ -> μ -> NetEff δ Unit
| recv : δ ->  (μ: Type) -> [Serialize μ] -> NetEff δ μ


-- Interpretation of the NetEffOld Signature in the IO Monad using Sockets
instance: MonadLift (NetEffOld) IO where
  monadLift x := match x with
  | NetEffOld.send sock m=> sock.send_val2 m
  | NetEffOld.recv sock μ => sock.recv_val2 (t:=μ)

-- Freer Monad over the NetEffOld Signature
@[reducible] def  NetM := Freer (NetEffOld)
@[reducible] def  NetM2 (δ:Type) := Freer (NetEff δ)



-- auxiliary Effect, sum type of either a net_eff or local_eff

@[reducible] def LocalProgramEff  (leff:Type -> Type 1) := SumEff NetEffOld leff
@[reducible] def LocalProgramEff2  (leff:Type -> Type 1) (δ:Type) := SumEff (NetEff δ) leff

-- A Monad for Local Effects where leff is the Effect Signature
@[reducible] def LocalM (leff: Type -> Type 1) := Freer (LocalProgramEff leff)
@[reducible] def LocalM2 (leff: Type -> Type 1) (δ:Type) := Freer (LocalProgramEff2 leff δ)



def IOe (a:Type) := IO a

-- effect for arbitrary IO
inductive IOEff: Type -> Type 1
| io: IO a -> IOEff a

instance IOeffLift: MonadLift (IOEff) IO where
  monadLift x := match x with
  | IOEff.io e => e

class Network {δ:Type} (ep: δ) where
  com {μ} [Serialize μ]: {s: δ} -> GVal s ep μ -> (r: δ) -> NetM (GVal r ep μ)

instance NetEpp {δ:Type} (socks: δ -> Socket): MonadLiftT (NetEff δ) IO where
  monadLift x := match x with
  | NetEff.send receiver m => (socks receiver).send_val2 m
  | NetEff.recv sender μ => (socks sender).recv_val2 (t:=μ)

-- Lifts a Local effect into the LocalM Monad # note the T for transitiv


-- instance : MonadLiftT (LocalProgramEff leff) (LocalM leff)  where
--   monadLift x := match x with
--   | .local_eff le => MonadLiftT.monadLift le
--   | .net_eff ne => MonadLiftT.monadLift ne


-- Lifts a Local effect into the LocalM Monad # note the T for transitiv
-- instance : MonadLiftT (leff) (LocalM leff) where
--   monadLift x := Effect.ToFreer (LocalProgramEff.local_eff x)

--Lifts a NetEffOld into the LocalM Monad


-- Lifts an LocalProgrameff into a Monad m if both, net and the loc effect can be lifted into the monad


-- Lifts a NetM into any LocalM (should not be needed?)
-- instance why: MonadLift (NetM) (LocalM eff) where
--   monadLift x := match x with
--     | .Do n cont => do
--       let res <- n
--       Freer.monadLift (cont res)
--     | .Return v => return v
