import chorlean.Freer
import chorlean.GVal
import Test.my_utils

#check ReaderT

-- Effect Signature that allows sending and receiving Values of types that implement Serialize
inductive NetEff: Type -> Type 1
| send {μ: Type} [Serialize μ] : Socket -> μ -> NetEff Unit
| recv : Socket ->  (μ: Type) -> [Serialize μ] -> NetEff μ

-- Interpretation of the NetEff Signature in the IO Monad using Sockets
instance: MonadLift (NetEff) IO where
  monadLift x := match x with
  | NetEff.send sock m=> sock.send_val2 m
  | NetEff.recv sock μ => sock.recv_val2 (t:=μ)

-- Freer Monad over the NetEff Signature
@[reducible] def  NetM := Freer (NetEff)

-- auxiliary Effect, sum type of either a net_eff or local_eff
inductive LocalProgramEff (leff:Type -> Type 1): Type -> Type 1
| net_eff: NetEff α -> LocalProgramEff leff α
| local_eff: leff α -> LocalProgramEff leff α

-- A Monad for Local Effects where leff is the Effect Signature
@[reducible] def LocalM (leff: Type -> Type 1) := Freer (LocalProgramEff leff)


-- Lifts a Local effect into the LocalM Monad # note the T for transitiv
instance : MonadLiftT (leff) (LocalProgramEff leff) where
  monadLift x := LocalProgramEff.local_eff x

instance : MonadLiftT (NetEff) (LocalProgramEff leff) where
  monadLift x := LocalProgramEff.net_eff x

-- instance : MonadLiftT (LocalProgramEff leff) (LocalM leff)  where
--   monadLift x := match x with
--   | .local_eff le => MonadLiftT.monadLift le
--   | .net_eff ne => MonadLiftT.monadLift ne


-- Lifts a Local effect into the LocalM Monad # note the T for transitiv
-- instance : MonadLiftT (leff) (LocalM leff) where
--   monadLift x := Effect.ToFreer (LocalProgramEff.local_eff x)

--Lifts a NetEff into the LocalM Monad
instance : MonadLift (NetEff) (LocalM leff) where
  monadLift x := Freer.toFreer (LocalProgramEff.net_eff x)


-- Lifts an LocalProgrameff into a Monad m if both, net and the loc effect can be lifted into the monad
instance [MonadLift eff m] [MonadLift NetEff m]: MonadLiftT (LocalProgramEff eff) m where
  monadLift x := match x with
  | .local_eff le => MonadLift.monadLift le
  | .net_eff ne => MonadLift.monadLift ne

def temp  {α : Type} [Monad m] [MonadLift (LocalProgramEff eff) m] : LocalM eff α → m α
| .Do e c => match e with
    | .local_eff le => do
      let res <- le
      temp (c res)
    | .net_eff ne => do
      let res <- ne
      temp (c res)
  | .Return v => return v

instance [MonadLift (LocalProgramEff eff) m] [Monad m]: MonadLiftT (LocalM eff) m where
  monadLift := temp

-- Lifts a NetM into any LocalM (should not be needed?)
-- instance why: MonadLift (NetM) (LocalM eff) where
--   monadLift x := match x with
--     | .Do n cont => do
--       let res <- n
--       Freer.monadLift (cont res)
--     | .Return v => return v
