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
abbrev NetM := Freer (NetEff)

-- def send (sock:Socket) (v:μ) [Serialize μ]: NetM Unit := Effect.ToFreer (NetEff.send sock v)
-- def recv (sock:Socket) {μ:Type} [Serialize μ]: NetM μ := Effect.ToFreer (NetEff.recv sock μ)

-- auxiliary Effect, sum type of either a net_eff or local_eff
inductive LocalProgramEff (leff:Type -> Type 1): Type -> Type 1
| net_eff: NetEff α -> LocalProgramEff leff α
| local_eff: leff α -> LocalProgramEff leff α

-- A Monad for Local Effects where leff is the Effect Signature
abbrev LocalM (leff: Type -> Type 1) := Freer (LocalProgramEff leff)


instance [MonadLift leff NetM]: MonadLift (LocalProgramEff leff) (NetM) where
  monadLift x := match x with
  | .local_eff le => MonadLift.monadLift le
  | .net_eff ne => Effect.ToFreer ne (Eff:=NetEff)

-- Lifts a Local into the LocalM Monad
instance : MonadLift (leff) (LocalM leff) where
  monadLift x := Effect.ToFreer (LocalProgramEff.local_eff x)

-- Lifts a NetEff into the LocalM Monad
instance : MonadLift (NetEff) (LocalM leff) where
  monadLift x := Effect.ToFreer (LocalProgramEff.net_eff x)


-- Lifts an LocalProgrameff into a Monad m if both, net and the loc effect can be lifted into the monad
instance [MonadLift eff m] [MonadLift NetEff m]: MonadLift (LocalProgramEff eff) m where
  monadLift x := match x with
  | .local_eff le => MonadLift.monadLift le
  | .net_eff ne => MonadLift.monadLift ne

-- Lifts a NetM into any LocalM (should not be needed?)
instance why: MonadLift (NetM) (LocalM eff) where
  monadLift x := match x with
    | .Do n cont => do
      let res <- MonadLift.monadLift n
      Freer.monadLift (cont res)
    | .Return v => return v
