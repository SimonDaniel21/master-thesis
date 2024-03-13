import chorlean.Freer
import chorlean.GVal
import Test.my_utils

#check ReaderT

-- Effect Signature that allows sending and receiving Values of types that implement Serialize
-- inductive NetEff_: Type -> Type 1
-- | send {μ: Type} [Serialize μ] : Socket -> μ -> NetEff Unit
-- | recv : Socket ->  (μ: Type) -> [Serialize μ] -> NetEff μ

inductive NetEff (δ:Type): Type -> Type 1
| send {μ: Type} [Serialize μ] : δ -> μ -> NetEff δ Unit
| recv : δ ->  (μ: Type) -> [Serialize μ] -> NetEff δ μ

-- Interpretation of the NetEffOld Signature in the IO Monad using Sockets
-- instance: MonadLift (NetEff) IO where
--   monadLift x := match x with
--   | NetEff.send sock m=> sock.send_val2 m
--   | NetEff.recv sock μ => sock.recv_val2 (t:=μ)

instance NetEPP {δ:Type} (ep: δ) [FinEnum δ] [Repr δ] (as: δ × δ -> Address := default_adress): MonadLiftT (NetEff δ) IO where
  monadLift x := match x with
  | NetEff.send r m=> do
    IO.println s!"sent value to {reprName r} {Serialize.pretty m}"
    let sock <-  (as ⟨ep, r⟩ ).connect_to
    sock.send_val2 m
    sock.close

  | NetEff.recv s μ => do
    let sock <- (as ⟨s, ep⟩).listen_on
    let res <- sock.recv_val2
    sock.close
    IO.println s!"recv value from {reprName s} {Serialize.pretty res}"
    return res

-- Freer Monad over the NetEffOld Signature
@[reducible] def NetM δ := Freer (NetEff δ)



-- auxiliary Effect, sum type of either a net_eff or local_eff

@[reducible] def LocalProgramEff δ (leff:Type -> Type 1) := SumEff (NetEff δ) leff

-- A Monad for Local Effects where leff is the Effect Signature
@[reducible] def LocalM δ (leff: Type -> Type 1) := Freer (LocalProgramEff δ leff)

def IOe (a:Type) := IO a

-- effect for arbitrary IO
inductive IOEff: Type -> Type 1
| io: IO a -> IOEff a

instance IOeffLift: MonadLift (IOEff) IO where
  monadLift x := match x with
  | IOEff.io e => e

-- class Network {δ:Type} (ep: δ) where
--   com {μ} [Serialize μ]: {s: δ} -> GVal s ep μ -> (r: δ) -> NetM δ (GVal r ep μ)

-- class Network2 {δ:Type} (ep: δ) where
--   com {μ} [Serialize μ]: {s: δ} -> GVal s ep μ -> (r: δ) -> NetEff (GVal r ep μ)


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
