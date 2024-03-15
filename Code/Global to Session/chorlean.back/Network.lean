import chorlean.Freer
import chorlean.GVal
import Test.my_utils

#check ReaderT


variable {α β: Type} -- alpha beta als normaler Type
variable {δ: Type} [DecidableEq δ]  -- delta als Location Type
variable (ep: δ)   -- delta als Location Type
variable {μ: Type} [Serialize μ]  -- mu wegen msg Type

-- Effect Signature that allows sending and receiving Values of types that implement Serialize
-- inductive NetEff_: Type -> Type 1
-- | send {μ: Type} [Serialize μ] : Socket -> μ -> NetEff Unit
-- | recv : Socket ->  (μ: Type) -> [Serialize μ] -> NetEff μ

inductive NetEff (ep: δ): Type -> Type 1
| send {μ: Type} [Serialize μ] : (r:δ) -> (r ≠ ep) -> μ -> NetEff ep Unit
| recv : (r:δ) -> (r ≠ ep) ->  (μ: Type) -> [Serialize μ] -> NetEff ep μ

-- Interpretation of the NetEffOld Signature in the IO Monad using Sockets
-- instance: MonadLift (NetEff) IO where
--   monadLift x := match x with
--   | NetEff.send sock m=> sock.send_val2 m
--   | NetEff.recv sock μ => sock.recv_val2 (t:=μ)



structure SockChannel (sender receiver ep: δ ) where
  recv_sock: GVal receiver ep Socket
  send_sock: GVal sender ep Socket

def init_sending_channel (sender ep:δ) (addr: Address):  IO (GVal sender ep Socket) := do
  if h:(sender = ep) then
    let sock <- addr.connect_to
    return GVal.Wrap h sock
  else
    return GVal.Empty h

def init_receiving_channel  (receiver ep: δ) (addr: Address):  IO (GVal receiver ep Socket) := do
  if h:(receiver = ep) then
    let sock <- addr.listen_on
    return GVal.Wrap h sock
  else
    return GVal.Empty h

-- epp for initializing a channel between two locations and printing dbg info to console
def init_channel  [Repr δ] (sender receiver ep: δ) (addr: Address):  IO (SockChannel sender receiver ep) := do
  if(dbg_print_init_sockets ∧ sender = ep) then
    IO.println s!"connecting out {reprName sender} -> {reprName receiver}"
  if(dbg_print_init_sockets ∧ receiver = ep) then
    IO.println s!"connecting in  {reprName sender} -> {reprName receiver}"
  let recv_sock: GVal receiver ep Socket <- init_receiving_channel receiver ep addr
  let send_sock:  GVal sender ep Socket <- init_sending_channel sender ep addr
  return ⟨recv_sock, send_sock⟩

structure SockNet {δ:Type} [DecidableEq δ] (ep: δ) [DecidableEq δ] where
  channels: List (Σ (id: δ×δ), SockChannel id.1 id.2 ep)
  complete: ∀ (k : δ×δ), (k.1 ≠ k.2) -> (channels.dlookup k).isSome

def SockNet.getChannel {δ:Type} [DecidableEq δ]  {ep: δ} (net:SockNet ep) (k:δ×δ) (not_self: k.1 ≠ k.2) : SockChannel k.1 k.2 ep :=
  (net.channels.dlookup k).get (by simp [net.complete, not_self])

def init_network [DecidableEq δ] [Repr δ] [FinEnum δ] (ep: δ) (as:  (k:δ×δ) -> Address := default_adress) : IO (SockNet ep) := do

  let filtered := (FinEnum.toList (δ×δ)).filter (fun k => k.2 ≠ k.1)
  let progs: List (Σ (k: (δ×δ)), Address)  := filtered.map (fun k => ⟨k, as k⟩ )
  let channels_prog: IO (List (Σ (k: δ×δ), SockChannel k.1 k.2 ep)):= progs.mapM (fun x => do
    let id := x.1
    let chan: SockChannel id.1 id.2 ep <-  init_channel id.1 id.2 ep x.2
    return ⟨id, chan⟩ )
  let cs <- channels_prog

  if(dbg_print_init_sockets) then
    IO.println ""
  return {
            channels := cs
            complete := fun k => by
              simp [List.dlookup_isSome, List.keys]
              sorry
              done
          }


instance NetEPP2 [FinEnum δ] [Repr δ] (ep: δ) (net: SockNet ep): MonadLiftT (NetEff ep) IO where
  monadLift x := match x with
  | NetEff.send r p m=> do
    let c := net.getChannel ⟨ ep, r⟩ (by sorry)  -- very simple prrof

    let sock := c.send_sock.unwrap (by simp)
    IO.println s!"{reprName ep} --> {reprName r} --> {Serialize.pretty m}"
    sock.send_val2 m

  | NetEff.recv s p μ => do
    let c := net.getChannel ⟨s, ep⟩ (by sorry)
    let sock := c.recv_sock.unwrap (by simp)
    let res <- sock.recv_val2
    IO.println s!"{reprName ep} <-- {reprName s} <-- {Serialize.pretty res}"
    return res




-- instance NetEPP {δ:Type} (ep: δ) [FinEnum δ] [Repr δ] (as: δ × δ -> Address := default_adress): MonadLiftT (NetEff δ) IO where
--   monadLift x := match x with
--   | NetEff.send r m=> do
--     IO.println s!"sent value to {reprName r} {Serialize.pretty m}"
--     let sock <-  (as ⟨ep, r⟩ ).connect_to
--     sock.send_val2 m
--     sock.close

--   | NetEff.recv s μ => do
--     let sock <- (as ⟨s, ep⟩).listen_on
--     let res <- sock.recv_val2
--     sock.close
--     IO.println s!"recv value from {reprName s} {Serialize.pretty res}"
--     return res

-- Freer Monad over the NetEffOld Signature
@[reducible] def NetM {δ:Type} (ep:δ) := Freer (NetEff ep)



-- auxiliary Effect, sum type of either a net_eff or local_eff

@[reducible] def LocalProgramEff {δ:Type} (ep:δ) (leff:Type -> Type 1) := SumEff (NetEff ep) leff

-- A Monad for Local Effects where leff is the Effect Signature
@[reducible] def LocalM {δ:Type} (ep:δ) (leff: Type -> Type 1) := Freer (LocalProgramEff ep leff)

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
