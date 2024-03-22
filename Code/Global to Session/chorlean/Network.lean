import chorlean.Freer
import chorlean.GVal
import chorlean.utils

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
| recv : (s:δ) -> (s ≠ ep) ->  (μ: Type) -> [Serialize μ] -> NetEff ep μ

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


instance NetEPP [FinEnum δ] [Repr δ] (ep: δ) (net: SockNet ep): MonadLiftT (NetEff ep) IO where
  monadLift x := match x with
  | NetEff.send r p m=> do

    let c := net.getChannel ⟨ ep, r⟩ (fun x => p (Eq.symm x))

    let sock := c.send_sock.unwrap (by simp)
    if dbg_print_net_msgs then
      IO.println s!"{reprName ep} --> {reprName r} --> {Serialize.pretty m}"
    sock.send_val2 m

  | NetEff.recv s p μ => do
    let c := net.getChannel ⟨s, ep⟩ p
    let sock := c.recv_sock.unwrap (by simp)

    let res <- sock.recv_val2
    if dbg_print_net_msgs then
      IO.println s!"{reprName ep} <-- {reprName s} <-- {Serialize.pretty res}"
    return res


@[reducible] def NetM {δ:Type} (ep:δ) := Freer (NetEff ep)



class LocSig (δ:Type) where
  sig: δ -> (Type -> Type 1)
  executable: ∀ (l:δ), MonadLiftT (sig l) IO


-- auxiliary Effect, sum type of either a net_eff or local_eff

@[reducible] def LocalProgramEff {δ:Type} (ep:δ) [sig:LocSig δ]:= SumEff (NetEff ep) (sig.sig ep)

-- A Monad for Local Effects where leff is the Effect Signature
@[reducible] def LocalM {δ:Type} (ep:δ) [LocSig δ] := Freer (LocalProgramEff ep)

def IOe (a:Type) := IO a

-- effect for arbitrary IO
inductive IOEff: Type -> Type 1
| io: IO a -> IOEff a

instance IOeffLift: MonadLift (IOEff) IO where
  monadLift x := match x with
  | IOEff.io e => e
