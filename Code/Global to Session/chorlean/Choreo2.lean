import Test.my_utils
import chorlean.Effects
import chorlean.Network
import Std.Data.Option.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Finmap
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.IntervalCases
variable {α β: Type} -- alpha beta als normaler Type
variable {δ: Type} [DecidableEq δ]  -- delta als Location Type
variable {μ: Type} [Serialize μ]  -- mu wegen msg Type


-- class Network {δ:Type} (ep: δ) where
--   com {μ} [Serialize μ]: {s: δ} -> GVal s ep μ -> (r: δ) -> NetM (GVal r ep μ)


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

-- epp for initializing one network socket
def init_channel [Repr δ] (sender receiver ep: δ) (addr: Address):  IO (SockChannel sender receiver ep) := do
  if(dbg_print_init_sockets ∧ sender = ep) then
    IO.println s!"connecting out {reprStr sender} -> {reprStr receiver}"
  if(dbg_print_init_sockets ∧ receiver = ep) then
    IO.println s!"connecting in  {reprStr sender} -> {reprStr receiver}"
  let recv_sock <- init_receiving_channel receiver ep addr
  let send_sock <- init_sending_channel sender ep addr
  return ⟨recv_sock, send_sock⟩

structure SockNet {δ:Type} [DecidableEq δ] (ep: δ) [DecidableEq δ] where
  channels: List (Σ (id: δ×δ), SockChannel id.1 id.2 ep)
  complete: ∀ (k : δ×δ), (k.1 ≠ k.2) -> (channels.dlookup k).isSome

def SockNet.getChannel {δ:Type} [DecidableEq δ]  {ep: δ} (net:SockNet ep) (k:δ×δ) (not_self: k.1 ≠ k.2) : SockChannel k.1 k.2 ep :=
  (net.channels.dlookup k).get (by simp [net.complete, not_self])

def init_network [DecidableEq δ] [Repr δ] [FinEnum δ] (ep: δ) (as:  (k:δ×δ) -> Address := default_adress) : IO (SockNet ep) := do

  let filtered := (FinEnum.toList (δ×δ)).filter (fun k => k.1 ≠ k.2)
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


#check LocalM


-- type with effect signature
class LocSig (δ:Type) where
  sig: δ -> (Type -> Type 1)
  executable: ∀ (l:δ), MonadLiftT (sig l) IO


inductive ChorEff (ep:δ) [LocSig δ]: Type -> Type 1 where
| Send_recv {μ} [Serialize μ] : {s:δ} -> GVal s ep μ  -> (r:δ) -> ChorEff ep (GVal r ep μ)
| Local {α} [DecidableEq δ] : (loc:δ) -> ([∀ x, Unpack loc ep x] -> Freer (LocSig.sig loc) α) -> ChorEff ep (GVal loc ep α)
--| Cond2 {decider:δ}: GVal decider ep Bool -> (Freer (ChorEff ep) a) -> (Freer (ChorEff ep) a) -> ChorEff ep a

inductive Choreo (ep:δ) [LocSig δ]: Type -> Type 1  where
| Cond {μ} {α} {decider:δ} [DecidableEq δ] [FinEnum δ] [Serialize μ]: GVal decider ep μ -> (μ -> Choreo ep α) -> Choreo ep α
| Do {α β} :  ChorEff ep β -> (β -> Choreo ep α) -> Choreo ep α
| Return {α}: α -> Choreo ep α


def Choreo.bind {ep:δ} [LocSig δ]{α β: Type} :
  Choreo ep α → (α → Choreo ep β) → Choreo ep β
| Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
| Choreo.Cond lv next, next' =>
  Choreo.Cond lv (fun x => bind (next x) next')
| Choreo.Return v, next' => next' v

instance {δ:Type} [DecidableEq δ]  [LocSig δ]{ep:δ}: Monad (Choreo (δ := δ) (ep := ep)) where
  pure x := Choreo.Return x
  bind  := Choreo.bind


def com {s: δ} (gv:GVal s ep μ) (r: δ): NetM δ (GVal r ep μ) := do
   let s := gv.owner
    if h:( s = ep) then
      let v := gv.unwrap h
      if h2:(r = ep) then
        return GVal.Wrap h2 v
      else
        let v := gv.unwrap h
        NetEff.send r v
        return GVal.Empty h2
    else
      if h2:(r = ep) then
        let v <- NetEff.recv s μ
        return GVal.Wrap h2 v
      else
        return GVal.Empty h2


def broadcast [FinEnum δ] {s: δ} (gv:GVal s ep μ): NetM δ μ := do

  let progs: List (Σ (r: δ), NetM δ (GVal r ep μ)) :=
    (FinEnum.toList δ).map (fun x => ⟨x, com gv x⟩)

  let mut gvs: List (Σ (r: δ), (GVal r ep μ)) := []
  -- mapM sollte eigentlich auch gehen
  for p in progs do
    let gv <- p.2
    gvs := gvs.concat ⟨p.1, gv⟩

  return GVal.reduce gvs (by sorry)

def ChorEff.epp' (ep:δ) [LocSig δ] {α : Type}: ChorEff ep α → LocalM δ (LocSig.sig ep) α
| ChorEff.Send_recv gv r => com gv r
| ChorEff.Local loc comp (α := α ) => do
  if h:( loc = ep) then
    have (x:Type) : Unpack loc ep x := ⟨fun gv => gv.unwrap h⟩
    let local_prog: Freer (LocSig.sig ep) α  := cast (by simp [h]) comp
    let res <- local_prog
    return GVal.Wrap h res
  else
    return  GVal.Empty h


instance EPP2 (ep:δ) [LocSig δ]: MonadLiftT (ChorEff ep) (LocalM δ (LocSig.sig ep)) where
  monadLift := ChorEff.epp' ep



def Choreo.epp' (ep:δ) [LocSig δ] {α : Type}: Choreo ep α → LocalM δ (LocSig.sig ep) α
 | Choreo.Cond gv cont => do

    let choice <- broadcast gv
    Choreo.epp' ep (cont choice)
  | Choreo.Return v => return v

  | Choreo.Do eff cont => do
    let res <- eff.epp' ep
    Choreo.epp' ep (cont res)



instance EPP (ep:δ) [LocSig δ]: MonadLiftT (Choreo ep) (LocalM δ (LocSig.sig ep)) where
  monadLift := Choreo.epp' ep

notation:55 "⤉" gv => (Unpack.unpack gv)

def toChoreo  [LocSig δ] (eff: ChorEff ep a (δ:=δ)): Choreo ep a:=
   Choreo.Do eff (Choreo.Return)

def send_recv {s:δ} (gv: GVal s ep μ) (r: δ)  [LocSig δ]:=
  toChoreo (ChorEff.Send_recv gv r )

def locally  [LocSig δ] (loc: δ)  (comp: [∀ x, Unpack loc ep x] -> Freer (LocSig.sig loc) α):=
  toChoreo (ChorEff.Local loc comp) (a:=GVal loc ep α)

def branch {decider:δ} [LocSig δ] (gv: GVal decider ep μ) (cont: μ -> Choreo ep α) [FinEnum δ] :=
    Choreo.Cond gv cont


notation:55 lv "~>" receiver => send_recv lv receiver

-- coerces GVal Unit types into Unit
-- lets you omit variable assignement with let in do notation for Unit Choreos
instance: CoeOut (GVal o ep Unit) Unit where
  coe _ := ()
