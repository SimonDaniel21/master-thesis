import Test.my_utils
import Std.Data.Option.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Finmap
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.IntervalCases
variable {α β: Type} -- alpha beta als normaler Type
variable {δ: Type} [DecidableEq δ]  -- delta als Location Type
variable {μ: Type} [Serialize μ]  -- mu wegen msg Type



inductive GVal (owner endpoint: δ) (α: Type)   where
| Wrap:  (owner = endpoint) -> α -> GVal owner endpoint α
| Empty: (owner ≠ endpoint) -> GVal owner endpoint α

def GVal.owner {δ} {o ep:δ} (_gv:GVal o ep α (δ:=δ)) : δ := o

def GVal.wrap (owner:δ) (endpoint: δ) (v:α) : GVal owner endpoint α :=
  if h:(owner = endpoint) then
    GVal.Wrap h v
  else
    GVal.Empty h

class Unpack (loc ep: δ) (α : Type) where
  unpack : GVal loc ep α → α

def GVal.unwrap {owner endpoint: δ}: GVal owner endpoint α -> (owner = endpoint) -> α
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction

instance {loc ep: δ}: ToString (GVal loc ep μ) where
  toString x :=
    if h:(loc = ep) then
      let val := x.unwrap h
      toString val
    else
      "Empty"


@[reducible] def LVal {ep:δ} (owner: δ) (α:Type) := GVal owner ep α

notation:55 α " @ " owner " # " ep  => GVal owner ep α
notation:55 α "@" owner =>  LVal owner α

class Network {δ:Type} (ep: δ) where
  com {μ} [Serialize μ]: {s: δ} -> GVal s ep μ -> (r: δ) -> IO (GVal r ep μ)


def GVal.reduce {α:Type}  (gvs: List (Σ (loc: δ), GVal loc ep α )) (complete: ∀ (loc : δ),  (gvs.dlookup loc).isSome):  α :=
  let local_gv := (gvs.dlookup ep).get (complete ep)
  let v := local_gv.unwrap (by simp)
  v

def Network.broadcast [FinEnum δ] (net: Network ep) {s: δ} (gv:GVal s ep μ): IO μ := do

  let progs: List (Σ (r: δ), IO (GVal r ep μ)) :=
    (FinEnum.toList δ).map (fun x => ⟨x, net.com gv x⟩)

  let mut gvs: List (Σ (r: δ), (GVal r ep μ)) := []
  -- mapM sollte eigentlich auch gehen
  for p in progs do
    let gv <- p.2
    gvs := gvs.concat ⟨p.1, gv⟩

  return GVal.reduce gvs (by sorry)

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

def SockNet.toNet {δ:Type} [Repr δ] [DecidableEq δ] {ep:δ} (snet: SockNet ep): Network ep :=
  ⟨fun gv r => do
    let s := gv.owner
    if h:( s = ep) then
      let v := gv.unwrap h
      if h2:(r = ep) then
        return GVal.Wrap h2 v
      else
        let h3: r != s := sorry
        let sock := (snet.getChannel (s, r) (by sorry)).send_sock.unwrap h
        let v := gv.unwrap h
        if dbg_print_net_msgs then
          IO.println s!"--> {reprName r} --> {Serialize.pretty v}"
        sock.send_val2 v
        return GVal.Empty h2
    else
      if h2:(r = ep) then
        let sock := (snet.getChannel (s, r) (by simp [h, h2])).recv_sock.unwrap h2
        let v <- sock.recv_val2
        if dbg_print_net_msgs then
          IO.println s!"<-- {reprName s} <-- {Serialize.pretty v}"
        return GVal.Wrap h2 v
      else
        return GVal.Empty h2⟩
instance  {δ:Type} [DecidableEq δ] {ep:δ} (snet: SockNet ep): Network ep where
  com gv r := do
    let s:= gv.owner
    if h:( s = ep) then
      let v := gv.unwrap h
      if h2:(r = ep) then
        return GVal.Wrap h2 v
      else
        let h3: r != s := sorry
        let sock := (snet.getChannel (s, r) (by sorry)).send_sock.unwrap h
        let v := gv.unwrap h
        sock.send_val2 v
        return GVal.Empty h2
    else
      if h2:(r = ep) then
        let sock := (snet.getChannel (s, r) (by simp [h, h2])).recv_sock.unwrap h2
        let v <- sock.recv_val2
        return GVal.Wrap h2 v
      else
        return GVal.Empty h2


def init_network [DecidableEq δ] [Repr δ] [FinEnum δ] (ep: δ) (as:  (k:δ×δ) -> (k.1 ≠ k.2) -> Address := default_adress) : IO (SockNet ep) := do

  let filtered := (FinEnum.toList (δ×δ)).filter (fun k => k.1 ≠ k.2)
  let progs: List (Σ (k: (δ×δ)), Address)  := filtered.map (fun k => ⟨k, as k (by sorry)⟩ )
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



inductive ChorEff (ep:δ): Type -> Type 1 where
| Send_recv {μ} [Serialize μ] : {s:δ} -> GVal s ep μ  -> (r:δ) -> ChorEff ep (GVal r ep μ)
| Local {α} [DecidableEq δ] : (loc:δ) -> ([∀ x, Unpack loc ep x] -> IO α) -> ChorEff ep (GVal loc ep α)
| Calc {α} [DecidableEq δ] : (loc:δ) -> ([∀ x, Unpack loc ep x] -> α) -> ChorEff ep (GVal loc ep α)

inductive Choreo (ep:δ): Type -> Type 1  where
| Cond {μ} {α} {decider:δ} [DecidableEq δ] [FinEnum δ] [Serialize μ]: GVal decider ep μ -> (μ -> Choreo ep α) -> Choreo ep α
--| Cond2 {decider:δ}: GVal Bool decider ep -> (Choreo a) -> (Choreo a) -> Choreo a
| Do {α β} :  ChorEff ep β -> (β -> Choreo ep α) -> Choreo ep α
| Return {α}: α -> Choreo ep α

def Choreo.bind {ep:δ} {α β: Type}:
  Choreo ep α → (α → Choreo ep β) → Choreo ep β
| Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
| Choreo.Cond lv next, next' =>
  Choreo.Cond lv (fun x => bind (next x) next')
-- | Choreo.Cond2 lv opt_a opt_b, next' =>
--   Choreo.Cond2 lv (bind opt_a next') (bind opt_b next')
| Choreo.Return v, next' => next' v

instance {δ:Type} [DecidableEq δ] {ep:δ}: Monad (Choreo (δ := δ) (ep := ep)) where
  pure x := Choreo.Return x
  bind  := Choreo.bind


def toChoreo (eff: ChorEff ep a) : Choreo ep a:=
   Choreo.Do eff (Choreo.Return)

def send_recv {s:δ} (gv: GVal s ep μ) (r: δ) :=
  toChoreo (ChorEff.Send_recv gv r )

def locally (loc: δ) (comp: [∀ x, Unpack loc ep x] -> IO α) :=
  toChoreo (ChorEff.Local loc comp) (a:=GVal loc ep α)

def compute (loc: δ) (comp: [∀ x, Unpack loc ep x] -> α) :=
  toChoreo (ChorEff.Calc loc comp) (a:=GVal loc ep α)

def branch {decider:δ} (gv: GVal decider ep μ) (cont: μ -> Choreo ep α) [FinEnum δ]:=
    Choreo.Cond gv cont

--axiom net2: ∀ (o ep:δ) (p: o = ep) (gv: GVal o ep μ) (chor: Choreo ep α), gv.unwrap (p) =



def send_recv_comp (s r: δ)  [Serialize μ] (comp: [∀ x, Unpack s ep x] -> IO μ):=
  do
  let gv <- locally s comp
  toChoreo (ChorEff.Send_recv gv r) (a:= GVal r ep μ)


def ChorEff.epp: ChorEff ep a -> (Network ep) -> IO a
| ChorEff.Send_recv gv receiver, net =>
  net.com gv receiver
| ChorEff.Local loc comp, net => do
    if h:( loc = ep) then
      have (x:Type) : Unpack loc ep x := ⟨fun gv => gv.unwrap h⟩
      let res <- comp
      return GVal.Wrap h res
    else
      return  GVal.Empty h
| ChorEff.Calc loc comp, net => do
    if h:( loc = ep) then
      have (x:Type) : Unpack loc ep x := ⟨fun gv => gv.unwrap h⟩
      let res := comp
      return GVal.Wrap h res
    else
      return  GVal.Empty h

def  Choreo.epp [net: Network ep]:
   Choreo ep a -> IO a
| Choreo.Return v => return v
| Choreo.Do eff next => do
  let res <- (eff.epp net)

  --have h: sizeOf (next res) < 1 + sizeOf eff := by sorry
  Choreo.epp (next res)
| Choreo.Cond gv cont (decider:= decider) (ep:=ep) => do
  IO.println "before choice"
  let choice <- net.broadcast gv
  (cont choice).epp




notation:55 lv "~>" receiver => send_recv lv receiver

notation:55 sender "~>" receiver "#" comp => send_recv_comp sender receiver comp

notation:55 sender "~~>" receiver comp => send_recv_comp sender receiver comp

def cast_gv {owner ep:δ}  (gv: GVal owner ep α ) [k:∀ x, Coe (GVal owner ep x) x]: α :=
  let c := k α
  c.coe gv

-- works similiar to normal coersion arrow ↑ but always casts to the underlying type
--notation:55 "⤉" gv => (cast_gv gv)
notation:55 "⤉" gv => Unpack.unpack gv


syntax "send " ident (" from " ident)? " to " term (" as " ident)?: doElem

macro_rules
| `(doElem|send $i to $r) => `(doElem| let $i:ident := <- (send_recv $i $r))
| `(doElem|send $i to $r as $y) => `(doElem| let $y:ident := <- (send_recv $i $r))
| `(doElem|send $i from $i2 to $r) => `(doElem| let $i:ident := <- (send_recv (sender:=$i2) $i $r))
--| `(doElem|send $i from $i2 to $r as $y) => `(doElem| let $i := <- (send_recv $i $r (sender:=$i2)) )

syntax "decision " ident term " else " term: term


macro_rules
| `(decision $i $t1 else $t2) => `(Choreo.Cond2 $i ($t1) ($t2))

inductive Example_Location
| alice | eve | bob
deriving Repr, Fintype

open Example_Location

def Example_Location.ofString: String -> Option Example_Location
| "alice" => .some alice
| "eve" => .some eve
| "bob" => .some bob
| _ => .none



instance : FinEnum Example_Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Example_Location).symm
