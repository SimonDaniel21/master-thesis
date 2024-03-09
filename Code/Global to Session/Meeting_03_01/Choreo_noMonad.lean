import Test.my_utils
import Std.Data.Option.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.FinEnum
import Mathlib.Data.Finmap
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.IntervalCases
--import Mathlib
--import Mathlib.Combinatorics.SimpleGraph.Basic

inductive Example_Location
| alice | eve | bob
deriving Repr, Fintype

open Example_Location

inductive LVal (owner: δ) (α: Type)   where
| Wrap: α -> LVal owner α
| Empty: LVal owner α

def LVal.bind {α β : Type}: LVal owner α → (α → LVal owner β) → LVal owner β
| LVal.Wrap x, next =>
  next x
| LVal.Empty , _ => LVal.Empty

def test_opt: Option Nat := do
  return 3

instance: Monad (LVal owner) where
  pure x :=
    LVal.Wrap x
  bind :=LVal.bind

  def temp_add (gv: LVal  bob Nat) : LVal  alice Nat := do
    return 3




inductive GVal (owner endpoint: δ) (α: Type)   where
| Wrap:  (owner = endpoint) -> α -> GVal owner endpoint α
| Empty: (owner ≠ endpoint) -> GVal owner endpoint α

def GVal.bind {α β : Type}: GVal owner endpoint α → (α → GVal owner endpoint β) → GVal owner endpoint β
| GVal.Wrap _ x, next =>
  next x
| GVal.Empty h, _ => GVal.Empty h

def test_opt: Option Nat := do
  return 3

instance (endpoint: δ): Monad (GVal owner endpoint) where
  pure x :=
    if h: (owner = endpoint) then
      GVal.Wrap h x
    else
      GVal.Empty h
  bind :=GVal.bind



#check ReaderT

def Choreo  {δ:Type} (ep: δ)  (α:Type):=   α

def dist_prog: Choreo ep Nat := sorry


  def temp_add (gv: GVal alice bob Nat) : GVal alice alice Nat := do
    return 3


inductive ChorEff' {δ:Type} (ep:δ): Type -> Type 1 where
| Send_recv [ser:Serialize a]: {sender:δ} -> GVal sender ep a  -> (receiver:δ) -> ChorEff' ep (GVal receiver ep a)
| Local : (loc:δ) -> ([∀ x, Coe (GVal loc ep x) x] -> IO a) -> ChorEff' ep (GVal loc ep a)

inductive Choreo' {δ:Type} (ep:δ): Type -> Type 1  where
| Do :  ChorEff' ep b -> (b -> Choreo' ep a) -> Choreo' ep a
| Return: a -> Choreo' ep a

def Choreo (δ : Type ) (α) :=
  (ep:δ) -> Choreo' ep α

protected def Choreo.bind {α β} (chor : Choreo δ α) (f : α → Choreo δ β) : Choreo δ β :=

  fun ep =>
    let temp := chor ep
    let temp2 := run temp
    (f temp) ep
    sorry






-- instance  : MonadLift (Choreo δ) where
--   monadLift x := fun _ => x

instance: Monad (Choreo δ) where
  bind := Choreo.bind
  pure x := fun _ep => x


def Choreo.read: Choreo δ δ
| x => x

def Choreo.LVal (owner:δ) (α:Type): Choreo δ (Type)
| ep => GVal owner ep α



def dist_prog: Choreo Example_Location Nat := do
  let vtype <- Choreo.LVal alice Nat
  return 3


#check StateT
#check ReaderT

def Choreo.epp {δ : Type u} {m : Type u → Type v} {α : Type u} (x : ReaderT ρ m α) (r : ρ) : m α :=
  x r

inductive GVal (α: Type) (owner endpoint: δ)   where
| Wrap:  (owner = endpoint) -> α -> GVal α owner endpoint
| Empty: (owner ≠ endpoint) -> GVal α owner endpoint

inductive LVal  (owner: δ) (α: Type)  where
| Wrap:    α -> LVal owner α
| Empty:LVal owner α


def GVal.wrap (owner endpoint: δ) (v:α) : GVal α owner endpoint :=
  if h:(owner = endpoint) then
    GVal.Wrap h v
  else
    GVal.Empty h

def GVal.unwrap {owner endpoint: δ}: GVal α owner endpoint -> (owner = endpoint) -> α
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction


instance {loc ep: δ} [DecidableEq δ]  [Fintype δ] [ToString t]: ToString (GVal t loc ep) where
  toString x :=
    if h:(loc = ep) then
      let val := x.unwrap h
      toString val
    else
      "Empty"


def Example_Location.ofString: String -> Option Example_Location
| "alice" => .some alice
| "eve" => .some eve
| "bob" => .some bob
| _ => none

structure ChorData (δ:Type) where
  ep: δ
  local_monads: δ -> (M: Type -> Type u_1) -> Monad M


#check ReaderM



inductive depType: Nat -> Type


infixl:55 "@" => fun {endpoint:String} (a:Type) (loc:String) => GVal a loc endpoint

class Network {δ:Type} (ep: δ) (M:Type → Type u_1) [Monad M] where
  com {t:Type} [Serialize t]: (s: δ) -> GVal t s ep -> (r: δ) -> M (GVal t r ep)


def GVal.reduce {α:Type} [DecidableEq δ] {ep: δ} (gvs: List (Σ (loc: δ), GVal α loc ep)) (complete: ∀ (loc : δ),  (gvs.dlookup loc).isSome):  α :=
  let local_gv := (gvs.dlookup ep).get (complete ep)
  let v := local_gv.unwrap (by simp)
  v


def Network.broadcast {δ:Type} [FinEnum δ] (M:Type → Type u_1) [Monad M] {ep: δ} (net: Network ep M) {t:Type} [Serialize t] (s: δ) (gv:GVal t s ep): M t := do
  --let gv <- com s gv ep
  --let v := gv.unwrap (by simp)
  let temp:=(FinEnum.toList δ)
  let res: List (Σ (r: δ), M (GVal t r ep)) :=
    (FinEnum.toList δ).mapM (fun x => do
      let msg_prog := net.com s gv x
      let msg <- msg_prog
      return ⟨x, msg⟩ )
  return v


structure SockChannel {δ:Type} [DecidableEq δ] (sender receiver ep: δ ) where
  recv_sock: GVal Socket receiver ep
  send_sock: GVal Socket sender ep

def init_sending_channel {δ:Type} [DecidableEq δ] (sender ep:δ) (addr: Address):  IO (GVal Socket sender ep) := do
  if h:(sender = ep) then
    let sock <- addr.connect_to
    return GVal.Wrap h sock
  else
    return GVal.Empty h

def init_receiving_channel {δ:Type} [DecidableEq δ] (receiver ep: δ) (addr: Address):  IO (GVal Socket receiver ep) := do
  if h:(receiver = ep) then
    let sock <- addr.listen_on
    return GVal.Wrap h sock
  else
    return GVal.Empty h

-- epp for initializing one network socket
def init_channel {δ:Type} [DecidableEq δ] [Repr δ] (sender receiver ep: δ) (addr: Address):  IO (SockChannel sender receiver ep) := do
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

def SockNet.toNet {δ:Type} [Repr δ] [DecidableEq δ] {ep:δ} (snet: SockNet ep): Network ep IO :=
  ⟨fun s gv r => do

    if h:( s = ep) then
      let v := gv.unwrap h
      if h2:(r = ep) then
        return GVal.Wrap h2 v
      else
        let h3: r != s := sorry
        let sock := (snet.getChannel (s, r) (by sorry)).send_sock.unwrap h
        let v := gv.unwrap h
        if dbg_print_net_msgs then
          IO.println s!"send to   {reprStr r} -> {Serialize.pretty v}"
        sock.send_val2 v
        return GVal.Empty h2
    else
      if h2:(r = ep) then
        let sock := (snet.getChannel (s, r) (by simp [h, h2])).recv_sock.unwrap h2
        let v <- sock.recv_val2
        if dbg_print_net_msgs then
          IO.println s!"recv from {reprStr s} -> {Serialize.pretty v}"
        return GVal.Wrap h2 v
      else
        return GVal.Empty h2⟩
instance  {δ:Type} [DecidableEq δ] {ep:δ} (snet: SockNet ep): Network ep IO where
  com s gv r := do

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

def init_network [DecidableEq δ] [Repr δ] [FinEnum δ] (ep: δ) (as:  (k:δ×δ) -> (k.1 ≠ k.2) -> Address) : IO (SockNet ep) := do

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


def send_recv  {δ:Type} [DecidableEq δ] {M: Type -> Type u_1} [Monad M]
  {a:Type} {ep:δ} [Serialize a] [net:Network ep M] {sender:δ} (gv: GVal a sender ep) (receiver: δ): M (GVal a receiver ep) := do
  net.com sender gv receiver


def locally  {δ:Type} [DecidableEq δ] {ep:δ} (loc: δ) {M: Type -> Type u_1} [Monad M]
  (comp: [∀ x, Coe (GVal x loc ep) x] -> M α): M (GVal α loc ep) := do
  if h:( loc = ep) then
      have (x:Type) : Coe (GVal x loc ep) x := ⟨fun gv => gv.unwrap h⟩
      let res <- comp
      return GVal.Wrap h res
    else
      return  GVal.Empty h

def compute {δ:Type} [DecidableEq δ] {ep:δ}
  (loc: δ) (comp: [∀ x, Coe (GVal x loc ep) x] -> α): (GVal α loc ep)  :=
  if h:( loc = ep) then
      have (x:Type) : Coe (GVal x loc ep) x := ⟨fun gv => gv.unwrap h⟩
      GVal.Wrap h (comp)
    else
      GVal.Empty h

def branch {δ:Type} [DecidableEq δ] {ep:δ} [Monad M] [net: Network ep M]
  {a:Type} [Serialize a] {decider:δ} (gv: GVal a decider ep) (cont: a -> M b):= do

  let endpoint_choice <- net.com decider gv ep
  let choice := endpoint_choice.unwrap (by simp)
  return (cont choice)

def send_recv_comp {δ:Type} [DecidableEq δ] {ep:δ}
  {a:Type} (endpoint: String) [Serialize b] (sender receiver: δ) (comp: [∀ x, Coe (GVal x sender ep) x] -> IO b):=
  do
  let gv <- locally sender comp
  toChoreo (ChorEff.Send_recv gv receiver) (a:= GVal b receiver ep)


notation:55 lv "~>" receiver => send_recv lv receiver

notation:55 sender "~>" receiver "#" comp => send_recv_comp sender receiver comp
--notation:55 sender "~>" receiver "pure" comp => send_recv_pure sender receiver comp

def cast_gv {δ:Type} {owner ep:δ}  [DecidableEq δ] (gv: GVal a owner ep) [k:∀ x, Coe (GVal x owner ep (δ:=δ)) x]: a :=
  let c := k a
  c.coe gv

-- works similiar to normal coersion arrow ↑ but always casts to the underlying type
notation:55 "⤉" gv => cast_gv gv

syntax "send " ident (" from " ident)? " to " term (" as " ident)?: doElem

macro_rules
| `(doElem|send $i to $r) => `(doElem| let $i:ident := <- (send_recv $i $r))
| `(doElem|send $i to $r as $y) => `(doElem| let $y:ident := <- (send_recv $i $r))
| `(doElem|send $i from $i2 to $r) => `(doElem| let $i:ident := <- (send_recv (sender:=$i2) $i $r))
--| `(doElem|send $i from $i2 to $r as $y) => `(doElem| let $i := <- (send_recv $i $r (sender:=$i2)) )

syntax "decision " ident term " else " term: term

macro_rules
| `(decision $i $t1 else $t2) => `(Choreo.Cond2 $i ($t1) ($t2))


def adresses (k:Example_Location × Example_Location)  (p: k.1 ≠ k.2):  Address :=
match k, p with
| (alice, bob), _ => .v4  (.mk 127 0 0 1) 2222
| (alice, eve), _ => .v4  (.mk 127 0 0 1) 2223
| (bob, alice), _ => .v4  (.mk 127 0 0 1) 2224
| (bob, eve), _ => .v4  (.mk 127 0 0 1) 2225
| (eve, bob), _ => .v4  (.mk 127 0 0 1) 2226
| (eve, alice), _ => .v4  (.mk 127 0 0 1) 2227


instance : FinEnum Example_Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Example_Location).symm


def silent_post (ep: Example_Location) [Network ep IO] : IO Unit := do

  let LVal (α:Type) (owner: Example_Location) := GVal α owner ep

  let input: LVal String alice <- locally alice do
    IO.println "enter a message"
    return <- IO.getLine

  let input <- send_recv input eve

  let msg <- locally eve (ep:=ep)  do
    return [⤉input, "eve"]

  let msg <- send_recv msg bob

  let msg: GVal (List String) bob ep   <- locally bob (M:= IO ) do
    let temp := ⤉msg
    return (⤉msg).concat "bob"

  let msg: GVal (List String) alice ep <- send_recv msg alice
  let _a:GVal Unit alice ep  <- locally alice do
    IO.println s!"alice ended with {⤉msg}"

  return ()


-- def main (args : List String): IO Unit := do
--   let mode := args.get! 0

--   let ep_opt := Location.ofString mode
--   if h: (ep_opt.isSome) then
--     let ep := ep_opt.get h

--     let net <-  init_network ep adresses
--     IO.println ""

--     have: Network ep := net.toNet

--     let res <- ((silent_post ep).epp)
--     IO.println (s!"res: {res}")

--     let te := ["hello", "world"]
--     let te2 <- te.mapM (fun x => IO.println x)
--     return ()
--   else
--     IO.println s!"{mode} is no valid endpoint"
--     return ()
