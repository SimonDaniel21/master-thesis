import Test.my_utils
import Std.Data.Option.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.FinEnum
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.IntervalCases
--import Mathlib
--import Mathlib.Combinatorics.SimpleGraph.Basic


inductive GVal (α: Type) (owner endpoint: Fin ω)   where
| Wrap:  (owner = endpoint) -> α -> GVal α owner endpoint
| Empty: (owner ≠ endpoint) -> GVal α owner endpoint

def GVal.wrap (owner endpoint: Fin ω) (v:α) : GVal α owner endpoint :=
  if h:(owner = endpoint) then
    GVal.Wrap h v
  else
    GVal.Empty h

def GVal.unwrap {owner endpoint: Fin n}: GVal α owner endpoint -> (owner = endpoint) -> α
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction

instance {loc ep: Fin n} [ToString t]: ToString (GVal t loc ep) where
  toString x :=
    if h:(loc = ep) then
      let val := x.unwrap h
      toString val
    else
      "Empty"

structure d_graph (n:Nat) where
  edge: Fin n -> Fin n -> Prop

def test_g: d_graph 3 := ⟨fun x y => match x, y with
  | 0, 1 => true
  | 0, 2 => true
  | 1, 2 => true
  | _, _ => false⟩

infixl:55 "@" => fun {endpoint:String} (a:Type) (loc:String) => GVal a loc endpoint

class Network (ep: Fin ω) where
  com  {t:Type} [Serialize t]: (s: Fin ω) -> GVal t s ep -> (r: Fin ω) -> IO (GVal t r ep)

structure SockChannel (sender receiver ep: Fin n) where
  recv_sock: GVal Socket receiver ep
  send_sock: GVal Socket sender ep

structure SockNet (ep: Fin ω) where
  channels: List (Σ (ls: Fin ω × Fin ω),  (SockChannel ls.fst ls.snd ep))
  h1: ∀ (l1 l2: Fin ω), (channels.dlookup (l1,l2)).isSome

def init_sending_channel (sender ep:Fin ω) (addr: Address):  IO (GVal Socket sender ep) := do
  if h:(sender = ep) then
    IO.println s!"waiting for"-- {sender} -> {receiver}"
    let sock <- addr.connect_to
    return GVal.Wrap h sock
  else
    return GVal.Empty h

def init_receiving_channel (receiver ep: Fin ω) (addr: Address):  IO (GVal Socket receiver ep) := do
  if h:(receiver = ep) then
    IO.println s!"waiting for"-- {sender} -> {receiver}"
    let sock <- addr.listen_on
    return GVal.Wrap h sock
  else
    return GVal.Empty h

-- epp for initializing one network socket
def init_channel (sender receiver ep: Fin ω) (addr: Address):  IO (SockChannel sender receiver ep) := do
  let recv_sock <- init_receiving_channel receiver ep addr
  let send_sock <- init_sending_channel sender ep addr
  return ⟨recv_sock, send_sock⟩

#eval ToString.toString (33)

/--
`O(n)`. `range n` is the numbers from `0` to `n` exclusive, in increasing order.
* `range 5 = [0, 1, 2, 3, 4]`
-/
def myrange (n : Nat) : List (Fin n) :=
  loop n []
where
  loop : Nat → List (Nat) → List (Fin n)
  | 0,   ns => ns
  | n+1, ns => loop n (n::ns)

#check Socket


def Socket2:= Unit

def init_socket (_address: Unit): IO Socket2 := return ()

def init_network (α:Type) [FinEnum α] (adress_of: α -> Unit): IO (List (α × Socket2)) := do
  let all_elems: List α := FinEnum.toList α   -- supposed to be the list of all α
  let init_progs: List (IO Socket2) := all_elems.map (fun x => init_socket (adress_of x))
  -- then execute all progs


def prog: IO Unit := do
  let net <- init_network Unit (fun _ => ())
  -- so now i can lookup Sockets by my supplied Type α = Unit
  let some_sock := (net.lookup ()) -- would need a proof that all α are in the list...

def get_socket (α:Type)

def init_network (ep:Fin ω) (adresses: Fin n -> Address) : IO (SockNet ep) := do
  let temp: List (Fin ω × Fin ω) := (List.range ω).product (List.range ω)

  _

-- | a::as => do
--   let rest <- init_network locs ep (port + UInt16.ofNat (locs.length - 1)) (missing:=as)
--   let net <- init_network' ls ep port a all
--   return ⟨ rest.channels ++ net.channels, by sorry⟩
-- | [] => do
--   IO.println "finished network initilization\n"
--   return ⟨[], by sorry⟩

inductive ChorEff {ω:Nat} {ep:Fin ω}: Type -> Type 1 where
| Send_recv [ser:Serialize a]: {sender:Fin ω} -> GVal a sender ep  -> (receiver:Fin ω) -> ChorEff (GVal a receiver ep)
| Local : (loc:Fin ω) -> ([∀ x, Coe (GVal x loc ep) x] -> IO a) -> ChorEff (GVal a loc ep)
| Calc : (loc:Fin ω) -> ([∀ x, Coe (GVal x loc ep) x] -> a) -> ChorEff (GVal a loc ep)

inductive Choreo (ω:Nat) (ep:Fin ω): Type -> Type 1  where
| Cond [Serialize a] {decider:Fin ω}: GVal a decider ep -> (a -> Choreo ω ep b) -> Choreo ω ep b
| Cond2 {decider:Fin ω}: GVal Bool decider ep -> (Choreo ω ep a) -> (Choreo ω ep a) -> Choreo ω ep a
| Do :  ChorEff b (ep:=ep) -> (b -> Choreo ω ep a) -> Choreo ω ep a
| Return: a -> Choreo ω ep a

def Choreo.bind {ω:Nat} {ep:Fin ω} {α β: Type}:
  Choreo α (ω := ω) (ep := ep)→ (α → Choreo β (ω := ω) (ep := ep)) → Choreo β (ω := ω) (ep := ep)
| Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
| Choreo.Cond lv next, next' =>
  Choreo.Cond lv (fun x => bind (next x) next')
| Choreo.Cond2 lv opt_a opt_b, next' =>
  Choreo.Cond2 lv (bind opt_a next') (bind opt_b next')
| Choreo.Return v, next' => next' v

instance {ω:Nat} {ep:Fin ω}: Monad (Choreo (ω := ω) (ep := ep)) where
  pure x := Choreo.Return x
  bind  := Choreo.bind

def toChoreo {ω:Nat} {ep:Fin ω} (eff: ChorEff a (ω := ω) (ep := ep)) : Choreo a (ω := ω) (ep := ep):=
   Choreo.Do eff (Choreo.Return)

def send_recv {ep:Fin ω}
  {a:Type} [Serialize a] {sender:Fin ω} (gv: GVal a sender ep ) (receiver: Fin ω) :=
  toChoreo (ChorEff.Send_recv gv receiver ) (a:=GVal a receiver ep)

def locally  {ep:Fin ω}
  (loc: Fin ω) (comp: [∀ x, Coe (GVal x loc ep) x] -> IO b) :=
  toChoreo (ChorEff.Local loc comp) (a:=GVal b loc ep)

def compute {ep:Fin ω}
  (loc: Fin ω) (comp: [∀ x, Coe (GVal x loc ep) x] -> b) :=
  toChoreo (ChorEff.Calc loc comp) (a:=GVal b loc ep)

def branch {ep:Fin ω}
    {a:Type} [Serialize a] {decider:Fin ω} (gv: GVal a decider ep) (cont: a -> Choreo ω ep b ):=
    Choreo.Cond gv cont

def branch' {ep:Fin ω}
  {a:Type} {decider:Fin ω} [Serialize b] (comp: [∀ x , Coe (GVal x decider ep ) x] -> IO b) (cont: b -> Choreo a (ω:= ω)):=
  do
  let gv <- locally decider comp (ω:= ω) (ep:=ep)
  Choreo.Cond gv cont

def send_recv_comp {ep:Fin ω}
  {a:Type} (endpoint: String) [Serialize b] (sender receiver: Fin ω) (comp: [∀ x, Coe (GVal x sender ep) x] -> IO b):=
  do
  let gv <- locally sender comp
  toChoreo (ChorEff.Send_recv gv receiver) (a:= GVal b receiver ep)


def ChorEff.epp {ep:Fin ω} [net: Network ω ep]:
  ChorEff a (ep:=ep)-> IO a
| ChorEff.Send_recv gv receiver (sender := sender) => do
  net.com sender gv receiver

| ChorEff.Local loc comp => do
    if h:( loc = ep) then

      have (x:Type) : Coe (GVal x loc ep) x := ⟨fun gv => gv.unwrap h⟩
      let res <- comp
      return GVal.Wrap h res
    else
      return  GVal.Empty h

| ChorEff.Calc loc comp => do
    if h:( loc = ep) then
      have (x:Type) : Coe (GVal x loc ep) x := ⟨fun gv => gv.unwrap h⟩
      return GVal.Wrap h (comp)
    else
      return  GVal.Empty h


partial def  Choreo.epp {ep:Fin ω} [net: Network Fin ω ep]:
   Choreo a (ω:=ω) (ep:=ep) -> IO a
| Choreo.Return v => return v
| Choreo.Do eff next => do
  let res <- (eff.epp)
  --have h: sizeOf (next res) < 1 + sizeOf eff := by sorry
  Choreo.epp (next res)
| Choreo.Cond gv cont (decider:= decider) (ep:=ep) => do
  let endpoint_choice <- net.com decider gv ep
  let choice := endpoint_choice.unwrap (by simp)
  (cont choice).epp
| Choreo.Cond2 gv opt_a opt_b (decider:= decider) (ep:=ep) => do
  let endpoint_choice <- net.com decider gv ep
  let choice := endpoint_choice.unwrap (by simp)
  if choice then
    opt_a.epp
  else
    opt_b.epp


notation:55 lv "~>" receiver => send_recv lv receiver

notation:55 sender "~>" receiver "#" comp => send_recv_comp sender receiver comp
--notation:55 sender "~>" receiver "pure" comp => send_recv_pure sender receiver comp


def cast_gv {ω:Nat} {owner ep:Fin ω}  (gv: GVal a owner ep) [k:∀ x, Coe (GVal x owner ep (ω:= ω)) x]: a :=
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

inductive Location
| alice | eve | bob

inductive Location2
| client | server

def alice: Fin 3 := 0
def eve: Fin 3 := 1
def bob: Fin 3 := 2

def silent_post (ep: Fin 3):

  Choreo 3 ep (GVal (List String) alice ep) := do

  let input: GVal String alice ep <- locally alice do
    IO.println "enter a message"
    return <- IO.getLine


  --let msg <- input ~> eve
  send input to eve

  let choice: GVal Bool alice ep <- compute alice true

  let temp <-
  decision choice
    return "hello"
  else
    return "nothello"

  let msg <- locally eve do
    return [↑input, "eve"]

  let msg <- send_recv msg bob

  let msg <- locally bob do
    let test:= msg
    return (⤉msg).concat "bob"

  let msg <- send_recv msg alice
  let _a <- locally alice do
    IO.println s!"alice ended with {⤉msg}"

  return msg


def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network test_cfg mode

  have k: Channel' "alice" "eve" mode := <- init_channel' "alice" "eve" mode ( .v4 (.mk 127 0 0 1) 1200)
  have: Channel' "eve" "bob" mode := <- init_channel' "eve" "bob" mode ( .v4 (.mk 127 0 0 1) 1201)
  have: Channel' "bob" "alice" mode := <- init_channel' "bob" "alice" mode ( .v4 (.mk 127 0 0 1) 1202)

  let res <- ((silent_post mode).epp)
  IO.println (s!"res: {res}")

  let te := ["hello", "world"]
  let te2 <- te.mapM (fun x => IO.println x)
  return ()
