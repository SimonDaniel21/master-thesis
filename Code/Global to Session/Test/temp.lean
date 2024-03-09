
--import Std.Data.Option.Basic
import Mathlib.Data.List.Sigma
--import Mathlib
--import Mathlib.Combinatorics.SimpleGraph.Basic

def Address := Unit -- IP Adress

-- represents distributed values. When programs get Projected to endpoints GVal only holds a value if (owner = endpoint)
inductive GVal (α: Type) (owner endpoint: LocTy)   where
| Wrap:  (owner = endpoint) -> α -> GVal α owner endpoint
| Empty: (owner ≠ endpoint) -> GVal α owner endpoint

-- desired typeclass with a send-receive operation
class Network (ep: LocTy) where
  com  {t:Type}: (sender: LocTy) -> GVal t sender ep -> (receiver: LocTy) -> IO (GVal t r ep)

import Mathlib.Data.List.Sigma

structure collection (α: Type) (β: α -> Type) [DecidableEq α] where
  data: List (Σ (v:α), β v)
  complete: ∀ (v:α), (data.dlookup v).isSome

def construct_collection [DecidableEq α]  (β: α -> Type) (f: (v:α) -> β v): collection α β :=
  ⟨
    sorry, sorry
  ⟩

-- so i can define

def f (α: Type)  (β: α -> Type) [DecidableEq α]  (v:α) (c:collection α β) : β v :=
  (c.data.dlookup v).get (by simp [c.complete])

-- struct that holds 2 distributed sockets for sending and receiving
structure SockChannel {δ:Type} [DecidableEq δ]  (sender receiver ep: LocTy) where
  recv_sock: GVal Socket receiver ep
  send_sock: GVal Socket sender ep

def init_channel {δ:Type} [DecidableEq δ] (sender receiver ep: δ) (addr: Address):  IO (SockChannel sender receiver ep) := do
  let recv_sock <- init_receiving_channel receiver ep addr
  let send_sock <- init_sending_channel sender ep addr
  return ⟨recv_sock, send_sock⟩

def init_channel {LocTy:Type} (sender receiver ep: LocTy) (addr: Address): IO (SockChannel sender receiver ep ()) := sorry

def init_network (n:Nat) (ep:δ) (adresses: Fin n -> Address) : IO (SockNet ep) := do
   let lst: List (Fin n × Address) := sorry


structure SockNet {δ:Type} [DecidableEq δ] (ep: δ) where
  channels: Lean.AssocList (δ × δ) (SockChannel l1 l2 ep)


def GVal.wrap (owner endpoint: LocTy) (v:α) : GVal α owner endpoint :=
  if h:(owner = endpoint) then
    GVal.Wrap h v
  else
    GVal.Empty h

abbrev Stringable := {t:Type} -> [ToString t] -> t

abbrev LocTy {δ:Type} [DecidableEq δ] [Fintype δ]:= δ

def GVal.unwrap [DecidableEq δ] {owner endpoint: δ}: GVal α owner endpoint -> (owner = endpoint) -> α
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction

instance {loc ep: δ} [DecidableEq δ]  [Fintype δ] [ToString t]: ToString (GVal t loc ep) where
  toString x :=
    if h:(loc = ep) then
      let val := x.unwrap h
      toString val
    else
      "Empty"

infixl:55 "@" => fun {endpoint:String} (a:Type) (loc:String) => GVal a loc endpoint

def init_sending_channel {δ:Type} [DecidableEq δ] (sender ep:δ) (addr: Address):  IO (GVal Socket sender ep) := do
  if h:(sender = ep) then
    IO.println s!"waiting for"-- {sender} -> {receiver}"
    let sock <- addr.connect_to
    return GVal.Wrap h sock
  else
    return GVal.Empty h

def init_receiving_channel {δ:Type} [DecidableEq δ] (receiver ep: δ) (addr: Address):  IO (GVal Socket receiver ep) := do
  if h:(receiver = ep) then
    IO.println s!"waiting for"-- {sender} -> {receiver}"
    let sock <- addr.listen_on
    return GVal.Wrap h sock
  else
    return GVal.Empty h

-- epp for initializing one network socket
def init_channel {δ:Type} [DecidableEq δ] (sender receiver ep: δ) (addr: Address):  IO (SockChannel sender receiver ep) := do
  let recv_sock <- init_receiving_channel receiver ep addr
  let send_sock <- init_sending_channel sender ep addr
  return ⟨recv_sock, send_sock⟩

#eval ToString.toString (33)

def init_network (n:Nat) (ep:δ) (adresses: Fin n -> Address) : IO (SockNet ep) := do
   let lst: List (Fin n × Address) := sorry

-- | a::as => do
--   let rest <- init_network locs ep (port + UInt16.ofNat (locs.length - 1)) (missing:=as)
--   let net <- init_network' ls ep port a all
--   return ⟨ rest.channels ++ net.channels, by sorry⟩
-- | [] => do
--   IO.println "finished network initilization\n"
--   return ⟨[], by sorry⟩

inductive ChorEff {δ:Type} [DecidableEq δ] {ep:δ}: Type -> Type 1 where
| Send_recv [ser:Serialize a]: {sender:δ} -> GVal a sender ep  -> (receiver:δ) -> ChorEff (GVal a receiver ep)
| Local : (loc:δ) -> ([∀ x, Coe (GVal x loc ep) x] -> IO a) -> ChorEff (GVal a loc ep)
| Calc : (loc:δ) -> ([∀ x, Coe (GVal x loc ep) x] -> a) -> ChorEff (GVal a loc ep)

inductive Choreo {δ:Type} [DecidableEq δ] {ep:δ}: Type -> Type 1  where
| Cond [Serialize a] {decider:δ}: GVal a decider ep -> (a -> Choreo b) -> Choreo b
| Cond2 {decider:δ}: GVal Bool decider ep -> (Choreo a) -> (Choreo a) -> Choreo a
| Do :  ChorEff b (ep:=ep) -> (b -> Choreo a) -> Choreo a
| Return: a -> Choreo a

def Choreo.bind {δ:Type} [DecidableEq δ] {ep:δ} {α β: Type}:
  Choreo α (δ := δ) (ep := ep)→ (α → Choreo β (δ := δ) (ep := ep)) → Choreo β (δ := δ) (ep := ep)
| Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
| Choreo.Cond lv next, next' =>
  Choreo.Cond lv (fun x => bind (next x) next')
| Choreo.Cond2 lv opt_a opt_b, next' =>
  Choreo.Cond2 lv (bind opt_a next') (bind opt_b next')
| Choreo.Return v, next' => next' v

instance {δ:Type} [DecidableEq δ] {ep:δ}: Monad (Choreo (δ := δ) (ep := ep)) where
  pure x := Choreo.Return x
  bind  := Choreo.bind

def toChoreo {δ:Type} [DecidableEq δ] {ep:δ} (eff: ChorEff a (δ := δ) (ep := ep)) : Choreo a (δ := δ) (ep := ep):=
   Choreo.Do eff (Choreo.Return)

def send_recv  {δ:Type} [DecidableEq δ] {ep:δ}
  {a:Type} [Serialize a] {sender:δ} (gv: GVal a sender ep ) (receiver: δ) :=
  toChoreo (ChorEff.Send_recv gv receiver ) (a:=GVal a receiver ep)

def locally  {δ:Type} [DecidableEq δ] {ep:δ}
  (loc: δ) (comp: [∀ x, Coe (GVal x loc ep) x] -> IO b) :=
  toChoreo (ChorEff.Local loc comp) (a:=GVal b loc ep)

def compute {δ:Type} [DecidableEq δ] {ep:δ}
  (loc: δ) (comp: [∀ x, Coe (GVal x loc ep) x] -> b) :=
  toChoreo (ChorEff.Calc loc comp) (a:=GVal b loc ep)

def branch {δ:Type} [DecidableEq δ] {ep:δ}
    {a:Type} [Serialize a] {decider:δ} (gv: GVal a decider ep) (cont: a -> Choreo b (δ:=δ)):=
    Choreo.Cond gv cont

def branch' {δ:Type} [DecidableEq δ] {ep:δ}
  {a:Type} {decider:δ} [Serialize b] (comp: [∀ x , Coe (GVal x decider ep ) x] -> IO b) (cont: b -> Choreo a (δ:=δ)):=
  do
  let gv <- locally decider comp (δ:=δ) (ep:=ep)
  Choreo.Cond gv cont

def send_recv_comp {δ:Type} [DecidableEq δ] {ep:δ}
  {a:Type} (endpoint: String) [Serialize b] (sender receiver: δ) (comp: [∀ x, Coe (GVal x sender ep) x] -> IO b):=
  do
  let gv <- locally sender comp
  toChoreo (ChorEff.Send_recv gv receiver) (a:= GVal b receiver ep)


def ChorEff.epp {δ:Type} [DecidableEq δ] {ep:δ} [net: Network δ ep]:
  ChorEff a (δ:=δ) (ep:=ep)-> IO a
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


partial def  Choreo.epp {δ:Type} [DecidableEq δ] {ep:δ} [net: Network δ ep]:
   Choreo a (δ:=δ) (ep:=ep) -> IO a
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

inductive Enum:Type
| A | B | C
deriving FinEnum

inductive A where
  | a
  | b
  | c
  deriving DecidableEq

#eval (A.ofNat 1).toCtorIdx
#eval sizeOf A
#eval 2 ∈ (Fin 3)

open A

class LocTya (n:Nat) where


def αEquiv : A ≃ Fin 3 where
  toFun x := ⟨A.toCtorIdx x, by cases x <;> simp⟩
  invFun x := A.ofNat x
  left_inv := A.ofNat_toCtorIdx
  right_inv := by
    intro ⟨x, h⟩
    interval_cases x <;> rfl

inductive Location:Type
| alice | bob | eve
deriving Repr, DecidableEq, Fintype

#eval Location.enumList.length

instance: FinEnum Location where
  card := 3
  equiv := sorry

#eval FinEnum.card Location

open Location
def tttt:= FinEnum.ofList [alice, bob, eve] (by decide)

#eval tttt.toList

def hmm: tttt := "hello"

#check FinEnum.card

def toList (ft: Type) [FinEnum ft] (mapping: ft -> α): List (ft × α) :=
  let temp:= FinEnum.card ft
  (FinEnum.card ft).toList.map (fun x => (x, mapping x))

def toList (ft: Type) [Fintype ft]: List ft :=
  Fintype.elems ft

#eval elems.toList
#eval Location.enumList
#eval elems

#eval s!"{repr Location.bob} "


def fs: Finset Location := {alice, bob, eve}

def mapp (fs:Finset Location) (f: Location -> Nat): List (fs × Nat) :=
  let temp := fs.toList
  let mapped := temp.map (fun x => (x, f x))
  mapped


#eval Location.alice = bob

abbrev myChor (ep: Location) := Choreo (δ:=Location) (ep:=ep)

def silent_post (ep: Location):

  myChor ep (GVal (List String) alice ep) := do

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
