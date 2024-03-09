import Test.my_utils
import Std.Data.Option.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Sigma
import Mathlib.Data.Fintype.Basic
--import Mathlib
--import Mathlib.Combinatorics.SimpleGraph.Basic

def Loc (locs: List String)  := {s:String // s ∈ locs}
#check Fintype

def Location: Finset String  :=  {"hello", "world"}

inductive my_type where
| hello | world
deriving Repr
#eval s!"{repr my_type.hello} "


def nat_mapping: my_type -> Nat
| .hello => 3
| .world => 2

--def Loc (locs: List String): Finset String :=

inductive GVal (α: Type) [DecidableEq δ] (owner endpoint: δ)   where
| Wrap:  (owner = endpoint) -> α -> GVal α owner endpoint
| Empty: (owner ≠ endpoint) -> GVal α owner endpoint

def GVal.wrap [DecidableEq δ] (owner endpoint: δ) (v:α) : GVal α owner endpoint :=
  if h:(owner = endpoint) then
    GVal.Wrap h v
  else
    GVal.Empty h

def GVal.unwrap  [DecidableEq δ] {owner endpoint: δ}: GVal α owner endpoint -> (owner = endpoint) -> α
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction

instance {loc ep: δ} [DecidableEq δ] [ToString t]: ToString (GVal t loc ep) where
  toString x :=
    if h:(loc = ep) then
      let val := x.unwrap h
      toString val
    else
      "Empty"

infixl:55 "@" => fun {endpoint:String} (a:Type) (loc:String) => GVal a loc endpoint

class Network (δ:Type) [DecidableEq δ] (ep: δ) where
  com  {t:Type} [Serialize t]: (s: δ) -> GVal t s ep -> (r: δ) -> IO (GVal t r ep)

structure SockChannel {δ:Type} [DecidableEq δ] (sender receiver ep: δ ) where
  recv_sock: GVal Socket receiver ep
  send_sock: GVal Socket sender ep

structure SockNet {δ:Type} [DecidableEq δ] (ep: δ) where
  channels: (l1:δ) -> (l2:δ) -> SockChannel l1 l2 ep

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
 -- {sender} -> {receiver}"
  if(ep = sender) then
     IO.println s!"init Channel to {strRepr sender}"
  let recv_sock <- init_receiving_channel receiver ep addr
  let send_sock <- init_sending_channel sender ep addr
  return ⟨recv_sock, send_sock⟩

-- def init_network' (locs: List String) (ep:Loc locs) (port: UInt16) (current:Loc locs): List (Loc locs) -> IO (SockNet locs ep)
-- | a::as => do
--   let addr: Address :=  .v4 ((.mk 127 0 0 1)) port
--   let ch <- init_channel current a ep addr
--   let rest <- init_network' locs ep (port + 1) current as
--   return ⟨ rest.channels.concat ⟨current, a, ch⟩, by sorry⟩
-- | [] => do
--   return ⟨ [], by sorry⟩

instance (locs: List String): DecidableEq (Loc locs) := fun ⟨s1, _⟩ ⟨⟩  =>


def mylookup (s r: Fin n) (ep: Fin n): List (Σ (r' s':Fin n), SockChannel s' r' ep) → Option (SockChannel s r ep)
  | []        => none
  | ⟨s',r',b⟩::es => match (s' = s) ∧ (r' = r)  with
    | true  => some b
    | false => lookup a es

def init_network (locs: List String) (ep:(Loc locs)) (port: UInt16) : IO (SockNet locs ep) := do
  for h: x in locs do
    IO.println x

  let mut port := port

  let mut res: List (Σ (s r: Loc locs), SockChannel s r ep) := []
  let mut inv_list: List String := []
  let mut sub: ∀ s, s ∈ inv_list -> s ∈ locs := by simp
  let mut full: ∀ l1 l2, (h1: l1 ∈ inv_list) -> (h2: l2 ∈ inv_list) ->
    ∃ s, ⟨⟨l1, sub l1 h1⟩ , ⟨l2, sub l2 h2⟩, s⟩ ∈ res := fun l1 l2 h1 h2 =>
    match inv_list with
    | [] => by sorry
    | a::as => by sorry


  for h: x in locs do
    for h2: y in locs do
      let addr: Address :=  .v4 ((.mk 127 0 0 1)) port
      let ch <- init_channel ⟨x, h⟩  ⟨y, h2⟩ ep addr
      res := res.concat ⟨⟨x,h⟩, ⟨y, h2⟩, ch⟩
      port := port + (1)
    port := port + (1)

  let temp := res.looku

  fun x y => res.lookup (x, y)

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

def compute {net: Network locs ep}
  (loc: Loc locs) (comp: [∀ x, Coe (GVal x loc ep) x] -> b) :=
  toChoreo net (ChorEff.Calc loc comp)

def branch {δ:Type} [DecidableEq δ] {ep:δ}
    {a:Type} [Serialize a] {decider:δ} (gv: GVal a decider ep) (cont: a -> Choreo b (δ:=δ)):=
    Choreo.Cond gv cont

def branch' {net: Network locs ep}
  {a:Type} [Serialize b] (comp: [∀ x, Coe (GVal x decider ep) x] -> IO b) (cont: b -> Choreo net a):=
  do
  let gv <- locally decider comp
  Choreo.Cond gv cont

def send_recv_comp {net: Network locs ep}
  {a:Type} (endpoint: String) [Serialize b] (sender receiver: Loc locs) (comp: [∀ x, Coe (GVal x sender ep) x] -> IO b):=
  do
  let gv <- locally sender comp
  toChoreo net (ChorEff.Send_recv gv receiver) (a:= GVal b receiver ep)


def ChorEff.epp {δ:Type} [DecidableEq δ] {ep:δ}: ChorEff a (δ:=δ) (ep:=ep)
   -> IO a
| ChorEff.Send_recv gv receiver (a:=a) (ser:=ser) (sender := sender) => do
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


partial def  Choreo.epp {net: Network locs ep}: Choreo net a -> IO a
| Choreo.Return v => return v
| Choreo.Do eff next => do
  let res <- (eff.epp)
  --have h: sizeOf (next res) < 1 + sizeOf eff := by sorry
  Choreo.epp (next res)
| Choreo.Cond gv cont (decider:= decider) (ep:=ep) => do
  let endpoint_choice <- net.com decider gv ep
  let choice := endpoint_choice.unwrap (by simp)
  (cont choice).epp



notation:55 lv "~>" receiver => send_recv lv receiver

notation:55 sender "~>" receiver "#" comp => send_recv_comp sender receiver comp
--notation:55 sender "~>" receiver "pure" comp => send_recv_pure sender receiver comp


def cast_gv (gv: GVal a owner ep) [k:∀ x, Coe (GVal x owner ep) x]: a :=
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

def locs: List String := ["alice", "bob", "eve"]

def L {locs: List String} (s:String):  (p: s ∈ locs := by decide) -> Loc locs :=
  fun p => ⟨s, p⟩

def alice: Loc locs := L "alice"
def bob: Loc locs := L "bob"
def eve: Loc locs := L "eve"

def silent_post  (ep: Loc locs) (net: Network locs ep)

  Choreo net (GVal (List String) ⟨alice, by decide⟩ ep) := do

  let input: GVal String alice ep <- locally alice do
    IO.println "enter a message"
    return <- IO.getLine


  --let msg <- input ~> (L "eve")
  send input to eve

  let choice: GVal Bool alice ep <- compute alice true

  let temp <-
  decision choice
    return "hello"
  else
    return "nothello"

  let temp:= msg

  let msg <- locally (L "eve") do
    return [↑msg, "eve"]

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
