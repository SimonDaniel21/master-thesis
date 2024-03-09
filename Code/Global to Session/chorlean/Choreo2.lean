import Test.my_utils
--import chorlean.Network
import Std.Data.Option.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Sigma
--import Mathlib
--import Mathlib.Combinatorics.SimpleGraph.Basic

structure MySet (a:Type) [BEq a] [LawfulBEq a] where
  items: List a
  unique: ∀ (v:a), v ∈ items -> items.count v <= 1

instance [ToString a] [BEq a] [LawfulBEq a]: ToString (MySet a) where
  toString x := toString x.items

def MySet.ofList (l: List a) [BEq a] [LawfulBEq a]: (p :∀ (v:a), v ∈ l -> l.count v <= 1 := by decide) -> MySet a :=
  fun p => ⟨l, p⟩

def MySet.toList [BEq a] [LawfulBEq a] (l: MySet a) : List a :=
  l.items

def MySet.map [BEq a] [LawfulBEq a] (l: MySet a): List a :=
  l.items

def tset: MySet String := MySet.ofList ["alice", "bob"]

#eval MySet.ofList ["alice", "bob"]

abbrev StrSet := MySet String


abbrev LocTy (locs : StrSet) := Subtype (fun s => s ∈ locs.items)

--abbrev LocTy (p : String → Prop) := Subtype p

abbrev Loc (locs: List String)  := {s:String // s ∈ locs}

inductive GVal (a:Type) (owner endpoint: Loc locs)   where
| Wrap:  (owner = endpoint) -> a -> GVal a owner endpoint
| Empty: (owner ≠ endpoint) -> GVal a owner endpoint

def GVal.wrap {a:Type} (owner endpoint: Loc locs) (v:a) : GVal a owner endpoint :=
  if h:(owner = endpoint) then
    GVal.Wrap h v
  else
    GVal.Empty h

def GVal.unwrap {a:Type} {owner endpoint: Loc locs}: (g: GVal a owner endpoint) -> (h: owner = endpoint) -> a
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction

instance {loc ep: Loc locs} [ToString t]: ToString (GVal t loc ep) where
  toString x :=
    if h:(loc = ep) then
      let val := x.unwrap h
      toString val
    else
      "Empty"


infixl:55 "@" => fun {endpoint:String} (a:Type) (loc:String) => GVal a loc endpoint

def Unwrap (owner endpoint: LocTy p) :=  {a:Type} -> GVal a owner endpoint -> a

def Net' := Type
def kkk: Net' := Nat

abbrev abs_channel := String × String


def string_subset := {s:String // ["alice", "bob", "eve"].contains s}
def subset: string_subset := ⟨"alice", by decide⟩

class Channel {locs: List String} (sender receiver ep: LocTy p)  where
  send_recv {t} [Serialize t]: GVal t sender ep -> IO (GVal t receiver ep)


-- class Network (p: String -> Prop) (ep: LocTy p) (channels: List (LocTy p × LocTy p)) where
--   com {sender receiver: LocTy p} {t} [Serialize t]: GVal t sender ep -> (q: p sender ∧ p receiver := by decide) -> IO (GVal t receiver ep)



class Network (locs: List String) (ep: Loc locs) where
  com  {t:Type} [Serialize t]: (s: Loc locs) -> GVal t s ep -> (r: Loc locs) -> IO (GVal t r ep)



-- abbrev Location (net:Network) := {s: String // net.locations.contains s}
-- def Loc {net:Network} (s:String): (p:net.locations.contains s:=by decide) ->  Location net := fun p => ⟨s, p⟩

-- def testNet: Network := Network.mk ["bob", "alice"] [(⟨"bob", by decide⟩ , ⟨"alice", by decide⟩ )] (fun x y => sorry)

-- def bob: Location testNet := Loc  "bob"
-- def alice: Location testNet := Loc  "alice"


-- class Net (channels: ) (ep: String)  where
--   com {sender receiver: String} {t} [Serialize t]: GVal t sender ep -> (p: channels.contains (sender, receiver) := by decide) -> IO (GVal t receiver ep)

-- class Channel' (sender receiver ep: String) (net: Net) (p: net.contains (sender, receiver) := by decide)  where
--   send_recv {t} [Serialize t]: GVal t sender ep -> IO (GVal t receiver ep)


-- instance: BEq (Σ (s r e:String), Channel' s r e) where
--   beq := fun ⟨s1, r1, e1, _i1⟩ ⟨s2, r2, e2, _i2⟩  =>
--     s1 = s2 && r1 = r2 && e1 = e2

-- instance: LawfulBEq (Σ (s r e:String), Channel' s r e) where
--   eq_of_beq := by sorry
--   rfl := by sorry


--theorem teo: ∀ (s r e:String) (net:Met), net.names.contains (s,r,e) -> Channel' s r e := b

structure PhysChannel (sender receiver ep: Loc locs) where
  recv_sock: GVal Socket receiver ep
  send_sock: GVal Socket sender ep

-- structure PhysNet (locs: StrSet) (addresses: (s:String) -> s ∈ locs.items -> Address) where
--   recv_socks: (l1 l2: LocTy locs)  -> GVal Socket l1 l2
--   send_socks: (l1 l2: LocTy locs)  -> GVal Socket l1 l2

#check ToString Nat


class C (s: String)
def tl: List (Σ (r:String), C r) := [⟨ "hello", ⟨⟩ ⟩ ]
--#check (tl.lookup "hello").get (by decide)

structure SocketNet (ls: List (String)) (ep: Loc ls) where
  channels: List (Σ (s r:Loc ls), PhysChannel s r ep)
  all_to_all: ∀ (s r:String), s ∈ ls ∧ r ∈ ls ->
    (s, r) ∈ (channels.map (fun ⟨x, y, _z⟩  => (x, y)))

instance (snet: SocketNet locs ep): Network locs ep where
  com :=  fun s gv r =>
    let temp := ((snet.channels. s).get (by sorry))
    ((temp.lookup r).get (by sorry)).


-- epp for initializing one network socket
def init_sending_channel (sender ep: Loc locs) (addr: Address):  IO (GVal Socket sender ep) := do
  if h:(sender = ep) then
    IO.println s!"waiting for"-- {sender} -> {receiver}"
    let sock <- addr.connect_to
    return GVal.Wrap h sock
  else
    return GVal.Empty h

def init_receiving_channel (receiver ep: Loc locs) (addr: Address):  IO (GVal Socket receiver ep) := do
  if h:(receiver = ep) then
    IO.println s!"waiting for"-- {sender} -> {receiver}"
    let sock <- addr.listen_on
    return GVal.Wrap h sock
  else
    return GVal.Empty h


-- epp for initializing one network socket
def init_channel (sender receiver ep: Loc locs) (addr: Address):  IO (PhysChannel sender receiver ep) := do
  let recv_sock <- init_receiving_channel receiver ep addr
  let send_sock <- init_sending_channel sender ep addr
  return ⟨recv_sock, send_sock⟩

def init_network' (ls: List (Loc locs)) (ep:Loc locs) (port: UInt16) (current:Loc locs): List (Loc locs) -> IO (PyhsNet ls ep)
| a::as => do
  let addr: Address :=  .v4 ((.mk 127 0 0 1)) port
  let ch <- init_channel current a ep addr
  let rest <- init_network' ls ep (port + 1) current as
  return ⟨ rest.channels.concat ⟨current, a, ch⟩, by sorry⟩
| [] => do
  return ⟨ [], by sorry⟩

def init_network (ls: List (Loc locs)) (ep:(Loc locs)) (port: UInt16:=3333) (all: List (Loc locs)): (missing:List (Loc locs) :=all) -> IO (PyhsNet ls ep)
| a::as => do
  let rest <- init_network ls ep (port + UInt16.ofNat (all.length - 1)) all (missing:=as)
  let net <- init_network' ls ep port a all
  return ⟨ rest.channels ++ net.channels, by sorry⟩
| [] => do
  IO.println "finished network initilization\n"
  return ⟨[], by sorry⟩





inductive ChorEff {net: Network locs ep}: Type -> Type 1 where
| Send_recv [ser:Serialize a]: {sender:Loc locs} -> GVal a sender ep  -> (receiver:Loc locs) -> ChorEff (GVal a receiver ep)
| Local : (loc:Loc locs) -> ([∀ x, Coe (GVal x loc ep) x] -> IO a) -> ChorEff (GVal a loc ep)
| Calc : (loc:Loc locs) -> ([∀ x, Coe (GVal x loc ep) x] -> a) -> ChorEff (GVal a loc ep)

inductive Choreo (net: Network locs ep): Type -> Type 1  where
| Cond {decider: Loc locs}: GVal Bool decider ep -> (Choreo net a) -> (Choreo net a) -> Choreo net a
| Do :  ChorEff b (ep:=ep) (net:=net) -> (b -> Choreo net a) -> Choreo net a
| Return: a -> Choreo net a

def Choreo.bind (net: Network locs ep) {α β: Type}:
  Choreo net α → (α → Choreo net β ) → Choreo net β
| Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind net (next x) next')
| Choreo.Cond lv opt_a opt_b, next' =>
  Choreo.Cond lv (bind net opt_a next') (bind net opt_b next')
| Choreo.Return v, next' => next' v

instance (net: Network locs ep): Monad (Choreo net) where
  pure x := Choreo.Return x
  bind  := Choreo.bind net

def toChoreo (net: Network locs ep) (eff: ChorEff a (net:=net)) : Choreo net a :=
   Choreo.Do eff (Choreo.Return)

def send_recv {net: Network locs ep}
  {a:Type} [Serialize a] (gv: GVal a sender ep) (receiver: Loc locs) := toChoreo net (ChorEff.Send_recv gv receiver ) (a:=GVal a receiver ep)
def locally {net: Network locs ep}
  (loc: Loc locs) (comp: [∀ x, Coe (GVal x loc ep) x] -> IO b) := toChoreo net (ChorEff.Local loc comp) (a:=GVal b loc ep)

def compute {net: Network locs ep}
  (loc: Loc locs) (comp: [∀ x, Coe (GVal x loc ep) x] -> b) := toChoreo net (ChorEff.Calc loc comp)

def branch {net: Network locs ep}
    {decider: Loc locs} (choice: GVal Bool decider ep) (opt_a: Choreo net a) (opt_b: Choreo net a) := Choreo.Cond choice opt_a opt_b

def branch' {net: Network locs ep}
  {a:Type} [Serialize b] (comp: [∀ x, Coe (GVal x decider ep) x] -> IO b) (cont: b -> Choreo net a):=
  do
  let gv <- locally decider comp
  Choreo.Cond gv cont

def send_recv_comp {net: Network locs ep} {a:Type} (endpoint: String) [Serialize b] (sender receiver: Loc locs) (comp: [∀ x, Coe (GVal x sender ep) x] -> IO b):=
  do
  let gv <- locally sender comp
  toChoreo net (ChorEff.Send_recv gv receiver) (a:= GVal b receiver ep)


def ChorEff.epp {net: Network locs ep}: ChorEff a (net:=net)
   -> IO a
| ChorEff.Send_recv gv receiver (a:=a) (ser:=ser) (sender := sender) => do
  net.com gv receiver

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
  have h: sizeOf (next res) < 1 + sizeOf eff := by sorry
  Choreo.epp (next res)
| Choreo.Cond gv opt_a opt_b (decider:= decider) (ep:=ep) => do
  let endpoint_choice <- net.com gv ep
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

def tmm: List (String × String) := [("alice", "bob")]

def tnet: List abs_channel := [⟨"alice", "eve" ⟩,
    ⟨"eve", "bob"⟩,
    ⟨"bob", "alice"⟩,
  ]

def locs: List String := ["alice", "bob", "eve"]


syntax "decision " ident " yes: " term " no: " term: term

syntax "decision " ident term " else " term: term

macro_rules
| `(decision $i yes: $t1 no: $t2) => `(branch $i ($t1) ($t2))
| `(decision $i $t1 else $t2) => `(branch $i ($t1) ($t2))

def L {locs: List String} (s:String):  (p: s ∈ locs := by decide) -> Loc locs :=
  fun p => ⟨s, p⟩

def alice: Loc locs := L "alice"
def bob: Loc locs := L "bob"
def eve: Loc locs := L "eve"

def silent_post  (ep: Loc locs) (net: Network locs ep):
  Choreo net (GVal (List String) ⟨alice, by decide⟩ ep) := do

  let input: GVal String alice ep <- locally alice do
    IO.println "enter a message"
    return <- IO.getLine


  --let msg <- input ~> (L "eve")
  send input from alice to eve

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

  let d <- locally eve do return false

  let s <-
  decision d do
    return "hello"
  else do
    return "not hello"

  let r <- branch d
    (do return "hello")
    (do return "not hello")

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


-- def testio: IO Unit := do
--   let te := ["hello", "world"]
--   let te2 <- te.filterMap (fun x => IO.println x)
--   return ()

-- #eval testio
