import Test.my_utils
import chorlean.Network

inductive LocVal (α: Type) (loc: String) where
| Wrap: α -> LocVal α loc
--| Failure: LocVal α loc
| Empty: LocVal α loc


@[reducible] def Store:= List ((a: Type ) × a)
@[reducible] def Env:= Lean.AssocList String Store


def fn2: Unit :=
  let v_opt: Option Nat := .some 2
  let p: v_opt.isSome := by trivial
  match v_opt, p with
  | some v, _ => ()


def helper (s:Store):= {n:Nat // n < s.length}


@[reducible] def lvv (a:Type) (s: Store) := { k: {n:Nat // n < s.length}  //
  let ⟨n2, p⟩ := k
  (s[n2]'p).fst  = a}

@[reducible] def dist_val (a:Type) (loc:String) (e: {env:Env // (env.contains loc)}) :=
  let ⟨en, p⟩ := e
  let loc_store := en.find? loc
  match loc_store with
  | some s => lvv a s
  | none => lvv a []



abbrev test_store: Store := [(⟨String, "asf"⟩) , ⟨Nat, 3423⟩]

def type1 := Unit
def type2 := Unit

def val1:type1 := ()
def val2:type2 := ()

def val3: type1 := val2

def testNat: Nat := 0

def lvv1: lvv String test_store := ⟨⟨  0, by decide⟩ , by simp⟩

#eval test_store[1].snd

def lvv.unpack (lv: lvv a s): a :=
  let ⟨k, p1⟩  := lv
  let ⟨n, p2⟩  := k
  let v := s[n]'p2
  let v_a: a := cast p1 v.snd
  v_a


#eval lvv1.unpack

inductive lv {a:Type} (i:Nat) (s: Store) (h1:i < s.length) (h2: s[i].fst = a) (h3: s[i].fst = a) [BEq a] where
| key: (v:a) -> ((s[i]'h1).snd == v) -> lv i s h1 h2 h3

def temmmm: lv 3 [(⟨String, "asf"⟩)] (by sorry) (by sorry) := lv.key 2

#reduce test_store[0].fst
abbrev Env:= List (String × Store)

-- @[reducible] def LocValT:= (a:Type) ->  (loc:String) ->  Type 1
-- abbrev LocVal (a:Type) := (s:Store) -> (i:Nat) -> (p: i < s.length:=by decide) -> (h: (s[i]'p).fst = a) -> a

-- inductive LocVal1 (α: Type) (loc: String) where
-- | v: LocVal1 α loc

-- inductive LocVal2 (α: Type) (loc: String) where
-- | Key: Nat -> LocVal2 α loc

--def aaa: LocVal2 Nat "alice" := ⟨222⟩

def some_nat2: (t:Type) × t := ⟨Nat, 2⟩ -- works
abbrev List_of_different_types := List ((t:Type) × t)
def List_of_different_types2 := List ((t:Type) × List t)

def tet: List_of_different_types2 := [⟨Nat,[2,3,4]⟩]


def test_list: List_of_different_types := [⟨Nat, 32⟩]

#eval test_list[0].snd

--def List_of_different_types := List ((t:Type) × t)
--def List_of_different_types.store: List_of_different_types

-- def LocVal_store.insert (s:LocVal_store) (v:a):  (LocVal_store × Nat) :=
--   (s.concat ⟨a,v⟩, s.length)



def temp: LocVal_store := []
-- def temp2 := temp.insert 2
-- def store2 := temp2.fst
-- def key2 := temp2.snd
-- def tempppo := store2[0]
-- #eval tempppo.snd

def testlist := [2,3,4]
def testlist2 := testlist.concat 10

#check List.get
def tttt := testlist2[3]


def test_list2: List_of_different_types := [⟨Nat, 32⟩, ⟨String, "hello"⟩]

infixl:55 "@" => LocVal

def notEmpty: LocVal a l -> Bool
| LocVal.Wrap _ =>  true
| LocVal.Empty => false


def valid (a:Type) (loc:String) := { vl: a @ loc // notEmpty vl }

infixl:55 "#@" => valid

def test: Nat #@ alice := ⟨LocVal.Wrap 3, by trivial⟩

class Key (l: String) where
  unwrap : (a @ l) → a

instance (l:String) : Key l where

-- def valid.bind: valid a1 @ l1 → (b → valid a2 @ l2) → valid a2 @ l2
-- | ⟨ lv, p ⟩ => match lv with
--   | .Wrap v, f => v
--   | .Failure, _f => .Failure

-- def wrap {a} (v:a) (l: String): a #@ l :=
--   ⟨ LocVal.Wrap v, by trivial ⟩


-- def unwrap: a #@ l -> a
-- | ⟨ lv, _ ⟩ => match lv with
--   | .Wrap v => v



def Unwrap (l:String)  :=   {a:Type} -> a @ l -> a

--def local_func (a:Type) (l:String):= (Unwrap l -> a)
--def local_prog (a:Type) (l:String):= (Unwrap l -> IO a)

abbrev abs_channel := (String × String)



abbrev LocVal_sstore:= List ((a:Type )  × a)

--abbrev lloc := (a:Type) -> (loc:String) -> (s:LocVal_sstore) -> (i:{n:Nat //(n < s.length)}) -> (h: (s[i]'i).fst = a) -> a

abbrev lloc := (a:Type) -> (loc:String) -> (s:LocVal_sstore) -> (i:Nat) -> (p: i < s.length:=by decide) -> (h: (s[i]'p).fst = a) -> a


def testLLoc: lloc Nat "client"

mutual
  inductive ChorEff {net: List abs_channel} : Type -> Type 1 where
  | Send_recv [Serialize a]: {s_store r_store:LocVal_sstore} -> {sender:String} -> LocVal2 a sender -> (receiver:String) -> (contains_channel: net.contains (sender, receiver) := by decide) -> ChorEff (LocVal2 a receiver)
  | Local : (loc:String) -> (Unwrap loc -> IO a) -> ChorEff (a @ loc)
  | Calc : (loc:String) -> (Unwrap loc -> a) -> ChorEff (a @ loc)
  | Cond [Serialize a]: a @ decider -> (a -> Choreo b) -> ChorEff b

  inductive Choreo {net: List abs_channel}: Type -> Type 1  where
  | Do :  ChorEff b -> (b -> Choreo a) -> Choreo a
  | Return: a -> Choreo a
end



def toChoreo (eff: (ChorEff a (net:=net))) : Choreo a (net:=net) :=
   Choreo.Do eff (Choreo.Return)



def Choreo.bind: Choreo α (net:=net) → (α → Choreo β (net:=net)) → Choreo β (net:=net)
  | Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
  | Choreo.Return v, next' => next' v
decreasing_by sorry

instance: Monad (Choreo (net:=net)) where
  pure x := Choreo.Return x
  bind  := Choreo.bind

class Kee (l: String) where
  unwrap : Nat → LocVal a l → a

abbrev Store:= List (String × LocVal_store)
def Store_ := List ((t: Type) × Nat × t)
--def Store_.unwrap : (s:Store_) -> Kee l → LocVal a l → a :=
--instance Key Store where unwrap := Store.unwrap



def LocVal_store.valid (store: Store) (lv: a @ l) (val: a): Prop :=
  have hp := store.length > lv.kee
  let temp := store[lv.kee]
  (hp) ∧ (store[lv.kee]!).fs

--def send_recv {a:Type} [Serialize a] (vl: a @ sender) (receiver:String) (_dont_send_to_yourself: sender != receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def send_recv {a:Type} {store:LocVal_store} {net: List abs_channel} [Serialize a] (vl: a @ sender) (receiver:String) (contains_channel: net.contains (sender, receiver) := by decide) := toChoreo (ChorEff.Send_recv vl receiver contains_channel (net:=net))
def locally {net: List abs_channel} (loc: String) (comp: (Unwrap loc) -> IO b) := toChoreo (ChorEff.Local loc comp (net:=net))
def compute {net: List abs_channel} (loc: String) (comp: (Unwrap loc) -> b) := toChoreo (ChorEff.Calc loc comp (net:=net))
def branch {net: List abs_channel} {a:Type} [Serialize a] (lv: a @ decider) (cont: a -> Choreo b):= toChoreo (ChorEff.Cond lv cont (net:=net))

-- def send_recv_locally {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> IO a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let lv <- toChoreo (ChorEff.Local sender comp)
--   toChoreo (ChorEff.Send_recv lv receiver)

-- def send_recv_pure {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let r := wrap (comp unwrap) sender
--   toChoreo (ChorEff.Send_recv r receiver)


mutual

  def ChorEff.epp_vars: ChorEff a (net:=net) -> (loc: List String) -> (LocVal_store)  -> Network a
  | ChorEff.Send_recv lv receiver contains_channel (sender:=sender), l, env => do
    if h: (sender == receiver) then
      match lv with
      | .Key k =>
        let un := env[k]?
        return LocVal2.Key k
    if (sender == l) then
      send receiver (unwrap lv)
      return .Empty
    else if (receiver == l) then
      let response <- (recv sender)
      return wrap response receiver
    else
      return .Empty
  | ChorEff.Local l1 comp, l2, env => do
    if j:( l1 == l2) then
      let res <- run (comp (unwrap))
      return wrap res l1
    else
      return .Empty
  | ChorEff.Calc l1 comp, l2, env => do
    if j:( l1 == l2) then
      return wrap (comp (unwrap)) l1
    else
      return .Empty
  | ChorEff.Cond lv fn (decider:=decider), loc, env => do
    if (loc == decider) then
      let choice := (unwrap lv)
      broadcast choice
      (fn (unwrap lv)).epp loc
    else
      let choice <- (recv decider)
      (fn choice).epp loc

  def Choreo.epp: Choreo a (net:=net) -> String -> Network a
  | Choreo.Return v, _ => Network.Return v
  | Choreo.Do eff next, loc => do
    let res <- (eff.epp loc)
    Choreo.epp (next res) loc

end


mutual



  def ChorEff.epp: ChorEff a (net:=net) -> String -> Network a
  | ChorEff.Send_recv lv receiver contains_channel (sender:=sender), l => do
    if h: (sender == receiver) then
      let unwr := (unwrap ⟨ lv,  sorry⟩ )
      return wrap (unwrap ⟨ lv,  sorry⟩ ) receiver
    if (sender == l) then
      send receiver (unwrap lv)
      return .Empty
    else if (receiver == l) then
      let response <- (recv sender)
      return wrap response receiver
    else
      return .Empty
  | ChorEff.Local l1 comp, l2 => do
    if j:( l1 == l2) then
      let res <- run (comp (unwrap))
      return wrap res l1
    else
      return .Empty
  | ChorEff.Calc l1 comp, l2 => do
    if j:( l1 == l2) then
      return wrap (comp (unwrap)) l1
    else
      return .Empty
  | ChorEff.Cond lv fn (decider:=decider), loc => do
    if (loc == decider) then
      let choice := (unwrap lv)
      broadcast choice
      (fn (unwrap lv)).epp loc
    else
      let choice <- (recv decider)
      (fn choice).epp loc

  def Choreo.epp: Choreo a (net:=net) -> String -> Network a
  | Choreo.Return v, _ => Network.Return v
  | Choreo.Do eff next, loc => do
    let res <- (eff.epp loc)
    Choreo.epp (next res) loc

end
decreasing_by sorry --TODO
def wrapped := wrap 3 "bob"
def unwrapped := unwrap wrapped (l:="bob")
#eval unwrapped



notation:55 lv "~>" receiver => send_recv lv receiver

--notation:55 sender "~>" receiver "##" comp => send_recv_locally sender receiver comp
--notation:55 sender "~>" receiver "pure" comp => send_recv_pure sender receiver comp


def test_net: List abs_channel :=
  [
    ("alice", "eve"),
    ("eve", "bob"),
    ("bob", "alice")
  ]

def silent_post: Choreo ((List String) @"alice") (net:= test_net):= do

  let input: String @ "alice" <- locally "alice" (fun _ => do
    IO.println "enter a message"
    return <- IO.getLine
  )

  let msg <- input ~> "eve"
  let msg <- locally "eve" fun un => return [(un msg), "eve"]

  let msg <- msg ~> "bob"

  let msg <- locally "bob" fun un => return (un msg).concat "bob"

  let msg <- send_recv msg "alice"
  return msg


def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network test_cfg mode
  let res <- ((silent_post).epp mode).run mode net
  IO.println (s!"res: {res}")
  return ()
