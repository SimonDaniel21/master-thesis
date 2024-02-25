import Test.my_utils
import chorlean.Network
import Std.Data.Option.Basic

def str_order (s1 s2: String) : Ordering :=
  if s1 == s2 then
    Ordering.eq
  else if s1 < s2 then
    Ordering.lt
  else
    Ordering.gt

@[reducible] def LStore:= List ((a: Type ) × a)
@[reducible] def GStore:= Lean.AssocList String LStore

@[reducible] def GStore.has (gs:GStore) (loc:String): Prop :=
  (gs.find? loc).isSome

@[reducible] def GStore.at (gs:GStore) (loc:String) (p: gs.has loc := by decide) :=
  (gs.find? loc).get p

@[reducible] def GStore.with (gs:GStore) (a:Type) (loc:String) (v:a) (p: gs.has loc := by decide):GStore :=
  (gs.erase loc).insert loc ((gs.at loc p).concat ⟨a, v⟩)


structure Location (s:String) (gs:GStore) where
  p: gs.has s

#check Lean.HashMap.find!

structure LVal (a:Type) (s: LStore) where
  n: Nat
  p1: n < s.length := by decide
  p2: (s[n]' p1).fst  = a := by simp

-- @[reducible] def GVal (a:Type) (loc:String) (env: GStore) ( p: (env.find? loc).isSome := by decide) :=
--   LVal a ((env.find? loc).get p)

-- structure GVal (a:Type) (loc:String) (env: GStore) where
--   n: Nat
--   p: (env.find? loc).isSome := by decide
--   s := (env.find? loc).get p
--   p1: n < s.length := by decide
--   p2: (s[n]' p1).fst  = a := by simp

structure GVal (a:Type) (loc:String) (gs: GStore) where
  lv: LVal a (gs.at loc p)
  p: gs.has loc := by decide


open Lean.HashMap

def test1: Lean.AssocList Nat Nat := [(2,1)].toAssocList'

#eval (test1.erase 2).toList

#eval (([(1,2), (2,4)].toAssocList').insert 1 3).toList

abbrev test_store: LStore := [(⟨String, "asf"⟩) , ⟨Nat, 3423⟩]
def test_env: GStore := [("alice", test_store)].toAssocList'


structure Wrap (a:Type) (v:a) (loc:String) (gs: GStore) where
  p1 : gs.has loc := by decide
  ls := (gs.at loc p1).concat ⟨a, v⟩
  ngs := (gs.erase loc).insert loc ls
  i := ls.length - 1
  lv: LVal a ((ngs.find? loc).get (sorry)) := LVal.mk i (sorry) (sorry)
  gv: GVal a loc ngs := GVal.mk lv (by sorry)

def wrap (a:Type) (v:a) (loc:String) (gs: GStore) (p1 : gs.has loc := by decide): GVal a loc (gs.with a loc v) :=
  let ls := (gs.at loc p1).concat ⟨a, v⟩
  let ngs := (gs.erase loc).insert loc ls
  let i := ls.length - 1
  let lv: LVal a ((ngs.find? loc).get (sorry)) := LVal.mk i (sorry) (sorry)
  let gv: GVal a loc ngs := GVal.mk lv (by sorry)
  gv

def lvv1: LVal String test_store := LVal.mk 0
#check ((test_env.find? "alice").get (sorry))
def dist_val: GVal String "alice" test_env := GVal.mk (LVal.mk 0 (s:=test_store))

def wrapped: Wrap Nat 3 "alice" test_env := Wrap.mk sorry sorry sorry sorry sorry sorry

#eval wrapped.lv

def LVal.unpack (lv: LVal a s): a :=
  cast lv.p2 (s[lv.n]'lv.p1).snd

def GVal.unpack {loc:String} {e:GStore} (gv: GVal a loc e): a :=
  let temp: LVal a ((e.find? loc).get gv.p) := gv.lv
  LVal.unpack temp


#eval dist_val.unpack


infixl:55 "@" => fun {gs:GStore} (a:Type) (loc:String) => GVal a loc gs

def Unwrap (loc:String) {a:Type} {gs:GStore} := GVal a loc gs -> a

mutual
  inductive ChorEff : Type -> Type 2 where
  | Send_recv [Serialize a] {gs:GStore} {sender:String}:  (gv: GVal a sender gs) -> (receiver: String) ->
    let a := 3
    ChorEff ( ((gs.find? receiver).get gs'.p)[])
  | Local : (loc:String) -> (Unwrap loc -> IO a) -> ChorEff (a @ loc)
  | Calc : (loc:String) -> (Unwrap loc -> a) -> ChorEff (a @ loc)
  | Cond [Serialize a] {decider:String}: a @ decider -> (a -> Choreo b) -> ChorEff b

  inductive Choreo: Type -> Type 2  where
  | Do :  ChorEff b -> (b -> Choreo a) -> Choreo a
  | Return: a -> Choreo a
end



def toChoreo (eff: (ChorEff a)) : Choreo a :=
   Choreo.Do eff (Choreo.Return)



def Choreo.bind: Choreo α → (α → Choreo β ) → Choreo β
  | Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
  | Choreo.Return v, next' => next' v
decreasing_by sorry

instance: Monad (Choreo) where
  pure x := Choreo.Return x
  bind  := Choreo.bind

--def send_recv {a:Type} [Serialize a] (vl: a @ sender) (receiver:String) (_dont_send_to_yourself: sender != receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def send_recv {a:Type} {sender receiver: String} {gs:GStore} [Serialize a] (gv: GVal a sender gs) (receiver:String) := toChoreo (ChorEff.Send_recv gv receiver )
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
