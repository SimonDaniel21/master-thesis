import Test.my_utils
import chorlean.Network
import Std.Data.Option.Basic
import Mathlib

variable (α β: Type)
--def myMap := {l: Lean.AssocList α β // l.}

def str_order (s1 s2: String) : Ordering :=
  if s1 == s2 then
    Ordering.eq
  else if s1 < s2 then
    Ordering.lt
  else
    Ordering.gt

open Lean (HashMap)

def tm :Lean.HashMap Nat Nat := Lean.HashMap.ofList [(1,1)]

@[reducible] def TStore:= List Type
@[reducible] def VStore:= List
@[reducible] def GStore:= Lean.AssocList String LStore

-- Structure that holds a String used as Names for Locations and a proof that this location exists in a given GStore gs
structure Loc (gs:GStore) where
  s: String
  p: (gs.find? s).isSome := by decide

instance (gs:GStore): BEq (Loc gs) where
  beq a b := a.s == b.s

@[reducible] def GStore.at (gs:GStore) (loc: Loc gs):=
  (gs.find? loc.s).get loc.p

@[reducible] def GStore.push (gs:GStore) (a:Type) (loc: Loc gs) :GStore :=
  gs.insert loc.s ((gs.at loc).concat a)

#check HashMap.find!

structure LVal (a:Type) (s: LStore) where
  n: Nat
  p1: n < s.length := by decide
  p2: (s[n]' p1) = a := by simp

structure GVal (a:Type) (gs: GStore) (loc: Loc gs) where
  lv: LVal a (gs.at loc)

variable (m:HashMap Nat Unit)
variable (v1 v2: Nat)


open Lean.HashMap


variable (α: Type)
variable (l: List α)
variable (v: α)
--variable (x: Nat)


structure Wrap (a:Type) (v:a) (gs: GStore) (loc:Loc gs)  where
  ls := (gs.at loc).concat a
  ngs := (gs.erase loc.s).insert loc.s ls
  nloc: Loc ngs := ⟨loc.s, by sorry⟩
  i := ls.length - 1
  lv: LVal a ((ngs.find? nloc.s).get (sorry)) := LVal.mk i (sorry) (sorry)
  gv: GVal a ngs nloc := GVal.mk lv

@[reducible] def Wrap_f (a:Type) (v:a) (gs: GStore) (loc:Loc gs) :=
  let ls := (gs.at loc).concat a
  let ngs := (gs.erase loc.s).insert loc.s ls
  let nloc: Loc ngs := ⟨loc.s, by sorry⟩
  let i := ls.length - 1
  let lv: LVal a ((ngs.find? nloc.s).get (sorry)) := LVal.mk i (sorry) (sorry)
  let gv: GVal a ngs nloc := GVal.mk lv
  gv


abbrev test_store: LStore := [(⟨String, "asf"⟩) , ⟨Nat, 3423⟩]
def test_env: GStore := [("alice", test_store)].toAssocList'
def lvv1: LVal String test_store := LVal.mk 0
#check ((test_env.find? "alice").get (sorry))


#check Wrap_f Nat 3

def wrapped := Wrap_f String "hello" test_env (Loc.mk "alice")

#check wrapped

#eval wrapped.lv.n

def LVal.unpack (lv: LVal a s) (s2: LStore): a :=
  cast lv.p2 (s[lv.n]'lv.p1).snd

def GVal.unwrap  {gs:GStore} {loc:Loc gs} (gv: GVal a gs loc): LVal a (gs.at loc) :=
  gv.lv

def GVal.unpack  {gs:GStore} {loc:Loc gs} (gv: GVal a gs loc): a :=
  let temp: LVal a (gs.at loc) := gv.lv
  LVal.unpack temp


#eval dist_val.unpack
#eval wrapped.unpack


infixl:55 "@" => fun {gs:GStore} (a:Type) (loc:String) => GVal a loc gs

def Unwrap {gs:GStore} (loc:Loc gs) := {a:Type} -> GVal a gs loc -> a

-- def change_loc {a:Type} (v:a) (gs: GStore) (fr to: Loc gs) (gv: GVal a gs fr)  :=
--   let ngv := Wrap_f a v gs to
--   let nls := (gs.at to).concat ⟨a, v⟩

--   gs.insert to.s ngv



mutual
  inductive ChorEff (gs:GStore): Type -> Type 1 where
  | Send_recv [Serialize a] {sender:Loc gs}:   (gv: GVal a gs sender) -> (receiver: Loc gs) -> ChorEff gs (Wrap_t a (gv.unpack) gs receiver)
  | Local : (loc:Loc gs) -> (Unwrap loc -> IO a) -> ChorEff gs (Wrap_t a (gv.unpack) gs receiver)
  -- | Calc : (loc:Loc gs) -> (Unwrap loc -> a) -> ChorEff gs (a )
  -- | Cond [Serialize a] {decider:String}: a  -> (a -> Choreo gs b) -> ChorEff gs b

  inductive Choreo (gs:GStore): Type -> Type 1  where
  | Do {ngs:GStore} :  ChorEff gs b -> (b -> Choreo gs a) -> Choreo gs a
  | Return: a -> Choreo gs a
end



def toChoreo {gs:GStore} (eff: (ChorEff gs a)) : Choreo gs a :=
  Choreo.Do eff (Choreo.Return ) (ngs:= [].toAssocList')



def Choreo.bind {gs: GStore} {α β :Type}: Choreo gs α → (α → Choreo gs β) → Choreo gs β
  | Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next') (ngs:= [].toAssocList')
  | Choreo.Return v, next' => next' v
decreasing_by sorry

instance {gs: GStore}: Monad (Choreo gs) where
  pure x := Choreo.Return x
  bind  := Choreo.bind

--def send_recv {a:Type} [Serialize a] (vl: a @ sender) (receiver:String) (_dont_send_to_yourself: sender != receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def send_recv {a:Type}  {gs:GStore} {sender receiver: Loc gs} [Serialize a] (gv: GVal a gs sender) := toChoreo (ChorEff.Send_recv gv receiver )
def locally {gs:GStore} {a:Type} (loc: Loc gs) (comp: (Unwrap loc -> IO a)) := toChoreo (ChorEff.Local loc comp)
-- def compute {net: List abs_channel} (loc: String) (comp: (Unwrap loc) -> b) := toChoreo (ChorEff.Calc loc comp (net:=net))
-- def branch {net: List abs_channel} {a:Type} [Serialize a] (lv: a @ decider) (cont: a -> Choreo b):= toChoreo (ChorEff.Cond lv cont (net:=net))

-- def send_recv_locally {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> IO a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let lv <- toChoreo (ChorEff.Local sender comp)
--   toChoreo (ChorEff.Send_recv lv receiver)

-- def send_recv_pure {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let r := wrap (comp unwrap) sender
--   toChoreo (ChorEff.Send_recv r receiver)


mutual

  def ChorEff.epp {gs: GStore}: ChorEff gs a -> Loc gs -> Network a
  | ChorEff.Send_recv (gv) receiver (sender:=sender) (a:=a) , l => do
    let v := gv.unpack
    if h: (sender == receiver) then
      return Wrap_f a v gs receiver
    if (sender == l) then
      send receiver.s v
      return Wrap_f a v gs receiver
    else if (receiver == l) then
      --recv {a : Type} (loc : String) [inst✝ : Serialize a] : Network a
      let response <- (recv sender.s (a:=a))
      return Wrap_f a v gs receiver
    else
      return Wrap_f a v gs receiver

  | ChorEff.Local l1 comp (a:=a), l2 => do
    if j:( l1 == l2) then
      let res <- run (comp (GVal.unpack))
      return GVal.mk a res gs l2
    else
      return Wrap_f a res gs l1
  -- | ChorEff.Calc l1 comp, l2 => do
  --   if j:( l1 == l2) then
  --     return wrap (comp (unwrap)) l1
  --   else
  --     return .Empty
  -- | ChorEff.Cond lv fn (decider:=decider), loc => do
  --   if (loc == decider) then
  --     let choice := (unwrap lv)
  --     broadcast choice
  --     (fn (unwrap lv)).epp loc
  --   else
  --     let choice <- (recv decider)
  --     (fn choice).epp loc

  def Choreo.epp {gs: GStore}: Choreo gs a ->  Loc gs -> LStore -> Network a
  | Choreo.Return v, _l, _ls => Network.Return v
  | Choreo.Do eff next, loc, ls => do
    let res <- (eff.epp loc)
    Choreo.epp (next res) loc ls
  decreasing_by sorry --TODO
end


notation:55 lv "~>" receiver => send_recv lv receiver


def tLoc: Loc test_env := ⟨ "alice", by decide⟩

def dist_val: GVal String test_env (Loc.mk "alice")  := GVal.mk (LVal.mk 0 (s:=test_store))


abbrev silent_gs_local: LStore :=[⟨Nat, 2⟩]
def silent_gs: GStore := [("alice", silent_gs_local), ("bob", []), ("eve", [])].toAssocList'

def alice: Loc silent_gs := ⟨ "alice", by decide⟩

def tg: GVal Nat silent_gs alice :=

  GVal.mk (LVal.mk 0 (s:=silent_gs_local))

def silent_post: Choreo silent_gs (GVal (List String) silent_gs (Loc.mk "alice")) := do

  -- let input: String @ "alice" <- locally "alice" (fun _ => do
  --   IO.println "enter a message"
  --   return <- IO.getLine
  -- )

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
