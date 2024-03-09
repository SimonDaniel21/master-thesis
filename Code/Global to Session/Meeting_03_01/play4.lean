import Test.my_utils
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

inductive Example_Location
| alice | eve | bob
deriving Repr, Fintype
open Example_Location

variable {α β: Type} -- alpha beta als normaler Type
variable {δ: Type} [DecidableEq δ]  -- delta als Location Type
variable {μ: Type} [Serialize μ]  -- mu wegen msg Type

inductive GVal (owner endpoint: δ) (α: Type)   where
| Wrap:  (owner = endpoint) -> α -> GVal owner endpoint α
| Empty: (owner ≠ endpoint) -> GVal owner endpoint α

inductive LVal (owner: δ) (α:Type)

#check ReaderT

--def LVal {δ:Type}  := δ -> Type

def GVal.wrap (owner:δ) (endpoint: δ) (v:α) : GVal owner endpoint α :=
  if h:(owner = endpoint) then
    GVal.Wrap h v
  else
    GVal.Empty h

def GVal.unwrap {owner endpoint: δ}: GVal owner endpoint α -> (owner = endpoint) -> α
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction

class Network (ep: δ) (m: Type -> Type) where
  com {μ:Type} [Serialize μ]: {s: δ} -> GVal s ep μ -> (r: δ) -> m (GVal r ep μ)

instance: Network ep IO where
  com := sorry

variable {M : Type → Type }



inductive ChorEff (ep:δ) (LM: δ ->  (m: Type -> Type) × Monad m): Type -> Type 1 where
| Send_recv {μ:Type} [Serialize μ]: {sender:δ} -> GVal sender ep μ -> (receiver:δ) -> ChorEff ep LM (GVal receiver ep μ)
| Local {α:Type}: (loc:δ) -> ((LM ep).1 α) -> ChorEff ep LM (GVal loc ep α)

inductive Choreo (ep:δ) (LM: δ -> (m:Type -> Type) × Monad m := (fun _ => ⟨IO, inferInstance⟩)) : Type u -> Type (u+1)  where
| Do :  ChorEff ep LM b -> (b -> Choreo ep LM a) -> Choreo ep LM a
| Return: a -> Choreo ep LM a

def Choreo.bind {α β: Type}:
  Choreo LM ep α → (α  → Choreo LM ep β) → Choreo LM ep β
| Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
| Choreo.Return v, next' => next' v

instance: Monad (Choreo LM ep) where
  pure x := Choreo.Return x
  bind := Choreo.bind

def ChorEff.epp (eff: ChorEff ep LM a (δ:=δ)) [net:Network ep (LM ep)]: (LM ep).1 a :=
  have: Monad (LM ep).1 := (LM ep).2
  match eff with
  | ChorEff.Send_recv gv receiver =>
    net.com gv receiver
  | ChorEff.Local loc op => do
    let res <- op
    let gv := GVal.wrap loc ep res
    return gv



def Choreo.epp {α:Type} (chor:Choreo ep LM α (δ:=δ)) [Network ep (LM ep)]: (LM ep).1 α :=
  have: Monad (LM ep).1 := (LM ep).2
  match chor with
  | Choreo.Do eff next => do
    let e <- eff.epp
    let rest := next e
    rest.epp
  | Choreo.Return v => return v


def locally (loc: δ) (op: (LM ep).1 a) [Monad (LM ep).1]: Choreo ep LM (GVal loc ep a) :=
  have: Monad (LM ep).1 := (LM ep).2
  Choreo.Do (ChorEff.Local loc op) (fun x => Choreo.Return x)

def send_recv {sender:δ} (gv: GVal sender ep μ) (receiver:δ): Choreo ep LM (GVal receiver ep μ) :=
  Choreo.Do (ChorEff.Send_recv gv receiver) (fun x => Choreo.Return x)

def F : Nat → (m : Type -> Type) × Monad m
  | 0 => ⟨IO, inferInstance⟩
  | 1 => ⟨ReaderM Nat, inferInstance⟩
  | _ => ⟨Option, inferInstance⟩

-- this line is a bit of a hack
attribute [local instance] Sigma.snd in
def multiMonad : (n : Nat) → (F n).1 Unit
  | 0 => do
    -- in IO
    IO.println "hello"
    return ()
  | 1 => do
    let temp <- pure
    return ()
  | _ => do
    -- in Option
    return ()


-- this line is a bit of a hack
attribute [local instance] Sigma.snd in
def multiMonad : (n : Nat) → (F n).1 Unit
  | 0 => do
    -- in IO
    return ()
  | _ => do
    -- in Option
    return ()


def LocalProgs: Example_Location ->  (m: Type -> Type) × Monad m
| bob => ⟨IO, inferInstance⟩
| alice => ⟨ReaderM Nat, inferInstance⟩
| eve => ⟨IO, inferInstance⟩

--attribute [local instance] Sigma.snd in
def dist_prog2 (ep: Example_Location): (Choreo ep LocalProgs) Nat :=
  have: Monad (LocalProgs bob).fst := (LocalProgs bob).snd
  do

  let temp <- locally bob (do
    IO.println "hello"
    return "")
  let temp <- locally alice (do
    let bla <- read
    return "")
  let tt2 <- send_recv temp bob
  return 23


inductive PrintIO (α:Type)
| Print: String -> (PrintIO α) -> PrintIO α
| Return: α -> PrintIO α

def PrintIO.run: PrintIO α -> IO α
| PrintIO.Print s next => do
  IO.println s
  next.run
| Return v => return v

def PrintIO.bind {α β : Type} : PrintIO α → (α → PrintIO β) → PrintIO β
| Return v, next => next v
| Print s cont, next =>
  PrintIO.Print s (bind (cont) next)

instance: Monad PrintIO where
  pure x := .Return x
  bind := PrintIO.bind

instance : MonadLift  PrintIO IO where
  monadLift pio := pio.run

def print (s: String): PrintIO Unit := .Print s (.Return ())

def prog: PrintIO Unit :=do
  print "Hello"

def Main: IO Unit := do
  prog
  return ()

#eval Main

class Printer (α:Type) where
  print: String -> Unit
