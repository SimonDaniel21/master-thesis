import Test.my_utils
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib
inductive Example_Location
| alice | eve | bob
deriving Repr, Fintype
open Example_Location

inductive GVal (owner endpoint: δ) (α: Type)   where
| Wrap:  (owner = endpoint) -> α -> GVal owner endpoint α
| Empty: (owner ≠ endpoint) -> GVal owner endpoint α

inductive LVal (owner: δ) (α:Type)

#check ReaderT

--def LVal {δ:Type}  := δ -> Type

def GVal.wrap (owner endpoint: δ) (v:α) : GVal owner endpoint α :=
  if h:(owner = endpoint) then
    GVal.Wrap h v
  else
    GVal.Empty h

def GVal.unwrap {owner endpoint: δ}: GVal owner endpoint α -> (owner = endpoint) -> α
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction

class Network {δ:Type} (ep: δ) where
  com [Serialize α]: (s: δ) -> GVal s ep α -> (r: δ) -> IO (GVal r ep α)


inductive ProgEff (δ:Type) : Type -> Type 1  where
| run : (loc:δ) -> (IO a) -> ProgEff δ (GVal loc ep a)


inductive Prog (δ:Type) : Type -> Type 1  where
| Do :  ProgEff δ b -> (b -> Prog δ a) -> Prog δ a
| Return {a:Type}: a -> Prog δ a


inductive ChorEff' (δ:Type) (ep:δ): Type -> Type 1  where
| Send_recv {a:Type} : {sender:δ} -> GVal sender ep a -> (receiver:δ) -> ChorEff' δ (LVal receiver α)
| Local : (loc:δ) -> (IO a) -> ChorEff' δ (LVal loc a)

inductive Choreo' (δ:Type) : Type -> Type 1  where
| Do :  ChorEff' δ b -> (b -> Choreo' δ a) -> Choreo' δ a
| Return {a:Type}: a -> Choreo' δ a

def Choreo'.bind {α β: Type}:
  Choreo' ep α → (α  → Choreo' ep β) → Choreo' ep β
| Choreo'.Do eff next, next' => Choreo'.Do eff (fun x => bind (next x) next')
| Choreo'.Return v, next' => next' v

instance: Monad (Choreo' δ) where
  pure x := Choreo'.Return x
  bind := Choreo'.bind

def Choreo (δ:Type) (α:Type) := δ -> α

def DVal (δ:Type) (owner: δ) (α:Type) := (ep:δ) -> GVal owner ep α

def  test : DVal Example_Location alice Nat := fun x => GVal.Wrap (owner := alice) (by exact?)  3

def locally (loc: δ) (op: IO a): Choreo' δ (LVal loc a) :=
  Choreo'.Do (ChorEff'.Local loc op) (fun x => Choreo'.Return x)

def Choreo.bind{α β : Type} (chor: Choreo δ α)  (next: α → Choreo δ β):   Choreo δ β  :=
  fun x =>
  (next (chor x)) x

def ChorEff'.epp: ChorEff' δ (LVal owner a) -> ProgEff δ (GVal owner ep a)
| ChorEff'.Local l op => ProgEff.run l op
| ChorEff'.Send_recv gv r=> sorry




def Choreo'.epp: Choreo' δ a -> Prog δ a :=



instance: Monad (Choreo δ) where
  pure x := fun _ => x
  bind chor next :=
    fun x => (next (chor x)) x

def send_recv: (sender receiver:δ) -> (gv: (ep:δ) -> GVal sender ep a) ->((ep2:δ) -> GVal receiver ep2 a):=
  sorry



def dist_prog: Choreo' Example_Location Nat := do
  let temp: LVal alice String <- locally alice (do
    IO.println ""
    return "")

  return 23
