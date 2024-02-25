import Mathlib


abbrev LocVal_store:= List ((a:Type )  × a)


-- inductive LocVal (a:Type) (loc:String) where
-- | some: a -> LocVal a loc
-- | empty: LocVal a loc

@[reducible] def LocVal (a:Type) (loc:String) := Nat

abbrev Store:= List ((a:Type ) × a)

inductive Term : Type -> Type 1
| Do: LocVal a loc -> Term b -> Term (LocVal a loc)
| Return: a -> Term a
def test: LocVal Nat "nata" := 3

def testTerm : Term Nat := .Do test (.Return test)

inductive DistVal (α: Type) (loc: String) where
| Wrap: α -> DistVal α loc
| Empty: DistVal α loc


def local_comp_type (l:String) (a:Type) := [∀ α, Coe (DistVal α l) α] -> IO a

def DistVal.notEmpty: DistVal a loc -> Prop
| Wrap _ => True -- Capitalized. `true` is a Bool which was being coerced into a `Prop`
| Empty => False

def local_comp (dv: DistVal Nat "alice"): local_comp_type "alice" Nat := do
  return dv + 2

theorem all_alice_exist : ∀ (x:Type) (dv: DistVal x "alice"), dv.notEmpty := by sorry

def DistVal.unwrap {α : Type} {l : String} : {dv : DistVal α l} → dv.notEmpty → α
| Wrap x, _ => x
| Empty, h => by simp [notEmpty] at h

def res : IO Nat :=
  have (α : Type) : Coe (DistVal α "alice") α := ⟨fun dv ↦ DistVal.unwrap (all_alice_exist α dv)⟩
  -- ^ You can always make a helper definition for creating these instances
  local_comp (DistVal.Wrap 3 (loc := "alice"))
