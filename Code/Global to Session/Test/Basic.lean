--import Mathlib

#eval List.range 4

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

def some_func (input: Nat):  Nat := input+1 -- assumed return input

theorem t12: ∀ (a b:Nat), f a = a :=  by sorry

def network_op (input: Nat):  IO Nat := do
  return <- IO.rand 0 input -- assumed return input

instance (n:Nat) : Coe (network_op) (Nat) where


axiom network_correctness: ∀ (n:Nat),
  (some_func n) = n

axiom network_always_works: ∀ (n:Nat) (w1: IO.RealWorld), ∃ w2: IO.RealWorld,
  (network_op n).run w1 = EStateM.Result.ok n w2


def ppp: some_func 4 = 4 := by simp [network_correctness 4]

#check Classical.choice ⟨4⟩

def p_Choice: 4 = Classical.choice ⟨4⟩ := by simp


#check network_correctness 3

def to_zero : Nat → IO Nat
| 0 => return 0
| n + 1 => do
  let b := 13
  let n2 <-

  let a := 12

  have: n = n2 := by simp [network_always_works]
  to_zero n2

#check Classical.choice

def to_zero_noIO : Nat → Nat
| 0 =>  0
| n + 1 =>
  let n2 := some_func n

  have: n2 = n := by simp [network_correctness]
  to_zero_noIO n2
