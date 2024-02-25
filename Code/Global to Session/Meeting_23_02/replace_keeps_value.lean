import Std.Data.AssocList
import Mathlib

structure contained_elem (l: Lean.AssocList Nat Unit) where
  n: Nat
  p: l.contains n := by decide

def test_list: Lean.AssocList Nat Unit := [(3, ())].toAssocList'
def ce: contained_elem test_list := contained_elem.mk 3

variable (x:Nat)

def ce2: contained_elem (test_list.replace 41 ()) := ce -- conversion works magically


def ce5: contained_elem (test_list.replace x ()) := ce -- conversion works magically

def ce3: contained_elem (test_list.replace x ()) :=
  cast
  (by
    congr
    by_cases h : x =
    · rw [h]
      rfl
    ·
      trivial
  ) ce -- conversion does not work


def fn5 (ce: contained_elem test_list) :=
  let test_list4 := test_list.replace 4 ()
  let ce56: contained_elem test_list4 := ce
  ()

def test: a -> b := by
  intro y;

def test54: false ∨ true := Or.inr rfl
theorem test55: false ∨ true := by
  apply Or.inr
  rfl

theorem test57: true ∧ true := by
  apply And.intro
  . rfl
  . rfl

#check beq_iff_eq

theorem str_deq_eq (s t: String):  (s==t) <-> s=t:=
  by exact beq_iff_eq s t

#check ->

-- theorem test255 (s1 s2: String): (s1 = s2) <-> (s1 == s2) :=by
--   apply Iff.intro
--   intro d_equality
--   induction s1 with
--   | mk => _
--   | cons a as => _


@[simp] theorem replace_keeps_loc (b: Type):
  ∀  (l: Lean.AssocList String b) (k k':String) (v:b),
    l.contains k -> (l.replace k' v).contains k := by simp?


@[simp] theorem replace_keeps_loc (a b: Type):
  ∀ [DecidableEq a] (l: Lean.AssocList a b) (k k':a) (v:b),
    l.contains k -> (l.replace k' v).contains k := by
    intro beq_a l k k' v h
    induction l with
     --simp [Lean.AssocList.replace, Lean.AssocList.contains]
    | nil =>  simp [Lean.AssocList.contains] at h
    | cons k2 v2 as tail_ih =>
      simp [Lean.AssocList.replace]
      cases (decEq k2 k') with
      | isTrue h2 =>
        simp [h2]
        simp [Lean.AssocList.contains]
        cases (decEq k k') with
        | isTrue h3 =>
          apply Or.inl
          simp only [h3]
        | isFalse h3 =>
          apply Or.inr
          simp [Lean.AssocList.contains] at h
          cases h with
          | inl h4 =>
            rw [<-h2] at h3
            rw [h4] at h3
            contradiction
          | inr h4 =>
            simp [h4]
      | isFalse h2 =>
        cases h3:(k2 == k') with
        | true =>
          sorry
        | false =>
          simp [h3]

          sorry




def ce5: contained_elem (test_list.replace x ()) := ce


def fn4 (n: Nat) :=
  let ce5: contained_elem (test_list2.erase 4) := ce -- conversion works magically
  if h:(n == 1) then
    let test_list3 := test_list.replace n ()
    let ce3: contained_elem test_list3 := ⟨ce.n, by simp [h]⟩
    ()
  else
  ()
