-- TASK --
inductive DSL where
  | CONSTANT (n: Nat) :DSL
  | DIVIDE: DSL -> DSL -> DSL
  | PLUS: DSL -> DSL -> DSL

inductive MyOptional (t: Type): Type
  | some (e: t): MyOptional t
  | none: MyOptional t

def eval: DSL -> MyOptional Nat
  | DSL.CONSTANT n => (MyOptional.some n)
  | DSL.DIVIDE a b => match eval a with
    | MyOptional.none => MyOptional.none
    | MyOptional.some v_a => (match eval b with
      | MyOptional.none => MyOptional.none
      | MyOptional.some v_b => if ( v_b == 0) then
        MyOptional.none
        else (MyOptional.some (v_a / v_b)))
  | DSL.PLUS a b => match eval a with
    | MyOptional.none => MyOptional.none
    | MyOptional.some v_a => (match eval b with
      | MyOptional.none => MyOptional.none
      | MyOptional.some v_b => MyOptional.some (v_a + v_b))

def eval2: DSL -> Option Nat
  | DSL.CONSTANT n => (Option.some n)
  | DSL.DIVIDE a b => do
    let v_a := <- eval2 a
    let v_b <- eval2 b
    if ( v_b == 0) then
      Option.none
    else (Option.some (v_a / v_b))
  | DSL.PLUS a b =>
    do
    Option.some ((<- eval2 a) + (<- eval2 b))


--- Higher order Terms ---

inductive Ty where
| nat: Ty
| string: Ty
| fn: Ty -> Ty -> Ty

@[reducible] def Ty.denote: Ty -> Type
| nat => Nat
| string => String
| fn a b => a.denote -> b.denote

inductive Term' (rep: Ty -> Type): Ty -> Type
  | var           : rep x -> Term' rep x
  | nat_const     : Nat -> Term' rep Ty.nat
  | string_const  : String -> Term' rep Ty.string
  | plus          : Term' rep Ty.nat -> Term' rep Ty.nat -> Term' rep Ty.nat
  | my_let           : Term' rep x -> (rep x -> Term' rep y) -> Term' rep y
  | lam           : (rep x -> Term' rep y) -> Term' rep (Ty.fn x y)
  | app           : Term' rep (Ty.fn x y) -> Term' rep x -> Term' rep y

def Term (ty: Ty) := {rep: Ty -> Type} -> Term' rep ty

open Ty (nat fn)

def add: Term (fn nat (fn nat nat)) :=
  Term'.lam fun x => Term'.lam fun y => Term'.plus (Term'.var x) (Term'.var y)


def three_test: Term nat :=
  Term'.app (Term'.app add (Term'.nat_const 1)) (Term'.nat_const 4)

#eval Nat.succ Nat.zero
def countVars: Term' (fun _ => Unit) ty -> Nat
  | .var _ => 1
  | .nat_const _ => 0
  | .string_const _ => 0
  | .plus a b => countVars a + countVars b
  | .app f a => countVars f + countVars a
  | .lam b => countVars ( b ())
  | .my_let a b => countVars a + countVars (b ())

example : countVars add = 2 := rfl

open Term'

def pretty (e: Term' (fun _ => String) ty) (i: Nat := 1) : String :=
  match e with
  | .var s => s
  | .nat_const n => toString n
  | string_const s => s
  | app f a => s!"({pretty f i} {pretty a i})"
  | plus a b => s!"({pretty a i} + {pretty b i})"
  | lam f     =>
    let x := s!"x_{i}"
    s!"(fun {x} => {pretty (f x) (i+1)})"
  | my_let a b  =>
    let x := s!"x_{i}"
    s!"(let {x} := {pretty a i}; => {pretty (b x) (i+1)}"

#eval pretty three_test

#check three_test

def length? {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => 1 + (length? ys)

#eval length? [1,2,3,45,56]
