
@[reducible] def Channel := String
@[reducible] def Variable := String
@[reducible] def Agent := String

inductive Ty : Type
  | nat: Ty
  | fn (a: Ty): Ty -> Ty

@[reducible] def Ty.denote : Ty → Type
  |nat    => Nat
  |fn a b => a.denote -> b.denote

inductive MyNat where
  | nat: Nat -> MyNat
  | nan: MyNat
