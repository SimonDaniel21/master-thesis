
@[reducible] def Channel := String
@[reducible] def Variable := String
@[reducible] def Function := String
@[reducible] def Location := String
@[reducible] def Label := String


@[reducible] def located (α: Type): Type := α × Location

inductive BranchChoice: Type
| fst
| snd
deriving BEq

instance: ToString BranchChoice where
  toString := fun x => match x with
  | BranchChoice.fst => "first"
  | BranchChoice.snd => "second"


inductive Ty : Type
| nat: Ty
| fn (a: Ty): Ty -> Ty

@[reducible] def Ty.denote : Ty → Type
|nat    => Nat
|fn a b => a.denote -> b.denote

inductive MyNat where
| nat: Nat -> MyNat
| nan: MyNat
