
@[reducible] def Channel := String
@[reducible] def Variable := String
@[reducible] def Function := String
@[reducible] def Location := String
@[reducible] def Label := String


@[reducible] def located (α: Type): Type := α × Location


instance {α} [ToString α]: ToString (located α) where
  toString := fun x => (toString x.fst) ++ "@" ++ x.snd

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

inductive Sorts where
| nat   : Sorts
| string: Sorts
| bool  : Sorts

inductive Value where
| nat   : Nat -> Value
| string: String -> Value
| bool  : Bool -> Value

def Value.denote (v: Value) : Sorts := match v with
| .nat _ => .nat
| .string _ => .string
| .bool _ => .bool


instance: ToString Sorts where
  toString := fun x => match x with
  | .nat => "Nat"
  | .bool => "Bool"
  | .string => "string"

instance: ToString Value where
  toString := fun x => match x with
  | .nat x => toString x
  | .bool x => toString x
  | .string x => toString x
