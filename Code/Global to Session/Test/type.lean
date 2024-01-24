
@[reducible] def Channel := String
@[reducible] def Variable := String
@[reducible] def Function := String
@[reducible] def Location := String
@[reducible] def Label := String

#check (2, "")

def ttt:Type := (Nat× String)

def tttt: ttt := (2,"")

@[reducible] def located (α) := (α×Location)

@[reducible] def locate  {α: Type}[ToString α] (v: α) (l: Location): located α := (v,l)

def located.loc: located α -> Location
| v => v.snd

def located.val: located α -> α
| v => v.fst


#check IO.println
instance {α} [ToString α]: ToString (located α) where
  toString := fun x => (toString x.val) ++ "@" ++ x.loc




--def Unwrap (l:Location) := ∀ a locate a l -> a

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
deriving BEq

inductive Value where
| nat   : Nat -> Value
| string: String -> Value
| bool  : Bool -> Value
deriving BEq

@[reducible] def Sorts.denote: Sorts -> Type
| nat => Nat
| string => String
| bool => Bool

def Value.denote (v: Value) : Sorts := match v with
| .nat _ => .nat
| .string _ => .string
| .bool _ => .bool

def Sorts.uid: Sorts -> Nat
| .nat => 1
| .bool => 2
| .string => 3

def Sorts.from_id: Nat -> Option Sorts
| 1 => Sorts.nat
| 2 => Sorts.bool
| 3 => Sorts.string
| _ => none

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
