import Test.my_utils
import chorlean.Network

inductive locVal (a:Type) (s:String) where
| Wrap: a -> locVal a s
| Empty: locVal a s

inductive List (α : Type u) where
  /-- `[]` is the empty list. -/
  | nil : List α
  /-- If `a : α` and `l : List α`, then `cons a l`, or `a :: l`, is the
  list whose first element is `a` and with `l` as the rest of the list. -/
  | cons: α -> List α -> List α


inductive capture (lvs: List (String × Type)) where
| nil: capture lvs
| cons: (s:String) -> (a:Type) -> (v:a) -> capture (lvs ++ [(s,a)])

inductive MutliEff where
| prog: String -> List (locVal v sd) -> MutliEff

#check List


inductive Mulit where
