import chorlean.Choreo

inductive Location
| A | B
deriving Repr
open Location

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

def counting_down: Nat -> Nat
| x+1 => counting_down x
| 0 => 0

def counting_down_dist (a b ep:Location) (v: GVal a ep Nat): Choreo ep (Nat):= do

  branch v fun
  | x+1 =>
    let b_val := GVal.wrap b ep x
    counting_down_dist b a ep b_val
  | 0 => return 42
decreasing_by sorry
