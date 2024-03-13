import chorlean.Choreo2

inductive Location
| A | B
deriving Repr
open Location

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

instance sig: LocSig Location where
  sig x := match x with
    | A => LogEff
    | B =>  LogEff
  executable x := match x with
    | A => inferInstance
    | B => inferInstance


def counting_down: Nat -> Nat
| x+1 => counting_down x
| 0 => 0

#check Option

inductive Bounded (n:Nat) (α:Type) where
| iter: (i:Nat) -> (i <= n) -> α -> Bounded n α
| out: Bounded n α

def counting_down_dist (a b ep:Location) (v: GVal a ep Nat) (i:Nat): Choreo ep (Nat):= do
  match i with
  | n+1 =>
    branch v fun
    | x+1 =>
      let b_val := GVal.wrap b ep x
      counting_down_dist b a ep b_val n
    | 0 => return 42
  | 0 => return 3
