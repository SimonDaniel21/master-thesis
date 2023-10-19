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
    let v_a := <- eval2 a
    let v_b := <- eval2 b
    Option.some ((<- eval2 a) + (<- eval2 b))