import Test.type

inductive EXPRESSION where
  | VAR (v: variableType) :EXPRESSION
  | CONSTANT (n: Nat) :EXPRESSION
  | DIVIDE: EXPRESSION -> EXPRESSION -> EXPRESSION
  | MULTIPLY: EXPRESSION -> EXPRESSION -> EXPRESSION
  | PLUS: EXPRESSION -> EXPRESSION -> EXPRESSION
  | MINUS: EXPRESSION -> EXPRESSION -> EXPRESSION

def EXPRESSION_TO_STRING: EXPRESSION -> String
  | EXPRESSION.VAR n => n
  | EXPRESSION.CONSTANT n => s!"{n}"
  | EXPRESSION.DIVIDE a b => "(" ++ (EXPRESSION_TO_STRING a) ++ " / " ++ (EXPRESSION_TO_STRING b) ++ ")"
  | EXPRESSION.MULTIPLY a b => "(" ++ (EXPRESSION_TO_STRING a) ++ " x " ++ (EXPRESSION_TO_STRING b) ++ ")"
  | EXPRESSION.PLUS a b => "(" ++ (EXPRESSION_TO_STRING a) ++ " + " ++ (EXPRESSION_TO_STRING b) ++ ")"
  | EXPRESSION.MINUS a b => "(" ++ (EXPRESSION_TO_STRING a) ++ " - " ++ (EXPRESSION_TO_STRING b) ++ ")"



instance: ToString EXPRESSION where 
  toString := EXPRESSION_TO_STRING

open EXPRESSION

inductive EXPRESSION_RESULT
  | some (value: Option Nat) : EXPRESSION_RESULT
  | UNKNOWN_VAR (name: variableType) : EXPRESSION_RESULT

instance: ToString EXPRESSION_RESULT where 
  toString (e: EXPRESSION_RESULT) := match e with
    | EXPRESSION_RESULT.some v_opt => match v_opt with
      | Option.some a => s!"{a}"
      | Option.none => "nan"
    | EXPRESSION_RESULT.UNKNOWN_VAR name => "expression contains unknown var: " ++ name

#check (List (Nat × Nat))

def eval_expression (var_map: List (variableType × Option Nat)): EXPRESSION -> EXPRESSION_RESULT
  | EXPRESSION.VAR n => 
    let var_value := var_map.lookup n
    if (var_value == Option.none) then
      EXPRESSION_RESULT.UNKNOWN_VAR n
    else
      EXPRESSION_RESULT.some var_value.get!

  | EXPRESSION.CONSTANT n => EXPRESSION_RESULT.some (Option.some n)

  | EXPRESSION.DIVIDE a b =>
    let er_a := eval_expression var_map a 
    let er_b := eval_expression var_map b
    match er_a with
    | EXPRESSION_RESULT.some v_a_opt => 
      match er_b with
      | EXPRESSION_RESULT.some v_b_opt =>
        EXPRESSION_RESULT.some 
        (
          do
          let v_a <- v_a_opt
          let v_b <- v_b_opt 
          if ( v_b == 0) then
            Option.none
          else Option.some (v_a / v_b)
            Option.some (v_a / v_b)
        )

      | EXPRESSION_RESULT.UNKNOWN_VAR v => EXPRESSION_RESULT.UNKNOWN_VAR v 
      
    | EXPRESSION_RESULT.UNKNOWN_VAR v => EXPRESSION_RESULT.UNKNOWN_VAR v 
  
  | EXPRESSION.MULTIPLY a b =>
    let er_a := eval_expression var_map a 
    let er_b := eval_expression var_map b
    match er_a with
    | EXPRESSION_RESULT.some v_a_opt => 
      match er_b with
      | EXPRESSION_RESULT.some v_b_opt =>
        EXPRESSION_RESULT.some 
        (
          do
          let v_a <- v_a_opt
          let v_b <- v_b_opt 
          Option.some (v_a * v_b)
        )

      | EXPRESSION_RESULT.UNKNOWN_VAR v => EXPRESSION_RESULT.UNKNOWN_VAR v 
      
    | EXPRESSION_RESULT.UNKNOWN_VAR v => EXPRESSION_RESULT.UNKNOWN_VAR v 

  | EXPRESSION.PLUS a b =>
    let er_a := eval_expression var_map a 
    let er_b := eval_expression var_map b
    match er_a with
    | EXPRESSION_RESULT.some v_a_opt => 
      match er_b with
      | EXPRESSION_RESULT.some v_b_opt =>
        EXPRESSION_RESULT.some 
        (
          do
          let v_a <- v_a_opt
          let v_b <- v_b_opt 
          Option.some (v_a + v_b)
        )

      | EXPRESSION_RESULT.UNKNOWN_VAR v => EXPRESSION_RESULT.UNKNOWN_VAR v 
      
    | EXPRESSION_RESULT.UNKNOWN_VAR v => EXPRESSION_RESULT.UNKNOWN_VAR v 

  | EXPRESSION.MINUS a b =>
    let er_a := eval_expression var_map a 
    let er_b := eval_expression var_map b
    match er_a with
    | EXPRESSION_RESULT.some v_a_opt => 
      match er_b with
      | EXPRESSION_RESULT.some v_b_opt =>
        EXPRESSION_RESULT.some 
        (
          do
          let v_a <- v_a_opt
          let v_b <- v_b_opt 
          Option.some (v_a - v_b)
        )

      | EXPRESSION_RESULT.UNKNOWN_VAR v => EXPRESSION_RESULT.UNKNOWN_VAR v 
      
    | EXPRESSION_RESULT.UNKNOWN_VAR v => EXPRESSION_RESULT.UNKNOWN_VAR v 
  


#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"

-- inductive TYPED_EXPRESSION: (List String) -> EXPRESSION -> Ty -> Type 
--   | TYPED_CONSTANT :  TYPED_EXPRESSION GAMMA EXPRESSION.CONSTANT nat
--   | TYPED_PLUS (typed_e1: TYPED_EXPRESSION GAMMA e1 nat)
--                (typed_e2: TYPED_EXPRESSION GAMMA e2 nat):
--                 TYPED_EXPRESSION GAMMA (EXPRESSION.PLUS e1 e2) nat


def vars: List (variableType × Option Nat) := [("v1", Option.some 3)]

#eval vars


def e_1: EXPRESSION := EXPRESSION.MULTIPLY (EXPRESSION.PLUS (EXPRESSION.CONSTANT 3) (EXPRESSION.CONSTANT 34)) (EXPRESSION.CONSTANT 2)
def e_2_nan: EXPRESSION := EXPRESSION.MULTIPLY (EXPRESSION.CONSTANT 2) (EXPRESSION.DIVIDE (EXPRESSION.CONSTANT 3) (EXPRESSION.CONSTANT 0))
def e_3_unknown: EXPRESSION := EXPRESSION.MULTIPLY (EXPRESSION.VAR "v_unknown") (EXPRESSION.DIVIDE (EXPRESSION.CONSTANT 3) (EXPRESSION.CONSTANT 0))
def e_4_var: EXPRESSION := EXPRESSION.MINUS (EXPRESSION.VAR "v1") (EXPRESSION.DIVIDE (EXPRESSION.CONSTANT 4) (EXPRESSION.CONSTANT 2))


#eval vars

#eval (e_1)
#eval (eval_expression vars e_1)

#eval (e_2_nan)
#eval (eval_expression vars e_2_nan)

#eval (e_3_unknown)
#eval (eval_expression vars e_3_unknown)

#eval (e_4_var)
#eval (eval_expression vars e_4_var)