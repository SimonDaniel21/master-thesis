import Test.type

inductive EXPRESSION where
  | VAR (v: Variable) :EXPRESSION
  | FUNC (f: Function) : EXPRESSION -> EXPRESSION
  | CONSTANT (n: Nat) :EXPRESSION
  | DIVIDE: EXPRESSION -> EXPRESSION -> EXPRESSION
  | MULTIPLY: EXPRESSION -> EXPRESSION -> EXPRESSION
  | PLUS: EXPRESSION -> EXPRESSION -> EXPRESSION
  | MINUS: EXPRESSION -> EXPRESSION -> EXPRESSION
  | SMALLER: EXPRESSION -> EXPRESSION -> EXPRESSION
  | EQUALS: EXPRESSION -> EXPRESSION -> EXPRESSION
deriving BEq


def EXPRESSION_TO_STRING: EXPRESSION -> String
  | EXPRESSION.FUNC f e => f ++ "(" ++ EXPRESSION_TO_STRING e ++ ")"
  | EXPRESSION.VAR n => n
  | EXPRESSION.CONSTANT n => s!"{n}"
  | EXPRESSION.DIVIDE a b => "(" ++ (EXPRESSION_TO_STRING a) ++ " / " ++ (EXPRESSION_TO_STRING b) ++ ")"
  | EXPRESSION.MULTIPLY a b => "(" ++ (EXPRESSION_TO_STRING a) ++ " x " ++ (EXPRESSION_TO_STRING b) ++ ")"
  | EXPRESSION.PLUS a b => "(" ++ (EXPRESSION_TO_STRING a) ++ " + " ++ (EXPRESSION_TO_STRING b) ++ ")"
  | EXPRESSION.MINUS a b => "(" ++ (EXPRESSION_TO_STRING a) ++ " - " ++ (EXPRESSION_TO_STRING b) ++ ")"
  | EXPRESSION.SMALLER a b => "(" ++ (EXPRESSION_TO_STRING a) ++ " < " ++ (EXPRESSION_TO_STRING b) ++ ")"
  | EXPRESSION.EQUALS a b => "(" ++ (EXPRESSION_TO_STRING a) ++ " == " ++ (EXPRESSION_TO_STRING b) ++ ")"




instance: ToString EXPRESSION where
  toString := EXPRESSION_TO_STRING

open EXPRESSION

inductive SYMBOL where
  | var (v: Variable) (amount: Nat) : SYMBOL
  | func (f: Function) (s: SYMBOL) (amount: Nat) : SYMBOL

inductive EXPRESSION_RESULT (x: Type) where
  | some (value: x) : EXPRESSION_RESULT x
  | DIV_BY_ZERO
  | UNKNOWN_VAR (name: Variable) : EXPRESSION_RESULT x
  | UNKNOWN_FUNC (name: Variable) : EXPRESSION_RESULT x
deriving BEq

def bind_expression_result:  EXPRESSION_RESULT α → (α → EXPRESSION_RESULT β) → EXPRESSION_RESULT β
  | EXPRESSION_RESULT.some v, f => f v
  | EXPRESSION_RESULT.UNKNOWN_VAR name, _ => EXPRESSION_RESULT.UNKNOWN_VAR name
  | EXPRESSION_RESULT.UNKNOWN_FUNC name, _ => EXPRESSION_RESULT.UNKNOWN_FUNC name
  | EXPRESSION_RESULT.DIV_BY_ZERO, _ => EXPRESSION_RESULT.DIV_BY_ZERO

def pure_expression_result {α : Type} (elem: α): EXPRESSION_RESULT α :=
  EXPRESSION_RESULT.some elem

instance: Monad EXPRESSION_RESULT where
  bind := bind_expression_result
  pure := pure_expression_result

instance: ToString (EXPRESSION_RESULT Nat) where
  toString (e: EXPRESSION_RESULT Nat) := match e with
    | EXPRESSION_RESULT.some v => toString v
    | EXPRESSION_RESULT.UNKNOWN_VAR name => "expression contains unknown var: " ++ name
    | EXPRESSION_RESULT.UNKNOWN_FUNC name => "expression contains unknown function: " ++ name
    | EXPRESSION_RESULT.DIV_BY_ZERO => "Division by zero "

def environment := (List (Variable × Nat)) ×  (List (Function × (Nat -> Nat)))

def test_list: List (String × String) := [("a", "eins"),  ("b", "zwei")]


#check environment

def test_type := Nat × Nat

def test_v : test_type := (2,3)

def var_map (env: environment): (List (Variable × Nat)) :=
  env.fst

def funcs (env: environment): (List (Function × (Nat -> Nat))) :=
  env.snd

def environment_to_string (env: environment):  String :=
  toString (var_map env)

def empty_environment : environment := ([],[])

instance: ToString environment where
  toString := environment_to_string


#check (List (Nat × Nat))
--def eval_expression (var_map: List (Variable × Nat)): EXPRESSION -> EXPRESSION_RESULT (Nat × List SYMBOL)
def eval_expression (env: environment) : EXPRESSION -> EXPRESSION_RESULT Nat
  | EXPRESSION.VAR n =>
    let var_value := (var_map env).lookup n
    if (var_value == Option.none) then
      EXPRESSION_RESULT.UNKNOWN_VAR n
    else
      EXPRESSION_RESULT.some var_value.get!

  | EXPRESSION.FUNC name argument  =>
    let func_opt := (funcs env).lookup name
    match func_opt with
    | Option.some func =>
      do
      let v_a <- eval_expression env argument
      EXPRESSION_RESULT.some (func v_a)

    | Option.none => EXPRESSION_RESULT.UNKNOWN_FUNC name

  | EXPRESSION.CONSTANT n => EXPRESSION_RESULT.some n

  | EXPRESSION.DIVIDE e_a e_b =>
    do
    let v_a <- eval_expression env e_a
    let v_b <- eval_expression env e_b

    if ( v_b == 0) then
      EXPRESSION_RESULT.DIV_BY_ZERO
    else
      EXPRESSION_RESULT.some (v_a / v_b)

  | EXPRESSION.MULTIPLY e_a e_b =>
    do
    let v_a <- eval_expression env e_a
    let v_b <- eval_expression env e_b
    EXPRESSION_RESULT.some (v_a * v_b)


  | EXPRESSION.PLUS e_a e_b =>
    do
    let v_a <- eval_expression env e_a
    let v_b <- eval_expression env e_b
    EXPRESSION_RESULT.some (v_a + v_b)

  | EXPRESSION.MINUS e_a e_b =>
    do
    let v_a <- eval_expression env e_a
    let v_b <- eval_expression env e_b
    EXPRESSION_RESULT.some (v_a - v_b)

  | EXPRESSION.SMALLER e_a e_b =>
    do
    let v_a <- eval_expression env e_a
    let v_b <- eval_expression env e_b
    if v_a < v_b then
      EXPRESSION_RESULT.some 1
    else
      EXPRESSION_RESULT.some 0

  | EXPRESSION.EQUALS e_a e_b =>
    do
    let v_a <- eval_expression env e_a
    let v_b <- eval_expression env e_b
    if v_a == v_b then
      EXPRESSION_RESULT.some 1
    else
      EXPRESSION_RESULT.some 0



-- inductive TYPED_EXPRESSION: (List String) -> EXPRESSION -> Ty -> Type
--   | TYPED_CONSTANT :  TYPED_EXPRESSION GAMMA EXPRESSION.CONSTANT nat
--   | TYPED_PLUS (typed_e1: TYPED_EXPRESSION GAMMA e1 nat)
--                (typed_e2: TYPED_EXPRESSION GAMMA e2 nat):
--                 TYPED_EXPRESSION GAMMA (EXPRESSION.PLUS e1 e2) nat


def vars: List (Variable × Nat) := [("v1", 3)]

def add_one (v: Nat): Nat :=
  v+1

def test_env : environment := (vars, [("add_one", add_one )])

#eval vars


def e_1: EXPRESSION := EXPRESSION.MULTIPLY (EXPRESSION.PLUS (EXPRESSION.CONSTANT 3) (EXPRESSION.CONSTANT 34)) (EXPRESSION.CONSTANT 2)
def e_2_nan: EXPRESSION := EXPRESSION.MULTIPLY (EXPRESSION.CONSTANT 2) (EXPRESSION.DIVIDE (EXPRESSION.CONSTANT 3) (EXPRESSION.CONSTANT 0))
def e_3_unknown: EXPRESSION := EXPRESSION.MULTIPLY (EXPRESSION.VAR "v_unknown") (EXPRESSION.DIVIDE (EXPRESSION.CONSTANT 3) (EXPRESSION.CONSTANT 0))
def e_4_var: EXPRESSION := EXPRESSION.MINUS (EXPRESSION.VAR "v1") (EXPRESSION.DIVIDE (EXPRESSION.CONSTANT 4) (EXPRESSION.CONSTANT 2))
def e_5_var_and_func: EXPRESSION := EXPRESSION.MINUS (EXPRESSION.VAR "v1") (EXPRESSION.FUNC "add_one" (EXPRESSION.CONSTANT 1))


#eval vars

#eval (e_1)
#eval (eval_expression test_env e_1 == EXPRESSION_RESULT.some 74)

#eval (e_2_nan)
#eval (eval_expression test_env e_2_nan == EXPRESSION_RESULT.DIV_BY_ZERO)

#eval (e_3_unknown)
#eval (eval_expression test_env e_3_unknown == EXPRESSION_RESULT.UNKNOWN_VAR "v_unknown")

#eval (e_4_var)
#eval (eval_expression test_env e_4_var == EXPRESSION_RESULT.some 1)

#eval (e_5_var_and_func)
#eval (eval_expression test_env e_5_var_and_func)
#eval (eval_expression test_env e_5_var_and_func == EXPRESSION_RESULT.some 1)
