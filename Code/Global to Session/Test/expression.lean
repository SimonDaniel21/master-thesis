import Test.type

inductive Exp where
  | VAR (v: Variable) :Exp
  | FUNC (f: Function) : Exp -> Exp
  | CONSTANT (n: Nat) :Exp
  | DIVIDE: Exp -> Exp -> Exp
  | MULTIPLY: Exp -> Exp -> Exp
  | PLUS: Exp -> Exp -> Exp
  | MINUS: Exp -> Exp -> Exp
  | SMALLER: Exp -> Exp -> Exp
  | EQUALS: Exp -> Exp -> Exp
deriving BEq

open Exp

def Exp_TO_STRING: Exp -> String
  | FUNC f e => f ++ "(" ++ Exp_TO_STRING e ++ ")"
  | VAR n => n
  | CONSTANT n => s!"{n}"
  | DIVIDE a b => "(" ++ (Exp_TO_STRING a) ++ " / " ++ (Exp_TO_STRING b) ++ ")"
  | MULTIPLY a b => "(" ++ (Exp_TO_STRING a) ++ " x " ++ (Exp_TO_STRING b) ++ ")"
  | PLUS a b => "(" ++ (Exp_TO_STRING a) ++ " + " ++ (Exp_TO_STRING b) ++ ")"
  | MINUS a b => "(" ++ (Exp_TO_STRING a) ++ " - " ++ (Exp_TO_STRING b) ++ ")"
  | SMALLER a b => "(" ++ (Exp_TO_STRING a) ++ " < " ++ (Exp_TO_STRING b) ++ ")"
  | EQUALS a b => "(" ++ (Exp_TO_STRING a) ++ " == " ++ (Exp_TO_STRING b) ++ ")"




instance: ToString Exp where
  toString := Exp_TO_STRING

open Exp

inductive SYMBOL where
  | var (v: Variable) (amount: Nat) : SYMBOL
  | func (f: Function) (s: SYMBOL) (amount: Nat) : SYMBOL

inductive Exp_RESULT (x: Type) where
  | some (value: x) : Exp_RESULT x
  | DIV_BY_ZERO
  | UNKNOWN_VAR (name: Variable) : Exp_RESULT x
  | UNKNOWN_FUNC (name: Variable) : Exp_RESULT x
deriving BEq

def bind_Exp_result:  Exp_RESULT α → (α → Exp_RESULT β) → Exp_RESULT β
  | Exp_RESULT.some v, f => f v
  | Exp_RESULT.UNKNOWN_VAR name, _ => Exp_RESULT.UNKNOWN_VAR name
  | Exp_RESULT.UNKNOWN_FUNC name, _ => Exp_RESULT.UNKNOWN_FUNC name
  | Exp_RESULT.DIV_BY_ZERO, _ => Exp_RESULT.DIV_BY_ZERO

def pure_Exp_result {α : Type} (elem: α): Exp_RESULT α :=
  Exp_RESULT.some elem

instance: Monad Exp_RESULT where
  bind := bind_Exp_result
  pure := pure_Exp_result

instance: ToString (Exp_RESULT Nat) where
  toString (e: Exp_RESULT Nat) := match e with
    | Exp_RESULT.some v => toString v
    | Exp_RESULT.UNKNOWN_VAR name => "Exp contains unknown var: " ++ name
    | Exp_RESULT.UNKNOWN_FUNC name => "Exp contains unknown function: " ++ name
    | Exp_RESULT.DIV_BY_ZERO => "Division by zero "

abbrev P_state := (List (Variable × Nat)) ×  (List (Function × (Nat -> Nat)))


def test_list: List (String × String) := [("a", "eins"),  ("b", "zwei")]


#check P_state

def test_type := Nat × Nat

def test_v : test_type := (2,3)

def var_map (env: P_state): (List (Variable × Nat)) :=
  env.fst

def funcs (env: P_state): (List (Function × (Nat -> Nat))) :=
  env.snd

def var_map_to_string (v: List (Variable × Nat)):  String :=
  match v with
  | List.cons (v_name, v_value) rest => v_name ++ "->" ++ toString v_value ++ ", " ++ var_map_to_string rest
  | List.nil => ""

def P_state_to_string (env: P_state):  String :=
  var_map_to_string (var_map env)

def empty_P_state : P_state := ([],[])

instance: ToString P_state where
  toString := P_state_to_string


#check (List (Nat × Nat))
--def eval_Exp (var_map: List (Variable × Nat)): Exp -> Exp_RESULT (Nat × List SYMBOL)
def eval_Exp (env: P_state) : Exp -> Exp_RESULT Nat
  | Exp.VAR n =>
    let var_value := (var_map env).lookup n
    if (var_value == Option.none) then
      Exp_RESULT.UNKNOWN_VAR n
    else
      Exp_RESULT.some var_value.get!

  | Exp.FUNC name argument  =>
    let func_opt := (funcs env).lookup name
    match func_opt with
    | Option.some func =>
      do
      let v_a <- eval_Exp env argument
      Exp_RESULT.some (func v_a)

    | Option.none => Exp_RESULT.UNKNOWN_FUNC name

  | Exp.CONSTANT n => Exp_RESULT.some n

  | Exp.DIVIDE e_a e_b =>
    do
    let v_a <- eval_Exp env e_a
    let v_b <- eval_Exp env e_b

    if ( v_b == 0) then
      Exp_RESULT.DIV_BY_ZERO
    else
      Exp_RESULT.some (v_a / v_b)

  | Exp.MULTIPLY e_a e_b =>
    do
    let v_a <- eval_Exp env e_a
    let v_b <- eval_Exp env e_b
    Exp_RESULT.some (v_a * v_b)


  | Exp.PLUS e_a e_b =>
    do
    let v_a <- eval_Exp env e_a
    let v_b <- eval_Exp env e_b
    Exp_RESULT.some (v_a + v_b)

  | Exp.MINUS e_a e_b =>
    do
    let v_a <- eval_Exp env e_a
    let v_b <- eval_Exp env e_b
    Exp_RESULT.some (v_a - v_b)

  | Exp.SMALLER e_a e_b =>
    do
    let v_a <- eval_Exp env e_a
    let v_b <- eval_Exp env e_b
    if v_a < v_b then
      Exp_RESULT.some 1
    else
      Exp_RESULT.some 0

  | Exp.EQUALS e_a e_b =>
    do
    let v_a <- eval_Exp env e_a
    let v_b <- eval_Exp env e_b
    if v_a == v_b then
      Exp_RESULT.some 1
    else
      Exp_RESULT.some 0



-- inductive TYPED_Exp: (List String) -> Exp -> Ty -> Type
--   | TYPED_CONSTANT :  TYPED_Exp GAMMA Exp.CONSTANT nat
--   | TYPED_PLUS (typed_e1: TYPED_Exp GAMMA e1 nat)
--                (typed_e2: TYPED_Exp GAMMA e2 nat):
--                 TYPED_Exp GAMMA (Exp.PLUS e1 e2) nat


def vars: List (Variable × Nat) := [("v1", 3)]

def add_one (v: Nat): Nat :=
  v+1

def test_env : P_state := (vars, [("add_one", add_one )])

#eval test_env
#eval vars


def e_1: Exp := Exp.MULTIPLY (Exp.PLUS (Exp.CONSTANT 3) (Exp.CONSTANT 34)) (Exp.CONSTANT 2)
def e_2_nan: Exp := Exp.MULTIPLY (Exp.CONSTANT 2) (Exp.DIVIDE (Exp.CONSTANT 3) (Exp.CONSTANT 0))
def e_3_unknown: Exp := Exp.MULTIPLY (Exp.VAR "v_unknown") (Exp.DIVIDE (Exp.CONSTANT 3) (Exp.CONSTANT 0))
def e_4_var: Exp := Exp.MINUS (Exp.VAR "v1") (Exp.DIVIDE (Exp.CONSTANT 4) (Exp.CONSTANT 2))
def e_5_var_and_func: Exp := Exp.MINUS (Exp.VAR "v1") (Exp.FUNC "add_one" (Exp.CONSTANT 1))


#eval vars

#eval (e_1)
#eval (eval_Exp test_env e_1 == Exp_RESULT.some 74)

#eval (e_2_nan)
#eval (eval_Exp test_env e_2_nan == Exp_RESULT.DIV_BY_ZERO)

#eval (e_3_unknown)
#eval (eval_Exp test_env e_3_unknown == Exp_RESULT.UNKNOWN_VAR "v_unknown")

#eval (e_4_var)
#eval (eval_Exp test_env e_4_var == Exp_RESULT.some 1)

#eval (e_5_var_and_func)
#eval (eval_Exp test_env e_5_var_and_func)
#eval (eval_Exp test_env e_5_var_and_func == Exp_RESULT.some 1)

def faraway2 := 3
