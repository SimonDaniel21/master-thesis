import Test.type

inductive Bop where
| EQUAL: Bop
| NOT: Bop
| AND: Bop
| SMALLER: Bop
deriving BEq

-- inductive Exp where
-- | VAR (v: Variable) :Exp
-- | FUNC (f: Function) : Exp -> Exp
-- | CONSTANT (n: Nat) :Exp
-- | DIVIDE: Exp -> Exp -> Exp
-- | MULTIPLY: Exp -> Exp -> Exp
-- | PLUS: Exp -> Exp -> Exp
-- | MINUS: Exp -> Exp -> Exp
-- | SMALLER: Exp -> Exp -> Exp
-- | EQUALS: Exp -> Exp -> Exp
-- --| BinExp: Bop -> Exp
-- deriving BEq
mutual
  inductive BExp where
  | not: BExp -> BExp
  | and: BExp -> BExp -> BExp
  | smaller: NExp -> NExp -> BExp
  | const: Bool -> BExp
  | var: Variable -> BExp
  deriving BEq

  inductive NExp where
  | plus: NExp -> NExp -> NExp
  | minus: NExp -> NExp -> NExp
  | multiply: NExp -> NExp -> NExp
  | divide: NExp -> NExp -> NExp
  | const: Nat -> NExp
  | var: Variable -> NExp
  | func: Function -> Array Exp -> NExp
  deriving BEq

  inductive SExp where
  | concat: SExp -> SExp -> SExp
  | const: String -> SExp
  | var: Variable -> SExp
  deriving BEq

  inductive Exp where
  | nexp (e: NExp): Exp
  | bexp (e: BExp): Exp
  | sexp (e: SExp): Exp
  deriving BEq
end



open Exp

inductive exp_error where
| wrong_type (got expected:Sorts) : exp_error
| unknown_var (name: Variable) : exp_error
| wrong_args_num(got expected: Nat): exp_error
| division_by_zero
deriving BEq

def exp_res := Except exp_error Value




abbrev P_state := (List (Variable × Value)) ×  (List (Function × Nat × Exp))

def P_state.var_map (env: P_state) := env.fst

def P_state.funcs (env: P_state) := env.snd


def try_map {α β err : Type}  (l: List α) (f: α -> Except err β ) : Except err (List β) :=
  match l with
  | [] => .ok []
  | a::as => do
    let current_eval <- f a
    let cont <- try_map as f
    return [current_eval] ++ cont

mutual
  def eval_NExp: NExp -> ReaderT P_state (Except exp_error) Value
  | .plus a b => do
    let val_a <- eval_NExp a
    let val_b <- eval_NExp b
    match val_a with
    | Value.nat n1 =>
      match val_b with
      | Value.nat n2 =>
        return Value.nat (n1+n2)
      | x => throw (exp_error.wrong_type x.denote Sorts.nat)
    | x => throw (exp_error.wrong_type x.denote Sorts.nat)
  | .minus a b => do
    let val_a <- eval_NExp a
    let val_b <- eval_NExp b
    match val_a with
    | Value.nat n1 =>
      match val_b with
      | Value.nat n2 =>
        return Value.nat (n1-n2)
      | x => throw (exp_error.wrong_type x.denote Sorts.nat)
    | x => throw (exp_error.wrong_type x.denote Sorts.nat)
  | .multiply a b => do
    let val_a <- eval_NExp a
    let val_b <- eval_NExp b
    match val_a with
    | Value.nat n1 =>
      match val_b with
      | Value.nat n2 =>
        return Value.nat (n1*n2)
      | x => throw (exp_error.wrong_type x.denote Sorts.nat)
    | x => throw (exp_error.wrong_type x.denote Sorts.nat)
  | .divide a b => do
    let val_a <- eval_NExp a
    let val_b <- eval_NExp b
    match val_a with
    | Value.nat n1 =>
      match val_b with
      | Value.nat n2 =>
        if n2 == 0 then
          throw (exp_error.division_by_zero)
        else
          return Value.nat (n1/n2)
      | x => throw (exp_error.wrong_type x.denote Sorts.nat)
    | x => throw (exp_error.wrong_type x.denote Sorts.nat)
  | .const n => do
    return Value.nat n
  | .var v => do
    let env <- read
    let var_value_opt := (env.var_map).lookup v
    match var_value_opt with
    | Option.none => throw (exp_error.unknown_var v)
    | Option.some var_value => match var_value with
      | .nat _  => return var_value
      | x => throw (exp_error.wrong_type x.denote Sorts.nat)
  | .func f_name args => do
    let env <- read
    let f_opt := (env.funcs).lookup f_name
    return Value.nat 999
    -- match f_opt with
    -- | Option.none => throw (exp_error.unknown_var f_name)
    -- | Option.some f =>

    --   if (f.fst != args.size) then
    --     throw (exp_error.wrong_args_num f.fst args.size)
    --   else
    --    --let arg_vals <- args.map (fun x => eval_exp x env)
    --     return Value.nat 999

    --   --let arg_vals <- n_eval_array args.toList env
    --   --let arg_vals <- try_map args.toList (fun x => eval_exp x env)


  def eval_BExp: BExp -> ReaderT P_state (Except exp_error) Value
  | .and a b => do
    let val_a <- eval_BExp a
    let val_b <- eval_BExp b
    match val_a with
    | Value.bool b1 =>
      match val_b with
      | Value.bool b2 =>
        return Value.bool (b1 && b2)
      | x => throw (exp_error.wrong_type x.denote Sorts.bool)
    | x => throw (exp_error.wrong_type x.denote Sorts.bool)
  | .smaller a b => do
    let val_a <- eval_NExp a
    let val_b <- eval_NExp b
    match val_a with
    | Value.nat a =>
      match val_b with
      | Value.nat b =>
        return Value.bool (a < b)
      | x => throw (exp_error.wrong_type x.denote Sorts.nat)
    | x => throw (exp_error.wrong_type x.denote Sorts.nat)
  | .not b => do
    let val <- eval_BExp b
    match val with
    | Value.bool val_b =>
      return Value.bool !val_b
    | x => throw (exp_error.wrong_type x.denote Sorts.bool)
  | .const b => do
    return Value.bool b
  | .var v => do
    let env <- read
    let var_value_opt := (env.var_map).lookup v
    match var_value_opt with
    | Option.none => throw (exp_error.unknown_var v)
    | Option.some var_value => match var_value with
      | .bool _  => return var_value
      | x => throw (exp_error.wrong_type x.denote Sorts.bool)

  def eval_SExp: SExp -> ReaderT P_state (Except exp_error) Value
  | .concat a b => do
    let val_a <- eval_SExp a
    let val_b <- eval_SExp b
    match val_a with
    | Value.string s1 =>
      match val_b with
      | Value.string s2 =>
        return Value.string (s1 ++ s2)
      | x => throw (exp_error.wrong_type x.denote Sorts.string)
    | x => throw (exp_error.wrong_type x.denote Sorts.string)
  | .const s => do
    return Value.string s
  | .var v => do
    let env <- read
    let var_value_opt := (env.var_map).lookup v
    match var_value_opt with
    | Option.none => throw (exp_error.unknown_var v)
    | Option.some var_value => match var_value with
      | .string _  => return var_value
      | x => throw (exp_error.wrong_type x.denote Sorts.nat)


  def eval_exp: Exp -> ReaderT P_state (Except exp_error) Value
  | Exp.nexp e => eval_NExp e
  | Exp.bexp e => eval_BExp e
  | Exp.sexp e => eval_SExp e


  def n_eval_array (array: List Exp) (env: P_state) : Except exp_error (Array Value) :=
    match array with
    | [] => .ok #[]
    | a::as => do
      let current_eval <- eval_exp a env
      let cont <- n_eval_array as env
      return #[current_eval].append cont
end




instance: ToString (exp_error) where
  toString (e: exp_error) := match e with
    | exp_error.division_by_zero => "Division by zero "
    | exp_error.wrong_type t1 t2 => "expected " ++ toString t2 ++ " but got " ++ toString t1
    | exp_error.unknown_var name => "Exp contains unknown var: " ++ name
    | .wrong_args_num got expected => "function got " ++ toString got ++ " args but expected " ++ toString expected

-- def Exp_TO_STRING: Exp -> String
-- | FUNC f e => f ++ "(" ++ Exp_TO_STRING e ++ ")"
-- | VAR n => n
-- | CONSTANT n => s!"{n}"
-- | DIVIDE a b => "(" ++ (Exp_TO_STRING a) ++ " / " ++ (Exp_TO_STRING b) ++ ")"
-- | MULTIPLY a b => "(" ++ (Exp_TO_STRING a) ++ " x " ++ (Exp_TO_STRING b) ++ ")"
-- | PLUS a b => "(" ++ (Exp_TO_STRING a) ++ " + " ++ (Exp_TO_STRING b) ++ ")"
-- | MINUS a b => "(" ++ (Exp_TO_STRING a) ++ " - " ++ (Exp_TO_STRING b) ++ ")"
-- | SMALLER a b => "(" ++ (Exp_TO_STRING a) ++ " < " ++ (Exp_TO_STRING b) ++ ")"
-- | EQUALS a b => "(" ++ (Exp_TO_STRING a) ++ " == " ++ (Exp_TO_STRING b) ++ ")"
mutual
  partial def NExp_toString (e: NExp):String := match e with
    | .plus a b => "(" ++ (NExp_toString a) ++ " + " ++ (NExp_toString b) ++ ")"
    | .minus a b => "(" ++ (NExp_toString a) ++ " - " ++ (NExp_toString b) ++ ")"
    | .multiply a b => "(" ++ (NExp_toString a) ++ " x " ++ (NExp_toString b) ++ ")"
    | .divide a b => "(" ++ (NExp_toString a) ++ " / " ++ (NExp_toString b) ++ ")"
    | .const c => toString c
    | .var n => n
    | .func name args=> name ++ "(" ++ toString (args.map (fun x => Exp_toString x) ) ++ ")"

  partial def BExp_toString (e: BExp):String := match e with
    | .not b => "(! " ++ (BExp_toString b) ++ ")"
    | .and a b => "(" ++ (BExp_toString a) ++ " && " ++ (BExp_toString b) ++ ")"
    | .smaller a b => "(" ++ (NExp_toString a) ++ " < " ++ (NExp_toString b) ++ ")"
    | .const c => toString c
    | .var n => n

  partial def SExp_toString (e: SExp):String := match e with
    | .concat a b => "(" ++ (SExp_toString a) ++ " ++ " ++ (SExp_toString b) ++ ")"
    | .const c => "\"" ++ c ++ "\""
    | .var n => n

  partial instance: ToString SExp where
    toString := SExp_toString
  partial instance: ToString BExp where
    toString := BExp_toString
  partial instance: ToString NExp where
    toString := NExp_toString
  partial def Exp_toString (e: Exp):String := match e with
    | .nexp e => NExp_toString e
    | .bexp e => BExp_toString e
    | .sexp e => SExp_toString e

  partial instance: ToString Exp where
    toString := Exp_toString


end
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



def test_list: List (String × String) := [("a", "eins"),  ("b", "zwei")]


#check P_state

def test_type := Nat × Nat

def test_v : test_type := (2,3)


def var_map_to_string (v: List (Variable × Value)):  String :=
  match v with
  | List.cons (v_name, v_value) rest => v_name ++ "->" ++ toString v_value ++ ", " ++ var_map_to_string rest
  | List.nil => ""

def P_state_to_string (env: P_state):  String :=
  var_map_to_string (env.var_map)

def empty_P_state : P_state := ([],[])

instance: ToString P_state where
  toString := P_state_to_string


#check (List (Nat × Nat))
--def eval_Exp (var_map: List (Variable × Nat)): Exp -> Exp_RESULT (Nat × List SYMBOL)
-- def eval_Exp (env: P_state) : Exp -> Exp_RESULT Nat
--   | Exp.VAR n =>
--     let var_value := (var_map env).lookup n
--     if (var_value == Option.none) then
--       Exp_RESULT.UNKNOWN_VAR n
--     else
--       Exp_RESULT.some var_value.get!

--   | Exp.FUNC name argument  =>
--     let func_opt := (funcs env).lookup name
--     match func_opt with
--     | Option.some func =>
--       do
--       let v_a <- eval_Exp env argument
--       Exp_RESULT.some (func v_a)

--     | Option.none => Exp_RESULT.UNKNOWN_FUNC name

--   | Exp.CONSTANT n => Exp_RESULT.some n

--   | Exp.DIVIDE e_a e_b =>
--     do
--     let v_a <- eval_Exp env e_a
--     let v_b <- eval_Exp env e_b

--     if ( v_b == 0) then
--       Exp_RESULT.DIV_BY_ZERO
--     else
--       Exp_RESULT.some (v_a / v_b)

--   | Exp.MULTIPLY e_a e_b =>
--     do
--     let v_a <- eval_Exp env e_a
--     let v_b <- eval_Exp env e_b
--     Exp_RESULT.some (v_a * v_b)


--   | Exp.PLUS e_a e_b =>
--     do
--     let v_a <- eval_Exp env e_a
--     let v_b <- eval_Exp env e_b
--     Exp_RESULT.some (v_a + v_b)

--   | Exp.MINUS e_a e_b =>
--     do
--     let v_a <- eval_Exp env e_a
--     let v_b <- eval_Exp env e_b
--     Exp_RESULT.some (v_a - v_b)

--   | Exp.SMALLER e_a e_b =>
--     do
--     let v_a <- eval_Exp env e_a
--     let v_b <- eval_Exp env e_b
--     if v_a < v_b then
--       Exp_RESULT.some 1
--     else
--       Exp_RESULT.some 0

--   | Exp.EQUALS e_a e_b =>
--     do
--     let v_a <- eval_Exp env e_a
--     let v_b <- eval_Exp env e_b
--     if v_a == v_b then
--       Exp_RESULT.some 1
--     else
--       Exp_RESULT.some 0



-- inductive TYPED_Exp: (List String) -> Exp -> Ty -> Type
--   | TYPED_CONSTANT :  TYPED_Exp GAMMA Exp.CONSTANT nat
--   | TYPED_PLUS (typed_e1: TYPED_Exp GAMMA e1 nat)
--                (typed_e2: TYPED_Exp GAMMA e2 nat):
--                 TYPED_Exp GAMMA (Exp.PLUS e1 e2) nat


def vars: List (Variable × Value) := [("v1", Value.nat 3), ("str_var", Value.string "World")]

def add_one_old (args: Array Value): exp_res :=
  let a0_opt := args[0]?
  match a0_opt with
  | some a0 => match a0 with
    | .nat n => return Value.nat (n+1)
    | x => throw (exp_error.wrong_type x.denote Sorts.nat)
  | none => throw (exp_error.wrong_args_num 0 1)

def add_one: Function × (Nat × Exp) := ("add_one", 1, Exp.nexp (NExp.plus (NExp.var "a0") (NExp.const 2)))

#check add_one

def test_env : P_state := (vars, [(add_one)])

#eval test_env
#eval vars


def e_1: Exp := Exp.nexp (NExp.multiply (NExp.plus (NExp.const 3) (NExp.const 34)) (NExp.const 2))
def e_2_nan: Exp := Exp.nexp (NExp.multiply (NExp.const 2) (NExp.divide (NExp.const 3) (NExp.const 0)))
def e_3_unknown: Exp := Exp.nexp (NExp.multiply (NExp.var "v_unknown") (NExp.divide (NExp.const 3) (NExp.const 0)))
def e_4_var: Exp := Exp.nexp (NExp.minus (NExp.var "v1") (NExp.divide (NExp.const 4) (NExp.const 2)))
def e_5_var_and_func: Exp := Exp.nexp (NExp.minus (NExp.var "v1") (NExp.func "add_one" #[Exp.nexp (NExp.const 1)]))
def e_6_bool: Exp := Exp.bexp (BExp.and (BExp.const true) (BExp.const false) )
def e_7_string: Exp := Exp.sexp (SExp.concat (SExp.const "Hello ") (SExp.var "str_var") )

#eval vars

#eval (e_1)
#eval (eval_exp e_1 test_env)
--#eval ((eval_exp e_1 test_env) == Except.ok (Value.nat 74))

#eval (e_2_nan)
#eval (eval_exp e_2_nan test_env)
--#eval (eval_exp test_env e_2_nan == .error exp_error.division_by_zero)

#eval (e_3_unknown)
#eval (eval_exp  e_3_unknown test_env)
--#eval (eval_Exp test_env e_3_unknown == Exp_RESULT.UNKNOWN_VAR "v_unknown")

#eval (e_4_var)
#eval (eval_exp  e_4_var test_env)
--#eval (eval_Exp test_env e_4_var == Exp_RESULT.some 1)


#eval (e_4_var)
#eval (eval_exp  e_4_var test_env)

#eval (e_5_var_and_func)
#eval (eval_exp  e_5_var_and_func test_env)
--#eval (eval_Exp test_env e_5_var_and_func == Exp_RESULT.some 1)

#eval (e_6_bool)
#eval (eval_exp  e_6_bool test_env)

#eval (e_7_string)
#eval (eval_exp  e_7_string test_env)



def faraway2 := 3


def test_array: List Exp := [Exp.nexp (NExp.const 5), Exp.sexp (SExp.const "bla")]

#eval n_eval_array test_array ([],[])
