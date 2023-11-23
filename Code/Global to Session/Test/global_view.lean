import Test.type
import Test.expression
import Lean
import Test.my_utils
import Test.my_logs

namespace G

  open Lean

  inductive P where
    | IF : Location -> Variable -> EXPRESSION -> P -> P -> P -> P
    | SEND_RECV    : Variable -> Location -> Location -> P -> P
    | COMPUTE (v: Variable) (e: EXPRESSION) (a: Location) :   P -> P
    | END     :  Location -> EXPRESSION -> P

  inductive T where
    | IF : Location -> T -> T -> T -> T
    | SEND_RECV    :  Location -> Location -> T -> T
    | END     :   T

  inductive Eval_error where
  | unknown_Location (a: Location) : Eval_error
  | expression_error (e: EXPRESSION_RESULT Nat): Eval_error
  | unknown_message_var (name: Variable) : Eval_error

  def Env := HashMap Location P_state

  abbrev Eval_res := ExceptT Eval_error (StateT Env (with_logs String)) Nat
end G

open G
open P

def GLOBAL_TO_TYPE: P -> T
  | IF l _ _ opt_a opt_b p => T.IF l (GLOBAL_TO_TYPE opt_a) (GLOBAL_TO_TYPE opt_b) (GLOBAL_TO_TYPE p)
  | SEND_RECV _ a b p => T.SEND_RECV a b (GLOBAL_TO_TYPE p)
  | COMPUTE _ _ _ p => (GLOBAL_TO_TYPE p)
  | END _ _ => T.END

def GP_TO_STRING: P -> String
  | IF a name e opt_a opt_b p => name ++ "@" ++ a ++ " <= if " ++ toString e ++ "\n" ++ GP_TO_STRING opt_a ++ "\nelse\n" ++ GP_TO_STRING opt_b ++ "\nend if\n" ++ GP_TO_STRING p
  | SEND_RECV v sender receiver p =>
    v ++ "@" ++ receiver ++ " <= " ++ v ++  "@" ++ sender ++ "\n" ++ (GP_TO_STRING p)
  | END a result => "RETURN " ++ toString result ++ "@" ++ a

  | COMPUTE v e a p => v ++  "@" ++ a ++ " <= " ++ (EXPRESSION_TO_STRING e) ++ " @" ++ a ++ "\n" ++ (GP_TO_STRING p)

instance: ToString P where
  toString := GP_TO_STRING

def GT_TO_STRING: T -> String
  | T.IF l t1 t2 p => "opt1: " ++ l ++ GT_TO_STRING t1 ++ "opt2: " ++ GT_TO_STRING t2 ++ "|" ++ GT_TO_STRING p
  | T.SEND_RECV sender receiver p =>
    sender ++ " --> " ++  receiver ++ "\n" ++ (GT_TO_STRING p) ++ ": Nat."
  | T.END => "end"

instance: ToString T where
  toString := GT_TO_STRING


instance: ToString Env where
  toString (e: Env) := list_to_continuos_string ((e.toList.map (fun x => "@" ++ x.fst ++ "\n  " ++ toString x.snd)).intersperse "\n")



open Eval_error


instance: ToString Eval_error where
  toString := fun x => match x with
  | Eval_error.unknown_Location a => "unknown Location " ++ a ++ " introduced"
  | Eval_error.expression_error e => "Expression Error:\n" ++ toString e
  | Eval_error.unknown_message_var v => "unknown message Variable: " ++ v


-- inductive global_evaluation_result_old (x: Type) where
--   | state (Env: global_P_state) (logs: List global_P_state) (result: x): global_evaluation_result_old x
--   | unknown_Location (a: Location) (logs: List global_P_state) : global_evaluation_result_old x
--   | expression_error (e: EXPRESSION_RESULT Nat) (logs: List global_P_state): global_evaluation_result_old x
--   | unknown_message_var (name: Variable) (logs: List global_P_state): global_evaluation_result_old x

instance: ToString (with_logs String (Except Eval_error Nat × Env)) where
  toString := fun eval =>
    let (res_e, e) := eval.value
    let result_string: String := match res_e with
    | Except.error e => "error:\n" ++ toString e
    | Except.ok res => "res:\n" ++ toString res
    "logs:\n" ++ list_to_string_seperated_by eval.logs "\n---------------------\n" ++ "Env:\n" ++ toString e ++ "\n" ++ result_string

def add  (b: Nat) (a: Nat := 2): Nat :=
  a + b

#eval (add 3 3)

def eval_global: P -> Eval_res
  | SEND_RECV v a b p =>
    do
    let state <- get
    append [toString state]
    append ["send_recv"]
    let sender_state_opt := state.find? a
    let receiver_state_opt := state.find? b

    match sender_state_opt with
    | Option.some sender_state =>
      match receiver_state_opt with
      | Option.some receiver_state =>
        let sender_value_opt := (var_map sender_state).lookup v

        match sender_value_opt with
        | Option.some sender_value =>
          let new_var_map: List (Variable × Nat) := (var_map receiver_state).concat (v, sender_value)
          let new_state: Env := (state.insert b (new_var_map, (funcs receiver_state)))
          set new_state
          eval_global p

        | Option.none => throw (Eval_error.unknown_message_var v)

      | Option.none => throw (Eval_error.unknown_Location b)
    | Option.none => throw (Eval_error.unknown_Location a)
   | COMPUTE v e a p =>
    do
      let state <- get
      append [toString state]
      append ["Compute"]
      let local_state_opt := state.find? a
      match local_state_opt with
      | Option.some local_state =>
        let evaluation := eval_expression local_state e
        match evaluation with
        | EXPRESSION_RESULT.some r =>
          let new_var_map: List (Variable × Nat) := (var_map local_state).concat (v, r)
          let new_state: Env := (state.insert a (new_var_map, (funcs local_state)))
          set new_state
          eval_global p
        | x => throw (Eval_error.expression_error x)

      | Option.none => throw (Eval_error.unknown_Location a)
  | IF a v e opt_a opt_b p =>
    do
    let state <- get
    append [toString state]
    append ["IF"]
    let local_state_opt := state.find? a
    match local_state_opt with
    | Option.some local_state =>
      let expr_result := eval_expression local_state e
      match expr_result with
      | EXPRESSION_RESULT.some r =>
        let new_var_map: List (Variable × Nat) := (var_map local_state).concat (v, r)
        let new_state: Env := (state.insert a (new_var_map, (funcs local_state)))
        set new_state
        eval_global p
      | x => throw (Eval_error.expression_error x)
    | Option.none => throw (Eval_error.unknown_Location a)
  | END a e =>
    do
    let state <- get
    let local_state_opt := state.find? a
    match local_state_opt with
    | Option.some local_state =>
      let evaluation := eval_expression local_state e
      match evaluation with
      | EXPRESSION_RESULT.some r => return r
      | x =>  throw (Eval_error.expression_error x)
    | Option.none => throw (Eval_error.unknown_Location a)


open Lean

def price_of (x: Nat): Nat := x + 100
def delivery_date (_x: Nat): Nat := 42

def l_test_Env1: P_state := ([("title", 0),("budget", 42)],[])
def l_test_Env2: P_state := ([],[("price_of", price_of), ("delivery_date_of", delivery_date)])

def g_test_Env : G.Env := HashMap.ofList [("buyer", l_test_Env1), ("seller", l_test_Env2)]


#eval g_test_Env

def test_program_1: P := SEND_RECV "var1" "client" "server" (END "client" (EXPRESSION.VAR "var1"))
def test_program_2: P := SEND_RECV "var1" "client" "server"
  (SEND_RECV "var2" "server" "client"
  (COMPUTE "var3" (EXPRESSION.DIVIDE (EXPRESSION.CONSTANT 2) (EXPRESSION.CONSTANT 0)) "server" (END "server" (EXPRESSION.VAR "var3"))))

#check (eval_global test_program_1 g_test_Env)

def trade_accept : P := (COMPUTE "date" (EXPRESSION.FUNC "delivery_date_of" (EXPRESSION.VAR "a")) "seller"
  (END "buyer" (EXPRESSION.VAR "date")))

def trade_decline : P := END "buyer" (EXPRESSION.CONSTANT 0)


def buyer_seller: P:= SEND_RECV "title" "buyer" "seller"
  (COMPUTE "price" (EXPRESSION.FUNC "price_of" (EXPRESSION.VAR "title")) "seller"
  (SEND_RECV "price" "seller" "buyer"
  (IF "buyer" "result" (EXPRESSION.SMALLER (EXPRESSION.VAR "price") (EXPRESSION.CONSTANT 300)) trade_accept trade_decline
  (END "buyer" (EXPRESSION.VAR "result")))))

def buyer_seller2: P := SEND_RECV "title" "buyer" "seller" (END "buyer" (EXPRESSION.VAR "title"))

#eval g_test_Env
#eval (buyer_seller)
#eval (eval_global buyer_seller g_test_Env)
#check (eval_global buyer_seller g_test_Env)

#eval (buyer_seller2)
#eval (eval_global buyer_seller2 g_test_Env)

#eval (test_program_1)

#eval (test_program_2)
#eval (eval_global test_program_2 HashMap.empty)
#eval (GLOBAL_TO_TYPE test_program_2)

#eval ( test_program_1)
