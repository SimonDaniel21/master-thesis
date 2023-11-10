import Test.type
import Test.expression
import Lean

inductive GLOBAL_PROGRAM where
  | IF : Agent -> Variable -> EXPRESSION -> GLOBAL_PROGRAM -> GLOBAL_PROGRAM -> GLOBAL_PROGRAM -> GLOBAL_PROGRAM
  | SEND_RECV    : Variable -> Agent -> Agent -> GLOBAL_PROGRAM -> GLOBAL_PROGRAM
  | END     :  Agent -> EXPRESSION -> GLOBAL_PROGRAM
  | COMPUTE (v: Variable) (e: EXPRESSION) (a: Agent) :   GLOBAL_PROGRAM -> GLOBAL_PROGRAM

inductive GLOBAL_SESSION_TYPE where
  | SEND_RECV    :  Variable -> Agent -> Agent -> GLOBAL_SESSION_TYPE -> GLOBAL_SESSION_TYPE
  | END     :   GLOBAL_SESSION_TYPE


def GLOBAL_TO_TYPE: GLOBAL_PROGRAM -> GLOBAL_SESSION_TYPE
  | GLOBAL_PROGRAM.IF a name e opt_a opt_b p => GLOBAL_SESSION_TYPE.END
  | GLOBAL_PROGRAM.SEND_RECV v a b p => GLOBAL_SESSION_TYPE.SEND_RECV v a b (GLOBAL_TO_TYPE p)
  | GLOBAL_PROGRAM.COMPUTE _ _ _ p => (GLOBAL_TO_TYPE p)
  | GLOBAL_PROGRAM.END _ _ => GLOBAL_SESSION_TYPE.END

def GLOBAL_PROGRAM_TO_STRING: GLOBAL_PROGRAM -> String
  | GLOBAL_PROGRAM.IF a name e opt_a opt_b p => name ++ "@" ++ a ++ " <= if " ++ toString e ++ "\n" ++ GLOBAL_PROGRAM_TO_STRING opt_a ++ "\nelse\n" ++ GLOBAL_PROGRAM_TO_STRING opt_b ++ "\nend if\n" ++ GLOBAL_PROGRAM_TO_STRING p
  | GLOBAL_PROGRAM.SEND_RECV v sender receiver p =>
    v ++ "@" ++ receiver ++ " <= " ++ v ++  "@" ++ sender ++ "\n" ++ (GLOBAL_PROGRAM_TO_STRING p)
  | GLOBAL_PROGRAM.END a result => "RETURN " ++ toString result ++ "@" ++ a

  | GLOBAL_PROGRAM.COMPUTE v e a p => v ++  "@" ++ a ++ " <= " ++ (EXPRESSION_TO_STRING e) ++ " @" ++ a ++ "\n" ++ (GLOBAL_PROGRAM_TO_STRING p)

instance: ToString GLOBAL_PROGRAM where
  toString := GLOBAL_PROGRAM_TO_STRING

def GLOBAL_TYPE_TO_STRING: GLOBAL_SESSION_TYPE -> String
  | GLOBAL_SESSION_TYPE.SEND_RECV v sender receiver p =>
    sender ++ " sends " ++ v ++ " to " ++  receiver ++ "\n" ++ (GLOBAL_TYPE_TO_STRING p)
  | GLOBAL_SESSION_TYPE.END => "END"

instance: ToString GLOBAL_SESSION_TYPE where
  toString := GLOBAL_TYPE_TO_STRING

open Lean

def global_environment := HashMap Agent environment

def temp (a: Agent) () :=

instance: ToString global_environment where
  toString (env: global_environment) := toString (env.toList.map environment_to_string intersperse "\n")


instance: ToString GLOBAL_SESSION_TYPE where
  toString := GLOBAL_TYPE_TO_STRING


inductive global_evaluation_result (x: Type) where
  | state (env: global_environment) (logs: List global_environment) (result: x): global_evaluation_result x
  | unknown_agent (a: Agent) (logs: List global_environment) : global_evaluation_result x
  | expression_error (e: EXPRESSION_RESULT Nat) (logs: List global_environment): global_evaluation_result x
  | unknown_message_var (name: Variable) (logs: List global_environment): global_evaluation_result x



def global_evaluation_result_to_string: global_evaluation_result Nat -> String
  | global_evaluation_result.state env logs res => "Logs: " ++ toString logs ++ toString env ++ "\n --> \n" ++ (toString res)
  | global_evaluation_result.unknown_agent a logs => "Logs: " ++ toString logs ++ "unknown agent " ++ a ++ " introduced"
  | global_evaluation_result.expression_error e logs => "Logs: " ++ toString logs ++ "Expression Error:\n" ++ toString e
  | global_evaluation_result.unknown_message_var v logs => "Logs: " ++ toString logs ++ "unknown message Variable: " ++ v

instance: ToString (global_evaluation_result Nat) where
  toString := global_evaluation_result_to_string

def global_evaluation (x: Type) := global_environment -> global_evaluation_result x

#eval (state)

def a: Writer
def bind_global_eval:  global_evaluation α → (α → global_evaluation β) → global_evaluation β
  | gl_eval, func, state =>
    let result := gl_eval state
    match result with
    | global_evaluation_result.state env logs res =>
      match (func res env) with
      | global_evaluation_result.state env2 logs2 res2 => global_evaluation_result.state env ((logs.append logs2).concat env2) res2
      | global_evaluation_result.unknown_agent a logs2 => global_evaluation_result.unknown_agent a logs
      | global_evaluation_result.expression_error e logs2 => global_evaluation_result.expression_error e logs
      | global_evaluation_result.unknown_message_var v logs2 => global_evaluation_result.unknown_message_var v logs
    | global_evaluation_result.unknown_agent a logs => global_evaluation_result.unknown_agent a logs
    | global_evaluation_result.unknown_message_var v logs => global_evaluation_result.unknown_agent v logs
    | global_evaluation_result.expression_error e logs => global_evaluation_result.expression_error e logs


def add  (b: Nat) (a: Nat := 2): Nat :=
  a + b

#eval (add 3 3)

def test_g_env: global_environment := HashMap.empty



def pure_global_eval {α : Type} (elem: α): global_evaluation α :=
  fun a => global_evaluation_result.state a [] elem

instance: Monad global_evaluation where
  bind := bind_global_eval
  pure := pure_global_eval

def eval_global: GLOBAL_PROGRAM -> global_evaluation Nat
  | GLOBAL_PROGRAM.IF a v e opt_a opt_b p, state =>
    let local_state_opt := state.find? a

    match local_state_opt with
    | Option.some local_state =>
      let expr_result := eval_expression local_state e
      match expr_result with
      | EXPRESSION_RESULT.some n =>
        let branch_eval := if n == 0 then eval_global opt_b else eval_global opt_a
        let branch_result := branch_eval state
        match branch_result with
        | global_evaluation_result.state env logs r =>
          let new_var_map: List (Variable × Nat) := (var_map local_state).concat (v, r)
          let new_state: global_environment := (state.insert a (new_var_map, (funcs local_state)))
          eval_global p new_state
        | x => x

      | y => global_evaluation_result.expression_error y [state]

    | Option.none => global_evaluation_result.unknown_agent a [state]


--BUG alsways Unknown agent a, never b :(
  | GLOBAL_PROGRAM.SEND_RECV v a b p, state =>
    let eval_result_opt :=
      do
      let sender_state <- state.find? a
      let receiver_state <- state.find? b
      let sender_value_opt := (var_map sender_state).lookup v

      match sender_value_opt with
      | Option.some sender_value =>
        let new_var_map: List (Variable × Nat) := (var_map receiver_state).concat (v, sender_value)
        let new_state: global_environment := (state.insert b (new_var_map, (funcs receiver_state)))
        Option.some (eval_global p new_state)

      | Option.none => Option.some (global_evaluation_result.unknown_message_var v [state])

    match eval_result_opt with
    | Option.some eval_result => eval_result
    | Option.none => global_evaluation_result.unknown_agent a [state]



  | GLOBAL_PROGRAM.COMPUTE v e a p, state =>
    let local_state_opt := state.find? a
    match local_state_opt with
    | Option.some local_state =>
      let evaluation := eval_expression local_state e
      match evaluation with
      | EXPRESSION_RESULT.some r =>
        let new_var_map: List (Variable × Nat) := (var_map local_state).concat (v, r)
        let new_state: global_environment := (state.insert a (new_var_map, (funcs local_state)))
        eval_global p new_state
      | x =>  global_evaluation_result.expression_error x [state]

    | Option.none => global_evaluation_result.unknown_agent a [state]

  | GLOBAL_PROGRAM.END a e, state =>
    let local_state_opt := state.find? a
    match local_state_opt with
    | Option.some local_state =>
      let evaluation := eval_expression local_state e
      match evaluation with
      | EXPRESSION_RESULT.some r =>
        global_evaluation_result.state state [state] r
      | x =>  global_evaluation_result.expression_error x [state]
    | Option.none => global_evaluation_result.unknown_agent a [state]


def price_of (x: Nat): Nat := x + 100

def l_test_env1: environment := ([("title", 0),("budget", 42)],[])
def l_test_env2: environment := ([],[("price_of", price_of)])

def g_test_env : global_environment := HashMap.ofList [("buyer", l_test_env1), ("seller", l_test_env2)]






#eval g_test_env

def test_program_1: GLOBAL_PROGRAM := GLOBAL_PROGRAM.SEND_RECV "var1" "client" "server" (GLOBAL_PROGRAM.END "client" (EXPRESSION.VAR "var1"))
def test_program_2: GLOBAL_PROGRAM := GLOBAL_PROGRAM.SEND_RECV "var1" "client" "server"
  (GLOBAL_PROGRAM.SEND_RECV "var2" "server" "client"
  (GLOBAL_PROGRAM.COMPUTE "var3" (EXPRESSION.DIVIDE (EXPRESSION.CONSTANT 2) (EXPRESSION.CONSTANT 0)) "server" (GLOBAL_PROGRAM.END "server" (EXPRESSION.VAR "var3"))))


def trade_accept : GLOBAL_PROGRAM := (GLOBAL_PROGRAM.COMPUTE "decision" (EXPRESSION.CONSTANT 1) "buyer"
  (GLOBAL_PROGRAM.SEND_RECV "decision" "buyer" "seller" (GLOBAL_PROGRAM.END "buyer" (EXPRESSION.CONSTANT 1))))

def trade_decline : GLOBAL_PROGRAM := (GLOBAL_PROGRAM.COMPUTE "decision" (EXPRESSION.CONSTANT 0) "buyer"
  (GLOBAL_PROGRAM.SEND_RECV "decision" "buyer" "seller" (GLOBAL_PROGRAM.END "buyer" (EXPRESSION.CONSTANT 0))))


def buyer_seller: GLOBAL_PROGRAM := GLOBAL_PROGRAM.SEND_RECV "title" "buyer" "seller"
  (GLOBAL_PROGRAM.COMPUTE "price" (EXPRESSION.FUNC "price_of" (EXPRESSION.VAR "title")) "seller"
  (GLOBAL_PROGRAM.SEND_RECV "price" "seller" "buyer"
  (GLOBAL_PROGRAM.IF "buyer" "decision" (EXPRESSION.SMALLER (EXPRESSION.VAR "price") (EXPRESSION.CONSTANT 300)) trade_accept trade_decline
  (GLOBAL_PROGRAM.END "buyer" (EXPRESSION.VAR "decision")))))

def buyer_seller2: GLOBAL_PROGRAM := GLOBAL_PROGRAM.SEND_RECV "title" "buyer" "seller" (GLOBAL_PROGRAM.END "buyer" (EXPRESSION.VAR "title"))

#eval g_test_env
#eval (buyer_seller)
#eval (eval_global buyer_seller g_test_env)


#eval (buyer_seller2)
#eval (eval_global buyer_seller2 g_test_env)

#eval (test_program_1)

#eval (test_program_2)
#eval (eval_global test_program_2 HashMap.empty)
#eval (GLOBAL_TO_TYPE test_program_2)
