import Test.type
import Test.expression
import Lean

inductive GLOBAL_PROGRAM where
  | IF : Agent -> Variable -> EXPRESSION -> GLOBAL_PROGRAM -> GLOBAL_PROGRAM -> GLOBAL_PROGRAM -> GLOBAL_PROGRAM
  | SEND_RECV    : Variable -> Agent -> Agent -> GLOBAL_PROGRAM -> GLOBAL_PROGRAM
  | END     :  Agent -> EXPRESSION -> GLOBAL_PROGRAM
  | COMPUTE (v: Variable) (e: EXPRESSION) (a: Agent) :   GLOBAL_PROGRAM -> GLOBAL_PROGRAM
  | CHOREO (a: Agent) (v: Variable) (chor: GLOBAL_PROGRAM) (location_map: List (Agent × Agent)): GLOBAL_PROGRAM -> GLOBAL_PROGRAM

inductive GLOBAL_SESSION_TYPE where
  | SEND_RECV    :  Variable -> Agent -> Agent -> GLOBAL_SESSION_TYPE -> GLOBAL_SESSION_TYPE
  | END     :   GLOBAL_SESSION_TYPE

open GLOBAL_PROGRAM

def GLOBAL_TO_TYPE: GLOBAL_PROGRAM -> GLOBAL_SESSION_TYPE
  | IF a name e opt_a opt_b p => GLOBAL_SESSION_TYPE.END
  | SEND_RECV v a b p => GLOBAL_SESSION_TYPE.SEND_RECV v a b (GLOBAL_TO_TYPE p)
  | COMPUTE _ _ _ p => (GLOBAL_TO_TYPE p)
  | END _ _ => GLOBAL_SESSION_TYPE.END
  | CHOREO _ _ _ _ _ => GLOBAL_SESSION_TYPE.END

def repeat_string (s: String) (n: Nat): String :=
  if n > 0 then
    repeat_string s (n -1) ++ s
  else
    ""

-- i for indents
def GLOBAL_PROGRAM_TO_STRING (i: Nat) (p: GLOBAL_PROGRAM):  String :=
  let leading_spaces := repeat_string "  " i
  let content: String := match p with
  | IF a name e opt_a opt_b p => name ++ "@" ++ a ++ " <= if " ++ toString e ++ "\n" ++ GLOBAL_PROGRAM_TO_STRING  (i + 1) opt_a ++ "\nelse\n" ++ GLOBAL_PROGRAM_TO_STRING (i + 1) opt_b ++ "\nend if\n" ++ GLOBAL_PROGRAM_TO_STRING i p
  | SEND_RECV v sender receiver p =>
    v ++ "@" ++ receiver ++ " <= " ++ v ++  "@" ++ sender ++ "\n" ++ (GLOBAL_PROGRAM_TO_STRING i p)
  | END a result => toString result ++ "@" ++ a
  | GLOBAL_PROGRAM.COMPUTE v e a p => v ++  "@" ++ a ++ " <= " ++ (EXPRESSION_TO_STRING e) ++ " @" ++ a ++ "\n" ++ (GLOBAL_PROGRAM_TO_STRING i p)
  | CHOREO a v chor location_map p => v ++ "@" ++ a ++  " <= CHOREO with " ++ toString location_map ++ "\n" ++ GLOBAL_PROGRAM_TO_STRING (i+1) chor ++ "\nEND_CHOREO\n" ++  GLOBAL_PROGRAM_TO_STRING i p
  leading_spaces ++ content

instance: ToString GLOBAL_PROGRAM where
  toString := (GLOBAL_PROGRAM_TO_STRING 0)

def GLOBAL_TYPE_TO_STRING: GLOBAL_SESSION_TYPE -> String
  | GLOBAL_SESSION_TYPE.SEND_RECV v sender receiver p =>
    sender ++ " sends " ++ v ++ " to " ++  receiver ++ "\n" ++ (GLOBAL_TYPE_TO_STRING p)
  | GLOBAL_SESSION_TYPE.END => "END"

instance: ToString GLOBAL_SESSION_TYPE where
  toString := GLOBAL_TYPE_TO_STRING

open Lean

def global_environment := HashMap Agent environment


instance: ToString global_environment where
  toString (env: global_environment) := toString (env.toList.map (fun x => x.fst ++ "\n" ++ toString x.snd ++ "\n\n"))


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


def test_map (pair: (Agent × environment)) (location_map: List (Agent × Agent)) : (Agent × environment) :=


def pure_global_eval {α : Type} (elem: α): global_evaluation α :=
  fun a => global_evaluation_result.state a [] elem

instance: Monad global_evaluation where
  bind := bind_global_eval
  pure := pure_global_eval

def eval_global: GLOBAL_PROGRAM -> global_evaluation Nat
  | IF a v e opt_a opt_b p, state =>
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
  | SEND_RECV v a b p, state =>
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



  | COMPUTE v e a p, state =>
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

  | END a e, state =>
    let local_state_opt := state.find? a
    match local_state_opt with
    | Option.some local_state =>
      let evaluation := eval_expression local_state e
      match evaluation with
      | EXPRESSION_RESULT.some r =>
        global_evaluation_result.state state [state] r
      | x =>  global_evaluation_result.expression_error x [state]
    | Option.none => global_evaluation_result.unknown_agent a [state]

  | CHOREO a v choreo location_map p, state =>
    let local_state_opt := state.find? a
    match local_state_opt with
    | Option.some local_state =>
      let inner_state :=
        HashMap.ofList (state.toList.map (fun x =>
          match location_map.lookup x.fst with
          | Option.some other => (other, x.snd)
          | Option.none => x ))
      let res: global_evaluation_result Nat := eval_global choreo inner_state

      match res with
      | global_evaluation_result.state env logs value =>
        let new_var_map: List (Variable × Nat) := (var_map local_state).concat (v, value)
        let new_state: global_environment := (state.insert a (new_var_map, (funcs local_state)))
        eval_global p new_state
      | x => x


    | Option.none => global_evaluation_result.unknown_agent a [state]


def testSet: Set String := []


def price_of (x: Nat): Nat := x + 100
def deliveryDate : Nat -> Nat := fun _ => 42
def calculate_share (x: Nat): Nat := x / 2

def l_test_env1_buyer: environment := ([("title", 0),("budget", 51)],[])
def l_test_env1_seller: environment := ([],[("price_of", price_of), ("deliveryDate", deliveryDate)])

def g_test_env : global_environment := HashMap.ofList [("buyer", l_test_env1_buyer), ("seller", l_test_env1_seller)]



#eval g_test_env

def test_program_1: GLOBAL_PROGRAM := GLOBAL_PROGRAM.SEND_RECV "var1" "client" "server" (GLOBAL_PROGRAM.END "client" (EXPRESSION.VAR "var1"))
def test_program_2: GLOBAL_PROGRAM := GLOBAL_PROGRAM.SEND_RECV "var1" "client" "server"
  (GLOBAL_PROGRAM.SEND_RECV "var2" "server" "client"
  (GLOBAL_PROGRAM.COMPUTE "var3" (EXPRESSION.DIVIDE (EXPRESSION.CONSTANT 2) (EXPRESSION.CONSTANT 0)) "server" (GLOBAL_PROGRAM.END "server" (EXPRESSION.VAR "var3"))))


def trade_accept : GLOBAL_PROGRAM := (GLOBAL_PROGRAM.END "seller"  (EXPRESSION.FUNC  "deliveryDate" (EXPRESSION.VAR "title")))

def trade_decline : GLOBAL_PROGRAM :=  (GLOBAL_PROGRAM.END "buyer" (EXPRESSION.CONSTANT 0))


def buyer_seller: GLOBAL_PROGRAM := GLOBAL_PROGRAM.SEND_RECV "title" "buyer" "seller"
  (GLOBAL_PROGRAM.COMPUTE "price" (EXPRESSION.FUNC "price_of" (EXPRESSION.VAR "title")) "seller"
  (GLOBAL_PROGRAM.SEND_RECV "price" "seller" "buyer"
  (GLOBAL_PROGRAM.IF "buyer" "result" (EXPRESSION.SMALLER (EXPRESSION.VAR "price") (EXPRESSION.VAR "budget")) trade_accept trade_decline
  (GLOBAL_PROGRAM.END "buyer" (EXPRESSION.VAR "result")))))


#eval g_test_env
#eval (buyer_seller)
#eval (eval_global buyer_seller g_test_env)
#check (eval_global buyer_seller g_test_env)


def two_buyer_ask_for_money: GLOBAL_PROGRAM := GLOBAL_PROGRAM.SEND_RECV "price" "borrower" "friend"
  (GLOBAL_PROGRAM.COMPUTE "share" (EXPRESSION.FUNC "calculate_share" (EXPRESSION.VAR "price")) "friend"
  (GLOBAL_PROGRAM.SEND_RECV "share" "friend" "borrower"
  (GLOBAL_PROGRAM.END "borrower" (EXPRESSION.VAR "share"))))


def two_buyer_protocol: GLOBAL_PROGRAM := GLOBAL_PROGRAM.SEND_RECV "title" "buyer" "seller"
  (GLOBAL_PROGRAM.COMPUTE "price" (EXPRESSION.FUNC "price_of" (EXPRESSION.VAR "title")) "seller"
  (GLOBAL_PROGRAM.SEND_RECV "price" "seller" "buyer"
  (GLOBAL_PROGRAM.CHOREO "buyer" "friends_share" two_buyer_ask_for_money [ ("guy","friend"), ("buyer", "borrower")]
  (GLOBAL_PROGRAM.IF "buyer" "result" (EXPRESSION.SMALLER (EXPRESSION.VAR "price") (EXPRESSION.PLUS (EXPRESSION.VAR "budget") (EXPRESSION.VAR "friends_share"))) trade_accept trade_decline
  (GLOBAL_PROGRAM.END "buyer" (EXPRESSION.VAR "result"))))))



def l_test_env2_buyer: environment := ([("price", 100),("budget", 49), ("title", 2)],[])
def l_test_env2_friend: environment := ([],[("calculate_share", calculate_share), ("deliveryDate", deliveryDate)])
def g_test_env2 : global_environment := HashMap.ofList [("borrower", l_test_env2_buyer), ("friend", l_test_env2_friend)]

def g_test_env3 : global_environment := HashMap.ofList [("buyer", l_test_env1_buyer), ("guy", l_test_env2_friend), ("seller", l_test_env1_seller)]


#eval (two_buyer_ask_for_money)
#eval (two_buyer_protocol)

#eval (eval_global two_buyer_ask_for_money g_test_env2)
#eval (eval_global two_buyer_protocol g_test_env3)
