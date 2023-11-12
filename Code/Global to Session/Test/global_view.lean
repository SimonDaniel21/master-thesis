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

#eval List.map (fun (x: Nat) => toString x) [1,2,3]
#eval [2,3,44].map (· + 2)
#eval (none).map (fun x => x*3)

#eval (pure "2.2" : Option String)
#eval pure (·*·+· ) <*> some 4 <*> some 3 <*> some 2

instance: Applicative List where
  pure := List.pure
  seq f x := List.bind f fun y => Functor.map y (x ())_

  #eval [(·*2)] <*> [2,3]



instance: ToString global_environment where
  toString (env: global_environment) := toString ((env.toList.map (fun x => x.fst ++ " ->¬" ++ toString x.snd ++ "¬")).intersperse "¬")


--instance: ToString global_environment where
--  toString (env: global_environment) := toString (env.toList.map environment_to_string intersperse "\n")


instance: ToString GLOBAL_SESSION_TYPE where
  toString := GLOBAL_TYPE_TO_STRING

structure program_state where
  var: Nat

structure with_logs (t: Type) where
  value: t
  logs: List String

instance: ToString (with_logs Nat) where
  toString := fun v_with_logs => "value => " ++ toString v_with_logs.value ++ "\nLogs =>¬" ++ toString v_with_logs.logs


def my_add2(v: Nat) : with_logs Nat :=
  {value := v+2, logs := ["+2 (" ++ toString v ++ ") "]}

def my_mult3(v: Nat) : with_logs Nat :=
  {value := v*3, logs := ["*3 (" ++ toString v ++ ") "]}

def bind_with_logs:  with_logs α → (α → with_logs β) → with_logs β :=
  fun x f =>
    let result := f x.value
    {value := result.value, logs := x.logs.append result.logs}

instance: Monad with_logs where
  bind := bind_with_logs
  pure := fun x => {value := x, logs := []}


#check (with_logs Nat)


def test: with_logs Nat := (do
  let x <- my_add2 2
  let y <- my_mult3 x
  return y)

#eval test


inductive evaluation_error where
  | unknown_agent (a: Agent) : evaluation_error
  | expression_error (e: EXPRESSION_RESULT Nat): evaluation_error
  | unknown_message_var (name: Variable) : evaluation_error


instance: ToString evaluation_error where
  toString := fun x => match x with
  | evaluation_error.unknown_agent a => "unknown agent " ++ a ++ " introduced"
  | evaluation_error.expression_error e => "Expression Error:\n" ++ toString e
  | evaluation_error.unknown_message_var v => "unknown message Variable: " ++ v

abbrev global_evaluation_result := ExceptT evaluation_error (StateM global_environment) Nat

inductive global_evaluation_result_old (x: Type) where
  | state (env: global_environment) (logs: List global_environment) (result: x): global_evaluation_result_old x
  | unknown_agent (a: Agent) (logs: List global_environment) : global_evaluation_result_old x
  | expression_error (e: EXPRESSION_RESULT Nat) (logs: List global_environment): global_evaluation_result_old x
  | unknown_message_var (name: Variable) (logs: List global_environment): global_evaluation_result_old x

def myStateM := StateM Nat Nat
#check myStateM


abbrev test_monad := ExceptT evaluation_error with_logs Nat

abbrev test_monad2 := ExceptT evaluation_error (StateM Nat) Nat


instance: ToString global_evaluation_result where
  toString := fun eval =>
   ""

def global_evaluation_old := global_environment -> global_evaluation_result

def add  (b: Nat) (a: Nat := 2): Nat :=
  a + b

#eval (add 3 3)

def test_g_env: global_environment := HashMap.empty

open GLOBAL_PROGRAM

def eval_global: GLOBAL_PROGRAM -> global_evaluation_result
  | SEND_RECV v a b p =>
    do
    let state <- get
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
          let new_state: global_environment := (state.insert b (new_var_map, (funcs receiver_state)))
          set new_state
          eval_global p

        | Option.none => throw (evaluation_error.unknown_message_var v)

      | Option.none => throw (evaluation_error.unknown_agent b)
    | Option.none => throw (evaluation_error.unknown_agent a)


    throw (evaluation_error.unknown_agent "agent9")
   | GLOBAL_PROGRAM.COMPUTE v e a p =>
    do
      let state <- get
      let local_state_opt := state.find? a
      match local_state_opt with
      | Option.some local_state =>
        let evaluation := eval_expression local_state e
        match evaluation with
        | EXPRESSION_RESULT.some r =>
          let new_var_map: List (Variable × Nat) := (var_map local_state).concat (v, r)
          let new_state: global_environment := (state.insert a (new_var_map, (funcs local_state)))
          set new_state
          eval_global p
        | x => throw (evaluation_error.expression_error x)

      | Option.none => throw (evaluation_error.unknown_agent a)
  | GLOBAL_PROGRAM.IF a v e opt_a opt_b p =>
    do
    let state <- get
    throw (evaluation_error.unknown_agent "if not supported")
  | GLOBAL_PROGRAM.END a e =>
    do
    let state <- get
    let local_state_opt := state.find? a
    match local_state_opt with
    | Option.some local_state =>
      let evaluation := eval_expression local_state e
      match evaluation with
      | EXPRESSION_RESULT.some r => return r
      | x =>  throw (evaluation_error.expression_error x)
    | Option.none => throw (evaluation_error.unknown_agent a)




def price_of (x: Nat): Nat := x + 100

def l_test_env1: environment := ([("title", 0),("budget", 42)],[])
def l_test_env2: environment := ([],[("price_of", price_of)])

def g_test_env : global_environment := HashMap.ofList [("buyer", l_test_env1), ("seller", l_test_env2)]


#eval g_test_env

def test_program_1: GLOBAL_PROGRAM := GLOBAL_PROGRAM.SEND_RECV "var1" "client" "server" (GLOBAL_PROGRAM.END "client" (EXPRESSION.VAR "var1"))
def test_program_2: GLOBAL_PROGRAM := GLOBAL_PROGRAM.SEND_RECV "var1" "client" "server"
  (GLOBAL_PROGRAM.SEND_RECV "var2" "server" "client"
  (GLOBAL_PROGRAM.COMPUTE "var3" (EXPRESSION.DIVIDE (EXPRESSION.CONSTANT 2) (EXPRESSION.CONSTANT 0)) "server" (GLOBAL_PROGRAM.END "server" (EXPRESSION.VAR "var3"))))

#eval eval_global test_program_1

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
