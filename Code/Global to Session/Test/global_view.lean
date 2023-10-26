import Test.type
import Test.expression

inductive GLOBAL_PROGRAM where
  | IF : Agent -> EXPRESSION -> GLOBAL_PROGRAM -> GLOBAL_PROGRAM -> GLOBAL_PROGRAM -> GLOBAL_PROGRAM
  | SEND_RECV    : Variable -> Agent -> Agent -> GLOBAL_PROGRAM -> GLOBAL_PROGRAM
  | END     :  Option (EXPRESSION) -> GLOBAL_PROGRAM
  | COMPUTE (v: Variable) (e: EXPRESSION) (a: Agent) :   GLOBAL_PROGRAM -> GLOBAL_PROGRAM

inductive GLOBAL_SESSION_TYPE where
  | SEND_RECV    :  Variable -> Agent -> Agent -> GLOBAL_SESSION_TYPE -> GLOBAL_SESSION_TYPE
  | END     :   GLOBAL_SESSION_TYPE


def GLOBAL_TO_TYPE: GLOBAL_PROGRAM -> GLOBAL_SESSION_TYPE
  | GLOBAL_PROGRAM.IF a e opt_a opt_b p => GLOBAL_SESSION_TYPE.END
  | GLOBAL_PROGRAM.SEND_RECV v a b p => GLOBAL_SESSION_TYPE.SEND_RECV v a b (GLOBAL_TO_TYPE p)
  | GLOBAL_PROGRAM.COMPUTE _ _ _ p => (GLOBAL_TO_TYPE p)
  | GLOBAL_PROGRAM.END _ => GLOBAL_SESSION_TYPE.END

-- instance: BEq AGENT where
--   beq:  AGENT -> AGENT -> Bool
--   | AGENT.client, AGENT.client => true
--   | AGENT.server, AGENT.server => true
--   | _, _ => false

def GLOBAL_PROGRAM_TO_STRING: GLOBAL_PROGRAM -> String
  | GLOBAL_PROGRAM.IF a e opt_a opt_b p => "if " ++ toString e ++ "\n" ++ GLOBAL_PROGRAM_TO_STRING opt_a ++ "\nelse\n" ++ GLOBAL_PROGRAM_TO_STRING opt_b ++ "\nend if\n" ++ GLOBAL_PROGRAM_TO_STRING p
  | GLOBAL_PROGRAM.SEND_RECV v sender receiver p =>
     sender ++ " sends " ++ v ++  " to " ++ receiver ++ "\n" ++ (GLOBAL_PROGRAM_TO_STRING p)
  | GLOBAL_PROGRAM.END result => match result with
    | some v => "RETURN " ++ toString v
    | none => "END"
  | GLOBAL_PROGRAM.COMPUTE v e a p => v ++ " <= " ++ (EXPRESSION_TO_STRING e) ++ " [" ++ a ++ "]\n" ++ (GLOBAL_PROGRAM_TO_STRING p)

instance: ToString GLOBAL_PROGRAM where
  toString := GLOBAL_PROGRAM_TO_STRING

def GLOBAL_TYPE_TO_STRING: GLOBAL_SESSION_TYPE -> String
  | GLOBAL_SESSION_TYPE.SEND_RECV v sender receiver p =>
    sender ++ " sends " ++ v ++ " to " ++  receiver ++ "\n" ++ (GLOBAL_TYPE_TO_STRING p)
  | GLOBAL_SESSION_TYPE.END => "END"

instance: ToString GLOBAL_SESSION_TYPE where
  toString := GLOBAL_TYPE_TO_STRING

inductive global_evaluation (x: Type) where
  | state (var_map: List (Variable × Nat)) (result: x): global_evaluation x

def bind_global_eval:  global_evaluation α → (α → global_evaluation β) → global_evaluation β
  | global_evaluation.state _ res, f => f res

def pure_global_eval {α : Type} (elem: α): global_evaluation α :=
  global_evaluation.state [] elem

instance: Monad global_evaluation where
  bind := bind_global_eval
  pure := pure_global_eval

#eval [("aaa", eval_expression [] (EXPRESSION.CONSTANT 3))]

def eval_global (var_map: List (Variable × Nat)): GLOBAL_PROGRAM -> EXPRESSION_RESULT Nat
  | GLOBAL_PROGRAM.IF  a e opt_a opt_b p =>
    do
    let expr_result <- eval_expression var_map e
    if expr_result == 0 then
      eval_global var_map opt_b
    else
      eval_global var_map opt_a
    eval_global var_map p

  | GLOBAL_PROGRAM.SEND_RECV v a b p => eval_global var_map p
  | GLOBAL_PROGRAM.COMPUTE v e a p =>
    do
    let evaluation <- eval_expression var_map e
    let new_var_map := var_map ++ [(v, evaluation)]
    eval_global new_var_map p
  | GLOBAL_PROGRAM.END r => match r with
    | Option.some r_v => eval_expression var_map r_v
    | Option.none => EXPRESSION_RESULT.some 0

instance: ToString (EXPRESSION_RESULT Nat) where
  toString (e: EXPRESSION_RESULT Nat) := match e with
    | EXPRESSION_RESULT.some v => toString v
    | EXPRESSION_RESULT.UNKNOWN_VAR name => "expression contains unknown var: " ++ name
    | EXPRESSION_RESULT.DIV_BY_ZERO => "Division by zero "


def eval_global_start (p: GLOBAL_PROGRAM): EXPRESSION_RESULT Nat :=
  eval_global [] p


def test_program_1: GLOBAL_PROGRAM := GLOBAL_PROGRAM.SEND_RECV "var1" "client" "server" (GLOBAL_PROGRAM.END Option.none)
def test_program_2: GLOBAL_PROGRAM := GLOBAL_PROGRAM.SEND_RECV "var1" "client" "server"
  (GLOBAL_PROGRAM.SEND_RECV "var2" "server" "client"
  (GLOBAL_PROGRAM.COMPUTE "var3" (EXPRESSION.DIVIDE (EXPRESSION.CONSTANT 2) (EXPRESSION.CONSTANT 0)) "server" (GLOBAL_PROGRAM.END (Option.some (EXPRESSION.VAR "var3")))))


def trade_accept : GLOBAL_PROGRAM := (GLOBAL_PROGRAM.COMPUTE "decision" (EXPRESSION.CONSTANT 1) "buyer"
  (GLOBAL_PROGRAM.SEND_RECV "decision" "buyer" "seller" (GLOBAL_PROGRAM.END (Option.some (EXPRESSION.VAR "price")))))

def trade_decline : GLOBAL_PROGRAM := (GLOBAL_PROGRAM.COMPUTE "decision" (EXPRESSION.CONSTANT 0) "buyer"
  (GLOBAL_PROGRAM.SEND_RECV "decision" "buyer" "seller" (GLOBAL_PROGRAM.END (Option.some (EXPRESSION.CONSTANT 0)))))


def buyer_seller: GLOBAL_PROGRAM := GLOBAL_PROGRAM.COMPUTE "title" (EXPRESSION.CONSTANT 2222) "buyer"
  (GLOBAL_PROGRAM.SEND_RECV "title" "buyer" "seller"
  (GLOBAL_PROGRAM.COMPUTE "price" (EXPRESSION.PLUS (EXPRESSION.VAR "title") (EXPRESSION.CONSTANT 2)) "seller"
  (GLOBAL_PROGRAM.SEND_RECV "price" "seller" "buyer"
  (GLOBAL_PROGRAM.IF "buyer" (EXPRESSION.SMALLER (EXPRESSION.VAR "price") (EXPRESSION.CONSTANT 300)) trade_accept trade_decline
  (GLOBAL_PROGRAM.END (Option.some (EXPRESSION.VAR "price")))))))



#eval (buyer_seller)
#eval (eval_global [] buyer_seller)

#eval (test_program_1)

#eval (test_program_2)
#eval (eval_global [] test_program_2)
#eval (GLOBAL_TO_TYPE test_program_2)
