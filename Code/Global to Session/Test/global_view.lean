import Test.agent
import Test.type
import Test.expression

inductive GLOBAL_PROGRAM where
  | SEND_RECV    :  channelVarType -> variableType -> AGENT -> AGENT -> GLOBAL_PROGRAM -> GLOBAL_PROGRAM
  | END     :   GLOBAL_PROGRAM
  | COMPUTE (v: variableType) (e: EXPRESSION) (a: AGENT) :   GLOBAL_PROGRAM -> GLOBAL_PROGRAM

inductive GLOBAL_SESSION_TYPE where
  | SEND_RECV    :  channelVarType -> variableType -> AGENT -> AGENT -> GLOBAL_SESSION_TYPE -> GLOBAL_SESSION_TYPE
  | END     :   GLOBAL_SESSION_TYPE


def GLOBAL_TO_TYPE: GLOBAL_PROGRAM -> GLOBAL_SESSION_TYPE
  | GLOBAL_PROGRAM.SEND_RECV c v a b p => GLOBAL_SESSION_TYPE.SEND_RECV c v a b (GLOBAL_TO_TYPE p)
  | GLOBAL_PROGRAM.COMPUTE _ _ _ p => (GLOBAL_TO_TYPE p)
  | GLOBAL_PROGRAM.END => GLOBAL_SESSION_TYPE.END

-- instance: BEq AGENT where 
--   beq:  AGENT -> AGENT -> Bool 
--   | AGENT.client, AGENT.client => true
--   | AGENT.server, AGENT.server => true
--   | _, _ => false

def GLOBAL_PROGRAM_TO_STRING: GLOBAL_PROGRAM -> String
  | GLOBAL_PROGRAM.SEND_RECV c v sender receiver p => 
    (AGENT_TO_STRING sender) ++ " --" ++ c ++ "--> " ++ (AGENT_TO_STRING receiver) ++ ": " ++ v ++  "\n" ++ (GLOBAL_PROGRAM_TO_STRING p)
  | GLOBAL_PROGRAM.END => "END"
  | GLOBAL_PROGRAM.COMPUTE v e a p => v ++ " <= " ++ (EXPRESSION_TO_STRING e) ++ " [" ++ (AGENT_TO_STRING a) ++ "]\n" ++ (GLOBAL_PROGRAM_TO_STRING p)

instance: ToString GLOBAL_PROGRAM where 
  toString := GLOBAL_PROGRAM_TO_STRING

def GLOBAL_TYPE_TO_STRING: GLOBAL_SESSION_TYPE -> String
  | GLOBAL_SESSION_TYPE.SEND_RECV c v sender receiver p => 
    (AGENT_TO_STRING sender) ++ " --" ++ c ++ "--> " ++ (AGENT_TO_STRING receiver) ++ ": " ++ v ++  "\n" ++ (GLOBAL_TYPE_TO_STRING p)
  | GLOBAL_SESSION_TYPE.END => "END"
  
instance: ToString GLOBAL_SESSION_TYPE where 
  toString := GLOBAL_TYPE_TO_STRING

def test_program_1: GLOBAL_PROGRAM := GLOBAL_PROGRAM.SEND_RECV "channel1" "var1" AGENT.client AGENT.server GLOBAL_PROGRAM.END
def test_program_2: GLOBAL_PROGRAM := GLOBAL_PROGRAM.SEND_RECV "channel1" "var1" AGENT.client AGENT.server 
  (GLOBAL_PROGRAM.SEND_RECV "channel2" "var2" AGENT.server AGENT.client 
  (GLOBAL_PROGRAM.COMPUTE "var3" (EXPRESSION.PLUS (EXPRESSION.CONSTANT 2) (EXPRESSION.CONSTANT 2)) AGENT.server GLOBAL_PROGRAM.END))


#eval (test_program_1)

#eval (test_program_2)
#eval (GLOBAL_TO_TYPE test_program_2)
