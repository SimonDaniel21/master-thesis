import Test.type
import Test.agent
import Test.expression

inductive LOCAL_PROGRAM where
  | SEND    :  channelVarType -> variableType -> AGENT -> LOCAL_PROGRAM -> LOCAL_PROGRAM
  | RECV    :  channelVarType -> variableType -> AGENT -> LOCAL_PROGRAM -> LOCAL_PROGRAM
  | END     :   LOCAL_PROGRAM
  | COMPUTE (v: variableType) (e: EXPRESSION) :   LOCAL_PROGRAM -> LOCAL_PROGRAM
 

inductive LOCAL_SESSION_TYPE where
  | SEND    :  channelVarType -> variableType -> AGENT -> LOCAL_SESSION_TYPE -> LOCAL_SESSION_TYPE
  | RECV    :  channelVarType -> variableType -> AGENT -> LOCAL_SESSION_TYPE -> LOCAL_SESSION_TYPE
  | END     :  LOCAL_SESSION_TYPE

def LOCAL_TO_TYPE: LOCAL_PROGRAM -> LOCAL_SESSION_TYPE
  | LOCAL_PROGRAM.SEND c v receiver p => LOCAL_SESSION_TYPE.SEND c v receiver (LOCAL_TO_TYPE p)
  | LOCAL_PROGRAM.RECV c v sender p => LOCAL_SESSION_TYPE.RECV c v sender (LOCAL_TO_TYPE p)
  | LOCAL_PROGRAM.COMPUTE _ _ p => (LOCAL_TO_TYPE p)
  | LOCAL_PROGRAM.END => LOCAL_SESSION_TYPE.END

def LOCAL_PROGRAM_TO_STRING: LOCAL_PROGRAM -> String
  | LOCAL_PROGRAM.SEND c v receiver p => 
    "!(" ++ (AGENT_TO_STRING receiver) ++ ", " ++ v ++ ")" ++ "\n" ++ (LOCAL_PROGRAM_TO_STRING p)
  | LOCAL_PROGRAM.RECV c v sender p => 
    "?(" ++ (AGENT_TO_STRING sender) ++ ", " ++ v ++ ")" ++ "\n" ++ (LOCAL_PROGRAM_TO_STRING p)
  | LOCAL_PROGRAM.COMPUTE v e p => v ++ " <= " ++ (EXPRESSION_TO_STRING e) ++ "\n" ++ (LOCAL_PROGRAM_TO_STRING p)
  | LOCAL_PROGRAM.END => "END"

def LOCAL_TYPE_TO_STRING: LOCAL_SESSION_TYPE -> String
  | LOCAL_SESSION_TYPE.SEND c v receiver p => 
    "!(" ++ (AGENT_TO_STRING receiver) ++ ", " ++ v ++ ")" ++ "\n" ++ (LOCAL_TYPE_TO_STRING p)
  | LOCAL_SESSION_TYPE.RECV c v sender p => 
    "?(" ++ (AGENT_TO_STRING sender) ++ ", " ++ v ++ ")" ++ "\n" ++ (LOCAL_TYPE_TO_STRING p)
  | LOCAL_SESSION_TYPE.END => "END"  

instance LOCAL_PROGRAM_DEBUG: ToString LOCAL_PROGRAM where 
  toString := LOCAL_PROGRAM_TO_STRING

instance: ToString LOCAL_SESSION_TYPE where 
  toString := LOCAL_TYPE_TO_STRING

def lp_1: LOCAL_PROGRAM := LOCAL_PROGRAM.SEND "channel1" "var1" AGENT.server LOCAL_PROGRAM.END
def lp_2: LOCAL_PROGRAM := LOCAL_PROGRAM.SEND "channel1" "var1" AGENT.server
  (LOCAL_PROGRAM.RECV "channel2" "var2" AGENT.server 
  (LOCAL_PROGRAM.COMPUTE "var3" (EXPRESSION.CONSTANT 3) LOCAL_PROGRAM.END))


#eval (lp_1)
#eval (LOCAL_TO_TYPE lp_1)

#eval (lp_2)
#eval (LOCAL_TO_TYPE lp_2)