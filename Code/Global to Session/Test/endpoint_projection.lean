import Test.global_view
import Test.local_view
import Test.expression


def endpoint_projection (a: Agent): GLOBAL_PROGRAM -> LOCAL_PROGRAM
  | (G.P.SEND_RECV c v sender receiver p) =>
    if (a == sender) then LOCAL_PROGRAM.SEND c v receiver (endpoint_projection a p)
    else if a == receiver then LOCAL_PROGRAM.RECV c v sender (endpoint_projection a p)
    else (endpoint_projection a p)
  | GLOBAL_PROGRAM.END res => match res with
    | Option.some v => LOCAL_PROGRAM.END
    | Option.none => LOCAL_PROGRAM.END
  | GLOBAL_PROGRAM.COMPUTE v e b p =>
    if (a == b) then LOCAL_PROGRAM.COMPUTE v e (endpoint_projection a p)
    else (endpoint_projection a p)

def endpoint_projection_type (a: Agent): GLOBAL_SESSION_TYPE -> LOCAL_SESSION_TYPE
  | (GLOBAL_SESSION_TYPE.SEND_RECV c v sender receiver p) =>
    if (a == sender) then LOCAL_SESSION_TYPE.SEND c v receiver (endpoint_projection_type a p)
    else if a == receiver then LOCAL_SESSION_TYPE.RECV c v sender (endpoint_projection_type a p)
    else (endpoint_projection_type a p)
  | GLOBAL_SESSION_TYPE.END => LOCAL_SESSION_TYPE.END

def test_global_program: GLOBAL_PROGRAM := (GLOBAL_PROGRAM.SEND_RECV "channel1" "var1" AGENT.client AGENT.server
(GLOBAL_PROGRAM.SEND_RECV "channel2" "var2" AGENT.server AGENT.client
(GLOBAL_PROGRAM.COMPUTE "var3" (EXPRESSION.PLUS (EXPRESSION.CONSTANT 2) (EXPRESSION.CONSTANT 4)) AGENT.server (GLOBAL_PROGRAM.END (Option.some (EXPRESSION.VAR "var3"))))))


def client_local_program: LOCAL_PROGRAM := endpoint_projection AGENT.client test_global_program
def server_local_program: LOCAL_PROGRAM := endpoint_projection AGENT.server test_global_program

def global_type: GLOBAL_SESSION_TYPE := GLOBAL_TO_TYPE test_global_program

#eval (test_global_program)
#eval (GLOBAL_TO_TYPE test_global_program)
#eval (eval_global [] test_global_program)

#eval (client_local_program)
#eval (server_local_program)

#eval (LOCAL_TO_TYPE client_local_program)
#eval (LOCAL_TO_TYPE server_local_program)

#eval (endpoint_projection_type AGENT.client global_type)
#eval (endpoint_projection_type AGENT.server global_type)
