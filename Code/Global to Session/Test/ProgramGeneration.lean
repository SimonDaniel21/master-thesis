import Test.local_view
import Socket

open L
open P

def local_addr (num: UInt16): Socket.SockAddr4 := .v4 (.mk 127 0 0 1) (4599 + num)

def phys_addr (loc: Location) (physical_mapping: List (Location × Socket.SockAddr4 )): Socket.SockAddr4 :=
  let phys_opt := physical_mapping.lookup loc
  match phys_opt with
  | Option.some phys => phys
  | Option.none => .v4 (.mk 127 0 0 1) 0



def init_local_program (addr: Socket.SockAddr4): String :=
 "let sock ← Socket.mk .inet .stream
  let local_addr: Socket.SockAddr4 := .v4 (.mk " ++ (addr.addr.replace "." " ") ++") " ++ (toString addr.port) ++ "
  sock.connect local_addr"

inductive synthesis_error where
| missing_mapping: Location -> synthesis_error

def LP_TO_Lean_Program (p: P) (loc: Location) (physical_mapping: List (Location × Socket.SockAddr4 )): Except synthesis_error String :=
  do
  let function_prefix := "def " ++ (loc.replace " " "_") ++ ": IO Nat := do\n"
  let local_addr_opt := physical_mapping.lookup loc
  match local_addr_opt with
  | some local_addr =>
    let function_prefix := function_prefix ++ (init_local_program local_addr)

    let recursion (i: Nat) (p: P): String :=
      let leading_spaces := repeat_string "  " i
      let content: String := match p with
      | IF e opt_a opt_b => "if " ++ toString e ++ "\n" ++ LP_TO_STRING (i+1) opt_a ++ "\nelse\n" ++ LP_TO_STRING (i+1) opt_b ++ "\n"
      | SEND e v receiver p =>
        "send " ++ toString e ++ " to " ++ v ++ "@" ++ receiver ++ "\n" ++ (LP_TO_STRING i p)
      | RECV v sender p =>
        v ++ " <= " ++  "recv from @" ++ sender ++ "\n" ++ (LP_TO_STRING i p)
      | SEND_LBL val loc p => "send_choice " ++ toString val ++ " to @" ++ loc ++ "\n" ++ (LP_TO_STRING i p)
      | BRANCH_ON decider opt_a opt_b => "choice@" ++ decider ++ "\n" ++  LP_TO_STRING (i+1) opt_a ++ "\n[]\n" ++ LP_TO_STRING (i+1) opt_b
      | COMPUTE v e p => v ++ " <= " ++ (Exp_TO_STRING e) ++ "\n" ++ (LP_TO_STRING i p)
      | NOOP p => LP_TO_STRING i p
      | END res => "RETURN " ++ toString res
      leading_spaces ++ content

    return function_prefix ++ (recursion 2 p)
  | none => throw (synthesis_error.missing_mapping loc)


instance: ToString synthesis_error where
  toString := fun x =>
    match x with
    | synthesis_error.missing_mapping l => "missing location [" ++ "] in mapping"

instance (loc: Location) (physical_mapping: List (Location × Socket.SockAddr4 )): ToString L.P where
  toString := fun x =>
    match LP_TO_Lean_Program x loc physical_mapping with
    | .ok s => s
    | .error e => toString e

#eval LP_TO_Lean_Program lp_1_sending "client" [("client", local_addr 0)]
#eval (LP_TO_Lean_Program lp_2_receiving "server" [])
