import Test.local_view
import Socket

open L
open P

def Loc (s: String) := Type

def Lc: String -> Type -> Type := fun _ x => x
#check Lc "Server"

def print_server (v: Lc "Server" String) := "34"
def hmmm := print_server
#check hmmm
def testfunc : IO Unit := do
  let b: Lc "client" String := "2"
  let a := print_server b
  return ()

def local_addr (num: UInt16): Socket.SockAddr4 := .v4 (.mk 127 0 0 1) (4599 + num)

def phys_addr (loc: Location) (physical_mapping: List (Location × Socket.SockAddr4 )): Socket.SockAddr4 :=
  let phys_opt := physical_mapping.lookup loc
  match phys_opt with
  | Option.some phys => phys
  | Option.none => .v4 (.mk 127 0 0 1) 0

def Socket.SockAddr4.toLeanString (addr: Socket.SockAddr4): String :=
  "(.v4 (.mk " ++ (addr.addr.replace "." " ") ++") " ++ (toString addr.port) ++ ")"

def init_local_program (addr: Socket.SockAddr4): String :=
 "let sock ← Socket.mk .inet .stream
  let local_addr: Socket.SockAddr4 := .v4 (.mk " ++ (addr.addr.replace "." " ") ++") " ++ (toString addr.port) ++ "
  sock.connect local_addr\n"

inductive synthesis_error where
| missing_mapping: Location -> synthesis_error




def generate_start_options_inner:  List Location -> String
| a::as => "else if mode == \"" ++ a ++ "\" then\n" ++ a ++ "\n" ++ generate_start_options_inner as
| [] => "else\nIO.println \"Unknown Location\"\nreturn ()"

def generate_start_options: List Location -> String
| a::as => "if mode == \"" ++ a ++ "\" then\n" ++ a ++ "\n" ++ generate_start_options_inner as
| [] => "IO.println \"no Location, exiting program\"\nreturn ()"


def addr_of: Location -> List (Location × Socket.SockAddr4) -> Except synthesis_error Socket.SockAddr4
| loc, mapping => match mapping.lookup loc with
  | some addr => return addr
  | none => throw (synthesis_error.missing_mapping loc)

-- def LP_TO_Lean_Program_new (prog: located P) (mapping: List (Location × Socket.SockAddr4)): Except synthesis_error (IO Unit) :=
--   let local_addr_opt := mapping.lookup prog.loc
--    match local_addr_opt with
--   | some local_addr =>
--      match prog.val with
--     | IF e opt_a opt_b  => return (IO.println "if")
--     | SEND e v receiver p => do
--       let recv_addr <- addr_of receiver mapping
--       recv_addr.send 2
--     | RECV v sender p => return (IO.println "recv")
--     | SEND_LBL val loc p => return (IO.println "sendlbl")
--     | BRANCH_ON decider opt_a opt_b => return (IO.println "branchon")
--     | COMPUTE v e p => return (IO.println "locally")
--     | NOOP p => return (IO.println "noop")
--     | END res => return (IO.println "done")
--     | FUNC n as e p => return (IO.println "ff")
--   | none => throw (synthesis_error.missing_mapping prog.loc)



def LP_TO_Lean_Program (p: located P) (physical_mapping: List (Location × Socket.SockAddr4 )): Except synthesis_error String :=
  do
  let function_prefix := "def " ++ p.loc ++ ": IO Nat := do\n"
  let local_addr_opt := physical_mapping.lookup p.loc
  match local_addr_opt with
  | some local_addr =>
    --let function_prefix := function_prefix ++ (init_local_program local_addr)

    let recursion (i: Nat) (p: located P): Except synthesis_error String :=
      let leading_spaces := repeat_string "  " i
      let content: Except synthesis_error String := match p.val with
      | IF e opt_a opt_b => return "if " ++ toString e ++ "\n" ++ LP_TO_STRING (i+1) opt_a ++ "\nelse\n" ++ LP_TO_STRING (i+1) opt_b ++ "\n"
      | SEND e v receiver p =>
        let rs_opt := physical_mapping.lookup receiver
        match rs_opt with
        | some rs =>
          return "send " ++ rs.toLeanString ++ " (Value.string \"content\")\n" ++ (LP_TO_STRING i p)
        | none => throw (synthesis_error.missing_mapping receiver)
      | RECV v sender p =>
        let ss_opt := physical_mapping.lookup sender
        match ss_opt with
        | some ss =>
          return "let " ++ v ++ " <- receive " ++ ss.toLeanString ++ "\n" ++ (LP_TO_STRING i p)
        | none => throw (synthesis_error.missing_mapping sender)
      | SEND_LBL val loc p => return "send_choice " ++ toString val ++ " to @" ++ loc ++ "\n" ++ (LP_TO_STRING i p)
      | BRANCH_ON decider opt_a opt_b => return "choice@" ++ decider ++ "\n" ++  LP_TO_STRING (i+1) opt_a ++ "\n[]\n" ++ LP_TO_STRING (i+1) opt_b
      | COMPUTE v e p => return  v ++ " <= " ++ (toString e) ++ "\n" ++ (LP_TO_STRING i p)
      | NOOP p => return  LP_TO_STRING i p
      | END res =>return  "RETURN " ++ toString res
      | FUNC n as e p =>return  "" ++ (LP_TO_STRING i p)
      return leading_spaces ++ (<- content)

    return function_prefix ++ (<-(recursion 2 p))
  | none => throw (synthesis_error.missing_mapping p.loc)

def LPS_TO_Lean_Program (ps: List (located P)) (physical_mapping: List (Location × Socket.SockAddr4 )): Except synthesis_error String :=
  do
  let main_func := "def main (args : List String): IO Nat := do\nlet mode := args.get! 0\n" ++ generate_start_options (physical_mapping.map (fun x => x.fst))
  match ps with
  | a::as =>
    let current <- LP_TO_Lean_Program a physical_mapping
    let cont <- LPS_TO_Lean_Program as physical_mapping
    return current ++ "\n" ++ cont
  | [] => return main_func

inductive funky: Type -> Type where
| func1 Nat: funky String

def func1: Type := fun (x:Nat) (y:Nat) => x+y
def func2:= fun (s:String) => toString s

def func3: Nat
| 1 => func1
| _ => func2


def TYPE_TO_Lean_Program (p: L.P) (loc: Location) (physical_mapping: List (Location × Socket.SockAddr4 )): Except synthesis_error String :=
  do
  let local_addr_opt := physical_mapping.lookup loc

  match local_addr_opt with
  | some local_addr =>
    --let function_prefix := function_prefix ++ (init_local_program local_addr)

    let recursion (i: Nat) (p: L.T): Except synthesis_error String :=
      let leading_spaces := repeat_string "  " i
      let content: Except synthesis_error String := match p with
      | IF opt_a opt_b => "broadcast [choice]\n"
      | SEND loc n => "send"
      | RECV      :  Location -> T -> T
      | SEND_LBL  :  Location -> BranchChoice -> T -> T
      | BRANCH_ON :  Location -> T -> T -> T  -- corresponds to External Choice
      | END       :  T
      return leading_spaces ++ (<- content)

    return function_prefix ++ (<-(recursion 2 p))
  | none => throw (synthesis_error.missing_mapping loc)



def TO_Lean_Program (p: P) (loc: Location) (physical_mapping: List (Location × Socket.SockAddr4 )): Except synthesis_error String :=
  do
  let function_prefix := "def " ++ (loc.replace " " "_") ++ ": IO Nat := do\n"
  let local_addr_opt := physical_mapping.lookup loc

  match local_addr_opt with
  | some local_addr =>
    --let function_prefix := function_prefix ++ (init_local_program local_addr)

    let recursion (i: Nat) (p: P): Except synthesis_error String :=
      let leading_spaces := repeat_string "  " i
      let content: Except synthesis_error String := match p with
      | IF e opt_a opt_b => return "if " ++ toString e ++ "\n" ++ LP_TO_STRING (i+1) opt_a ++ "\nelse\n" ++ LP_TO_STRING (i+1) opt_b ++ "\n"
      | SEND e v receiver p =>
        let rs_opt := physical_mapping.lookup receiver
        match rs_opt with
        | some rs =>
          return "send " ++ rs.toLeanString ++ " (Value.string \"content\")\n" ++ (LP_TO_STRING i p)
        | none => throw (synthesis_error.missing_mapping receiver)
      | RECV v sender p =>
        let ss_opt := physical_mapping.lookup sender
        match ss_opt with
        | some ss =>
          return "let " ++ v ++ " <- receive " ++ ss.toLeanString ++ "\n" ++ (LP_TO_STRING i p)
        | none => throw (synthesis_error.missing_mapping sender)
      | SEND_LBL val loc p => return "send_choice " ++ toString val ++ " to @" ++ loc ++ "\n" ++ (LP_TO_STRING i p)
      | BRANCH_ON decider opt_a opt_b => return "choice@" ++ decider ++ "\n" ++  LP_TO_STRING (i+1) opt_a ++ "\n[]\n" ++ LP_TO_STRING (i+1) opt_b
      | COMPUTE v e p => return  v ++ " <= " ++ (toString e) ++ "\n" ++ (LP_TO_STRING i p)
      | NOOP p => return  LP_TO_STRING i p
      | END res =>return  "RETURN " ++ toString res
      | FUNC n as e p =>return  "" ++ (LP_TO_STRING i p)
      return leading_spaces ++ (<- content)

    return function_prefix ++ (<-(recursion 2 p))
  | none => throw (synthesis_error.missing_mapping loc)

instance: ToString synthesis_error where
  toString := fun x =>
    match x with
    | synthesis_error.missing_mapping l => "missing location [" ++ "] in mapping"

-- instance (loc: Location) (physical_mapping: List (Location × Socket.SockAddr4 )): ToString L.P where
--   toString := fun x =>
--     match LP_TO_Lean_Program x loc physical_mapping with
--     | .ok s => s
--     | .error e => toString e

#eval lp_1_sending
#eval lp_2_receiving

def physmap := [("client", local_addr 0), ("server", local_addr 1)]

#eval (generate_start_options (physmap.map (fun x => x.fst)))
#eval LP_TO_Lean_Program (lp_1_sending, "client") physmap
#eval (LP_TO_Lean_Program (lp_2_receiving, "server") physmap)


#eval (LPS_TO_Lean_Program  [(lp_2_receiving, "server"), (lp_1_sending, "client")] physmap)

def test_array2: Array Nat := #[1]



def main (args : List String): IO (UInt32) := do

  IO.println "run main"
  -- match (LP_TO_Lean_Program_new (lp_1_sending, "bbb") physmap) with
  -- | .ok v => v
  -- | .error e => IO.println e

  return 0
