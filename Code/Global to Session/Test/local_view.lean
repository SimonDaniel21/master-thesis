import Test.type
import Test.location
import Test.expression
import Test.my_logs
import Test.my_utils
import Socket

namespace L

  inductive P where
  | FUNC      : Function -> Array Sorts -> Exp -> P -> P
  | IF        : Exp -> P -> P -> P
  | SEND      : Exp -> Variable -> Location -> P -> P
  | SEND_LBL  : BranchChoice -> Location -> P -> P
  | RECV      : Variable -> Location -> P -> P
  | BRANCH_ON : Location -> P -> P -> P
  | END       : Exp -> P
  | NOOP      : P -> P
  | COMPUTE (v: Variable) (e: Exp) :   P -> P


  inductive T where
  | IF        :  T -> T -> T              -- Internal Choice
  | SEND      :  Location -> T -> T
  | RECV      :  Location -> T -> T
  | SEND_LBL  :  Location -> BranchChoice -> T -> T
  | BRANCH_ON :  Location -> T -> T -> T  -- corresponds to External Choice
  | END       :  T

  def boring_end := P.END (Exp.nexp (NExp.const 0))

  abbrev with_location (a: Type) := ReaderM Location a

  abbrev PM := with_location P
  abbrev TM := with_location T


  inductive eval_error where
  | Exp_error (e: Exp) (err: exp_error): eval_error
  | info (i: String) : eval_error
  | deadlock: eval_error


  abbrev msg := ((Location × Location)  × Variable) × Value
  abbrev lbl_msg := (Location × Location) × BranchChoice

  inductive eval_status where
  | finished  : Value -> eval_status
  | blocking  : eval_status
  | ready     : eval_status
  deriving BEq

  structure eval_state where
    env     : P_state
    loc     : Location
    prog    : P
    status  : eval_status := eval_status.ready

  structure group_eval_state where
    messages: List msg
    l_msgs  : List lbl_msg
    current : eval_state
    progs   : List eval_state
    results : List (located Value)

  --abbrev eval_resM := ExceptT eval_error (StateM state) eval_res

  abbrev trace := List (group_eval_state)
end L

open L
open P

def LOCAL_TO_TYPE: L.P -> L.T
  | IF l opt_1 opt_2 => T.IF (LOCAL_TO_TYPE opt_1) (LOCAL_TO_TYPE opt_2)
  | SEND _e v receiver p => T.SEND receiver (LOCAL_TO_TYPE p)
  | RECV v sender p => T.RECV sender (LOCAL_TO_TYPE p)
  | SEND_LBL val loc p => T.SEND_LBL loc val (LOCAL_TO_TYPE p)
  | BRANCH_ON decider opt_a opt_b => T.BRANCH_ON decider (LOCAL_TO_TYPE opt_a) (LOCAL_TO_TYPE opt_b)
  | COMPUTE _ _ p => (LOCAL_TO_TYPE p)
  | NOOP p => LOCAL_TO_TYPE p
  | END _ => T.END
  | FUNC _ _ _ p => LOCAL_TO_TYPE p


def substitute_end (new_end: L.P):L.P -> L.P
  | IF l opt_a opt_b => IF l (substitute_end new_end opt_a) (substitute_end new_end opt_b)
  | SEND e v receiver p => SEND e v receiver (substitute_end new_end p)
  | RECV v sender p => RECV v sender (substitute_end new_end p)
  | SEND_LBL val loc p => SEND_LBL val loc (substitute_end new_end p)
  | BRANCH_ON decider opt_a opt_b => BRANCH_ON decider  (substitute_end new_end opt_a)  (substitute_end new_end opt_b)
  | COMPUTE v e p => COMPUTE v e (substitute_end new_end p)
  | FUNC n as e p => FUNC n as e (substitute_end new_end p)
  | NOOP p => NOOP (substitute_end new_end p)
  | END _ => new_end


def LP_TO_STRING_single(i: Nat) (p: P): String :=
  let leading_spaces := repeat_string "  " i
  let content: String := match p with
  | IF e opt_a opt_b => "if " ++ toString e ++ "\n" ++ LP_TO_STRING_single (i+1) opt_a ++ "\nelse\n" ++ LP_TO_STRING_single (i+1) opt_b ++ "\n"
  | SEND e v receiver _p =>
    "send " ++ toString e ++ " to " ++ v ++ "@" ++ receiver
  | RECV v sender _p =>
    v ++ " <= " ++  "recv from @" ++ sender
  | SEND_LBL val loc _p => "send_choice " ++ toString val ++ " to @" ++ loc ++ "\n"
  | BRANCH_ON decider opt_a opt_b => "choice@" ++ decider ++ "\n" ++  LP_TO_STRING_single (i+1) opt_a ++ "\n[]\n" ++ LP_TO_STRING_single (i+1) opt_b
  | COMPUTE v e _p => v ++ " <= " ++ (Exp_toString e)
  | FUNC n as e _p => n ++ toString as ++ " := " ++ (Exp_toString e)
  | NOOP _p => ""
  | END res => "return " ++ toString res
  leading_spaces ++ content

def LP_TO_STRING(i: Nat) (p: P): String :=
  let leading_spaces := repeat_string "  " i
  let content: String := match p with
  | IF e opt_a opt_b => "if " ++ toString e ++ "\n" ++ LP_TO_STRING (i+1) opt_a ++ "\nelse\n" ++ LP_TO_STRING (i+1) opt_b ++ "\n"
  | SEND e v receiver p =>
    "send " ++ toString e ++ " to " ++ v ++ "@" ++ receiver ++ "\n" ++ (LP_TO_STRING i p)
  | RECV v sender p =>
    v ++ " <= " ++  "recv from @" ++ sender ++ "\n" ++ (LP_TO_STRING i p)
  | SEND_LBL val loc p => "send_choice " ++ toString val ++ " to @" ++ loc ++ "\n" ++ (LP_TO_STRING i p)
  | BRANCH_ON decider opt_a opt_b => "choice@" ++ decider ++ "\n" ++  LP_TO_STRING (i+1) opt_a ++ "\n[]\n" ++ LP_TO_STRING (i+1) opt_b
  | COMPUTE v e p => v ++ " <= " ++ (Exp_toString e) ++ "\n" ++ (LP_TO_STRING i p)
  | FUNC n as e p => n ++ toString as ++ " := " ++ (Exp_toString e) ++ (LP_TO_STRING i p)
  | NOOP p => LP_TO_STRING i p
  | END res => "return " ++ toString res
  leading_spaces ++ content


def LT_TO_STRING (i: Nat) (t: T): String :=
  let leading_spaces := repeat_string "  " i
  let nl := "\n" ++ leading_spaces
  let content: String := match t with
  | T.IF opt1 opt2 => "⊕" ++ "{" ++ nl ++ LT_TO_STRING (i+1) opt1 ++ nl ++ "[]" ++nl ++ LT_TO_STRING (i+1) opt2 ++ "\n}"
  | T.SEND receiver p =>
    "!(" ++ receiver  ++ ", Nat)." ++ "\n" ++ (LT_TO_STRING i p)
  | T.RECV sender p =>
    "?(" ++ sender ++ ", Nat)." ++ "\n" ++ (LT_TO_STRING i p)
  | T.SEND_LBL receiver b p =>  "!(" ++ receiver ++ ", branch=" ++ toString b ++ ")" ++ "\n" ++ (LT_TO_STRING i p)
  | T.BRANCH_ON loc opt_a opt_b => "choice@" ++ loc ++ "{" ++ nl ++ LT_TO_STRING (i+1) opt_a ++ nl ++ "[]" ++ nl ++ LT_TO_STRING (i+1) opt_b ++ "\n}"
  | T.END => "end"
  leading_spaces ++ content

instance: ToString L.P where
  toString := LP_TO_STRING 0

instance: ToString L.T where
  toString := LT_TO_STRING 0

instance: ToString L.eval_status where
  toString := fun x => match x with
  | eval_status.finished r  => "finished (" ++ toString r ++ ")"
  | eval_status.blocking    => "blocking"
  | eval_status.ready       => "ready"

instance: ToString L.eval_error where
  toString := fun x => match x with
    | eval_error.Exp_error e err => "Exp error + " ++ toString e ++ " -> " ++ toString err
    | eval_error.info s => "Error: " ++ s
    | eval_error.deadlock => "Deadlock"

instance: ToString L.eval_state where
  toString := fun x =>
    x.loc ++ "(" ++ toString x.status ++ "):\n" ++ toString x.env

instance: ToString L.group_eval_state where
  toString := fun x =>
    let other_progs := (x.progs.map (fun y => toString y.prog))
    let state_strings := list_to_string_seperated_by (x.progs.map (fun x => toString x))  "\n  "
   "branch_messages:\n  " ++ toString x.l_msgs ++ "\nmessages:\n  " ++ toString x.messages ++ "\nstates:\n  " ++ toString x.current ++ "\n  " ++ state_strings ++ "\nprogram@" ++ x.current.loc ++ ":\n " ++ LP_TO_STRING_single 0 x.current.prog ++ "\n" ++toString other_progs

instance: ToString trace where
  toString := fun x => list_to_string_seperated_by (x.map (fun y => toString y)) "\n--------------------------------\n"

instance: ToString (Except eval_error eval_status × group_eval_state) where
  toString := fun x => match x.fst with
    | Except.ok res =>  toString x.snd ++ "result: " ++ toString res
    | Except.error e => toString x.snd ++ "error:" ++ toString e


-- swaps the current eval_state with an eval_state that is "ready". returns none if there are none
def swap_running_program (s: group_eval_state): Option group_eval_state :=
  let canidates := s.progs.filter (fun x => x.status == eval_status.ready)
  match canidates with
  | [] => Option.none
  | nc::_ =>
    let without_new := s.progs.filter (fun x => x.loc != nc.loc)
    let new_others := without_new.cons s.current
    Option.some {s with current := nc, progs := new_others}

-- sets the current eval_status to blocking and tries to swap
def block_current (s: group_eval_state): Option group_eval_state :=
  swap_running_program {s with current := {s.current with status := eval_status.blocking}}

-- sets the current eval_status to finish with res and tries to swap
def finish_current (s: group_eval_state) (res: Value): Option group_eval_state :=
  swap_running_program {s with current := {s.current with status := eval_status.finished res}}

--
def activate (s: group_eval_state): group_eval_state :=
  let active_progs := s.progs.map (fun x => {x with status :=
    match x.status with
    | eval_status.finished r =>  eval_status.finished r
    | eval_status.blocking => eval_status.ready
    | x => x
    })
  {s with progs := active_progs}

def send_to_all (locs: List Location) (b: BranchChoice) (p: L.P): L.P :=
  match locs with
  | [] => L.P.NOOP p
  | x::xs => L.P.SEND_LBL b x (send_to_all xs b p)

partial def eval_local (s: group_eval_state): ExceptT eval_error (StateM trace) (List (located Value)) := do
  set ((<-get) ++ [s])

  let running_program := s.current.prog
  dbg_trace toString running_program ++ "\n"
  let c_env := s.current.env

  match running_program with
  | NOOP p => eval_local {s with current := {s.current with prog := p}}
  | IF e opt_a opt_b =>

    let evaluation := eval_exp e c_env
      match evaluation with
      | .ok r =>
        let broadcast_msgs: List lbl_msg := s.progs.map (fun x => ((s.current.loc, x.loc), if r == (Value.bool true) then BranchChoice.fst else BranchChoice.snd))
        let new_state: group_eval_state := activate { s with l_msgs := s.l_msgs ++ broadcast_msgs, current := {s.current with prog := if r == (Value.bool true) then opt_a else opt_b},}
        eval_local new_state
      | .error err => throw (eval_error.Exp_error e err)

  | SEND e v receiver p => do

    let evaluation := eval_exp e c_env
    match evaluation with
    | .ok r =>
      let new_message: msg := (((s.current.loc, receiver), v), r)
      let new_state := { s with messages := s.messages.cons new_message, current := {s.current with prog := p}}
      eval_local (activate new_state)
    | .error err => throw (eval_error.Exp_error e err)

  | RECV v_name sender p => do
    let awaited_msg: (Location×Location) × Variable  := ((sender, s.current.loc), v_name)
    let v_opt := s.messages.lookup awaited_msg
    match v_opt with
    | Option.some v =>
      let new_var_map: List (Variable × Value) := (c_env.var_map).concat (v_name, v)
      let new_env: P_state := (new_var_map, (c_env.funcs))
      let new_state := { s with current := {s.current with env := new_env, prog := p}, messages:= s.messages.erase (awaited_msg, v) }
      eval_local new_state
    | Option.none =>
      let swap_state_opt := block_current s
      match swap_state_opt with
      | Option.some swap_state =>
        eval_local swap_state
      | Option.none =>
        throw eval_error.deadlock
  | COMPUTE v e p => do
    let evaluation := eval_exp e c_env
    match evaluation with
    | .ok r =>
      let new_var_map: List (Variable × Value) := (c_env.var_map).concat (v, r)
      let new_env: P_state := (new_var_map, (c_env.funcs))
      let new_state := { s with current := {s.current with env := new_env, prog := p} }
      eval_local new_state
    | .error err => throw (eval_error.Exp_error e err)
  | FUNC n as e p => do
    let new_state := { s with current := {s.current with prog := p} }
    eval_local new_state

  | END res_Exp =>

    let evaluation := eval_exp res_Exp s.current.env
    match evaluation with
    | .ok r =>
      let located_res := (r, s.current.loc)
      let s := {s with results := s.results.concat located_res}
      let swap_state_opt := finish_current s r
      match swap_state_opt with
      | Option.some swap_state =>
        eval_local swap_state
      | Option.none => return s.results
    | .error err => throw (eval_error.Exp_error res_Exp err)

  | SEND_LBL val loc p => do
    let new_message: lbl_msg := (((s.current.loc, loc)), val)
    let new_state := { s with l_msgs := s.l_msgs.cons new_message, current := {s.current with prog := p}}
    eval_local new_state
  | BRANCH_ON decider opt_a opt_b =>
    let v_opt := s.l_msgs.lookup (decider, s.current.loc)
    match v_opt with
    | Option.some b =>
      let new_state:=
        if b == BranchChoice.fst then
        { s with current := {s.current with prog := opt_a}}
        else
        { s with current := {s.current with prog := opt_b}}
      eval_local new_state

    | Option.none =>
      let swap_state_opt := block_current s
      match swap_state_opt with
      | Option.some swap_state =>
        eval_local swap_state
      | Option.none =>
        throw eval_error.deadlock


def lp_1_sending: P := P.SEND (Exp.nexp (NExp.var "var1")) "var1" "server" (boring_end)



def lp_2_receiving: P := P.RECV "var1" "client"
  (P.END (Exp.nexp (NExp.var "var1")))

def l_env_1: P_state := ([("var1", Value.nat 101)], [])

def lstate_1_send: eval_state := { loc := "client", env := l_env_1, prog:= lp_1_sending }
def lstate_1_receive: eval_state := { loc := "server", env := empty_P_state, prog:= lp_2_receiving }


def temp_prg: L.P := L.P.SEND (Exp.nexp (NExp.const 3)) "sa" "anywhere" (L.P.END (Exp.nexp (NExp.const 3)))
def lstate_3_test: eval_state := { loc := "client", env := l_env_1, prog:= temp_prg}

def state_of (starter: eval_state) (others: List eval_state): group_eval_state :={
  results:= []
  messages:= [],
  l_msgs:=   [],
  progs   := others
  current := starter
}

def state_1_send_then_receive: group_eval_state :=
  state_of lstate_1_receive [(lstate_1_send)]


def state_2_only_receive: group_eval_state :=
  state_of lstate_1_receive []

def state_3_only_send: group_eval_state :=
  state_of lstate_1_send []

def test_state : group_eval_state := state_of lstate_3_test []

#eval (lp_1_sending)
#eval (lp_2_receiving)


#eval (LOCAL_TO_TYPE lp_1_sending)
#eval (eval_local state_1_send_then_receive [])

#eval (LOCAL_TO_TYPE lp_2_receiving)
#eval (eval_local state_2_only_receive [])

#eval (eval_local state_3_only_send [])

#eval (eval_local test_state [])
