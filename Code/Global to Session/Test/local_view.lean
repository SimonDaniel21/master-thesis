import Test.type
import Test.location
import Test.expression
import Test.my_logs
import Test.my_utils

namespace L

  inductive P where
    | IF        : Variable -> Exp -> P -> P -> P -> P
    | SEND      : Exp -> Variable -> Location -> P -> P
    | RECV      : Variable -> Location -> P -> P
    | END       : Option Exp -> P
    | NOOP      : P -> P
    | COMPUTE (v: Variable) (e: Exp) :   P -> P

  inductive T where
    | IF      :  Variable -> T -> T -> T -> T
    | SEND    :  Variable -> Location -> T -> T
    | RECV    :  Variable -> Location -> T -> T
    | END     :  T

  inductive eval_error where
    | Exp_error (e: Exp_RESULT Nat): eval_error
    | unknown_message_var (name: Variable) : eval_error
    | deadlock: eval_error


  abbrev msg := ((Location × Location)  × Variable) × Nat

  ---abbrev eval_res := ExceptT eval_error (StateT env (OptionT (with_logs String))) (Nat × (List msg))


  inductive eval_res where
  | finished  : Option Nat -> eval_res
  | waiting   : eval_res

  structure local_state where
    env     : P_state
    loc     : Location
    prog    : P
    ready   : Bool  := true

  structure state where
    messages: List msg
    current : local_state
    progs   : List (Location × local_state)

  abbrev eval_resM := ExceptT eval_error (StateM state) eval_res

end L

open L
section PROGRAM
open P



def LP_status_string (b: Bool) := if b then "ready" else "blocking"

def LOCAL_TO_TYPE: P -> T
  | IF v _ opt_1 opt_2 p => T.IF v (LOCAL_TO_TYPE opt_1) (LOCAL_TO_TYPE opt_2) (LOCAL_TO_TYPE p)
  | SEND _e v receiver p => T.SEND v receiver (LOCAL_TO_TYPE p)
  | RECV v sender p => T.RECV v sender (LOCAL_TO_TYPE p)
  | COMPUTE _ _ p => (LOCAL_TO_TYPE p)
  | NOOP p => LOCAL_TO_TYPE p
  | END _ => T.END


def substitute_end (new_end: L.P):L.P -> L.P
  | IF v l opt_1 opt_2 p => IF v l opt_1 opt_2 (substitute_end new_end p)
  | SEND e v receiver p => SEND e v receiver (substitute_end new_end p)
  | RECV v sender p => RECV v sender (substitute_end new_end p)
  | COMPUTE v e p => COMPUTE v e (substitute_end new_end p)
  | NOOP p => NOOP (substitute_end new_end p)
  | END _ => new_end



def LP_TO_STRING(i: Nat) (p: P): String :=
  let leading_spaces := repeat_string "  " i
  let content: String := match p with
  | IF v e opt_a opt_b p => v ++ " <= if " ++ toString e ++ "\n" ++ LP_TO_STRING (i+1) opt_a ++ "\nelse\n" ++ LP_TO_STRING (i+1) opt_b ++ "\nend if\n" ++ LP_TO_STRING (i) p
  | SEND e v receiver p =>
    v ++ "@" ++ receiver ++ " <= " ++ toString e ++  "@" ++ "local" ++ "\n" ++ (LP_TO_STRING i p)
  | RECV v sender p =>
    v ++ "@" ++ "local" ++ " <= " ++ v ++  "@" ++ sender ++ "\n" ++ (LP_TO_STRING i p)
  | COMPUTE v e p => v ++ " <= " ++ (Exp_TO_STRING e) ++ "\n" ++ (LP_TO_STRING i p)
  | NOOP p => LP_TO_STRING i p
  | END res => "RETURN " ++ toString res
  leading_spaces ++ content

def LT_TO_STRING: T -> String
  | T.IF v opt1 opt2 p => "[]"
  | T.SEND v receiver p =>
    "!(" ++ receiver ++ ", " ++ v ++ ")" ++ "\n" ++ (LT_TO_STRING p)
  | T.RECV v sender p =>
    "?(" ++ sender ++ ", " ++ v ++ ")" ++ "\n" ++ (LT_TO_STRING p)
  | T.END => "END"

instance: ToString L.P where
  toString := LP_TO_STRING 0

instance: ToString L.T where
  toString := LT_TO_STRING

instance: ToString L.eval_res where
  toString := fun x => match x with
    | eval_res.finished r => toString r
    | eval_res.waiting => "waiting..."

instance: ToString L.eval_error where
  toString := fun x => match x with
    | eval_error.Exp_error e => "Exp error + " ++ toString e
    | eval_error.unknown_message_var v => "unknown message var: " ++ v
    | eval_error.deadlock => "Deadlock"

instance: ToString L.local_state where
  toString := fun x =>
    x.loc ++ "(" ++ LP_status_string x.ready ++ "):\n" ++ toString x.env

instance: ToString L.state where
  toString := fun x =>
    let state_strings := list_to_string_seperated_by (x.progs.map (fun x => toString x.snd))  "\n"
   "messages:\n" ++ toString x.messages ++ "\nrunning:\n" ++ toString x.current ++ "\nothers:\n" ++ state_strings

instance: ToString (Except eval_error eval_res × state) where
  toString := fun x => match x.fst with
    | Except.ok res =>  toString x.snd ++ "result: " ++ toString res
    | Except.error e => toString x.snd ++ "error:" ++ toString e



def swap_running_program (s: state): Option state :=
  let canidates := s.progs.filter (fun x => x.snd.ready)
  match canidates with
  | [] => Option.none
  | nc::_ =>
    let without_new := s.progs.filter (fun x => x.fst != nc.fst)
    let new_others := without_new.cons (s.current.loc, {s.current with ready := false})

    Option.some {s with current := nc.snd, progs := new_others}

def normal_recursive (x: Nat) :=
  match x with
  | 0 => 0
  | n+1 => normal_recursive n
/-
def monad_recursion: StateM Nat Nat :=
  do
  let state <- get
  match state with
  | 0 => return 0
  | n+1 =>
    set (state-1)
    monad_recursion
-/

/--
def eval_local: eval_resM := do
  let state <- get
  let running_program := state.current.prog
  let c_env := state.current.env

  match running_program with
  | IF v e opt_a opt_b p =>

    let evaluation := eval_Exp c_env e
      match evaluation with
      | Exp_RESULT.some r =>
        let new_var_map: List (Variable × Nat) := (var_map c_env).concat (v, r)
        let new_env: P_state := (new_var_map, (funcs c_env))
        set { state with current := {state.current with env := new_env, prog := p} }
        eval_local
      | x => throw (eval_error.Exp_error x)

  | SEND v receiver p => do
    let var_opt := (var_map c_env).lookup v
    match var_opt with
    | Option.some var =>
      let new_message: msg := (((state.current.loc, receiver), v), var)
      set { state with messages := state.messages.cons new_message, current := {state.current with prog := p}}
      eval_local
    | Option.none => throw (eval_error.unknown_message_var v)

  | RECV v_name sender p => do
    let v_opt := state.messages.lookup ((sender, state.current.loc), v_name)
    match v_opt with
    | Option.some v =>
      let new_var_map: List (Variable × Nat) := (var_map c_env).concat (v_name, v)
      let new_env: P_state := (new_var_map, (funcs c_env))
      set { state with current := {state.current with env := new_env, prog := p} }
      eval_local
    | Option.none => return eval_res.waiting

  | COMPUTE v e p => do
    let evaluation := eval_Exp c_env e
    match evaluation with
    | Exp_RESULT.some r =>
      let new_var_map: List (Variable × Nat) := (var_map c_env).concat (v, r)
      let new_env: P_state := (new_var_map, (funcs c_env))
      set { state with current := {state.current with env := new_env, prog := p} }
      eval_local
    | x => throw (eval_error.Exp_error x)

  | END res_Exp_opt =>
    match res_Exp_opt with
    | Option.some res_Exp => do
      let state <- get
      let evaluation := eval_Exp state.current.env res_Exp
      match evaluation with
      | Exp_RESULT.some r =>
        return eval_res.finished r
      | x => throw (eval_error.Exp_error x)
    | Option.none => do
      let state <- get
      let swap_state_opt := swap_running_program state
      match swap_state_opt with
      | Option.some swap_state =>
        set swap_state
        eval_local
      | Option.none => throw eval_error.deadlock
 --/

def lp_1_sending: P := P.SEND (Exp.VAR "var1") "var1" "server" (P.END Option.none)
def lp_2_receiving: P := P.RECV "var1" "client"
  (P.END (Option.some (Exp.VAR "var1")))

def l_env_1: P_state := ([("var1", 101)], [])

def lstate_1_send: local_state := { loc := "client", env := l_env_1, prog:= lp_1_sending }
def lstate_1_receive: local_state := { loc := "server", env := empty_P_state, prog:= lp_2_receiving }


def state_1_send_then_receive: state := {
  messages:= [],
  progs   := [("server", lstate_1_receive)],
  current := lstate_1_send
}

def state_2_only_receive: state := {
  messages:= [],
  progs   := [("server", lstate_1_receive)],
  current := lstate_1_send
}

#eval (lp_1_sending)
#eval (LOCAL_TO_TYPE lp_1_sending)
--#eval (eval_local lp_1_sending state_1_send_then_receive)

#eval (lp_2_receiving)
#eval (LOCAL_TO_TYPE lp_2_receiving)
--#eval (eval_local lp_2_receiving state_2_receiving)
