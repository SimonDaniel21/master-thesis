import Test.type
import Test.expression
import Lean
import Test.my_utils
import Test.my_logs
import Test.local_view


namespace G

  open Lean

  inductive P where
    | IF : Exp -> Location -> Variable -> Location -> P -> P -> P -> P
    | SEND_RECV    : Exp -> Location -> Variable -> Location -> P -> P
    | COMPUTE (v: Variable) (e: Exp) (a: Location) :   P -> P
    | END     :  Location -> Exp -> P

  inductive T where
    | IF : Location -> T -> T -> T -> T
    | SEND_RECV    :  Location -> Location -> T -> T
    | END     :   T

  inductive Eval_error where
  | unknown_Location (a: Location) : Eval_error
  | Exp_error (e: Exp_RESULT Nat): Eval_error
  | unknown_message_var (name: Variable) : Eval_error

  def Env := HashMap Location P_state

  abbrev Eval_res := ExceptT Eval_error (StateT Env (with_logs String)) Nat
end G

open G
open P


def GLOBAL_TO_TYPE: P -> T
  | IF _e el _v _vl opt_a opt_b p => T.IF el (GLOBAL_TO_TYPE opt_a) (GLOBAL_TO_TYPE opt_b) (GLOBAL_TO_TYPE p)
  | SEND_RECV _e sender _v receiver p => T.SEND_RECV sender receiver (GLOBAL_TO_TYPE p)
  | COMPUTE _ _ _ p => (GLOBAL_TO_TYPE p)
  | END _ _ => T.END


-- i for indents
def GP_TO_STRING (i: Nat) (p: P):  String :=
  let leading_spaces := repeat_string "  " i
  let content: String := match p with
  | IF e el v vl opt_a opt_b p => v ++ "@" ++ vl ++ " <= if " ++ toString e ++ "@" ++ el ++ "\n" ++
    GP_TO_STRING  (i + 1) opt_a ++ "\nelse\n" ++ GP_TO_STRING (i + 1) opt_b ++ "\nend if\n" ++ GP_TO_STRING i p
  | SEND_RECV e sender v receiver p =>
    v ++ "@" ++ receiver ++ " <= " ++ toString e ++  "@" ++ sender ++ "\n" ++ (GP_TO_STRING i p)
  | END l result => toString result ++ "@" ++ l
  | COMPUTE v e l p => v ++  "@" ++ l ++ " <= " ++ (Exp_TO_STRING e) ++ " @" ++ l ++ "\n" ++ (GP_TO_STRING i p)
  leading_spaces ++ content

def GT_TO_STRING (i: Nat) (t: T): String :=
  let leading_spaces := repeat_string "  " i
  let content: String := match t with
  | T.IF _ t1 t2 p => "[]\n" ++ GT_TO_STRING (i+1) t1 ++ "\n[]\n" ++ GT_TO_STRING (i+1) t2 ++ "\n" ++ GT_TO_STRING i p
  | T.SEND_RECV sender receiver p =>
    sender ++ " --> " ++  receiver ++  ": Nat.\n" ++ (GT_TO_STRING i p)
  | T.END => "end"
  leading_spaces ++ content


open Eval_error

instance: ToString G.P where
  toString := GP_TO_STRING 0

instance: ToString G.T where
  toString := GT_TO_STRING 0

instance: ToString G.Env where
  toString (e: Env) := list_to_continuos_string ((e.toList.map (fun x => "@" ++ x.fst ++ "\n  " ++ toString x.snd)).intersperse "\n")


instance: ToString G.Eval_error where
  toString := fun x => match x with
  | Eval_error.unknown_Location a => "unknown Location " ++ a ++ " introduced"
  | Eval_error.Exp_error e => "Exp Error:\n" ++ toString e
  | Eval_error.unknown_message_var v => "unknown message Variable: " ++ v


-- inductive global_evaluation_result_old (x: Type) where
--   | state (Env: global_P_state) (logs: List global_P_state) (result: x): global_evaluation_result_old x
--   | unknown_Location (a: Location) (logs: List global_P_state) : global_evaluation_result_old x
--   | Exp_error (e: Exp_RESULT Nat) (logs: List global_P_state): global_evaluation_result_old x
--   | unknown_message_var (name: Variable) (logs: List global_P_state): global_evaluation_result_old x

instance: ToString (with_logs String (Except Eval_error Nat × Env)) where
  toString := fun eval =>
    let (res_e, e) := eval.value
    let result_string: String := match res_e with
    | Except.error e => "error:\n" ++ toString e
    | Except.ok res => "res:\n" ++ toString res
    "logs:\n" ++ list_to_string_seperated_by eval.logs "\n---------------------\n" ++ "Env:\n" ++ toString e ++ "\n" ++ result_string

def add  (b: Nat) (a: Nat := 2): Nat :=
  a + b

#eval (add 3 3)

def eval_global: P -> Eval_res
  | SEND_RECV e sender v receiver p =>
    do
    let state <- get
    append [toString state]
    append ["send_recv"]
    let sender_state_opt := state.find? sender
    let receiver_state_opt := state.find? receiver

    match sender_state_opt with
    | Option.some sender_state =>
      match receiver_state_opt with
      | Option.some receiver_state =>
        let Exp_result := eval_Exp sender_state e
        match Exp_result with
        | Exp_RESULT.some r =>
          let new_var_map: List (Variable × Nat) := (var_map receiver_state).concat (v, r)
          let new_state: Env := (state.insert receiver (new_var_map, (funcs receiver_state)))
          set new_state
          eval_global p
        | x => throw (Eval_error.Exp_error x)
      | Option.none => throw (Eval_error.unknown_Location receiver)
    | Option.none => throw (Eval_error.unknown_Location sender)
   | COMPUTE v e a p =>
    do
      let state <- get
      append [toString state]
      append ["Compute"]
      let local_state_opt := state.find? a
      match local_state_opt with
      | Option.some local_state =>
        let evaluation := eval_Exp local_state e
        match evaluation with
        | Exp_RESULT.some r =>
          let new_var_map: List (Variable × Nat) := (var_map local_state).concat (v, r)
          let new_state: Env := (state.insert a (new_var_map, (funcs local_state)))
          set new_state
          eval_global p
        | x => throw (Eval_error.Exp_error x)

      | Option.none => throw (Eval_error.unknown_Location a)
  | IF e el v vl opt_a opt_b p =>
    do
    let state <- get
    append [toString state]
    append ["IF"]
    let expr_state_opt := state.find? el
    let var_state_opt := state.find? vl
    match expr_state_opt with
    | Option.some local_state =>
      match var_state_opt with
      | Option.some var_state =>
        let Exp_result := eval_Exp local_state e
        match Exp_result with
        | Exp_RESULT.some r =>
          let new_var_map: List (Variable × Nat) := (var_map var_state).concat (v, r)
          let new_state: Env := (state.insert vl (new_var_map, (funcs var_state)))
          set new_state
          eval_global p
        | x => throw (Eval_error.Exp_error x)
      | Option.none => throw (Eval_error.unknown_Location vl)
    | Option.none => throw (Eval_error.unknown_Location el)
  | END a e =>
    do
    let state <- get
    let local_state_opt := state.find? a
    match local_state_opt with
    | Option.some local_state =>
      let evaluation := eval_Exp local_state e
      match evaluation with
      | Exp_RESULT.some r => return r
      | x =>  throw (Eval_error.Exp_error x)
    | Option.none => throw (Eval_error.unknown_Location a)

def combine (lst: List (List Location)): List Location :=
  let combine_two: List Location -> List Location -> List Location := fun x y =>
    (x.append y).eraseDups
  match lst with
  | [] => []
  | x::xs => combine_two x (combine xs)

def result_location: G.P -> Location
  | IF _ _ _ _ _ _ p => result_location p
  | SEND_RECV _ _ _ _ p => result_location p
  | END l _ => l
  | COMPUTE _ _ _ p => result_location p

def participants: G.P -> List Location
  | IF e el v vl opt_a opt_b p => combine [(participants opt_b), (participants opt_a), (participants p), [el, vl]]
  | SEND_RECV _e sender _v receiver p =>
    combine [(participants p ), [receiver, sender]]
  | END l _ => [l]
  | COMPUTE _v _e l _p =>[l]

def send_to_all (locs: List Location) (v: Variable) (val: Nat) (p: L.P): L.P :=
  match locs with
  | [] => L.P.NOOP p
  | x::xs => L.P.SEND (Exp.CONSTANT val) v x (send_to_all xs v val p)



def EPP (prog: G.P) (l: Location) (bi: Nat := 0): L.P :=
  match prog with
  | IF e el v vl opt_a opt_b p =>
    let choice_var_name := "branch_" ++ el ++ "_" ++ toString bi
    if(l == el)then
      let others := (participants prog).erase l
      let result_var_name := "branch_res_" ++ l ++ "_" ++ toString bi
      let fst_branch := send_to_all others choice_var_name 0 (EPP opt_a l)
      let snd_branch := send_to_all others choice_var_name 1 (EPP opt_b l)
      let fst_res_loc := result_location opt_a
      let snd_res_loc := result_location opt_b
      let first_branch := if fst_res_loc == l then
        fst_branch
      else
        let recv_return: L.P := L.P.RECV result_var_name fst_res_loc (L.P.END (Exp.VAR result_var_name))
        substitute_end recv_return fst_branch
      let second_branch := if snd_res_loc == l then
        snd_branch
      else
        let recv_return: L.P := L.P.RECV result_var_name snd_res_loc (L.P.END (Exp.VAR result_var_name))
        substitute_end recv_return snd_branch
      L.P.IF v e first_branch second_branch (EPP p l)
    else
      L.P.RECV choice_var_name el
      (L.P.IF "dummy" (Exp.VAR choice_var_name) (EPP opt_a l) (EPP opt_b l) (EPP p l))

  | SEND_RECV e sender v receiver p =>
    if(l == sender)then
      L.P.SEND e v receiver (EPP p l)
    else if(l==receiver) then
      L.P.RECV v sender (EPP p l)
    else
      EPP p l

  | END end_loc result =>
    if(l == end_loc)then
      L.P.END (Option.some result)
    else
      L.P.END Option.none

  | COMPUTE v e comp_loc p =>
    if(l == comp_loc)then
      L.P.COMPUTE v e (EPP p l)
    else
      EPP p l


open Lean

def price_of (x: Nat): Nat := x + 100
def delivery_date (_x: Nat): Nat := 42

def l_test_Env1: P_state := ([("title", 0),("budget", 42)],[])
def l_test_Env2: P_state := ([],[("price_of", price_of), ("delivery_date_of", delivery_date)])

def g_test_Env : G.Env := HashMap.ofList [("buyer", l_test_Env1), ("seller", l_test_Env2)]


#eval g_test_Env

def test_program_1: P := SEND_RECV (Exp.VAR "var1") "client" "var1" "server" (END "client" (Exp.VAR "var1"))
def test_program_2: P := SEND_RECV (Exp.VAR "var1") "var1" "client" "server"
  (SEND_RECV (Exp.VAR "var2") "server" "var2" "client"
  (COMPUTE "var3" (Exp.DIVIDE (Exp.CONSTANT 2) (Exp.CONSTANT 0)) "server" (END "server" (Exp.VAR "var3"))))

#check (eval_global test_program_1 g_test_Env)

def trade_accept: P := (END "seller"  (Exp.FUNC  "deliveryDate" (Exp.VAR "title")))

def trade_decline: P :=  (END "buyer" (Exp.CONSTANT 0))


def buyer_seller: P := SEND_RECV (Exp.VAR "title") "buyer" "requested_title" "seller"
  (COMPUTE "price" (Exp.FUNC "price_of" (Exp.VAR "requested_title")) "seller"
  (SEND_RECV (Exp.VAR "price") "seller" "price" "buyer"
  (IF "buyer" "result" (Exp.SMALLER (Exp.VAR "price") (Exp.VAR "budget")) trade_accept trade_decline
  (END "buyer" (Exp.VAR "result")))))

def buyer_seller2: P := SEND_RECV (Exp.VAR "title") "buyer" "title" "seller" (END "buyer" (Exp.VAR "title"))

#eval g_test_Env
#eval (buyer_seller)

#eval (participants buyer_seller)
#eval (EPP buyer_seller "buyer")
#eval (EPP buyer_seller "seller")
#eval (eval_global buyer_seller g_test_Env)
#check (eval_global buyer_seller g_test_Env)

#eval (buyer_seller2)
#eval (eval_global buyer_seller2 g_test_Env)

#eval (test_program_1)

#eval (test_program_2)
#eval (eval_global test_program_2 HashMap.empty)
#eval (GLOBAL_TO_TYPE buyer_seller)

#eval ( test_program_1)
