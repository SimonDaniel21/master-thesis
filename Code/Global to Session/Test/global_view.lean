import Test.type
import Test.expression
import Lean
import Test.my_utils
import Test.my_logs
import Test.local_view


namespace G

  open Lean


  inductive P where
  | IF : located Exp -> P -> P -> P
  | SEND_RECV    : located Exp -> located Variable -> P -> P
  | COMPUTE (v: Variable) (e: Exp) (a: Location) :   P -> P
  | END     : Exp -> Location -> P

  inductive MyType where
  | nat   : MyType


  inductive T where
  --| IF : Location -> T -> T -> T -> T
  | SEND_RECV   : Location -> Location -> MyType -> T -> T
  | BRANCH      : Location -> T -> T -> T
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


def Type_Locations: T -> List Location
| T.SEND_RECV sender receiver _dt t => ([sender, receiver] ++ Type_Locations t).eraseDups
| T.BRANCH loc opt_a opt_b => ([loc] ++ Type_Locations opt_a ++ Type_Locations opt_b).eraseDups
| T.END => []

def GLOBAL_TO_TYPE: P -> T
| IF (_e, el) opt_a opt_b =>  T.BRANCH el (GLOBAL_TO_TYPE opt_a) (GLOBAL_TO_TYPE opt_b)
| SEND_RECV (_e, sender) (_v, receiver) p => T.SEND_RECV sender receiver MyType.nat (GLOBAL_TO_TYPE p)
| COMPUTE _ _ _ p => (GLOBAL_TO_TYPE p)
| END _ _ => T.END


-- i for indents
def GP_TO_STRING (i: Nat) (p: P):  String :=
  let leading_spaces := repeat_string "  " i
  let content: String := match p with
  | IF (e, el) opt_a opt_b => "if " ++ toString e ++ "@" ++ el ++ "\n" ++
    GP_TO_STRING  (i + 1) opt_a ++ "\nelse\n" ++ GP_TO_STRING (i + 1) opt_b ++ "\n"
  | SEND_RECV (e, sender) (v, receiver) p =>
    v ++ "@" ++ receiver ++ " <= " ++ toString e ++  "@" ++ sender ++ "\n" ++ (GP_TO_STRING i p)
  | END result l => toString result ++ "@" ++ l
  | COMPUTE v e l p => v ++  "@" ++ l ++ " <= " ++ (Exp_TO_STRING e) ++ " @" ++ l ++ "\n" ++ (GP_TO_STRING i p)
  leading_spaces ++ content

 def MyType_TO_STRING (i: Nat) (t: MyType): String := match t with
| MyType.nat => "Nat"

def GT_TO_STRING (i: Nat) (t: T): String :=
  let leading_spaces := repeat_string "  " i
  let nl := "\n" ++ leading_spaces
  let content: String := match t with
  | T.BRANCH chooser t1 t2 =>
    let observer := (Type_Locations t).erase chooser
    chooser ++ "--> ("  ++ (list_to_string_seperated_by observer ",") ++ "):" ++ nl ++ "{ fst:" ++ nl ++ GT_TO_STRING (i+2) t1 ++ nl ++ "[]snd: "
      ++ nl ++ GT_TO_STRING (i+2) t2 ++ nl ++ "}" ++ "\n"
  | T.SEND_RECV sender receiver t p =>
    sender ++ " --> " ++  receiver ++  ": " ++ MyType_TO_STRING i t ++ ".\n" ++ (GT_TO_STRING i p)
  | T.END => "end"
  leading_spaces ++ content


  --| MyType.branch t1 t2 => "  opt_a: " ++ GT_TO_STRING (i+1) t1 ++ "\n[]opt_b: " ++  GT_TO_STRING (i+1) t2


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
  | SEND_RECV (e, sender) (v, receiver) p =>
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
  | IF (e, el) opt_a opt_b =>
    do
    let state <- get
    append [toString state]
    append ["IF"]
    let expr_state_opt := state.find? el
    match expr_state_opt with
    | Option.some expr_state =>
      let Exp_result := eval_Exp expr_state e
      match Exp_result with
      | Exp_RESULT.some n =>
        if n == 0 then
          eval_global opt_b
        else
          eval_global opt_a
      | x => throw (Eval_error.Exp_error x)
    | Option.none => throw (Eval_error.unknown_Location el)
  | END e a =>
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
  | IF _ _ p => result_location p
  | SEND_RECV _ _ p => result_location p
  | END _ l => l
  | COMPUTE _ _ _ p => result_location p

def participants: G.P -> List Location
  | IF (_, el) opt_a opt_b => combine [(participants opt_b), (participants opt_a), [el]]
  | SEND_RECV (_e, sender) (_v, receiver) p =>
    combine [(participants p ), [receiver, sender]]
  | END _ l => [l]
  | COMPUTE _v _e l _p =>[l]




def EPP_P (prog: G.P) (l: Location) (bi: Nat := 0): L.P :=
  match prog with
  | IF (e, el) opt_a opt_b =>
    let others := (participants prog).erase l
    let fst_branch := (EPP_P opt_a l)
    let snd_branch := (EPP_P opt_b l)

    if (l == el) then
      let fst_branch := send_to_all others BranchChoice.fst fst_branch
      let snd_branch := send_to_all others BranchChoice.snd snd_branch
      L.P.IF e (EPP_P opt_a l) (EPP_P opt_b l)
    else
      L.P.BRANCH_ON el fst_branch snd_branch

  | SEND_RECV (e, sender) (v, receiver) p =>
    if(l == sender)then
      L.P.SEND e v receiver (EPP_P p l)
    else if(l==receiver) then
      L.P.RECV v sender (EPP_P p l)
    else
      EPP_P p l

  | END result end_loc =>
    if(l == end_loc)then
      L.P.END result
    else
      L.boring_end

  | COMPUTE v e comp_loc p =>
    if(l == comp_loc)then
      L.P.COMPUTE v e (EPP_P p l)
    else
      EPP_P p l

def EPP_T (gt: G.T) (l: Location): L.T :=
  match gt with
  | G.T.SEND_RECV sender receiver dt nt =>
    if(l == sender)then
      L.T.SEND receiver (EPP_T nt l)
    else if(l==receiver) then
      L.T.RECV sender (EPP_T nt l)
    else
      EPP_T nt l
  | G.T.BRANCH loc t1 t2 =>
    if l == loc then
      L.T.IF (EPP_T t1 l) (EPP_T t2 l)
    else
      L.T.BRANCH_ON loc (EPP_T t1 l) (EPP_T t2 l)
  | G.T.END => L.T.END



open Lean

def price_of (x: Nat): Nat := x + 100
def delivery_date (_x: Nat): Nat := 42

def l_test_Env1: P_state := ([("title", 0),("budget", 422)],[])
def l_test_Env2: P_state := ([],[("price_of", price_of), ("delivery_date_of", delivery_date)])

def g_test_Env : G.Env := HashMap.ofList [("buyer", l_test_Env1), ("seller", l_test_Env2)]


#eval g_test_Env

def test_program_1: P := SEND_RECV ((Exp.VAR "var1"), "client") ("var1", "server") (END (Exp.VAR "var1") "client")
def test_program_2: P := SEND_RECV ((Exp.VAR "var1"), "var1") ("client", "server")
  (SEND_RECV ((Exp.VAR "var2"), "server") ("var2", "client")
  (COMPUTE "var3" (Exp.DIVIDE (Exp.CONSTANT 2) (Exp.CONSTANT 0)) "server" (END (Exp.VAR "var3") "seller")))

#check (eval_global test_program_1 g_test_Env)

def trade_accept: P := (SEND_RECV ((Exp.FUNC  "delivery_date_of" (Exp.VAR "requested_title")), "seller") ("delivery_date", "buyer")
  (END (Exp.VAR "delivery_date") "seller"))

def trade_decline: P :=  (END (Exp.CONSTANT 33) "buyer" )

def buyer_seller: P := SEND_RECV ((Exp.VAR "title"), "buyer") ("requested_title", "seller")
  (SEND_RECV (Exp.FUNC "price_of" ((Exp.VAR "requested_title")), "seller") ("price", "buyer")
  (IF ((Exp.SMALLER (Exp.VAR "price") (Exp.VAR "budget")), "buyer") trade_accept trade_decline))

def buyer_seller2: P := SEND_RECV ((Exp.VAR "title"), "buyer") ("title", "seller") (END (Exp.VAR "title") "buyer" )

def buyer_seller_type := GLOBAL_TO_TYPE buyer_seller

#eval g_test_Env
#eval (buyer_seller)


#eval buyer_seller_type

#eval (buyer_seller_type)


#eval (EPP_T buyer_seller_type "buyer")
#eval (EPP_T buyer_seller_type "seller")

#eval (eval_global buyer_seller g_test_Env)


def buyer_local_program: L.P := EPP_P buyer_seller "buyer"
def buyer_local_state: L.local_state := { loc := "buyer", env := l_test_Env1, prog:= buyer_local_program }

def seller_local_program: L.P := EPP_P buyer_seller "seller"
def seller_local_state: L.local_state := { loc := "seller", env := l_test_Env2, prog:= seller_local_program }

#eval (LOCAL_TO_TYPE buyer_local_program)
#eval (LOCAL_TO_TYPE seller_local_program)


def state_3_only_buyer: L.state := state_of buyer_local_state []


#eval (eval_local state_3_only_buyer [])



def state_4_buyer_seller: L.state := state_of seller_local_state [buyer_local_state]

#eval state_4_buyer_seller
#eval swap_running_program state_4_buyer_seller

#eval (buyer_local_program)
#eval (seller_local_program)
#eval (EPP_P buyer_seller "buyer")
#eval (eval_local state_4_buyer_seller [])
