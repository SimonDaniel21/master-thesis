import «Test».type
import Test.global_view
import Test.local_view

inductive DSL 
| PLUS:DSL->DSL->DSL
| CONSTANT:Nat->DSL
| SERVER_VAR


open Ty

#check (List.Mem.head _ : (1 ∈ [1,2,3]))
#check (List.Mem.tail _ (List.Mem.head _ ): (2 ∈ [1,2,3]))

-- def addstring: String-> String->String := String.append 
-- instance aneinander: Add String where 
--   add := addstring


inductive EXPRESSION where
  | CONSTANT : EXPRESSION
  | PLUS (e1: EXPRESSION) (e2: EXPRESSION):  EXPRESSION


inductive TYPED_EXPRESSION: (List String) -> EXPRESSION -> Ty -> Type 
  | TYPED_CONSTANT :  TYPED_EXPRESSION GAMMA EXPRESSION.CONSTANT nat
  | TYPED_PLUS (typed_e1: TYPED_EXPRESSION GAMMA e1 nat)
               (typed_e2: TYPED_EXPRESSION GAMMA e2 nat):
                TYPED_EXPRESSION GAMMA (EXPRESSION.PLUS e1 e2) nat







inductive TYPED_GLOBAL_PROGRAM (GAMMA: List variableType) (DELTA: List channelVarType) : GLOBAL_PROGRAM -> Type
  | SEND_RECV (channel_name: channelVarType) (var_name: variableType) (P:GLOBAL_PROGRAM):
    channel_name ∈ DELTA -> var_name ∈ GAMMA -> TYPED_GLOBAL_PROGRAM GAMMA DELTA (GLOBAL_PROGRAM.SEND_RECV channel_name var_name P)

inductive Term' : Ty -> Type
  | var (t: Ty) : Nat -> Term' t
  | const (n: Nat): Term' nat




mutual
  inductive TYPE where
    | _string    : TYPE
    | _real    : TYPE
    | branch : String->GLOBAL_TYPE->String->GLOBAL_TYPE->TYPE

  inductive GLOBAL_TYPE
  | SEND_RECEIVE: AGENT->AGENT->TYPE->GLOBAL_TYPE->GLOBAL_TYPE
  | END: GLOBAL_TYPE

end

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"


def agent_to_string (a: AGENT) : String := match a with
  | AGENT.client => "client"
  | AGENT.server => "server"

mutual
  def type_to_string :TYPE -> String 
    | TYPE._string => "string"
    | TYPE._real => "real"
    | TYPE.branch s1 g1 s2 g2 => (String.replace ("{\n" ++ s1 ++ ": " ++ to_global_string g1 ++ "\n" ++ s2 ++ ": " ++ to_global_string g2) "\n" "\n  ") ++ "\n}"
    
  def to_global_string (g: GLOBAL_TYPE) : String := match g with
  | GLOBAL_TYPE.SEND_RECEIVE a b t g => (String.append (String.append (String.append (String.append (agent_to_string a) " -> ") (agent_to_string b)) ": ") (type_to_string t)) ++ to_global_string g
  | GLOBAL_TYPE.END => "" 
end

instance debug_string: ToString GLOBAL_TYPE where 
  toString := to_global_string

instance debug_type_string: ToString TYPE where 
  toString := type_to_string

-- instance: Lean.Eval GLOBAL_TYPE where 
--   eval g b := IO.println (g ())


#eval GLOBAL_TYPE.SEND_RECEIVE AGENT.client AGENT.server TYPE._string (GLOBAL_TYPE.SEND_RECEIVE AGENT.client AGENT.client TYPE._real GLOBAL_TYPE.END)

#eval  GLOBAL_TYPE.SEND_RECEIVE AGENT.client AGENT.server 
(TYPE.branch "success" (GLOBAL_TYPE.SEND_RECEIVE AGENT.client AGENT.server TYPE._string GLOBAL_TYPE.END)
 "failure" (GLOBAL_TYPE.SEND_RECEIVE AGENT.client AGENT.server TYPE._string GLOBAL_TYPE.END)) GLOBAL_TYPE.END

#eval TYPE.branch "success" (GLOBAL_TYPE.SEND_RECEIVE AGENT.client AGENT.server TYPE._string GLOBAL_TYPE.END) "failure" (GLOBAL_TYPE.SEND AGENT.client AGENT.server TYPE._string GLOBAL_TYPE.END)
def inc: Nat -> Nat
| a => a+1

#reduce List.map inc [1,2,3] 

def joinStringsWith (s1: String) (s2: String) (s3: String) : String :=
  String.append (String.append s2 s1) s3



#reduce eval (DSL.CONSTANT 2)
def temp: Int := 4
#eval if (3+2 < 10) then temp else 5
#check (if 3 == 4 then "equal" else "not equal")
#check IO.println (joinStringsWith ", " "one\n" "and another")

#check (joinStringsWith)

open Ty (nat fn)

def Term (ty: Ty) := (rep: Ty -> Type) -> Term' rep ty

def pretty (e : Term' (fun _ => String) ty) (i : Nat := 1) : String :=
  match e with
  | .var s     => s
  | .const n   => toString n
  | .app f a   => s!"({pretty f i} {pretty a i})"
  | .plus a b  => s!"({pretty a i} + {pretty b i})"
  | .lam f     =>
    let x := s!"x_{i}"
    s!"(fun {x} => {pretty (f x) (i+1)})"
  | .let a b  =>
    let x := s!"x_{i}"
    s!"(let {x} := {pretty a i}; => {pretty (b x) (i+1)}"

#eval 