import «Test»

inductive DSL 
| PLUS:DSL->DSL->DSL
| CONSTANT:Nat->DSL
| SERVER_VAR

inductive Ty : Type
  | nat: Ty
  | fn (a: Ty): Ty -> Ty

@[reducible] def Ty.denote : Ty → Type 
  |nat    => Nat
  |fn a b => a.denote -> b.denote

open Ty

#check (List.Mem.head _ : (1 ∈ [1,2,3]))
#check (List.Mem.tail _ (List.Mem.head _ ): (2 ∈ [1,2,3]))

-- def addstring: String-> String->String := String.append 
-- instance aneinander: Add String where 
--   add := addstring

def channelVarType := String
def variableType := String

inductive AGENT where
  | client    : AGENT
  | server    : AGENT

def AGENT_TO_STRING: AGENT -> String
  | AGENT.client => "client"
  | AGENT.server => "server"

instance AGENT_DEBUG: ToString AGENT where 
  toString := AGENT_TO_STRING


inductive EXPRESSION where
  | CONSTANT : EXPRESSION
  | PLUS (e1: EXPRESSION) (e2: EXPRESSION):  EXPRESSION


inductive TYPED_EXPRESSION: (List String) -> EXPRESSION -> Ty -> Type 
  | TYPED_CONSTANT :  TYPED_EXPRESSION GAMMA EXPRESSION.CONSTANT nat
  | TYPED_PLUS (typed_e1: TYPED_EXPRESSION GAMMA e1 nat)
               (typed_e2: TYPED_EXPRESSION GAMMA e2 nat):
                TYPED_EXPRESSION GAMMA (EXPRESSION.PLUS e1 e2) nat

inductive GLOBAL_PROGRAM where
  | SEND_RECV    :  channelVarType -> variableType -> AGENT -> AGENT -> GLOBAL_PROGRAM -> GLOBAL_PROGRAM
  | END     :   GLOBAL_PROGRAM
  | COMPUTE (v: variableType) (e: EXPRESSION) (a: AGENT) :   GLOBAL_PROGRAM -> GLOBAL_PROGRAM
 
def AGENT_EQUALITY (a: AGENT): AGENT -> Bool
  | AGENT.client => a = AGENT.client
  | AGENT.server => false

def GLOBAL_PROGRAM_TO_STRING: GLOBAL_PROGRAM -> String
  | GLOBAL_PROGRAM.SEND_RECV c v sender receiver p => 
    (AGENT_TO_STRING sender) ++ " --" ++ "> " ++ (AGENT_TO_STRING receiver) ++ "\n" ++ (GLOBAL_PROGRAM_TO_STRING p)
  | GLOBAL_PROGRAM.END => "END"
  | GLOBAL_PROGRAM.COMPUTE v e a p => "++--"

instance GLOBAL_PROGRAM_DEBUG: ToString GLOBAL_PROGRAM where 
  toString := GLOBAL_PROGRAM_TO_STRING

#eval (GLOBAL_PROGRAM.SEND_RECV "channel1" "var1" GLOBAL_PROGRAM.END)

#eval (GLOBAL_PROGRAM.SEND_RECV "channel1" "var1" AGENT.client AGENT.server 
(GLOBAL_PROGRAM.SEND_RECV "channel2" "var2" AGENT.server AGENT.client 
GLOBAL_PROGRAM.END))

inductive LOCAL_PROGRAM where
  | SEND    :  channelVarType -> variableType -> AGENT -> LOCAL_PROGRAM -> LOCAL_PROGRAM
  | RECV    :  channelVarType -> variableType -> AGENT -> LOCAL_PROGRAM -> LOCAL_PROGRAM
  | END     :   LOCAL_PROGRAM
  | COMPUTE (v: variableType) (e: EXPRESSION) :   LOCAL_PROGRAM -> LOCAL_PROGRAM
 

def LOCAL_PROGRAM_TO_STRING: LOCAL_PROGRAM -> String
  | LOCAL_PROGRAM.SEND c v receiver p => 
    "send(" ++ (AGENT_TO_STRING receiver) ++ "\n" ++ (LOCAL_PROGRAM_TO_STRING p)
  | LOCAL_PROGRAM.RECV c v sender p => 
    "receive(" ++ (AGENT_TO_STRING sender) ++ "\n" ++ (LOCAL_PROGRAM_TO_STRING p)
  | LOCAL_PROGRAM.COMPUTE v e p => "++--"
  | LOCAL_PROGRAM.END => "END"
  
-- ENDPOINT PROJECTION --
def GLOBAL_TO_LOCAL (a: AGENT): GLOBAL_PROGRAM -> LOCAL_PROGRAM
  | (GLOBAL_PROGRAM.SEND_RECV c v sender receiver p) => 
    if (a == sender) then LOCAL_PROGRAM.SEND c v (GLOBAL_TO_LOCAL a p)
    else if a == receiver then LOCAL_PROGRAM.RECV c v (GLOBAL_TO_LOCAL a p)
    else (GLOBAL_TO_LOCAL a p)
  | GLOBAL_PROGRAM.END => LOCAL_PROGRAM.END
  | GLOBAL_PROGRAM.COMPUTE v e b p =>
    if (a == b) then LOCAL_PROGRAM.COMPUTE v e (GLOBAL_TO_LOCAL a p)
    else (GLOBAL_TO_LOCAL a p)


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