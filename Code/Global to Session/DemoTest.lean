import Socket
import Test.type
import Test.my_utils

-- TASK --
inductive DSL where
  | CONSTANT (n: Nat) :DSL
  | DIVIDE: DSL -> DSL -> DSL
  | PLUS: DSL -> DSL -> DSL

inductive MyOptional (t: Type): Type
  | some (e: t): MyOptional t
  | none: MyOptional t

def eval: DSL -> MyOptional Nat
  | DSL.CONSTANT n => (MyOptional.some n)
  | DSL.DIVIDE a b => match eval a with
    | MyOptional.none => MyOptional.none
    | MyOptional.some v_a => (match eval b with
      | MyOptional.none => MyOptional.none
      | MyOptional.some v_b => if ( v_b == 0) then
        MyOptional.none
        else (MyOptional.some (v_a / v_b)))
  | DSL.PLUS a b => match eval a with
    | MyOptional.none => MyOptional.none
    | MyOptional.some v_a => (match eval b with
      | MyOptional.none => MyOptional.none
      | MyOptional.some v_b => MyOptional.some (v_a + v_b))

def eval2: DSL -> Option Nat
  | DSL.CONSTANT n => (Option.some n)
  | DSL.DIVIDE a b => do
    let v_a := <- eval2 a
    let v_b <- eval2 b
    if ( v_b == 0) then
      Option.none
    else (Option.some (v_a / v_b))
  | DSL.PLUS a b =>
    do
    Option.some ((<- eval2 a) + (<- eval2 b))



--- Higher order Terms ---

-- inductive Ty where
-- | nat: Ty
-- | string: Ty
-- | fn: Ty -> Ty -> Ty

-- @[reducible] def Ty.denote: Ty -> Type
-- | nat => Nat
-- | string => String
-- | fn a b => a.denote -> b.denote

-- inductive Term' (rep: Ty -> Type): Ty -> Type
--   | var           : rep x -> Term' rep x
--   | nat_const     : Nat -> Term' rep Ty.nat
--   | string_const  : String -> Term' rep Ty.string
--   | plus          : Term' rep Ty.nat -> Term' rep Ty.nat -> Term' rep Ty.nat
--   | my_let           : Term' rep x -> (rep x -> Term' rep y) -> Term' rep y
--   | lam           : (rep x -> Term' rep y) -> Term' rep (Ty.fn x y)
--   | app           : Term' rep (Ty.fn x y) -> Term' rep x -> Term' rep y

-- def Term (ty: Ty) := {rep: Ty -> Type} -> Term' rep ty

-- open Ty (nat fn)

-- def add: Term (fn nat (fn nat nat)) :=
--   Term'.lam fun x => Term'.lam fun y => Term'.plus (Term'.var x) (Term'.var y)

-- --def add_toString: Term (fn nat (fn nat string)) :=
-- --  Term'.lam fun x => Term'.lam fun y => (Term'.plus (Term'.var x) (Term'.var y))



-- def three_test: Term nat :=
--   Term'.app (Term'.app add (Term'.nat_const 1)) (Term'.nat_const 4)

-- #eval Nat.succ Nat.zero
-- def countVars: Term' (fun _ => Unit) ty -> Nat
--   | .var _ => 1
--   | .nat_const _ => 0
--   | .string_const _ => 0
--   | .plus a b => countVars a + countVars b
--   | .app f a => countVars f + countVars a
--   | .lam b => countVars ( b ())
--   | .my_let a b => countVars a + countVars (b ())

-- example : countVars add = 2 := rfl

-- open Term'

-- def pretty (e: Term' (fun _ => String) ty) (i: Nat := 1) : String :=
--   match e with
--   | .var s => s
--   | .nat_const n => toString n
--   | string_const s => s
--   | app f a => s!"({pretty f i} {pretty a i})"
--   | plus a b => s!"({pretty a i} + {pretty b i})"
--   | lam f     =>
--     let x := s!"x_{i}"
--     s!"(fun {x} => {pretty (f x) (i+1)})"
--   | my_let a b  =>
--     let x := s!"x_{i}"
--     s!"(let {x} := {pretty a i}; => {pretty (b x) (i+1)}"

-- #eval pretty three_test

-- #check three_test

-- def length? {α : Type} (xs : List α) : Nat :=
--   match xs with
--   | [] => 0
--   | y :: ys => 1 + (length? ys)

-- #eval length? [1,2,3,45,56]


def addr : Socket.SockAddr4 := .v4 (.mk 127 0 0 1) 8889

def Bool_to_bytes: to_bytes_t Bool := fun b => String_to_bytes (toString b)
def Bool_from_bytes: from_bytes_t Bool := fun bs => do
  let str <- String_from_bytes bs
  match str with
  | "false" => return false
  | "true" => return true
  | _ => throw "received unconvertable bool"


def Value.to_bytes: to_bytes_t Value := fun v => match v with
| .nat n => Nat.to_bytes n
| .bool b => Bool_to_bytes b
| .string s => String_to_bytes s

def Value.from_bytes (s: Sorts): from_bytes_t Value:= fun bs => do match s with
| .nat => return Value.nat (<-Nat.from_bytes bs)
| .bool => return Value.bool (<-Bool_from_bytes bs)
| .string => return Value.string (<-String_from_bytes bs)


def Socket.sendStr (sock: Socket) (msg: String): IO Unit := do
  let bytes := msg.toUTF8
  let sz ← sock.send bytes
  IO.println s!"sent: {msg}"
  assert! sz == bytes.size.toUSize

def Socket.recvStr (sock: Socket) (max: USize := 4096): IO String := do
  let recv ← sock.recv max
  if recv.size == 0 then return ""
  let str := String.fromUTF8Unchecked recv
  IO.println s!"recv: {str}"
  return str

def Socket.send_val (sock: Socket) (msg: Value): IO Unit := do
  let bytes := Value.to_bytes msg
  let sz ← sock.send bytes
  IO.println s!"sent: {msg}"
  assert! sz == bytes.size.toUSize

def Socket.recv_val (sock: Socket) (s: Sorts) (max: USize := 4096): IO Value := do
  let recv ← sock.recv max
  if recv.size == 0 then throw (IO.Error.otherError 2 "received msg with 0 bytes")
  let msg := Value.from_bytes s recv
  IO.println s!"recv: {msg}"
  match msg with
  | .ok v => return v
  | .error e => throw (IO.Error.otherError 2 e)





def handle (sock : Socket) : IO Unit := do
  IO.println "handler start"
  let msg ← sock.recvStr
  let resp ← sock.sendStr s!"response to {msg}"
  IO.println "handler done"

def serverloop : IO Unit := do
  let sock ← Socket.mk .inet .stream
  sock.bind addr
  sock.listen 1
  while true do
    let (client, _sa) ← sock.accept
    handle client
  return ()



-- def main (args : List String) : IO Unit := do
--   let mode := args.get! 0
--   if mode == "client" then
--     client <| args.get! 1
--   else if mode == "server" then
--     serverloop
--   else
--     IO.println "Unknown mode"
--     return ()



def client2: IO Unit := do
  let sock ← Socket.mk .inet .stream
  let local_addr: Socket.SockAddr4 := .v4 (.mk 127 0 0 1) 4599
  sock.connect local_addr

def recv (addr: Socket.SockAddr4) (s: Sorts): IO Value := do
  IO.println "waiting for recieve"
  let sock ← Socket.mk .inet .stream
  sock.bind addr
  sock.listen 1
  IO.println ("bound")
  let (client, _sa) ← sock.accept
  sock.close
  IO.println ("accepted")
  let msg ← client.recv_val s
  IO.println ("received: " ++ toString msg)
  client.close
  return msg

def send (addr: Socket.SockAddr4) (v: Value) : IO Unit := do
  IO.println "start blocking send"
  let sock ← Socket.mk .inet .stream
  sock.connect addr
  sock.send_val v
  sock.close



def server: IO Nat := do
    let var1 <- recv (.v4 (.mk 127 0 0 1) 4600) Sorts.bool
    return 0

def client: IO Nat := do
    send (.v4 (.mk 127 0 0 1) 4600) (Value.bool false)
    return 0


-- def main (args : List String) : IO Unit := do
--   let mode := args.get! 0
--   if mode == "client" then
--     client <| args.get! 1
--   else if mode == "server" then
--     serverloop
--   else
--     IO.println "Unknown mode"
--     return ()





inductive SessionType where
| send (t: Type) [Serialize t]: Location -> SessionType -> SessionType
| receive (t: Type) [Serialize t]: Location -> SessionType -> SessionType
--| branch: SessionType -> Location -> SessionType -> SessionType
--| choose: SessionType -> SessionType -> SessionType -> SessionType
| end: SessionType

inductive SessionStep where
| send (t:Type ) [Serialize t]: (t -> IO Unit) -> SessionStep
| receive (t:Type ) [Serialize t]: IO t -> SessionStep
| done: SessionStep

-- | .send t l n =>
--   let msg: Nat := 2
--   .send (socket.send_any msg)
-- | .receive te l n =>
--   .receive te (socket.recv_any (t:=te))
-- | .end => _



def SessionType.next (s: SessionType) (socket: Socket.SockAddr4): SessionStep := match s with
| SessionType.send t l n =>
  SessionStep.send t (fun x => (socket.send x))
| SessionType.receive recv_type l n =>
  SessionStep.receive recv_type (socket.recv (t:=recv_type))
| SessionType.end => SessionStep.done


def SessionType.toString: SessionType -> String
| SessionType.send t l n => s!"send t to {l}\n{n.toString}"
| SessionType.receive recv_type l n => s!"recv t from {l}\n{n.toString}"
| SessionType.end => s!"end"

instance: ToString SessionType where
  toString := SessionType.toString

def test_session_type: SessionType := .send Nat "other" .end



#eval test_session_type
#check (test_session_type.next addr)


--| .choose a b n => s!"choose to\n{n.toString}"
  --| .end => "end"



def SessionException: SessionType -> String
| expected => "expected " ++ toString expected

def SessionSendTypeE: Type -> String
| expected => "sent wrong type"


-- inductive SessionException where
-- | wrong_op: SessionType -> SessionType -> SessionException
-- | wrong_dest: Location -> SessionException



-- structure Session where
--   type: SessionType
--   phys_mapping: List (Location × Socket.SockAddr4)

def Session:= (SessionType × List (Location × Socket.SockAddr4))




-- def SessionType.is_send: SessionType -> Bool
-- | .send _ _ _ => true
-- | _ => false



-- def SessionType.send_val_old (s: SessionType) (pm: List (Location × Socket.SockAddr4)) (α: Sorts) (v: (α.denote)) [ToString α.denote] [Serialize α.denote]: Except String (SessionType × (IO Unit)) := match s with
-- | .send t l n =>
--   if (t != α) then
--     throw ("sending wrong type")
--   else
--   let dest_opt := pm.lookup l
--   match dest_opt with
--   | some d =>
--     return (n, d.send_any v)
--   | none => throw ("couldnt find addr for {l}")
-- | _ => throw "did not expect send"



-- def SessionType.recv_val (α: Sorts) (pm: List (Location × Socket.SockAddr4)) (s: SessionType) [ToString α.denote] [Serialize α.denote]: Except String (SessionType × (IO α.denote)) := match s with
-- | .receive t l n =>
--   if (t != α) then
--     throw ("receiving wrong type")
--   else
--   let source_opt := pm.lookup l
--   match source_opt with
--   | some s =>
--     return (n, s.recv_any α)
--   | none => throw ("couldnt find addr for {l}")
-- | _ => throw "did not expect send"




def main (args : List String): IO (UInt32) := do

  let mode := args.get! 0
  if mode == "client" then
    client
  else if mode == "server" then
    server
  else
    IO.println "Unknown Location"
    return 1
  return 0


-- def SessionType.next (phys_mapping: List (Location × Socket.SockAddr4 )) : SessionType -> SessionStep -> SessionType
-- | .send t l n => fun x => n
-- | .receive t l n => n
-- | .branch t l n => n
-- | .choose t l n => n
-- | .end => .end

-- def SessionType.do_send {α} [Serialize α] (v: α) (phys_mapping: List (Location × Socket.SockAddr4 )) : SessionType -> SessionType
-- | .send t l n => n
-- | _ =>

-- benutzung

-- session mit phys_mapping

-- session.next 111

-- let msg <- session.next

-- match session.next with
-- | first =>
-- | second =>


-- #check located Nat

-- inductive NP where
-- | IF : located Exp -> NP -> NP -> NP
-- | SEND_RECV    : located Exp -> located Variable -> P -> P
-- | COMPUTE (v: Variable) (e: Exp) (a: Location) :   P -> P
-- | def_func      : Function -> Array Sorts -> Exp -> P -> P
-- | END     : located Exp -> P

-- #check located


-- def Network.prog: Network -> IO Unit
-- | .send t v => IO.println "sends"
-- | .recv t v => IO.println "receives"
-- | .run t v => do
--   IO.println "runs"
--   v

-- def do_send {t} (val:t) (s:Socket.SockAddr4) [Serialize t]: IO Unit :=
--   s.send_any val

-- def do_recv {t} (s:Socket.SockAddr4) [Serialize t]:  Network (IO t) :=
--   Network.recv (s.recv_any)

-- def Network.do_run (prog: IO t):  Network (IO t) :=
--   Network.run prog

-- def bind_Network:  Network α → (α → Network β) → Network β
-- | .send v, f => f v
-- | .recv v, f => f v
-- | .run prog, f => f prog

-- instance: Monad Network where
--   bind := bind_Network
--   pure := fun x => .run x


-- def test_net := Network.send 3


-- def net_prog: Network String := do
--   let temp <- do_send 3 addr
--   Network.send 3

-- def main3 (args : List String): IO (UInt32) := do
--   let blaa <- IO.println ""
--   pure 3
