import Socket

-- millis to wait for resend after a failed send try
def send_timeout_duration: UInt32 := 200

def list_to_string_seperated_by (l: List String) (s: String): String :=
  match l with
  |   a::b::as => a ++ s ++ (list_to_string_seperated_by (b::as) s)
  |   a::[] => a
  |   [] => ""

def list_to_continuos_string (l: List String): String :=
  list_to_string_seperated_by l ""

def repeat_string (s: String) (n: Nat): String :=
  if n > 0 then
    repeat_string s (n -1) ++ s
  else
    ""

def newLine (i: Nat): String :=
  "\n" ++ repeat_string "  " i

def pad_until (s: String) (i: Nat): String :=
  s ++ repeat_string " " (i - s.length)


def to_bytes_t (α) := α -> ByteArray
def from_bytes_t (α) := ByteArray -> Except String α

class Serialize (a: Type) extends ToString a where
  to_bytes: a -> ByteArray
  from_bytes: ByteArray -> Except String a
  type_name: String
  pretty: a -> String := fun x => s!"{x}: {type_name}"



def String.to_bytes: to_bytes_t String := fun s => s.toUTF8
def String.from_bytes: from_bytes_t String := fun bs => return (String.fromUTF8Unchecked bs)

def Nat.to_bytes: to_bytes_t Nat := fun n => String.to_bytes (toString n)
def Nat.from_bytes: from_bytes_t Nat:= fun bs => do
  let str <- String.from_bytes bs
  let nat_opt := String.toNat? str
  match nat_opt with
  | some nat =>
    return nat
  | none => throw "received unconvertable nat"

instance: Serialize Nat where
  from_bytes := Nat.from_bytes
  to_bytes := Nat.to_bytes
  type_name := "Nat"

instance: Serialize String where
  from_bytes := String.from_bytes
  to_bytes := String.to_bytes
  type_name := "String"


def tn: Nat :=3
#eval (Serialize.pretty " 2")


abbrev address := Socket.SockAddr4

instance: ToString address where
  toString x := s!"{x.addr}@{x.port}"


-- def Socket.SockAddr4.send (a: address) (msg: t) [Serialize t]: IO Unit := do
--   IO.println s!"send on: {a}"
--   let bytes := Serialize.to_bytes msg
--   let sock ← Socket.mk .inet .stream
--   repeat
--     try
--       sock.connect a
--       break
--     catch _ =>
--       IO.sleep send_timeout_duration
--   let sz ← sock.send bytes
--   sock.close
--   assert! sz == bytes.size.toUSize

def Socket.send_ (sock: Socket) (msg: t) [Serialize t]: IO Unit := do
  let bytes := Serialize.to_bytes msg
  let sz ← sock.send bytes
  assert! sz == bytes.size.toUSize

-- def broadcast (msg: t) [Serialize t]: List address -> IO Unit
-- | [] => return ()
-- | a::as =>
--   do
--   a.send msg
--   broadcast msg as



def Socket.SockAddr4.connect_to (addr: address): IO Socket := do
  IO.println s!"connect to: {addr}"
  let sock ← Socket.mk .inet .stream
  repeat
    try
      sock.connect addr
      break
    catch _ =>
      IO.sleep send_timeout_duration
  return sock

def Socket.SockAddr4.listen_on (addr: address): IO Socket := do
  IO.println s!"binding on: {addr}"
  let sock ← Socket.mk .inet .stream
  sock.bind addr
  sock.listen 1
  let (client, _sa) ← sock.accept
  return client


def Socket.recv_ (sock: Socket) (max: USize := 4096) [Serialize t]: IO t := do
  let recv ← sock.recv max
  if recv.size == 0 then throw (IO.Error.otherError 2 "received msg with 0 bytes")

  let msg := Serialize.from_bytes recv
  match msg with
  | .ok val =>
    IO.println s!"recv: {msg}"
    return val
  | .error e => throw (IO.Error.userError e)

-- def Socket.SockAddr4.recv (addr: address) (max: USize := 4096) [Serialize t]: IO t := do
--   IO.println s!"recv on: {addr}"
--   let sock ← Socket.mk .inet .stream
--   sock.bind addr
--   sock.listen 1
--   let (client, _sa) ← sock.accept
--   sock.close
--   let recv ← client.recv max
--   client.close

--   if recv.size == 0 then throw (IO.Error.otherError 2 "received msg with 0 bytes")

--   let msg := Serialize.from_bytes recv
--   match msg with
--   | .ok val =>
--     IO.println s!"recv: {msg}"
--     return val
--   | .error e => throw (IO.Error.otherError 2 e)

/-

def combine {α: Type} (lst: List (List α)): List α :=
  let combine_two: List α -> List α -> List α := fun x y =>
    (x.append y).eraseDups
  match lst with
  | [] => []
  | x::xs => combine_two x (combine xs)
-/
