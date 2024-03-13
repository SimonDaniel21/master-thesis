import Socket
import Mathlib.Data.FinEnum
--prints sent and received network bytes
def dbg_print_net_msgs := true
def dbg_print_init_sockets := true
def dbg_print_net_bytes := false

-- millis to wait for resend after a failed send try
def send_timeout_duration: UInt32 := 200



def String.toBool?: String -> Option Bool
| "false" => some false
| "true" => some true
| _ => none

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

class Serialize (a: Type) extends ToString a, Inhabited a where
  to_bytes: a -> ByteArray
  from_bytes: ByteArray -> Except String a
  type_name: String
  pretty: a -> String := fun x => s!"{x}: {type_name}"



def String.byte_count (s:String): Nat :=
  s.toUTF8.size
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

--def List.to_bytes {a:Type} [Serialize a]: to_bytes_t (List a) := fun l => l.length.toUInt16.to_bytes++l.length.to_bytes



#eval toString true

def t1:UInt16 := 600
def t2: UInt8 := t1.toUInt8
def t3: UInt8 := (t1.shiftRight 8).toUInt8
#eval t2
#eval t3
#eval (t2.toUInt16) + (t3.toUInt16.shiftLeft 8)

def Bool.to_bytes: to_bytes_t Bool := fun x => (toString x).to_bytes

def Bool.from_bytes: from_bytes_t Bool := fun bs => do
  let str <- String.from_bytes bs
  let bool_opt := String.toBool? str
  match bool_opt with
  | some b =>
    return b
  | none => throw "received unconvertable nat"

#check UInt16

def res := ByteArray.mkEmpty 1
#eval res
def res2 := res.push 2
#eval res2
def res3 := res.push 3
#eval res3

#eval #[1,2,3,4,5,6].toSubarray 2 3

def UInt8.to_bytes: to_bytes_t UInt8 := fun x =>
  (ByteArray.mkEmpty 1).push x

def UInt8.from_bytes: from_bytes_t UInt8 := fun bs => do
  let uint8_opt := bs.data.get? 0
  match uint8_opt with
  | some v =>
    return v
  | none => throw "received unconvertable UInt8"

def UInt16.to_bytes: to_bytes_t UInt16 := fun x =>
  let lower: UInt8 := x.toUInt8
  let upper: UInt8 := (x.shiftRight 8).toUInt8
  ((ByteArray.mkEmpty 2).push lower).push upper

def UInt16.from_bytes: from_bytes_t UInt16 := fun bs => do
  let lower_opt := bs.data.get? 0
  let upper_opt := bs.data.get? 1
  match lower_opt with
  | some lower =>
     match upper_opt with
    | some upper =>
      return lower.toUInt16 + ((upper).toUInt16.shiftLeft 8)
    | none => throw "received unconvertable UInt16"
  | none => throw "received unconvertable UInt16"


def JoinByteArrayList: List ByteArray -> ByteArray
| [] => ByteArray.mkEmpty 0
| a::as => a ++ JoinByteArrayList as

def List.to_bytes [Serialize a]: to_bytes_t (List a)
| l =>
  let list_size := l.length.toUInt16
  let data := l.map (fun x =>
    let bytes := Serialize.to_bytes x
    let len := bytes.size.toUInt16
    (len.to_bytes ++ bytes)
  )
  let res_byte_array := JoinByteArrayList data
  list_size.to_bytes ++ res_byte_array

def List.from_bytes_rec [Serialize a]: Nat -> from_bytes_t (List a)
| 0, bs => .ok []
| x+1, bs => do
  let len <- UInt16.from_bytes (bs.extract 0 2)
  --dbg_trace s!"len: {len}"

  let data <- Serialize.from_bytes (a:=a) (bs.extract 2 (2+(len.toNat)))
  let rest <- List.from_bytes_rec (x) (bs.extract (2+(len.toNat)) bs.data.size)
  return [data] ++ rest

def List.from_bytes [Serialize a]: from_bytes_t (List a) := fun bs => do
  let list_size_bytes := bs.extract 0 2
  let list_data_bytes := bs.extract 2 bs.size
  let list_size <- (UInt16.from_bytes (list_size_bytes))
  List.from_bytes_rec list_size.toNat list_data_bytes


instance: Serialize Nat where
  from_bytes := Nat.from_bytes
  to_bytes := Nat.to_bytes
  type_name := "Nat"

instance: Serialize Bool where
  from_bytes := Bool.from_bytes
  to_bytes := Bool.to_bytes
  type_name := "Bool"

instance: Serialize String where
  from_bytes := String.from_bytes
  to_bytes := String.to_bytes
  type_name := "String"

instance (a:Type) [Serialize a]: Serialize (List a) where
  from_bytes := List.from_bytes
  to_bytes := List.to_bytes
  type_name := s!"List ({Serialize.type_name a})"

def test_bytes1 := UInt16.to_bytes 4444

def empty_nats: List Nat:= []

def test_bytes := ["hellö", "world","shrt", "longer text"].to_bytes

def test_bytes2:= empty_nats.to_bytes


abbrev Address := Socket.SockAddr4

instance: ToString Address where
  toString x := s!"{x.addr}@{x.port}"


def Socket.send_val (sock: Socket) (msg: t) [Serialize t]: IO Unit := do
  let bytes := Serialize.to_bytes msg
  let sz ← sock.send bytes
  IO.println s!"send bytes: {bytes}"
  assert! sz == bytes.size.toUSize

def Socket.send_val2 (sock: Socket) (msg: t) [Serialize t]: IO Unit := do
  let payload := Serialize.to_bytes msg
  let size_info: ByteArray := payload.size.toUInt16.to_bytes
  let bytes := size_info ++ payload
  let sz ← sock.send bytes
  if dbg_print_net_bytes then
    IO.println s!"send bytes {bytes}"
  assert! sz == bytes.size.toUSize

def Socket.SockAddr4.connect_to (addr: Address): IO Socket := do
  let sock ← Socket.mk .inet .stream
  repeat
    try
      sock.connect addr
      break
    catch _ =>
      IO.sleep send_timeout_duration
  return sock

def Socket.SockAddr4.listen_on (addr: Address): IO Socket := do
  let sock ← Socket.mk .inet .stream
  sock.bind addr
  sock.listen 1
  let (client, _sa) ← sock.accept
  return client


def Socket.recv_val (sock: Socket) (max: USize := 4096) [Serialize t]: IO t := do
  let recv ← sock.recv max
  IO.println s!"recv bytes: {recv}"
  if recv.size == 0 then throw (IO.Error.otherError 2 "received msg with 0 bytes")

  let msg := Serialize.from_bytes recv
  match msg with
  | .ok val =>
    --IO.println s!"recv: {msg}"
    return val
  | .error e => throw (IO.Error.userError e)

def Socket.recv_val2 (sock: Socket) (max: USize := 4096) [Serialize t]: IO t := do
  let size_info_opt := UInt16.from_bytes (<- sock.recv 2)
  match size_info_opt with
  | .ok size_info =>
    let payload <- sock.recv (USize.ofNat size_info.toNat)
    if dbg_print_net_bytes then
      IO.println s!"recv bytes {payload}"
    if payload.size != size_info.toNat then throw (IO.Error.otherError 2 s!"payload size [{size_info}] does not match up with received [{payload.size}]")

    let msg := Serialize.from_bytes payload
    match msg with
    | .ok val =>
      return val
    | .error e => throw (IO.Error.userError e)
  | .error e => throw (IO.Error.userError e)



def IO.getLine: IO String := do
  let stdin <- IO.getStdin
  return (<-stdin.getLine).dropRight 1

def IO.getBool: IO Bool := do
  let str <- IO.getLine
  return str == "y"

def IO.getNat: IO Nat := do
  let str <- IO.getLine
  return str.toNat!

def List.seperate (l: List a) (n: Nat):  (List a × List a) :=
 let l1 := l.drop n
 let l2 := (l.reverse.drop (l.length - n)).reverse
 (l2, l1)


-- returns a List where the first n elements are removed from a list and appended to the end
-- examples [1,2,3].shuffle 1 => [2,3,1]
-- examples [1,2,3].shuffle 2 => [3,1,2]

def List.shuffle (l: List a) (n: Nat := 1):  List a :=
  let pre := (l.reverse.drop (l.length - n)).reverse
  l.drop n ++ pre

#eval [1,2,3,4,5,6].shuffle 2

/-

def combine {α: Type} (lst: List (List α)): List α :=
  let combine_two: List α -> List α -> List α := fun x y =>
    (x.append y).eraseDups
  match lst with
  | [] => []
  | x::xs => combine_two x (combine xs)
-/


def default_adress (k:δ × δ) (start_port: Nat := 2222) [FinEnum δ]:  Address :=
  let port: Nat := start_port + (FinEnum.equiv k.1) * (FinEnum.card δ) + (FinEnum.equiv k.2)
  .v4  (.mk 127 0 0 1) port.toUInt16

def reprName (v:α) [Repr α]: String :=
  let rs := reprStr v
  (rs.dropWhile (fun x => x != '.')).drop 1

inductive Foo : Type
| a : Foo
| b : Nat -> Foo
deriving Repr

def FinEnum.ofString? (s:String) [FinEnum α][Repr α]:  Option α := do
  for e in (FinEnum.toList α) do
    if (reprName e == s) then
      return e
  Option.none

def FinEnum.ofString! (s:String) [FinEnum α][Repr α] [Inhabited α]:  α :=
  let opt := FinEnum.ofString? s
  match opt with
  | some v => v
  | none => Inhabited.default
