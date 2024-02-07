import Socket

def port: UInt16 := 8889 -- only works on this port
def addr (port: UInt16) : Socket.SockAddr4 := .v4 (.mk 127 0 0 1) port

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

def client (port: UInt16) (arg : String) : IO Unit := do
  let sock ← Socket.mk .inet .stream
  let sa : Socket.SockAddr4 := addr port
  sock.connect sa
  sock.sendStr arg
  let resp <- sock.recvStr
  IO.println ("response: " ++ resp)

def handle (client : Socket) : IO Unit := do
  IO.println "handler start"
  let msg ← client.recvStr
  client.sendStr s!"response to {msg}"

def server (port: UInt16): IO Unit := do
  let sock ← Socket.mk .inet .stream
  let sa : Socket.SockAddr4 := addr port
  sock.bind sa
  sock.listen 1
  while true do
    let (client, _sa) ← sock.accept
    handle client
  return ()

def main (args : List String) : IO Unit := do
  let mode := args.get! 0
  --let port := (args.get! 1).toNat!.toUInt16

  let nc <- IO.Channel.new (α := Nat)

  let task1 <- IO.asTask (do IO.sleep 1000; IO.println "print task 1"; nc.sync.send 2; return 2;)
  let task2 <- IO.asTask (do
    let answer <- nc.sync.recv?;
    IO.println ("print task 2: " ++ (toString answer));
    return 2;)

  if mode == "client" then
    (client <| port) (args.get! 1)
  else if mode == "server" then
    server port
  else
    IO.println "Unknown mode"
    return ()



def Box (l: String) (x: Type) := Nat

class Key (l: String) where
  unwrap :  Box l x → x

def Box.unwrap [h: Key l]: Box l x → x := h.unwrap

def Store := List ((t: Type) × Nat × t)
--def Store.unwrap : Key l → Box l x → x
instance Key Store where unwrap := Store.unwrap

def fooCode [Key l] (x: Box l Nat) (y: Box r Nat): Nat :=
  x.unwrap + 1
