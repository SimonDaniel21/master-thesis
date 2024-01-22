import Test.my_utils

abbrev Cfg := List ((String × String) × (address))
abbrev Channel := (String × String) × Socket

abbrev Net:= List (Channel)
def test: address :=  .v4 ((.mk 127 0 0 1)) 33
def tc: Cfg := [(("client", "server"), test)]

def local_cfg_for: String -> List String -> UInt16 -> Cfg
| _, [], _ => []
| loc, l::ls, p =>
  if (l == loc) then
    local_cfg_for loc ls p
  else
    [((loc, l), .v4 ((.mk 127 0 0 1)) p)] ++ local_cfg_for loc ls (p+1)


def init_net: String -> List String -> UInt16 -> Cfg
| _, [], _ => []
| loc, l::ls, p =>
  if (l == loc) then
    local_cfg_for loc ls p
  else
    [((loc, l), .v4 ((.mk 127 0 0 1)) p)] ++ local_cfg_for loc ls (p+1)

class T (α: Type) where
  fn: Unit

inductive A  where
| e (α: Type) [T α]: A

def fn: A -> Unit
| A.e v => ()

inductive NetEff : Type -> Type 1 where
| send {a: Type} [Serialize a]: String -> a -> NetEff Unit
| broadcast {a: Type} [Serialize a]: List String -> a -> NetEff Unit
| recv {a: Type} [Serialize a]: String -> NetEff a

inductive Network (a:Type) where
| Do    : NetEff b -> (b -> Network a ) -> Network a
| Return: a ->  Network a

def NetEff.run : NetEff a -> String -> Net -> IO a
| NetEff.send receiver v, sender, c => do
  let sock_opt := c.lookup (sender, receiver)
  match sock_opt with
  | some sock =>
    sock.send_ v
  | none =>
    throw (IO.Error.userError s!"cannot find addr {sender} x {receiver} in cfg for send")
| NetEff.recv sender, receiver, c => do
  let sock_opt := c.lookup (sender, receiver)
  match sock_opt with
  | some sock =>
    sock.recv_
  | none =>
    throw (IO.Error.userError s!"cannot find location {sender} x {receiver} in cfg for receive")
| NetEff.broadcast (l::ls) v, sender, c => do
  (NetEff.send l v).run sender c
  (NetEff.broadcast ls v).run sender c
| NetEff.broadcast [] _, _ ,c => do
  return ()




def Network.run : Network a -> String -> Net ->  IO a
| Do eff next, loc, net => do
  let res <- eff.run loc net
  (next res).run loc net
| Return v, _, _ => do
  return v

def Network.bind : Network α → (α → Network β) → Network β
  | .Do eff next, next' => .Do eff (fun x => bind (next x) next')
  | .Return v, next' => next' v

instance: Monad Network where
  pure x := Network.Return x
  bind  := Network.bind

instance (loc: String) (c: Cfg): MonadLift Network IO where
  monadLift := fun x => Network.run x loc c


def toNetwork (eff: NetEff a): Network a :=
  Network.Do eff (Network.Return)

def send {a:Type} (loc: String) (v:a) [Serialize a]:= toNetwork (NetEff.send loc v)
def recv {a:Type} (loc: String) [Serialize a]:= toNetwork (NetEff.recv loc (a:=a))

def data: UInt16 := 2

def Net_Alice: Network Nat := do
  send "eve" 55
  --let res: Nat <- recv "alice"
  return 4

def Net_Bob: Network (Unit) := do
  --let res: Nat <- recv "bob"
  send "eve" (3)

def Net_Eve: Network Unit := do
  let res: Nat <- recv "eve"
  --send "alice" (res+1)


def test_cfg := init_net "alice" ["alice", "bob", "eve", "", "2"] 6665

#eval test_cfg.length
--2-2
--3-6
--4-12
--5-20

-- epp for initializing one network socket
def init_channel (loc sender receiver: String) (addr: address):  IO (Option Channel) := do
  if sender == receiver then
    throw (IO.Error.userError "cannot init a channel where sender == receiver")
  else if (loc == sender) then
    let sock <- addr.connect_to
    return some ((sender,receiver), sock)
  else if (loc == receiver) then
    let sock <- addr.listen_on
    return some ((sender,receiver), sock)
  else return none


-- epp for initializing fully meshed network socketsq
def init_network: Cfg -> String -> IO Net
| ((sender, receiver), addr)::as, loc => do
  let chn_opt <- init_channel loc sender receiver  addr
  match chn_opt with
  | some chnl =>
    let rest <- init_network as loc
    return [chnl] ++ rest
  | none => init_network as loc
| [], _ => do
  return []


def main (args : List String): IO Unit := do

  let mode := args.get! 0
  if mode == "alice" then
    let r <- Net_Alice.run test_cfg
    IO.println (s!"res {Serialize.pretty r}")
  else if mode == "bob" then
    Net_Bob.run test_cfg
  else if mode == "eve" then
    Net_Eve.run test_cfg
  else
    IO.println "Unknown Location"
