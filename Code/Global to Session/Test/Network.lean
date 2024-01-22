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


def local_cfg: (locs: List String) -> UInt16 -> (missing: List String := locs) -> Cfg
| _, _, [] => []
| all, p, l::ls => local_cfg_for l all p ++ local_cfg all (p + UInt16.ofNat (all.length - 1)) ls


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

instance (loc: String) (n: Net): MonadLift Network IO where
  monadLift := fun x => Network.run x loc n


def toNetwork (eff: NetEff a): Network a :=
  Network.Do eff (Network.Return)

def send {a:Type} (loc: String) (v:a) [Serialize a]:= toNetwork (NetEff.send loc v)
def recv {a:Type} (loc: String) [Serialize a]:= toNetwork (NetEff.recv loc (a:=a))

def data: UInt16 := 2

def Net_Alice (s: String): Network Nat := do
  send "eve" (s ++ "-alice")
  let res: Nat <- recv "bob"
  return res

def Net_Bob: Network (Unit) := do
  let s: String <- recv "eve"
  send "bob" (s ++ "-bob")

def Net_Eve: Network Unit := do
  let s: String <- recv "alice"
  send "eve" (s ++ "-eve")


def test_cfg := local_cfg ["alice", "bob", "eve"] 6665

#eval test_cfg
--2-2
--3-6
--4-12
--5-20

-- epp for initializing one network socket
def init_channel (loc sender receiver: String) (addr: address):  IO (Option Channel) := do
  if sender == receiver then
    throw (IO.Error.userError "cannot init a channel where sender == receiver")
  else if (loc == sender) then
    IO.println s!"waiting for {sender} -> {receiver}"
    let sock <- addr.connect_to
    return some ((sender,receiver), sock)
  else if (loc == receiver) then
    IO.println s!"waiting for {sender} -> {receiver}"
    let sock <- addr.listen_on
    return some ((sender,receiver), sock)
  else return none


-- epp for initializing fully meshed network sockets
def init_network: Cfg -> String -> IO Net
| ((sender, receiver), addr)::as, loc => do
  let chn_opt <- init_channel loc sender receiver  addr
  match chn_opt with
  | some chnl =>
    let rest <- init_network as loc
    return [chnl] ++ rest
  | none => init_network as loc
| [], _ => do
  IO.println "finished network initilization"
  return []


def main (args : List String): IO Unit := do

  let mode := args.get! 0
  let net <- init_network test_cfg mode
  if mode == "alice" then
    let r <- (Net_Alice (args.get! 1)).run  "alice" net
    IO.println (s!"res {Serialize.pretty r}")
  else if mode == "bob" then
    Net_Bob.run "bob" net
  else if mode == "eve" then
    Net_Eve.run "eve" net
  else
    IO.println "Unknown Location"