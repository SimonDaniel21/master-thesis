import Test.my_utils
import Std.Data.Option.Basic

def dbg_prints := true

abbrev Cfg := List ((String × String) × (Address))
abbrev Channel := (String × String)
abbrev ChannelSocket := Channel × Socket

abbrev LCfg := Lean.AssocList String Address
--abbrev LNet := List String

structure LNet where
  sending: List (String)
  receiving: List (String)

structure SendableLoc (net:LNet) where
  s: String
  p: (net.sending.contains s)

structure ReceivableLoc (net:LNet) where
  s: String
  p: (net.receiving.contains s)

-- @[reducible] def LNet.at (net:LNet) (loc:NetLoc net):=
--   (net.find? loc.s).get loc.p




abbrev sym := true
abbrev uni := false

def gen_fullmesh_cfg_for: String -> List String -> (port:UInt16:=3333) -> Cfg
| _, [], _ => []
| loc, l::ls, p =>
  if (l == loc) then
    gen_fullmesh_cfg_for loc ls p
  else
    [((loc, l), .v4 ((.mk 127 0 0 1)) p)] ++ gen_fullmesh_cfg_for loc ls (p+1)


-- creates a fully meshed net configuration
def gen_fullmesh_cfg: (locs: List String) -> (port:UInt16:=3333) -> (missing: List String := locs) -> Cfg
| _, _, [] => []
| all, p, l::ls => gen_fullmesh_cfg_for l all p ++ gen_fullmesh_cfg all (p + UInt16.ofNat (all.length - 1)) ls


-- creates a net cfg from pairs of (Location) Strings, and an additional bool that,
-- if set two true will create a channel in the opposing direction aswell
def gen_cfg: (locs: List ((String × String) × Bool)) -> (port:UInt16:=3333) -> Cfg
| [], p => []
| ((s, r), bidirectional)::ls, p =>
  let cs := [((s, r), .v4 ((.mk 127 0 0 1)) p)]
  if (bidirectional) then
    let p := p+1
    let cs := cs ++ [((r, s), .v4 ((.mk 127 0 0 1)) p)]
    cs ++ gen_cfg ls (p+1)
  else
    cs ++ gen_cfg ls (p+1)


class T (α: Type) where
  fn: Unit

inductive A  where
| e (α: Type) [T α]: A

def fn: A -> Unit
| A.e v => ()


inductive NetEff {cfg: LCfg} : LNet -> Type  -> Type 1  where
| C_Open (c: (String × Address)) {net:LNet}:  NetEff (net.concat c.fst) Unit
| C_Close (c:Channel) {net:LNet}: NetEff net Unit
| Run {a: Type} {net:LNet}:  IO a -> NetEff net a
| Send {a: Type} {net:LNet} [Serialize a]: SendableLoc net -> a -> NetEff net Unit
| Broadcast {a: Type} {net:LNet} [Serialize a]: a -> NetEff net Unit
| Broadcast_except {a: Type} {net:LNet} [Serialize a]: List String -> a -> NetEff net Unit
| Recv {a: Type} {net:LNet} [Serialize a]: ReceivableLoc net -> NetEff net a

inductive Network (a:Type) where
| Do  {net:LNet} {cfg:LCfg}: NetEff net b  -> ( b -> Network a )-> Network a
| Return: a ->  Network a


-- def NetEff.toString : NetEff a -> String -> String
-- | NetEff.Run _comp, loc=> s!"{loc} does computation"
-- | NetEff.Send receiver v, sender=> s!"{sender} sends {Serialize.pretty v} to {receiver}"
-- | NetEff.Recv sender (a:=b), receiver => s!"{receiver} receives {Serialize.type_name b} from {sender}"
-- | NetEff.Broadcast  v, sender => s!"broadcast"
-- | NetEff.Broadcast_except  v _, sender => s!"broadcast"


-- function that takes a Value, Net and LocString and returns a program that sends the value to
-- all channels that the LocString can send to in the Net

structure PhysNet where
  sending: Lean.AssocList String Socket
  receiving: Lean.AssocList String Socket

def NetEff.run : NetEff net a (cfg:=cfg) -> (pnet: PhysNet) ->
  (∀ (s:String), net.receiving.contains s -> (pnet.receiving.find? s).isSome)
  ∧ (∀ (s:String), net.sending.contains s -> (pnet.sending.find? s).isSome)
  ->  IO a
| NetEff.Run comp (a:=a), pnet, p => do
  if dbg_prints then
    IO.println s!"computing"
  comp
| NetEff.Send receiver v, pnet, p => do
  if dbg_prints then
    IO.println s!"send to {receiver.s} ({Serialize.pretty v})"
  let sock := (pnet.sending.find? receiver.s).get (by simp [receiver.p, p])
  sock.send_val2 v

| NetEff.Recv (a:=_t) sender, pnet, p => do
  if dbg_prints then
    IO.println s!"recv from {sender.s} :{Serialize.type_name _t}"
  let sock := (pnet.receiving.find? sender.s).get (by simp [sender.p, p])
  sock.recv_val2

| NetEff.Broadcast v, pnet, p => do

  for x in net.sending do
    let sock := (pnet.sending.find? x).get (by sorry)
    if dbg_prints then
      IO.println s!"broadcast to {x} ({Serialize.pretty v})"
    sock.send_val2 v

| NetEff.Broadcast_except es v,pnet, p => do
   for x in net.sending do
    let sock := (pnet.sending.find? x).get (by sorry)
    if dbg_prints then
      IO.println s!"broadcast to {x} ({Serialize.pretty v})"
    sock.send_val2 v

| NetEff.C_Open c, pnet, p => do
  IO.println s!"open channel to {c.fst}"

| NetEff.C_Close c, pnet, p  => do
   IO.println s!"close channel"



def Network.run : Network a -> (net: LNet) -> (pnet: PhysNet) ->
  (∀ (s:String), net.receiving.contains s -> (pnet.receiving.find? s).isSome)
  ∧ (∀ (s:String), net.sending.contains s -> (pnet.sending.find? s).isSome)
| Do eff next, loc, net, pnet, p => do
  let res <- eff.run loc net
  (next res).run loc net
| Return v, _, _, _, _ => do
  return v

def Network.bind : Network α → (α → Network β) → Network β
  | .Do eff next, next' => .Do eff (fun x => bind (next x) next')
  | .Return v, next' => next' v

instance: Monad Network where
  pure x := Network.Return x
  bind  := Network.bind

instance (loc: String) (n: Net): MonadLift Network IO where
  monadLift := fun x => Network.run x loc n


-- def toNetwork (eff: NetEff a): Network a :=
--   Network.Do eff (Network.Return (a:=a))


-- def run {a:Type} (comp: IO a) := toNetwork (NetEff.Run comp)
-- def send {a:Type} (loc: String) (v:a) [Serialize a]:= toNetwork (NetEff.Send loc v)
-- def broadcast {a:Type} (v:a) [Serialize a]:= toNetwork (NetEff.Broadcast v)
-- def broadcast_except {a:Type} (es: List String) (v:a) [Serialize a]:= toNetwork (NetEff.Broadcast_except es v)
-- def recv {a:Type} (loc: String) [Serialize a]:= toNetwork (NetEff.Recv loc (a:=a))
-- def send_mult {a:Type} (locs: List String) (v:a) [Serialize a] : Network Unit := match locs with
-- | [] => return ()
-- | l::ls  => do
--   send l v
--   send_mult ls v


def data: UInt16 := 2

def Net_Alice (s: String): Network String := do
  send "eve" (s ++ "-alice")
  let res: String <- recv "bob"
  return res

def Net_Bob: Network (Unit) := do
  let s: String <- recv "eve"
  send "alice" (s ++ "-bob")

def Net_Eve: Network Unit := do
  let s: String <- recv "alice"
  send "bob" (s ++ "-eve")


def test_cfg := gen_fullmesh_cfg ["alice", "bob", "eve"] 6665

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
  IO.println "finished network initilization\n"
  return []


def main_ (args : List String): IO Unit := do

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
