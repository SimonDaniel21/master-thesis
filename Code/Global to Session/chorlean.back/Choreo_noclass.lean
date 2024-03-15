import Test.my_utils
import chorlean.Network
import Std.Data.Option.Basic

inductive GVal (a:Type) (owner endpoint: String)  where
| Wrap:  (owner = endpoint) -> a -> GVal a owner endpoint
| Empty: (owner ≠ endpoint) -> GVal a owner endpoint

def GVal.wrap {a:Type} (owner endpoint: String) (v:a): GVal a owner endpoint:=
  if h:(owner = endpoint) then
    GVal.Wrap h v
  else
    GVal.Empty h

def GVal.unwrap {a:Type} {owner endpoint: String}: (g: GVal a owner endpoint) -> (h: owner = endpoint) -> a
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction

instance {loc ep: String} [ToString t]: ToString (GVal t loc ep) where
  toString x :=
    if h:(loc = ep) then
      let val := x.unwrap h
      toString val
    else
      "Empty"


infixl:55 "@" => fun {endpoint:String} (a:Type) (loc:String) => GVal a loc endpoint

def Unwrap (owner endpoint: String) :=  {a:Type} -> GVal a owner endpoint -> a

class Channel' (sender receiver ep: String) where
  -- send {t:Type} [Serialize t]: GVal t sender ep -> IO Unit
  -- recv [Serialize t]: IO (GVal t receiver ep)
  send_recv {t} [Serialize t]: GVal t sender ep -> IO (GVal t receiver ep)

structure Net' (ep: String) where
  channels: List ({s r:String} -> Channel' s r ep)

structure PhysChannel (sender receiver ep: String) where
  recv_sock: GVal Socket receiver ep
  send_sock: GVal Socket sender ep

instance {sender receiver ep: String}: Coe (PhysChannel sender receiver ep) (Channel' sender receiver ep) where
  coe pc :=
    ⟨
      fun x => do
        if h:(sender = ep) then
        let val := x.unwrap h
        if h2:(receiver = ep) then
          return GVal.Wrap h2 val
        else
          (pc.send_sock.unwrap h).send_val2 val
          return GVal.Empty h2
        else if j:(receiver = ep) then
          let msg <- (pc.recv_sock.unwrap j).recv_val2
          return GVal.Wrap j msg
        else
          return GVal.Empty j
    ⟩

def verbose_boilerplate {sender receiver ep: String}  (pc: PhysChannel sender receiver ep): Channel' sender receiver ep :=
  ⟨
    fun x => do
      if h:(sender = ep) then
      let val := x.unwrap h
      if h2:(receiver = ep) then
        return GVal.Wrap h2 val
      else
        (pc.send_sock.unwrap h).send_val2 val
        return GVal.Empty h2
      else if j:(receiver = ep) then
        let msg <- (pc.recv_sock.unwrap j).recv_val2
        return GVal.Wrap j msg
      else
        return GVal.Empty j
  ⟩



instance (pc: PhysChannel sender receiver ep): Channel' sender receiver ep where
  -- send x :=
  --   if h:(sender = ep) then
  --     (pc.send_sock.unwrap h).send_val2 (x.unwrap h)
  --   else
  --     return

  -- recv :=
  --   if h:(receiver = ep) then do
  --     let msg <- (pc.recv_sock.unwrap h).recv_val2
  --     return GVal.Wrap h msg
  --   else
  --     return GVal.Empty h

  send_recv x := do
    if h:(sender = ep) then
      let val := x.unwrap h
      if h2:(receiver = ep) then
        return GVal.Wrap h2 val
      else
        (pc.send_sock.unwrap h).send_val2 val
        return GVal.Empty h2
    else if j:(receiver = ep) then
      let msg <- (pc.recv_sock.unwrap j).recv_val2
      return GVal.Wrap j msg
    else
      return GVal.Empty j

structure Set2 (a: Type) [BEq a] where
  items: List a
  unique: ∀ (v: a), items.contains v -> ¬  (items.erase v).contains v

def my_set: Set2 Nat := ⟨[], by exact fun v a => (fun {b} => by decide) rfl⟩
def myset := {2,3,4}
structure Nett where
  channels: Set (String × String)
  p_sym: ∀ (l1 l2: String), channels.contains ⟨l1, l2⟩  -> channels.contains ⟨l2, l1⟩
  p_connected: ∀ (l: String), channels.contains ⟨l, ⟩  -> channels.contains ⟨l2, l1⟩

def phys_net (ep:String) := List ({sender receiver: String} -> PhysChannel sender receiver ep)


-- epp for initializing one network socket
def init_sending_channel (sender ep: String) (addr: Address):  IO (GVal Socket sender ep) := do
  if h:(sender = ep) then
    IO.println s!"waiting for"-- {sender} -> {receiver}"
    let sock <- addr.connect_to
    return GVal.Wrap h sock
  else
    return GVal.Empty h

def init_receiving_channel (receiver ep: String) (addr: Address):  IO (GVal Socket receiver ep) := do
  if h:(receiver = ep) then
    IO.println s!"waiting for"-- {sender} -> {receiver}"
    let sock <- addr.listen_on
    return GVal.Wrap h sock
  else
    return GVal.Empty h


-- epp for initializing one network socket
def init_channel' (sender receiver ep: String) (addr: Address):  IO (PhysChannel sender receiver ep) := do
  let recv_sock <- init_receiving_channel receiver ep addr
  let send_sock <- init_sending_channel sender ep addr
  return ⟨recv_sock, send_sock⟩


inductive ChorEff {endpoint:String} {net:Net' endpoint}: Type -> Type 1 where
| Send_recv [Serialize a]: {sender:String} -> GVal a sender endpoint  -> (receiver:String) -> (p: net.channels.contains (sender)) -> ChorEff (GVal a receiver endpoint)
| Local : (loc:String) -> ([∀ x, Coe (GVal x loc endpoint) x] -> IO a) -> ChorEff (GVal a loc endpoint)
| Calc : (loc:String) -> ([∀ x, Coe (GVal x loc endpoint) x] -> a) -> ChorEff (GVal a loc endpoint)

inductive Choreo (endpoint:String) {net:Net' endpoint}: Type -> Type 1  where
| Cond [Serialize a]: GVal a decider endpoint -> (a -> Choreo endpoint b) -> Choreo endpoint b
| Do :  ChorEff b (endpoint:=endpoint) -> (b -> Choreo endpoint a) -> Choreo endpoint a
| Return: a -> Choreo endpoint a

def Choreo.bind (ep:String) {net:Net'} {α β: Type}:  Choreo ep α (net:=net) → (α → Choreo ep β (net:=net)) → Choreo ep β (net:=net)
| Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind ep (next x) next')
| Choreo.Cond lv next, next' =>
  Choreo.Cond lv (fun x => bind ep (next x) next')
| Choreo.Return v, next' => next' v

instance (ep: String) {net:Net'}: Monad (Choreo ep (net:=net)) where
  pure x := Choreo.Return x
  bind  := Choreo.bind ep

def toChoreo {net:Net'} (endpoint:String) (eff: ChorEff a (endpoint:=endpoint) (net:=net)) : Choreo endpoint a (net:=net) :=
   Choreo.Do eff (Choreo.Return)

--def send_recv {a:Type} [Serialize a] (vl: a @ sender) (receiver:String) (_dont_send_to_yourself: sender != receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def send_recv {net:Net'} {a:Type} {endpoint sender: String} [Serialize a] (gv: GVal a sender endpoint) (receiver: String) (p: net.channels.contains (sender, receiver) := by decide) :=
  toChoreo endpoint (ChorEff.Send_recv gv receiver (net:= net) p)
def locally {net:Net'} {endpoint: String} (loc: String) (comp: [∀ x, Coe (GVal x loc endpoint) x] -> IO b) := toChoreo endpoint (ChorEff.Local loc comp (net:=net))
def compute {net:Net'} (loc: String) (comp: [∀ x, Coe (GVal x loc endpoint) x] -> b) := toChoreo endpoint (ChorEff.Calc loc comp (net:=net))
def branch {net:Net'} {endpoint: String}  {a:Type} [Serialize a] (gv: GVal a decider endpoint) (cont: a -> Choreo endpoint b (net:= net)):= Choreo.Cond gv cont
def branch' {net:Net'} {endpoint: String}  {a:Type} [Serialize b] (comp: [∀ x, Coe (GVal x decider endpoint) x] -> IO b) (cont: b -> Choreo endpoint a (net:= net)):=
  do
  let gv <- locally decider comp
  Choreo.Cond gv cont
def send_recv_comp {net:Net'} {a:Type} (endpoint: String) [Serialize b] (sender receiver: String) (comp: [∀ x, Coe (GVal x sender endpoint) x] -> IO b) (p: net.channels.contains (sender, receiver) := by decide) :=
  do
  let gv <- locally sender comp
  toChoreo endpoint (ChorEff.Send_recv gv receiver (net:= net) p)

-- def ChorEff.epp {ep:String}: ChorEff a (endpoint := ep)
--    -> Network a
-- | ChorEff.Send_recv gv receiver (sender:=sender) => do
--   if h:(sender = ep) then
--     let val := gv.unwrap h
--     if h2:(receiver = ep) then
--       return GVal.Wrap h2 val
--     else
--       send receiver val
--       return GVal.Empty h2
--   else if j:(receiver = ep) then
--     let response <- (recv sender)
--     return GVal.Wrap j response
--   else
--     return  GVal.Empty j

-- | ChorEff.Local loc comp => do
--     if h:( loc = ep) then

--       have (x:Type) : Coe (GVal x loc ep) x := ⟨fun gv => gv.unwrap h⟩
--       let res <- run comp
--       return GVal.Wrap h res
--     else
--       return  GVal.Empty h

-- | ChorEff.Calc loc comp => do
--     if h:( loc = ep) then
--       have (x:Type) : Coe (GVal x loc ep) x := ⟨fun gv => gv.unwrap h⟩
--       return GVal.Wrap h (comp)
--     else
--       return  GVal.Empty h

-- def Choreo.epp {ep:String}: Choreo ep a -> Network a
-- | Choreo.Cond gv cont (decider:= decider) (endpoint:=ep) => do
--   if h:(decider = ep) then
--     let choice := (gv.unwrap h)
--     broadcast choice
--     have p: sizeOf (cont (GVal.unwrap gv h)) < 1 + sizeOf decider + sizeOf gv := by sorry
--     (cont choice).epp
--   else
--     let choice <- (recv decider)
--     have p: sizeOf (cont choice) < 1 + sizeOf decider + sizeOf gv := by sorry
--     (cont choice).epp
-- | Choreo.Return v => Network.Return v
-- | Choreo.Do eff next => do
--   let res <- (eff.epp)
--   have h: sizeOf (next res) < 1 + sizeOf eff := by sorry
--   Choreo.epp (next res)


def ChorEff.epp {ep:String} {net:Net'}: ChorEff a (endpoint := ep) (net:=net)
   -> IO a
| ChorEff.Send_recv gv receiver p => do
  (net.channels.lookup (ep, receiver)).get p
  Channel'.send_recv gv

| ChorEff.Local loc comp => do
    if h:( loc = ep) then

      have (x:Type) : Coe (GVal x loc ep) x := ⟨fun gv => gv.unwrap h⟩
      let res <- comp
      return GVal.Wrap h res
    else
      return  GVal.Empty h

| ChorEff.Calc loc comp => do
    if h:( loc = ep) then
      have (x:Type) : Coe (GVal x loc ep) x := ⟨fun gv => gv.unwrap h⟩
      return GVal.Wrap h (comp)
    else
      return  GVal.Empty h

def Choreo.epp {ep:String}: Choreo ep a -> IO a
| Choreo.Cond gv cont (decider:= decider) (endpoint:=ep) => do
  if h:(decider = ep) then
    let choice := (gv.unwrap h)

    --broadcast choice
    have p: sizeOf (cont (GVal.unwrap gv h)) < 1 + sizeOf decider + sizeOf gv := by sorry
    (cont choice).epp
  else
    --let choice <- (recv decider)
    --have p: sizeOf (cont choice) < 1 + sizeOf decider + sizeOf gv := by sorry
    --(cont choice).epp
    return sorry
| Choreo.Return v => return v
| Choreo.Do eff next => do
  let res <- (eff.epp)
  have h: sizeOf (next res) < 1 + sizeOf eff := by sorry
  Choreo.epp (next res)

abbrev Choreo2 {a:Type}:= String -> Network a -> Type

notation:55 lv "~>" receiver => send_recv lv receiver

notation:55 sender "~>" receiver "#" comp => send_recv_comp sender receiver comp
--notation:55 sender "~>" receiver "pure" comp => send_recv_pure sender receiver comp


def cast_gv (gv: GVal a owner ep) [k:∀ x, Coe (GVal x owner ep) x]: a :=
  let c := k a
  c.coe gv

-- works similiar to normal coersion arrow ↑ but always casts to the underlying type
notation:55 "⤉" gv => cast_gv gv

syntax "send " ident " to " term (" as " ident)?: doElem
macro_rules
| `(doElem|send $i to $r) => `(doElem| let $i:ident := <- (send_recv $i $r))
| `(doElem|send $i to $r as $y) => `(doElem| let $y:ident := <- (send_recv $i $r))

abbrev net22 (ep:String) (ns: List (String × String)) := [∀ (x: (String× String)), ns.contains x -> Channel' x.fst x.snd ep]
#check net22
#check Channel' "" "" ""

def tmm: List (String × String) := [("alice", "bob")]

def silent_post (ep:String)
  (k: List (Channel' "" "" ""))
  [∀ (x: (String× String)), tmm.contains x -> Channel' x.fst x.snd ep]
  [Channel' "alice" "eve" ep] [Channel' "eve" "bob" ep] [Channel' "bob" "alice" ep]:
  Choreo ep (GVal (List String) "alice" ep):= do

  let input: String @ "alice" <- locally "alice" do
    IO.println "enter a message"
    return <- IO.getLine


  let msg <- input ~> "eve"
  let msg <- locally "eve" do
    return [↑msg, "eve"]

  let msg <- send_recv msg "bob"

  let msg <- locally "bob" do
    return (⤉msg).concat "bob"

  let msg <- send_recv msg "alice"
  let _a: Unit @ "alice" <- locally "alice" do
    IO.println s!"alice ended with {⤉msg}"

  return msg

abbrev netT (ep: String) := List ({sender receiver: String} -> Channel' sender receiver ep)

structure Net2 (ep: String) where
  cs: List ((sender receiver: String) -> Channel' sender receiver ep)


def tt: List ((s:String) -> Nat) := [fun x => 3 ]

def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network test_cfg mode

  have k: Channel' "alice" "eve" mode := <- init_channel' "alice" "eve" mode ( .v4 (.mk 127 0 0 1) 1200)
  have: Channel' "eve" "bob" mode := <- init_channel' "eve" "bob" mode ( .v4 (.mk 127 0 0 1) 1201)
  have: Channel' "bob" "alice" mode := <- init_channel' "bob" "alice" mode ( .v4 (.mk 127 0 0 1) 1202)

  let testn: netT mode := [k]

  let res <- ((silent_post mode).epp)
  IO.println (s!"res: {res}")

  let te := ["hello", "world"]
  let te2 <- te.mapM (fun x => IO.println x)
  return ()


-- def testio: IO Unit := do
--   let te := ["hello", "world"]
--   let te2 <- te.filterMap (fun x => IO.println x)
--   return ()

-- #eval testio
