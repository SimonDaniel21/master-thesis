import Test.my_utils
import chorlean.Network
import Std.Data.Option.Basic
--import Mathlib

inductive GVal (a:Type) (owner endpoint: String)  where
| Wrap:  (owner = endpoint) -> a -> GVal a owner endpoint
| Empty: (owner ≠ endpoint) -> GVal a owner endpoint

def GVal.unwrap {a:Type} {owner endpoint: String}: (g: GVal a owner endpoint) -> (h: owner = endpoint) -> a
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction



infixl:55 "@" => fun {endpoint:String} (a:Type) (loc:String) => GVal a loc endpoint

def Unwrap (owner endpoint: String) :=  {a:Type} -> GVal a owner endpoint -> a

-- inductive Choreo (endpoint:String): Type -> Type 1  where
-- --| Cond [Serialize a]: a @ decider -> (a -> Choreo b) -> Choreo b
-- | Do :  ChorEff b (endpoint:=endpoint) -> (b -> Choreo endpoint a) -> Choreo endpoint a
-- | Return: a -> Choreo endpoint a



inductive Choreo (endpoint:String): Type -> Type 1 where
| DoSend_recv [Serialize a]: {sender:String} -> GVal a sender endpoint -> (receiver:String) -> (GVal a receiver endpoint -> Choreo endpoint n) -> Choreo endpoint n
| DoLocal : (loc:String) -> ((loc = endpoint) -> IO a)  -> (GVal a loc endpoint-> Choreo endpoint n) -> Choreo endpoint n
--| Calc : (loc:String) -> (Unwrap loc -> a)  -> (a @ loc -> Choreo n) -> Choreo n
--| Cond {decider:String} [Serialize a]: a @ decider -> (a -> Choreo b) -> (b -> Choreo n) -> Choreo n
| Return: a -> Choreo endpoint a


def Choreo.bind (ep:String) {α β: Type}:  Choreo ep α → (α → Choreo ep β) → Choreo ep β
| Choreo.DoSend_recv v receiver next, next' => Choreo.DoSend_recv v receiver (fun x => bind ep (next x) next')
| Choreo.DoLocal loc comp next, next' => Choreo.DoLocal loc comp (fun x => bind ep (next x) next')
| Choreo.Return v, next' => next' v

instance (ep: String): Monad (Choreo ep) where
  pure x := Choreo.Return x
  bind  := Choreo.bind ep

--def send_recv {a:Type} [Serialize a] (vl: a @ sender) (receiver:String) (_dont_send_to_yourself: sender != receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def send_recv {a:Type} {endpoint sender: String} [Serialize a] (gv: GVal a sender endpoint) (receiver: String) := Choreo.DoSend_recv gv receiver (fun x => Choreo.Return x)
def locally {endpoint: String} (loc: String) (comp: (loc = endpoint) -> IO b) :=  Choreo.DoLocal loc comp (fun x => Choreo.Return x)
-- def compute {net: List abs_channel} (loc: String) (comp: (Unwrap loc) -> b) := toChoreo (ChorEff.Calc loc comp (net:=net))
-- def branch {net: List abs_channel} {a:Type} [Serialize a] (lv: a @ decider) (cont: a -> Choreo b):= toChoreo (ChorEff.Cond lv cont (net:=net))

-- def send_recv_locally {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> IO a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let lv <- toChoreo (ChorEff.Local sender comp)
--   toChoreo (ChorEff.Send_recv lv receiver)

-- def send_recv_pure {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let r := wrap (comp unwrap) sender
--   toChoreo (ChorEff.Send_recv r receiver)


def Choreo.epp {ep:String}: Choreo ep a -> Network a
| Choreo.DoSend_recv gv receiver next (sender:=sender) => do
  if h:(sender = ep) then
    let val := gv.unwrap h
    if h2:(receiver = ep) then
      (next (GVal.Wrap h2 val)).epp
    else
      send receiver val
      (next (GVal.Empty h2)).epp
  else if j:(receiver = ep) then
    let response <- (recv sender)
    (next (GVal.Wrap j response)).epp
  else
    (next (GVal.Empty j)).epp

| Choreo.DoLocal loc comp next => do
    if h:( loc = ep) then
      let res <- run (comp h)
      (next (GVal.Wrap h res)).epp
    else
      (next (GVal.Empty h)).epp
| Choreo.Return v => Network.Return v
| Choreo.Do eff next => do
  let res <- (eff.epp)
  have h: sizeOf (next res) < 1 + sizeOf eff := by sorry
  Choreo.epp (next res)

abbrev Choreo2 {a:Type}:= String -> Network a -> Type

--notation:55 lv "~>" receiver => send_recv lv receiver

--notation:55 sender "~>" receiver "##" comp => send_recv_locally sender receiver comp
--notation:55 sender "~>" receiver "pure" comp => send_recv_pure sender receiver comp

def silent_post (ep:String): Choreo ep (GVal (List String) "alice" ep):= do

  let input: String @ "alice" <- locally "alice" (fun _ => do
    IO.println "enter a message"
    return <- IO.getLine
  )

  let msg <- send_recv input "eve"
  let msg <- locally "eve" fun h => return [(msg.unwrap h), "eve"]

  let msg <- send_recv msg "bob"

  let msg <- locally "bob" fun h => return (msg.unwrap h).concat "bob"

  let msg <- send_recv msg "alice"
  let _a: Unit @ "alice" <- locally "alice" (fun h => do
    IO.println s!"alice ended with {msg.unwrap h}"
  )
  return msg


def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network test_cfg mode
  let temp := silent_post mode
  let endpoint_program: Choreo2 (GVal (List String) "alice") := temp.epp
  let res <- ((silent_post mode).epp).run mode net
  --IO.println (s!"res: {res}")
  return ()
