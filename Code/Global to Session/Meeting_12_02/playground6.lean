import Test.my_utils
import chorlean.Network
import Std.Data.Option.Basic
import Mathlib

inductive GVal (a:Type) (owner endpoint: String)  where
| Wrap:  (owner = endpoint) -> a -> GVal a owner endpoint
| Empty: (owner ≠ endpoint) -> GVal a owner endpoint

def GVal.unwrap {a:Type} {owner endpoint: String}: (g: GVal a owner endpoint) -> (h: owner = endpoint) -> a
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction



infixl:55 "@" => fun {endpoint:String} (a:Type) (loc:String) => GVal a loc endpoint

def Unwrap (owner endpoint: String) :=  {a:Type} -> GVal a owner endpoint -> a

inductive ChorEff {endpoint:String}: Type -> Type 1 where
| Send_recv [Serialize a]: {sender:String} -> GVal a sender endpoint  -> (receiver:String) -> ChorEff (GVal a receiver endpoint)
| Local : (loc:String) -> ((loc = endpoint) -> IO a) -> ChorEff (GVal a loc endpoint)
-- | Calc : (loc:String) -> (Unwrap loc -> a) -> ChorEff (a @ loc)

inductive Choreo (endpoint:String): Type -> Type 1  where
--| Cond [Serialize a]: a @ decider -> (a -> Choreo b) -> Choreo b
| Do :  ChorEff b (endpoint:=endpoint) -> (b -> Choreo endpoint a) -> Choreo endpoint a
| Return: a -> Choreo endpoint a

def Choreo.bind (ep:String) {α β: Type}:  Choreo ep α → (α → Choreo ep β) → Choreo ep β
| Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind ep (next x) next')
-- | Choreo.Cond lv next, next' =>
--   Choreo.Cond lv (fun x => bind (next x) next')
| Choreo.Return v, next' => next' v


instance (ep: String): Monad (Choreo ep) where
  pure x := Choreo.Return x
  bind  := Choreo.bind ep

def toChoreo (endpoint:String) (eff: ChorEff a (endpoint:=endpoint)) : Choreo endpoint a :=
   Choreo.Do eff (Choreo.Return)

--def send_recv {a:Type} [Serialize a] (vl: a @ sender) (receiver:String) (_dont_send_to_yourself: sender != receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def send_recv {a:Type} {endpoint sender: String} [Serialize a] (gv: GVal a sender endpoint) (receiver: String) := toChoreo endpoint (ChorEff.Send_recv gv receiver )
def locally {endpoint: String} (loc: String) (comp: (loc = endpoint) -> IO b) := toChoreo endpoint (ChorEff.Local loc comp)
-- def compute {net: List abs_channel} (loc: String) (comp: (Unwrap loc) -> b) := toChoreo (ChorEff.Calc loc comp (net:=net))
-- def branch {net: List abs_channel} {a:Type} [Serialize a] (lv: a @ decider) (cont: a -> Choreo b):= toChoreo (ChorEff.Cond lv cont (net:=net))

-- def send_recv_locally {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> IO a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let lv <- toChoreo (ChorEff.Local sender comp)
--   toChoreo (ChorEff.Send_recv lv receiver)

-- def send_recv_pure {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let r := wrap (comp unwrap) sender
--   toChoreo (ChorEff.Send_recv r receiver)

def ChorEff.epp {ep:String}: ChorEff a (endpoint := ep)
   -> Network a
| ChorEff.Send_recv gv receiver (sender:=sender) => do
  if h:(sender = ep) then
    let val := gv.unwrap h
    if h2:(receiver = ep) then
      return GVal.Wrap h2 val
    else
      send receiver val
      return GVal.Empty h2
  else if j:(receiver = ep) then
    let response <- (recv sender)
    return GVal.Wrap j response
  else
    return  GVal.Empty j

| ChorEff.Local loc comp => do
    if h:( loc = ep) then
      let res <- run (comp h)
      return GVal.Wrap h res
    else
      return  GVal.Empty h

def Choreo.epp {ep:String}: Choreo ep a -> Network a
| Choreo.Return v => Network.Return v
| Choreo.Do eff next => do
  let res <- (eff.epp)
  have h: sizeOf (next res) < 1 + sizeOf eff := by sorry
  Choreo.epp (next res)



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
  let endpoint_program := temp.epp
  let res <- ((silent_post mode).epp).run mode net
  --IO.println (s!"res: {res}")
  return ()
