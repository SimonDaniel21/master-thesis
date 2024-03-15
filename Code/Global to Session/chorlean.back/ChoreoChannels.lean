import Test.my_utils
import chorlean.Network
import Std.Data.Option.Basic
--import Mathlib

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

infixl:55 "@" => fun {endpoint:String} (a:Type) (loc:String) => GVal a loc endpoint

def Unwrap (owner endpoint: String) :=  {a:Type} -> GVal a owner endpoint -> a

inductive ChorEff {endpoint:String}: Type -> Type 1 where
| Send_recv [Serialize a] [SendChannel]: {sender:String} -> GVal a sender endpoint  -> (receiver:String) -> ChorEff (GVal a receiver endpoint)
| Local : (loc:String) -> ([∀ x, Coe (GVal x loc endpoint) x] -> IO a) -> ChorEff (GVal a loc endpoint)
| Calc : (loc:String) -> ([∀ x, Coe (GVal x loc endpoint) x] -> a) -> ChorEff (GVal a loc endpoint)

inductive Choreo (endpoint:String): Type -> Type 1  where
| Cond [Serialize a]: GVal a decider endpoint -> (a -> Choreo endpoint b) -> Choreo endpoint b
| Do :  ChorEff b (endpoint:=endpoint) -> (b -> Choreo endpoint a) -> Choreo endpoint a
| Return: a -> Choreo endpoint a

def Choreo.bind (ep:String) {α β: Type}:  Choreo ep α → (α → Choreo ep β) → Choreo ep β
| Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind ep (next x) next')
| Choreo.Cond lv next, next' =>
  Choreo.Cond lv (fun x => bind ep (next x) next')
| Choreo.Return v, next' => next' v

instance (ep: String): Monad (Choreo ep) where
  pure x := Choreo.Return x
  bind  := Choreo.bind ep

def toChoreo (endpoint:String) (eff: ChorEff a (endpoint:=endpoint)) : Choreo endpoint a :=
   Choreo.Do eff (Choreo.Return)

--def send_recv {a:Type} [Serialize a] (vl: a @ sender) (receiver:String) (_dont_send_to_yourself: sender != receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def send_recv {a:Type} {endpoint sender: String} [Serialize a] (gv: GVal a sender endpoint) (receiver: String) := toChoreo endpoint (ChorEff.Send_recv gv receiver )
def locally {endpoint: String} (loc: String) (comp: [∀ x, Coe (GVal x loc endpoint) x] -> IO b) := toChoreo endpoint (ChorEff.Local loc comp)
def compute (loc: String) (comp: [∀ x, Coe (GVal x loc endpoint) x] -> b) := toChoreo endpoint (ChorEff.Calc loc comp)
def branch {endpoint: String}  {a:Type} [Serialize a] (gv: GVal a decider endpoint) (cont: a -> Choreo endpoint b):= Choreo.Cond gv cont
def branch' {endpoint: String}  {a:Type} [Serialize b] (comp: [∀ x, Coe (GVal x decider endpoint) x] -> IO b) (cont: b -> Choreo endpoint a):=
  do
  let gv <- locally decider comp
  Choreo.Cond gv cont
def send_recv_comp {a:Type} (endpoint: String) [Serialize b] (sender receiver: String) (comp: [∀ x, Coe (GVal x sender endpoint) x] -> IO b)  :=
  do
  let gv <- locally sender comp
  toChoreo endpoint (ChorEff.Send_recv gv receiver)

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

      have (x:Type) : Coe (GVal x loc ep) x := ⟨fun gv => gv.unwrap h⟩
      let res <- run comp
      return GVal.Wrap h res
    else
      return  GVal.Empty h

| ChorEff.Calc loc comp => do
    if h:( loc = ep) then
      have (x:Type) : Coe (GVal x loc ep) x := ⟨fun gv => gv.unwrap h⟩
      return GVal.Wrap h (comp)
    else
      return  GVal.Empty h

def Choreo.epp {ep:String}: Choreo ep a -> Network a
| Choreo.Cond gv cont (decider:= decider) (endpoint:=ep) => do
  if h:(decider = ep) then
    let choice := (gv.unwrap h)
    broadcast choice
    have p: sizeOf (cont (GVal.unwrap gv h)) < 1 + sizeOf decider + sizeOf gv := by sorry
    (cont choice).epp
  else
    let choice <- (recv decider)
    have p: sizeOf (cont choice) < 1 + sizeOf decider + sizeOf gv := by sorry
    (cont choice).epp
| Choreo.Return v => Network.Return v
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

-- def silent_post (ep:String): Choreo ep (GVal (List String) "alice" ep):= do

--   let input: String @ "alice" <- locally "alice" do
--     IO.println "enter a message"
--     return <- IO.getLine


--   let msg <- input ~> "eve"
--   let msg <- locally "eve" do
--     return [↑msg, "eve"]

--   let msg <- send_recv msg "bob"

--   let msg <- locally "bob" do
--     return (⤉msg).concat "bob"

--   let msg <- send_recv msg "alice"
--   let _a: Unit @ "alice" <- locally "alice" do
--     IO.println s!"alice ended with {⤉msg}"

--   return msg
