import Test.my_utils
import chorlean.Network
--import Mathlib

inductive LocVal (α: Type) (loc: String) where
| Wrap: α -> LocVal α loc
| Empty: LocVal α loc


infixl:55 "@" => LocVal

instance [Serialize a]: ToString (a @ l) where
  toString := fun x => match x with
    | .Wrap v => toString v ++ "@" ++ toString l
    | .Empty => "Empty"

def wrap {a} (v:a) (l: String): a @ l:=
  LocVal.Wrap v

def exists_locally: LocVal a l -> Bool
| LocVal.Wrap _ =>  true
| LocVal.Empty => false

def unwrap (lv: a @ l) (_ex: exists_locally lv :=sorry):  a := match lv with
| LocVal.Wrap v =>  v


def Unwrap (l:String)  :=   {a:Type} -> a @ l -> a

def local_func (a:Type) (l:String):= (Unwrap l -> a)
def local_prog (a:Type) (l:String):= (Unwrap l -> IO a)

abbrev ChannelC := (String × String)


inductive Choreo: (List ChannelC) -> Type -> Type 1 where
| Send_recv {cs: List ChannelC} [Serialize a]: {sender:String} -> a @ sender -> (receiver:String) -> (a @ receiver -> Choreo cs n) -> (p:(cs.contains (sender, receiver)) := by decide) -> Choreo cs n
| Local {cs: List ChannelC} : (loc:String) -> (Unwrap loc -> IO a)  -> (a @ loc -> Choreo cs n) -> Choreo cs n
| Calc {cs: List ChannelC} : (loc:String) -> (Unwrap loc -> a)  -> (a @ loc -> Choreo cs n) -> Choreo cs n
| Cond {cs dcs: List ChannelC} {decider:String} [Serialize a]: a @ decider -> (a -> Choreo dcs b) -> (b -> Choreo cs n) -> Choreo cs n
| C_Open {cs: List ChannelC}: (c:ChannelC) ->  Choreo (cs.concat c) n -> (p: !(cs.contains c) := by decide) -> Choreo cs n
| C_Close {cs: List ChannelC}: (c:ChannelC) ->  Choreo (cs.erase c) n -> (p: (cs.contains c) := by decide) -> Choreo cs n
| Return : a -> Choreo cs a

-- graded monad ?
-- paramerized monad
-- indexed monad
def Choreo.bind {α β : Type}:  Choreo cs α → (α → Choreo cs β) → Choreo cs β
| Choreo.Send_recv v receiver next, next' => Choreo.Send_recv v receiver (fun x => bind (next x) next')
| Choreo.Local loc comp next, next' => Choreo.Local loc comp (fun x => bind (next x) next')
| Choreo.Calc loc comp next, next' => Choreo.Calc loc comp (fun x => bind (next x) next')
| Choreo.Cond lv d next, next' => Choreo.Cond lv d (fun x => bind (next x) next')
| Choreo.C_Open c next, next' =>
  let t1 := next
  Choreo.C_Open c (bind next next')
| Choreo.Return v, next' => next' v

instance {cs: List ChannelC}: Monad (Choreo cs) where
  pure x := Choreo.Return x
  bind  := sorry


--def send_recv {a:Type} [Serialize a] (vl: a @ sender) (receiver:String) (_dont_send_to_yourself: sender != receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def send_recv {a:Type} {cs: List ChannelC} {sender:String} [Serialize a] (vl: a @ sender) (receiver:String) (p:(cs.contains (sender, receiver)) := by decide) := Choreo.Send_recv vl receiver (fun x => Choreo.Return x) p (cs:=cs)
def locally {cs: List ChannelC} (loc: String) (comp: (Unwrap loc) -> IO b) := Choreo.Local loc comp (fun x => Choreo.Return x) (cs:=cs)
def compute {cs: List ChannelC} (loc: String) (comp: (Unwrap loc) -> b) := Choreo.Calc loc comp (fun x => Choreo.Return x) (cs:=cs)
def branch {a:Type} {cs: List ChannelC} {decider:String} [Serialize a] (lv: a @ decider) (cont: a -> Choreo cs b) :=
  let temp:= (fun x => Choreo.Return x (a:=b) (cs := cs))
  Choreo.Cond (a:=a) (b:=b) lv cont temp
-- def open_channel {a:Type} {cs: List ChannelC} (c: ChannelC)  := Choreo.C_Open c (cs:=cs) (n:=a)
-- def close_channel {a:Type} {cs: List ChannelC} (c: ChannelC)  := Choreo.C_Close c (cs:=cs) (n:=a)


-- def send_recv_locally {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> IO a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let lv <- toChoreo (ChorEff.Local sender comp)
--   toChoreo (ChorEff.Send_recv lv receiver)

-- def send_recv_pure {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let r := wrap (comp unwrap) sender
--   toChoreo (ChorEff.Send_recv r receiver)Network


def Choreo.epp: Choreo cs a -> String -> Network a
| Choreo.Send_recv lv receiver (sender:=sender) next p, l => do
  if (sender == receiver) then
    let temp := wrap (unwrap lv) receiver
    (next temp).epp l

  else if (sender == l) then
    send receiver (unwrap lv)
    (next .Empty).epp l
  else if (receiver == l) then
    let response <- (recv sender)
    let temp := wrap response receiver
    (next temp).epp l
  else
    (next .Empty).epp l
| Choreo.Local l1 comp next, l2 => do
  if j:( l1 == l2) then
    let res <- run (comp (unwrap))
    let temp := wrap res l1
    (next temp).epp l2
  else
    (next .Empty).epp l2
| Choreo.Calc l1 comp next, l2 => do
  if j:( l1 == l2) then
    let temp :=  wrap (comp (unwrap)) l1
    (next temp).epp l2
  else
    (next .Empty).epp l2
| Choreo.Cond lv fn next (decider:=decider), loc => do
  if (loc == decider) then
    let choice := (unwrap lv)
    broadcast choice
    let temp <- (fn choice).epp loc
    (next temp).epp loc
  else
    let choice <- (recv decider)
    --(fn choice).epp loc
    let temp <- (fn choice).epp loc
    (next temp).epp loc
| Choreo.C_Open c n p, loc =>
  n.epp loc
| Choreo.C_Close c n p, loc =>
  n.epp loc
| Choreo.Return v, _ => Network.Return v

def wrapped := wrap 3 "bob"
def unwrapped := unwrap wrapped (l:="bob")
#eval unwrapped



notation:55 lv "~>" receiver => send_recv lv receiver

-- notation:55 sender "~>" receiver "##" comp => send_recv_locally sender receiver comp
-- notation:55 sender "~>" receiver "pure" comp => send_recv_pure sender receiver comp


def silent_post_ugly :=
  Choreo.Local "alice" (cs := [])  (fun _ => do
    IO.println "enter a message"
    return <- IO.getLine
  )
  (fun input => .C_Open ("alice", "eve")
  (.Send_recv input "eve"
  (fun msg => .C_Open ("alice", "bob")
  (.C_Close ("alice", "eve")
  (.C_Open ("eve", "alice")
  (.Send_recv input "bob"
  (fun msg =>
  (.Return msg))))))))


def silent_post: Choreo [("alice", "eve"), ("eve", "bob")] ((List String) @"alice"):= do

  let input: String @ "alice" <- locally "alice" (fun _ => do
    IO.println "enter a message"
    return <- IO.getLine
  )

  let msg <- input ~> "eve"
  let msg <- locally "eve" fun un => return [(un msg), "eve"]

  -- start connection and change type of choreo

  let msg <- send_recv msg "bob"
  let msg <- locally "bob" fun un => return (un msg).concat "bob"

  let msg <- send_recv msg "alice"
  return msg
