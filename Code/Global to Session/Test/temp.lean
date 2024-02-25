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

inductive Choreo: List ChannelC -> Type -> Type 1 where
| Send_recv (c: ChannelC) : (p: cs.contains c := by decide) -> Choreo cs n
| Create (c:ChannelC) : Choreo (cs.concat c) n -> (p: !(cs.contains c) := by decide) -> Choreo cs n
| Return: a -> Choreo cs a

inductive Induct : List String → Type where
| Use : (s : String) -> (p : ls.contains s:= by decide) ->  Induct ls
| Add : (s : String) -> Induct (ls.concat s) -> (p : !(ls.contains s):= by decide) -> Induct ls
| Rmv : (s : String) -> Induct (ls.erase s) -> (p : (ls.contains s):= by decide) -> Induct ls

def t11 := Induct.Add (ls := []) "hello" (Induct.Use "hello") -- does not fill in (by decide) automatically
def t21 := Induct.Add (ls := []) "hello" (Induct.Use "hello") -- works


def t23 := Induct.Add (ls := []) "hello" (Induct.Rmv "hello" (Induct.Add "hello" (Induct.Use "hello"))) -- works

def test : "a" == "b" := by rfl

def test2 : "a" == "b" :=
  try
  by decide



#check decide

def c1 :=

  Choreo.Create ("alice", "bob") (cs := []) (n:=Nat)
     (Choreo.Create ("alice", "bob")
        (Choreo.Send_recv ("alice", "bob")) )


def c2 := c1 (Choreo.Create ("alice", "bob") (n:=Nat))

def Choreo.bind {α: (List ChannelC) -> Type}: Choreo (α) → (α → Choreo β) → Choreo β
| Choreo.Send_recv lv next , next' => Choreo.Send_recv lv (fun x => bind (next x) next')
| Choreo.create c next, next' => Choreo.create c (bind (next) next')
| Choreo.Return v, next' => next' v

instance: Monad Choreo where
  pure x := Choreo.Return x
  bind  := Choreo.bind

abbrev CChoreo := StateT (List ChannelC) Choreo

--def send_recv {a:Type} [Serialize a] (vl: a @ sender) (receiver:String) (_dont_send_to_yourself: sender != receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def send_recv {a:Type} {sender:String} [Serialize a] (vl: a @ sender) (receiver:String) := Choreo'.Send_recv vl receiver (fun x => Choreo'.Return x)
-- def locally (loc: String) (comp: (Unwrap loc) -> IO b) := Choreo'.Local loc comp (fun x => Choreo'.Return x)
-- def compute (loc: String) (comp: (Unwrap loc) -> b) := Choreo'.Calc loc comp (fun x => Choreo'.Return x)
-- def branch {a:Type} {decider:String} [Serialize a] (lv: a @ decider) (cont: a -> Choreo' b) :=
--   let temp:= (fun x => Choreo'.Return x (a:=b))
--   Choreo'.Cond (a:=a) (b:=b) lv cont temp

def open_channel (c: ChannelC): CChoreo Unit := do
  let s <- get
  set (s.concat c)
  return ()

def close_channel (c: ChannelC): CChoreo Unit := do
  let s <- get
  set (s.erase c)
  return ()
-- def send_recv_locally {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> IO a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let lv <- toChoreo (ChorEff.Local sender comp)
--   toChoreo (ChorEff.Send_recv lv receiver)

-- def send_recv_pure {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let r := wrap (comp unwrap) sender
--   toChoreo (ChorEff.Send_recv r receiver)

def Choreo'.epp: Choreo' a -> String -> Network a
| Choreo'.Send_recv lv receiver (sender:=sender) next, l => do
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
| Choreo'.Local l1 comp next, l2 => do
  if j:( l1 == l2) then
    let res <- run (comp (unwrap))
    let temp := wrap res l1
    (next temp).epp l2
  else
    (next .Empty).epp l2
| Choreo'.Calc l1 comp next, l2 => do
  if j:( l1 == l2) then
    let temp :=  wrap (comp (unwrap)) l1
    (next temp).epp l2
  else
    (next .Empty).epp l2
| Choreo'.Cond lv fn next (decider:=decider), loc => do
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
| Choreo'.Return v, _ => Network.Return v


def wrapped := wrap 3 "bob"
def unwrapped := unwrap wrapped (l:="bob")
#eval unwrapped



notation:55 lv "~>" receiver => send_recv lv receiver

-- notation:55 sender "~>" receiver "##" comp => send_recv_locally sender receiver comp
-- notation:55 sender "~>" receiver "pure" comp => send_recv_pure sender receiver comp
