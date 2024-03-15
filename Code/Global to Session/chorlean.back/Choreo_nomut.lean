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

def LocVal.isEmpty: LocVal a l -> Bool
| LocVal.Wrap _ =>  false
| LocVal.Empty => true

def LocVal.notEmpty (lv:LocVal a l):  Bool := ! lv.isEmpty

def unwrap (lv: a @ l) (_ex: lv.notEmpty := sorry):  a := match lv with
| LocVal.Wrap v =>  v


def Unwrap (l:String)  :=   {a:Type} -> a @ l -> a

def local_func (a:Type) (l:String):= (Unwrap l -> a)
def local_prog (a:Type) (l:String):= (Unwrap l -> IO a)




inductive Choreo: Type -> Type 1 where
| Send_recv [Serialize a]: {sender:String} -> a @ sender -> (receiver:String) -> (a @ receiver -> Choreo n) -> Choreo n
| Local : (loc:String) -> (Unwrap loc -> IO a)  -> (a @ loc -> Choreo n) -> Choreo n
| Calc : (loc:String) -> (Unwrap loc -> a)  -> (a @ loc -> Choreo n) -> Choreo n
| Cond {decider:String} [Serialize a]: a @ decider -> (a -> Choreo b) -> (b -> Choreo n) -> Choreo n
| Return: a -> Choreo a


def Choreo.bind: Choreo α → (α → Choreo β) → Choreo β
| Choreo.Send_recv v receiver next, next' => Choreo.Send_recv v receiver (fun x => bind (next x) next')
| Choreo.Local loc comp next, next' => Choreo.Local loc comp (fun x => bind (next x) next')
| Choreo.Calc loc comp next, next' => Choreo.Calc loc comp (fun x => bind (next x) next')
| Choreo.Cond lv d next, next' => Choreo.Cond lv d (fun x => bind (next x) next')
| Choreo.Return v, next' => next' v

instance: Monad Choreo where
  pure x := Choreo.Return x
  bind  := Choreo.bind


--def send_recv {a:Type} [Serialize a] (vl: a @ sender) (receiver:String) (_dont_send_to_yourself: sender != receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def send_recv {a:Type} {sender:String} [Serialize a] (vl: a @ sender) (receiver:String) := Choreo.Send_recv vl receiver (fun x => Choreo.Return x)
def locally (loc: String) (comp: (Unwrap loc) -> IO b) := Choreo.Local loc comp (fun x => Choreo.Return x)
def compute (loc: String) (comp: (Unwrap loc) -> b) := Choreo.Calc loc comp (fun x => Choreo.Return x)
def branch {a:Type} {decider:String} [Serialize a] (lv: a @ decider) (cont: a -> Choreo b) :=
  let temp:= (fun x => Choreo.Return x (a:=b))
  Choreo.Cond (a:=a) (b:=b) lv cont temp

-- def send_recv_locally {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> IO a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let lv <- toChoreo (ChorEff.Local sender comp)
--   toChoreo (ChorEff.Send_recv lv receiver)

-- def send_recv_pure {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let r := wrap (comp unwrap) sender
--   toChoreo (ChorEff.Send_recv r receiver)

def Choreo.epp: Choreo a -> (s:String) ->
  (∀ (a:Type) (loc:String) (lv: a @ loc),
    ((loc == s) -> lv.notEmpty)
    ∧ ((loc != s) -> lv.isEmpty))

  -> Network a

| Choreo.Send_recv lv receiver (sender:=sender) next, ep, p => do
  if h:(sender == ep) then
    let v := (unwrap lv (by simp [p, h]))
    if (sender == receiver) then
      (next (wrap v receiver)).epp ep p
    else
      send receiver v
      (next .Empty).epp ep p

  else if (receiver == ep) then
    let response <- (recv sender)
    let temp := wrap response receiver
    (next temp).epp ep p
  else
    (next .Empty).epp ep p
| Choreo.Local l1 comp next, l2, p => do
  if j:( l1 == l2) then
    let un: Unwrap l1 := unwrap
    let res <- run (comp (un))
    let temp := wrap res l1
    (next temp).epp l2 p
  else
    (next .Empty).epp l2 p
| Choreo.Calc l1 comp next, l2, p => do
  if j:( l1 == l2) then
    let un: Unwrap l1 := unwrap
    let temp :=  wrap (comp (un)) l1
    (next temp).epp l2 p
  else
    (next .Empty).epp l2 p
| Choreo.Cond lv fn next (decider:=decider), loc, p => do
  if (loc == decider) then
    let choice := (unwrap lv (by sorry))
    broadcast choice
    let temp <- (fn choice).epp loc p
    (next temp).epp loc p
  else
    let choice <- (recv decider)
    --(fn choice).epp loc
    let temp <- (fn choice).epp loc p
    (next temp).epp loc p
| Choreo.Return v, _, _ => Network.Return v


def wrapped := wrap 3 "bob"
def unwrapped := unwrap wrapped (l:="bob")
#eval unwrapped



notation:55 lv "~>" receiver => send_recv lv receiver

-- notation:55 sender "~>" receiver "##" comp => send_recv_locally sender receiver comp
-- notation:55 sender "~>" receiver "pure" comp => send_recv_pure sender receiver comp
