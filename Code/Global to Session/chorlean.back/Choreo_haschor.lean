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


--def Unwrap (l:String)  :=   {a:Type} -> a @ l -> a




def local_func (a:Type) (l:String):= (Unwrap l -> a)
def local_prog (a:Type) (l:String):= (Unwrap l -> IO a)

mutual
  inductive SesEff: Type -> Type 1 where
  | Send_recv [Serialize a]: {sender:String} -> a @ sender -> (receiver:String) -> SesEff (a @ receiver)
  | Cond [Serialize a]: a @ decider -> (a -> Session b) -> SesEff b

  inductive Session: Type -> Type 1  where
  | Do :  SesEff b -> Session a -> Session a
  | Return: a -> Session a
end


mutual
  inductive ChorEff: Type -> Type 1 where
  | Send_recv [Serialize a]: {sender:String} -> a @ sender -> (receiver:String) -> ChorEff (a @ receiver)
  | Local : (loc:String) -> ([∀ α, Coe (α @ l) α]  -> IO a) -> ChorEff (a @ loc)
  | Calc : (loc:String) -> (Unwrap loc -> a) -> ChorEff (a @ loc)
  | Cond [Serialize a]: a @ decider -> (a -> Choreo b) -> ChorEff b

  inductive Choreo: Type -> Type 1  where
  | Do :  ChorEff b -> (b -> Choreo a) -> Choreo a
  | Return: a -> Choreo a
end

inductive Choreo': Type -> Type 1 where
| Send_recv [Serialize a]: {sender:String} -> a @ sender -> (receiver:String) -> (a @ receiver -> Choreo' n) -> Choreo' n
| Local : (loc:String) -> (Unwrap loc -> IO a)  -> (a @ loc -> Choreo' n) -> Choreo' n
| Calc : (loc:String) -> (Unwrap loc -> a)  -> (a @ loc -> Choreo' n) -> Choreo' n
| Cond [Serialize a]: a @ decider -> (a -> Choreo b) -> (a @ receiver -> Choreo' n) -> Choreo' n
| Return: a -> Choreo' a

-- mutual
--   def ChorEff.toString: ChorEff a -> String
--   | ChorEff.Send_recv lv receiver => s!"send from l to {receiver}"
--   | ChorEff.Local loc comp => s!"comp at {loc}"
--   | ChorEff.Calc loc comp => s!"calc at {loc}"
--   | ChorEff.Cond lv cont => s!"cond???"

--   def Choreo.toString: Choreo a -> String
--   | Choreo.Do eff next => s!"do {eff.toString}\n"
--   | Choreo.Return _ => s!"end "
-- end


#check Choreo


def toChoreo (eff: ChorEff a) : Choreo a :=
   Choreo.Do eff (Choreo.Return)



def Choreo.bind: Choreo α → (α → Choreo β) → Choreo β
  | Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
  | Choreo.Return v, next' => next' v
decreasing_by sorry

def Choreo'.bind: Choreo' α → (α → Choreo' β) → Choreo' β
| Choreo'.Send_recv v receiver next, next' => Choreo'.Send_recv v receiver (fun x => bind (next x) next')
| Choreo'.Local loc comp next, next' => Choreo'.Local loc comp (fun x => bind (next x) next')
| Choreo'.Calc loc comp next, next' => Choreo'.Calc loc comp (fun x => bind (next x) next')
| Choreo'.Cond lv d next, next' => Choreo'.Cond lv d (fun x => bind (next x) next')
| Choreo'.Return v, next' => next' v


instance: Monad Choreo where
  pure x := Choreo.Return x
  bind  := Choreo.bind

instance: Monad Choreo' where
  pure x := Choreo'.Return x
  bind  := Choreo'.bind

--def send_recv {a:Type} [Serialize a] (vl: a @ sender) (receiver:String) (_dont_send_to_yourself: sender != receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def send_recv {a:Type} [Serialize a] (vl: a @ sender) (receiver:String) := toChoreo (ChorEff.Send_recv vl receiver)
def locally (loc: String) (comp: (Unwrap loc) -> IO b) := toChoreo (ChorEff.Local loc comp)
def compute (loc: String) (comp: (Unwrap loc) -> b) := toChoreo (ChorEff.Calc loc comp)
def branch {a:Type} [Serialize a] (lv: a @ decider) (cont: a -> Choreo b):= toChoreo (ChorEff.Cond lv cont)

def send_recv_locally {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> IO a) (_dont_send_to_yourself: sender != receiver := by decide):= do
  let lv <- toChoreo (ChorEff.Local sender comp)
  toChoreo (ChorEff.Send_recv lv receiver)

def send_recv_pure {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> a) (_dont_send_to_yourself: sender != receiver := by decide):= do
  let r := wrap (comp unwrap) sender
  toChoreo (ChorEff.Send_recv r receiver)


instance (a:Type): Inhabited (Network a) := sorry

mutual
  partial def ChorEff.epp: ChorEff a -> String -> Network a
  | ChorEff.Send_recv lv receiver (sender:=sender), l => do
    if (sender == receiver) then
      return wrap (unwrap lv) receiver
    if (sender == l) then
      send receiver (unwrap lv)
      return .Empty
    else if (receiver == l) then
      let response <- (recv sender)
      return wrap response receiver
    else
      return .Empty
  | ChorEff.Local l1 comp, l2 => do
    if j:( l1 == l2) then
      let res <- run (comp (unwrap))
      return wrap res l1
    else
      return .Empty
  | ChorEff.Calc l1 comp, l2 => do
    if j:( l1 == l2) then
      return wrap (comp (unwrap)) l1
    else
      return .Empty
  | ChorEff.Cond lv fn (decider:=decider), loc => do
    if (loc == decider) then
      let choice := (unwrap lv)
      broadcast choice
      (fn (unwrap lv)).epp loc
    else
      let choice <- (recv decider)
      (fn choice).epp loc

  partial def Choreo.epp: Choreo a -> String -> Network a
  | Choreo.Return v, _ => Network.Return v
  | Choreo.Do eff next, loc => do
    let res <- (eff.epp loc)
    Choreo.epp (next res) loc

end


def wrapped := wrap 3 "bob"
def unwrapped := unwrap wrapped (l:="bob")
#eval unwrapped



notation:55 lv "~>" receiver => send_recv lv receiver

notation:55 sender "~>" receiver "##" comp => send_recv_locally sender receiver comp
notation:55 sender "~>" receiver "pure" comp => send_recv_pure sender receiver comp
