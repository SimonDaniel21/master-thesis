import Test.my_utils
import chorlean.Network

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

def Unwrap (l:String) :=   {a:Type} -> a @ l -> a



mutual
  inductive ChorEff: Type -> Type 1 where
  | Send_recv [Serialize a]: {sender:String} -> a @ sender -> (receiver:String) -> ChorEff (a @ receiver)
  | Local : (loc:String) -> (Unwrap loc -> IO a) -> ChorEff (a @ loc)
  | Calc : (loc:String) -> (Unwrap loc -> a) -> ChorEff (a @ loc)
  | Cond [Serialize a]: a @ decider -> (a -> Choreo b) -> ChorEff b

  inductive Choreo: Type -> Type 1  where
  | Do :  ChorEff b -> (b -> Choreo a) -> Choreo a
  | Return: a -> Choreo a
end


#check Choreo

def toChoreo (eff: ChorEff a) : Choreo a :=
   Choreo.Do eff (Choreo.Return)

def send_recv {a:Type} [Serialize a] (vl: a @ sender) (receiver:String) (_dont_send_to_yourself: sender != receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def locally (loc: String) (comp: (Unwrap loc) -> IO b) := toChoreo (ChorEff.Local loc comp)
def compute (loc: String) (comp: (Unwrap loc) -> b) := toChoreo (ChorEff.Calc loc comp)
def branch {a:Type} [Serialize a] (lv: a @ decider) (cont: a -> Choreo b):= toChoreo (ChorEff.Cond lv cont)


infixl:55 "~>" => send_recv

def Choreo.bind: Choreo α → (α → Choreo β) → Choreo β
  | Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
  | Choreo.Return v, next' => next' v
decreasing_by sorry

instance: Monad Choreo where
  pure x := Choreo.Return x
  bind  := Choreo.bind

mutual
  def ChorEff.epp: ChorEff a -> String -> Network a
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
      let res := (comp (unwrap))
      return wrap res l1
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

  def Choreo.epp: Choreo a -> String -> Network a
  | Choreo.Return v, _ => Network.Return v
  | Choreo.Do eff next, loc => do
    let res <- (eff.epp loc)
    Choreo.epp (next res) loc

end
decreasing_by sorry --TODO
