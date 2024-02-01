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

def unwrap (lv: a @ l) (_ex: exists_locally lv := by decide):  a := match lv with
| LocVal.Wrap v =>  v

def Unwrap (l:String) := {a:Type} -> (lv: a @ l) -> (j: exists_locally lv) -> a

def testa := Unwrap "inge"
def inge := "inge"
def testu: Unwrap inge := fun x p => unwrap x (l:="inge") p
def testw := wrap 23 "inge"

def testApp := testu testw

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
  | Send_recv [Serialize a]: {sender:String} -> (lv:a @ sender) -> (j:exists_locally lv := by decide) -> (receiver:String) -> ChorEff (a @ receiver)
  | Local : (loc:String) -> (Unwrap loc -> IO a) -> ChorEff (a @ loc)
  | Calc : (loc:String) -> (Unwrap loc -> a) -> ChorEff (a @ loc)
  | Cond [Serialize a]: (lv: a @ decider) -> (j:exists_locally lv := by decide) -> (a -> Choreo b) -> ChorEff b

  inductive Choreo: Type -> Type 1  where
  | Do :  ChorEff b -> (b -> Choreo a) -> Choreo a
  | Return: a -> Choreo a
end


#check Choreo


def toChoreo (eff: ChorEff a) : Choreo a :=
   Choreo.Do eff (Choreo.Return)



def Choreo.bind: Choreo α → (α → Choreo β) → Choreo β
  | Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
  | Choreo.Return v, next' => next' v
decreasing_by sorry

instance: Monad Choreo where
  pure x := Choreo.Return x
  bind  := Choreo.bind

def send_recv {a:Type} [Serialize a] (lv: a @ sender) (receiver:String) (p:exists_locally lv := by decide):= toChoreo (ChorEff.Send_recv lv p receiver)
def locally (loc: String) (comp: (Unwrap loc) -> IO b) := toChoreo (ChorEff.Local loc comp)
def compute (loc: String) (comp: (Unwrap loc) -> b) := toChoreo (ChorEff.Calc loc comp)
def branch {a:Type} [Serialize a] (lv: a @ decider) (p:exists_locally lv := by decide) (cont: a -> Choreo b):= toChoreo (ChorEff.Cond lv p cont)

-- def send_recv_locally {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> IO a) (p:exists_locally lv := by decide) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let lv <- toChoreo (ChorEff.Local sender comp)
--   toChoreo (ChorEff.Send_recv lv p receiver)

-- def send_recv_pure {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let un: Unwrap sender := fun x p => unwrap x p
--   let r := wrap (comp un) sender
--   toChoreo (ChorEff.Send_recv r receiver)


mutual
  def ChorEff.epp: ChorEff a -> String -> Network a
  | ChorEff.Send_recv (a:=a) lv p receiver  (sender:=sender), l => do
    if k:(sender == receiver) then
      return wrap (unwrap lv p) receiver
    if (sender == l) then
      send receiver (unwrap lv p)
      return .Empty
    else if (receiver == l) then
      let response <- (recv sender)
      return wrap response receiver
    else
      return .Empty
  | ChorEff.Local l1 comp, l2 => do
    if j:( l1 == l2) then
      let un: Unwrap l1 := fun x p => unwrap x p
      let res <- run (comp (un))
      return wrap res l1
    else
      return .Empty
  | ChorEff.Calc l1 comp, l2 => do
    if j:( l1 == l2) then
      let un: Unwrap l1 := fun x p => unwrap x p
      return wrap (comp (un)) l1
    else
      return .Empty
  | ChorEff.Cond lv p fn (decider:=decider), loc => do
    if (loc == decider) then
      let choice := (unwrap lv p)
      broadcast choice
      (fn (unwrap lv p)).epp loc
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
def wrapped := wrap 3 "bob"
def unwrapped := unwrap wrapped (l:="bob")
#eval unwrapped



notation:55 lv "~>" receiver => send_recv lv receiver

-- notation:55 sender "~>" receiver "##" comp => send_recv_locally sender receiver comp
-- notation:55 sender "~>" receiver "pure" comp => send_recv_pure sender receiver comp


def silent_post: Choreo (String @"alice"):= do

  let input: LocVal String "alice" <- locally "alice" (fun un => do
    IO.println "enter a message"
    let stdin <- IO.getStdin
    return <- stdin.getLine
  )

  let msg <- locally "alice" fun un => return (un input sorry) ++ "-alice_mut"


  let msg <- send_recv msg "eve" sorry

  let msg <- locally "eve" fun un => return (un msg sorry) ++ "-eve"

  let msg <- send_recv msg "bob" sorry
  let msg <- locally "bob" fun un => return (un msg sorry) ++ "-bob"

  let msg <- send_recv msg "alice" sorry
  return msg
