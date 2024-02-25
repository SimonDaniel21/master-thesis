import Test.my_utils
import chorlean.Network


@[reducible] def LocVal (α: Type) (loc: String): Type := Nat
infixl:55 "@" => LocVal


class Key (l: String) where
  unwrap : x @ l → x

def LocVal.unwrap [h: Key l]: x @ l → x := h.unwrap

 def Store := List ((t: Type)  × t)

def test_store: Store := [(List, [])]

def Store.insert (store: Store (t:=ta)): (v:t) -> Store (t:=ta) :=
  s ++ s

def unwrap :  LocVal x l → x
|  0 => _
| 1 =>

def test: Nat @ "client" := 35
#check Nat @ "client"

instance [Serialize a]: ToString (a @ l) where
  toString := fun x => match x with
    | .Wrap v => toString v ++ "@" ++ toString l
    | .Empty => "Empty"

def notEmpty: LocVal a l -> Bool
| LocVal.Wrap _ =>  true
| LocVal.Empty => false

def valid (a:Type) (loc:String) := { vl: a @ loc // notEmpty vl }
infixl:55 "#@" => valid


def valid.bind: valid a1 @ l1 → (b → valid a2 @ l2) → valid a2 @ l2
| ⟨ lv, p ⟩ => match lv with
  | .Wrap v, f => v
  | .Failure, _f => .Failure

def wrap {a} (v:a) (l: String): a #@ l :=
  ⟨ LocVal.Wrap v, by trivial ⟩


def unwrap: a #@ l -> a
| ⟨ lv, _ ⟩ => match lv with
  | .Wrap v => v



def Unwrap (l:String)  :=   {a:Type} -> a @ l -> a #@ l

def local_func (a:Type) (l:String):= (Unwrap l -> a)
def local_prog (a:Type) (l:String):= (Unwrap l -> IO a)

abbrev abs_channel := (String × String)

mutual
  inductive ChorEff {net: List abs_channel}: Type -> Type 1 where
  | Send_recv [Serialize a]: {sender:String} -> a @ sender -> (receiver:String) -> (contains_channel: net.contains (sender, receiver) := by decide) -> ChorEff (a @ receiver)
  | Local : (loc:String) -> (Unwrap loc -> IO a) -> ChorEff (a @ loc)
  | Calc : (loc:String) -> (Unwrap loc -> a) -> ChorEff (a @ loc)
  | Cond [Serialize a]: a @ decider -> (a -> Choreo b) -> ChorEff b

  inductive Choreo {net: List abs_channel}: Type -> Type 1  where
  | Do :  ChorEff b -> (b -> Choreo a) -> Choreo a
  | Return: a -> Choreo a
end



def toChoreo (eff: (ChorEff a (net:=net))) : Choreo a (net:=net) :=
   Choreo.Do eff (Choreo.Return)



def Choreo.bind: Choreo α (net:=net) → (α → Choreo β (net:=net)) → Choreo β (net:=net)
  | Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
  | Choreo.Return v, next' => next' v
decreasing_by sorry

instance: Monad (Choreo (net:=net)) where
  pure x := Choreo.Return x
  bind  := Choreo.bind

--def send_recv {a:Type} [Serialize a] (vl: a @ sender) (receiver:String) (_dont_send_to_yourself: sender != receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def send_recv {a:Type} {net: List abs_channel} [Serialize a] (vl: a @ sender) (receiver:String) (contains_channel: net.contains (sender, receiver) := by decide) := toChoreo (ChorEff.Send_recv vl receiver contains_channel (net:=net))
def locally {net: List abs_channel} (loc: String) (comp: (Unwrap loc) -> IO b) := toChoreo (ChorEff.Local loc comp (net:=net))
def compute {net: List abs_channel} (loc: String) (comp: (Unwrap loc) -> b) := toChoreo (ChorEff.Calc loc comp (net:=net))
def branch {net: List abs_channel} {a:Type} [Serialize a] (lv: a @ decider) (cont: a -> Choreo b):= toChoreo (ChorEff.Cond lv cont (net:=net))

-- def send_recv_locally {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> IO a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let lv <- toChoreo (ChorEff.Local sender comp)
--   toChoreo (ChorEff.Send_recv lv receiver)

-- def send_recv_pure {a:Type} [Serialize a] (sender receiver:String) (comp: (Unwrap sender) -> a) (_dont_send_to_yourself: sender != receiver := by decide):= do
--   let r := wrap (comp unwrap) sender
--   toChoreo (ChorEff.Send_recv r receiver)



def temp:= do
  let a: Option Nat := none
  let b: Option Nat := some 1
  let c := (<-a) + (<-b)
  return c

mutual

  def ChorEff.epp_vars: ChorEff a (net:=net) -> (loc:String) -> List a #@ loc -> Network a
  | ChorEff.Send_recv lv receiver contains_channel (sender:=sender), l, env => do
    if h: (sender == receiver) then
      let unwr := (unwrap ⟨ lv,  sorry⟩ )
      return wrap (unwrap ⟨ lv,  sorry⟩ ) receiver
    if (sender == l) then
      send receiver (unwrap lv)
      return .Empty
    else if (receiver == l) then
      let response <- (recv sender)
      return wrap response receiver
    else
      return .Empty
  | ChorEff.Local l1 comp, l2, env => do
    if j:( l1 == l2) then
      let res <- run (comp (unwrap))
      return wrap res l1
    else
      return .Empty
  | ChorEff.Calc l1 comp, l2, env => do
    if j:( l1 == l2) then
      return wrap (comp (unwrap)) l1
    else
      return .Empty
  | ChorEff.Cond lv fn (decider:=decider), loc, env => do
    if (loc == decider) then
      let choice := (unwrap lv)
      broadcast choice
      (fn (unwrap lv)).epp loc
    else
      let choice <- (recv decider)
      (fn choice).epp loc

  def Choreo.epp: Choreo a (net:=net) -> String -> Network a
  | Choreo.Return v, _ => Network.Return v
  | Choreo.Do eff next, loc => do
    let res <- (eff.epp loc)
    Choreo.epp (next res) loc

end


mutual



  def ChorEff.epp: ChorEff a (net:=net) -> String -> Network a
  | ChorEff.Send_recv lv receiver contains_channel (sender:=sender), l => do
    if h: (sender == receiver) then
      let unwr := (unwrap ⟨ lv,  sorry⟩ )
      return wrap (unwrap ⟨ lv,  sorry⟩ ) receiver
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

  def Choreo.epp: Choreo a (net:=net) -> String -> Network a
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

--notation:55 sender "~>" receiver "##" comp => send_recv_locally sender receiver comp
--notation:55 sender "~>" receiver "pure" comp => send_recv_pure sender receiver comp


def test_net: List abs_channel :=
  [
    ("alice", "eve"),
    ("eve", "bob"),
    ("bob", "alice")
  ]

def silent_post: Choreo ((List String) @"alice") (net:= test_net):= do

  let input: String @ "alice" <- locally "alice" (fun _ => do
    IO.println "enter a message"
    return <- IO.getLine
  )

  let msg <- input ~> "eve"
  let msg <- locally "eve" fun un => return [(un msg), "eve"]

  let msg <- msg ~> "bob"

  let msg <- locally "bob" fun un => return (un msg).concat "bob"

  let msg <- send_recv msg "alice"
  return msg


def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network test_cfg mode
  let res <- ((silent_post).epp mode).run mode net
  IO.println (s!"res: {res}")
  return ()
