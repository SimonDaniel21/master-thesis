import Test.my_utils
import chorlean.Network

inductive LocVal (α: Type) (loc: String) [Serialize α] where
| Wrap: α -> LocVal α loc
| Empty: LocVal α loc

instance [Serialize a]: ToString (LocVal a l) where
  toString := fun x => match x with
    | .Wrap v => toString v ++ "@" ++ toString l
    | .Empty => "Empty"

def wrap {a} (v:a) (l: String)[Serialize a]: LocVal a l:=
  LocVal.Wrap v

infixl:55 "@" => fun (a:Type) (l:String) [Serialize a] => LocVal a l

def unwrap [Serialize a]: (LocVal a l) -> a
| LocVal.Wrap v =>  v
| LocVal.Empty => panic!"tried to unwrap Value from different Location, this should NOT happen in an well typed program!"


def Unwrap (l:String) :=   {a:Type} -> [Serialize a] -> LocVal a l -> a



mutual
  inductive ChorEff: Type -> Type 1 where
  | Send_recv [Serialize a]: {sender:String} -> LocVal a sender -> (receiver:String) -> ChorEff (LocVal a receiver)
  | Local {a:Type} [Serialize a]: (loc:String) -> (Unwrap loc -> IO b) -> ChorEff (LocVal b loc)
  | Cond [Serialize a]: (decider:String) -> LocVal a decider -> (a -> Choreo b) -> ChorEff b

  inductive Choreo: Type -> Type 1  where
  | Do :  ChorEff b -> (b -> Choreo a) -> Choreo a
  | Return: a -> Choreo a
end





#check Choreo

def toChoreo (eff: ChorEff a) : Choreo a :=
   Choreo.Do eff (Choreo.Return)

def send_recv {a:Type} [Serialize a] (vl: LocVal a sender) (receiver:String) (_dont_send_to_yourself: sender != receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def locally {a:Type} [Serialize a]  (loc: String) (comp: (Unwrap loc) -> IO b) := toChoreo (ChorEff.Local (a:=a) loc comp)


infixl:55 "~>" => send_recv

def Choreo.bind: Choreo α → (α → Choreo β) → Choreo β
  | Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
  | Choreo.Return v, next' => next' v
decreasing_by sorry

instance: Monad Choreo where
  pure x := Choreo.Return x
  bind  := Choreo.bind

-- def ChorEff.run : ChorEff a -> IO a
-- | send_recv _ _ _ => do
--   return ()

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
    if (l1 == l2) then
      let res <- run (comp unwrap)
      return wrap res l1
    else
      return .Empty
  | ChorEff.Cond lv fn (decider:=decider), loc => do
    if (loc == decider) then
     (fn (unwrap lv)).epp loc
    else
      let res <- (recv decider)
      (fn res).epp loc



  def Choreo.epp: Choreo a -> String -> Network a
  | Choreo.Return v, _ => Network.Return v
  | Choreo.Do eff next, loc => do
    let res <- (eff.epp loc)
    Choreo.epp (next res) loc

end
decreasing_by sorry --TODO




def testChor (input: Nat @"client"): Choreo (LocVal Nat "client"):= do
  let input <- input ~> "server"

  return .Empty


inductive not_print where
| nothing: not_print

def fn_t :=   {a:Type} -> [ToString a] -> a -> String

def fn2: fn_t -> Unit := fun x => let temp:= x 33
  let temp2 := x ""
  ()

def silent_post: Choreo (LocVal String "alice"):= do

  let alice_nat: LocVal Nat "alice" := wrap 2 "alice"
  let alice_string := wrap "hello" "alice"

  let test := ChorEff.Local "alice" (a:=String) (fun un => do
    let test :=  toString (un alice_nat) ++ un alice_string
    IO.println "enter a message"
    let stdin <- IO.getStdin
    return <- stdin.getLine
  )
  let temp <- toChoreo test

  -- let input: LocVal String "alice" <- locally "alice" (fun un => do
  --   let test :=  toString (un alice_nat) ++ un alice_string
  --   IO.println "enter a message"
  --   let stdin <- IO.getStdin
  --   return <- stdin.getLine
  -- )
  --let msg <- locally "alice" fun un => return (un input) ++ "-alice_mut"

  --let msg <- send_recv msg "eve"
  --let msg <- locally "eve" fun un => return (un msg) ++ "-eve"

  --let msg <- send_recv msg "bob"
  --let msg <- locally "bob" fun un => return (un msg) ++ "-bob"

  --let msg <- send_recv msg "alice"
  return .Empty

def book_seller: Choreo (LocVal String "buyer"):= do
  let stdin_buyer <- locally "buyer" fun _ => return <- IO.getStdin

  let title <- locally "buyer" (fun _ => do
    IO.println "enter a book title:"
    let stdin <- IO.getStdin
    return <- stdin.getLine
  )
  let title <- title ~> "seller"
  let price <- locally "seller" (a:= Nat) (fun un => if (un title) == "Moby Dick" then return 100 else return 200)
  let msg <- locally "alice" (a:=String) fun un => return (un input) ++ "-alice_mut"

  let msg <- send_recv msg "eve"
  let msg <- locally "eve" fun un => return (un msg) ++ "-eve"

  let msg <- send_recv msg "bob"
  let msg <- locally "bob" fun un => return (un msg) ++ "-bob"

  let msg <- send_recv msg "alice"
  return msg



def client_epp (input: Nat) := (testChor (wrap input "client")).epp "client"
def server_epp := (testChor .Empty).epp "server"

def test_cfg_2 := local_cfg ["client", "server"] 3333

#print client_epp

def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network test_cfg mode
  let res <- ((silent_post).epp mode).run mode net
  IO.println (s!"res: {Serialize.pretty (unwrap res)}")
  return ()




def F.{u} (α : Type u) : Type u := Prod α α

#check F    -- Type u → Type u
#check #[3,4,5,6]
