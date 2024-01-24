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

-- this mutual is kind of ugly because it has to be explicetely parameterized over 2 types and locations,
-- without mutual type parameters can be taken implicetely
-- mutual
--   inductive ChorEff (a:Type) [i1: Serialize a] {b:Type}  {loc1 loc2:String}   [i2: Serialize b]  where
--   | Send_recv: (l1:String) -> LocVal a l1  -> ChorEff a
--   | Local : ((LocVal a loc -> a) -> IO a) -> ChorEff a
--   | Cond: LocVal b loc2 -> (b -> Choreo a) -> ChorEff a

--   inductive Choreo (a: Type)[i1: Serialize a] {b:Type}{loc1 loc2:String}    [i2: Serialize b]  where
--   | Do:  ChorEff a (b:=b) (loc1:=loc1) (loc2:=loc2) -> (c -> Choreo a) -> Choreo a
--   | Return: a -> Choreo a
-- end

inductive ChorEff : (Type) -> Type 1 where
| Send_recv {a: Type} [Serialize a]: (l1:String) -> LocVal a l1 -> (l2:String) -> ChorEff (LocVal a l2)
| Local {a:Type} [Serialize a]: (l:String) -> ((LocVal a l -> a) -> IO a) -> ChorEff (LocVal a l)

inductive Choreo (a: Type) where
| Do    : ChorEff b -> (b -> Choreo a ) -> Choreo a
| Return: a -> Choreo a

def toChoreo  (eff: ChorEff a) : Choreo a :=
   Choreo.Do eff (Choreo.Return)

def send_recv {a:Type} [Serialize a] (l1: String) (vl: LocVal a l1) (l2:String):= toChoreo (ChorEff.Send_recv l1 vl l2)
def locally {a:Type} [Serialize a] (l: String) (comp: (LocVal a l -> a) -> IO a) := toChoreo (ChorEff.Local l comp)

def Choreo.bind: Choreo α → (α → Choreo β) → Choreo β
  | Choreo.Do eff next, next' => .Do eff (fun x => bind (next x) next')
  | Choreo.Return v, next' => next' v

instance: Monad Choreo where
  pure x := Choreo.Return x
  bind  := Choreo.bind

def ChorEff.epp: ChorEff a -> String -> Network a
| ChorEff.Send_recv sender lv receiver (a:=a), l => do
  if (sender == receiver) then
    return wrap (unwrap lv) receiver
  if (sender == l) then
    send receiver (unwrap lv)
    return .Empty
  else if (receiver == l) then
    let response <- (recv sender (a:= a))
    return wrap response receiver
  else
    return .Empty
| ChorEff.Local l1 comp, l2 => do
  if (l1 == l2) then
    let res <- run (comp unwrap)
    return wrap res l1
  else
    return .Empty

def Choreo.epp: Choreo a -> String -> Network a
| Choreo.Return v, _ => Network.Return v
| Choreo.Do eff next, loc => do
  let res <- (eff.epp loc)
  Choreo.epp (next res) loc

def silent_post: Choreo (LocVal String "alice"):= do
  let input <- locally "alice" (fun _ => do
    IO.println "enter a message"
    let stdin <- IO.getStdin
    return <- stdin.getLine
  )
  let msg: (LocVal Nat "alice") <- locally "alice" (fun un => do
    return 2
  )
  let msg <- send_recv "alice" msg "eve"

  let msg <- locally "eve" (fun un => do
    return (un msg) ++ "-eve"
  )
  let msg <- send_recv "eve" msg "bob"

  let msg <- locally "bob" (fun un => do
    return (un msg) ++ "-bob"
  )
  let msg <- send_recv "bob" msg "alice"
  return msg

def test_cfg_2 := local_cfg ["client", "server"] 3333

def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network test_cfg mode
  let res <- ((silent_post).epp mode).run mode net
  IO.println (s!"res: {Serialize.pretty (unwrap res)}")
  return ()
