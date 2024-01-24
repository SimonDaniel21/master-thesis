import Test.my_utils
import chorlean.Network

-- Location Type, using a String on Type level
inductive LocTy: String → Type where
| named n: LocTy n

inductive LocVal (α: Type) (loc: String) [Serialize α] where
| Wrap: α -> LocVal α loc
| Empty: LocVal α loc


#check (fun (x:Nat) (y:Nat) => x+y)

#check LocVal.Wrap 3

instance: ToString (LocTy l) where
  toString := fun x => match x with
    | LocTy.named l => l


instance [Serialize a]: ToString (LocVal a l) where
  toString := fun x => match x with
    | .Wrap v => toString v ++ "@" ++ toString l
    | .Empty => "Empty"


#eval LocVal.Wrap 2 (loc := "client")

@[reducible] def located (α:Type) (l: String): Type:= (α × LocTy l)


def wrap {a} (v:a) (l: String)[Serialize a]: LocVal a l:=
  LocVal.Wrap v

infixl:55 "@" => fun (a:Type) (l:String) [Serialize a] => LocVal a l

def unwrap [Serialize a]: (LocVal a l) -> a
| LocVal.Wrap v =>  v
| LocVal.Empty => panic!"tried to unwrap Value from different Location, this should NOT happen in an well typed program!"

-- def unwrap [Serialize a]: (a @ l) -> [ Inhabited a] -> a
-- | LocVal.Wrap v =>  v
-- | LocVal.Empty => panic!"tried to unwrap Value from different Location, this should NOT happen in an well typed program!"


--def Unwrap a l [Serialize a]:= (LocVal a l -> a) -> IO a

-- inductive ChorEff : (Type) -> Type 1 where
-- | Send_recv {a: Type} [Serialize a]: (l1:String) -> LocVal a l1 -> (l2:String) -> ChorEff (LocVal a l2)
-- | Local {a:Type} [Serialize a]: (l:String) -> ((LocVal a l -> a) -> IO a) -> ChorEff (LocVal a l)

-- inductive Choreo (a: Type) where
-- | Do    : ChorEff b -> (b -> Choreo a ) -> Choreo a
-- | Return: a -> Choreo a

inductive I (a:Type)  where
| e: I a


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


inductive Choreo: Type -> Type 1 where
| Do_Send_recv [Serialize a]: (sender:String) -> LocVal a sender -> (receiver:String) -> (LocVal a receiver -> Choreo b) -> Choreo b
| Do_Local [Serialize a]: (loc:String) -> ((LocVal a loc -> a) -> IO a) -> (LocVal a loc -> Choreo b) -> Choreo b
| Return [Serialize a]: LocVal a l -> Choreo (LocVal a l)

#check Choreo


def send_recv {a:Type} [Serialize a] (l1: String) (vl: LocVal a l1) (l2:String):=  Choreo.Do_Send_recv l1 vl l2 (fun x => Choreo.Return (unwrap x))
def locally {a:Type} [Serialize a] (l: String) (comp: (LocVal a l -> a) -> IO a) := Choreo.Do_Local l comp (fun x => Choreo.Return (unwrap x))


def Choreo.bind: Choreo α → (α → Choreo β) → Choreo β
| Choreo.Do_Send_recv sender vl receiver next, next' =>  .Do_Send_recv sender vl receiver (fun x => bind (next x) next')
| Choreo.Do_Local loc comp next, next' => .Do_Local loc comp (fun x => bind (next x) next')
| Choreo.Return v, next' => next' v

instance (loc:String): Monad Choreo where
  pure x := Choreo.Return (wrap x loc)
  bind  := Choreo.bind

-- def ChorEff.run : ChorEff a -> IO a
-- | send_recv _ _ _ => do
--   return ()

def Choreo.epp: Choreo a -> String -> Network a
| Choreo.Do_Send_recv sender lv receiver next, loc => do
  if (sender == receiver) then
    let res := wrap (unwrap lv) receiver
    Choreo.epp (next res) loc
  else if (sender == loc) then
    send receiver (unwrap lv)
    Choreo.epp (next .Empty) loc
  else if (receiver == loc) then
    let response <- (recv sender)
    let res := wrap response receiver
    Choreo.epp (next res) loc
  else
    Choreo.epp (next .Empty) loc
| Choreo.Do_Local l1 comp next, l2 => do
  if (l1 == l2) then
    let res <- run (comp unwrap)
    let res := wrap res l1
    Choreo.epp (next (res)) l2
  else
    Choreo.epp (next .Empty) l2
| Choreo.Return v, _ => Network.Return v


def test_locally := locally "aaa" (fun un => do
  IO.println ""
  return 2)

def silent_post: Choreo (LocVal String "alice"):= do
  let input <- locally "alice" (fun un => do
    IO.println "enter a message"
    let stdin <- IO.getStdin
    return <- stdin.getLine
  )
  let msg <- locally "alice" (fun un => do
    return  input ++ "-alice"
  )
  let msg <- send_recv "alice" (wrap msg "alice") "eve"

  let msg <- locally "eve" (fun un => do
    return ( msg) ++ "-eve"
  )
  let msg <- send_recv "eve" (wrap msg "eve") "bob"

  let msg <- locally "bob" (fun un => do
    return ( msg) ++ "-bob"
  )
  let msg <- send_recv "bob" (wrap msg "bob") "alice"
  return wrap msg "alice"



def test_cfg_2 := local_cfg ["client", "server"] 3333


def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network test_cfg mode
  let res <- ((silent_post).epp mode).run mode net
  IO.println (s!"res: {Serialize.pretty (unwrap res)}")
  return ()




def F.{u} (α : Type u) : Type u := Prod α α

#check F    -- Type u → Type u
#check #[3,4,5,6]
