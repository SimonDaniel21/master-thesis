import Test.my_utils

-- Location Type, using a String on Type level
inductive LocTy: String → Type where
| named n: LocTy n

structure LocVal (α: Type) where
  val: α
  loc: String

#check (fun (x:Nat) (y:Nat) => x+y)

#check LocValue.Wrap 3 (.named "client")

instance: ToString (LocTy l) where
  toString := fun x => match x with
    | LocTy.named l => l


instance [ToString a]: ToString (LocValue a l) where
  toString := fun x => match x with
    | .Wrap v => toString v ++ "@" ++ toString l
    | .Empty => "Empty"


#check LocValue.Wrap 2

@[reducible] def located (α:Type) (l: String): Type:= (α × LocTy l)


infixl:55 "@" => located


def wrap {a} (v:a) (l: String): LocValue a (LocTy.named l):=
  LocValue.Wrap v


def unwrap: LocValue a l -> [Inhabited a] -> a
| .Wrap v =>  v
| .Empty => panic!"tried to unwrap Value from different Location, this should NOT happen in an well typed program!"

def three:Nat := 3

#eval  (wrap 43423 "client")


#check (Nat)@"client"

def takeclientnat: located Nat "client" -> Nat := fun x => 3

--def is_2 := Loc.named "client2"

def take_3: LocTy "client" -> Nat := fun x => 3

def is_2 := LocTy.named "client"

#check take_3 is_2

def test := ∀ (x:Nat),

inductive Network where
| send (a: address) (msg: Nat): Network
| recv (a: address) [Serialize t]: t -> Network
| run: IO a -> Network

inductive Net (a:Type) where
| send: Net a
| run: Net a


inductive Choreo (a: Type) where
| send_recv: String -> String -> Choreo a -> Choreo a
| locally: IO x -> String -> Choreo a -> Choreo a
| done: IO a -> String -> Choreo a


def test_prog: IO Unit := do

  IO.println "hello"

def locc (s:String) (t:Type): Type:= (s×t)

def mapping_t := List (String × address)

def Unwrap (String l):= forall a, (LocValue.Wrap a (LocTy.named "")) -> a


def epp (l:String) (cfg:mapping_t): Choreo a -> IO (Option a)
| .locally prog loc rest =>
  do
  IO.println "local compute"
  let _ <-prog
  epp l cfg rest
| .send_recv sender_loc receiver_loc rest =>
  let sender_opt := cfg.lookup sender_loc
  let receiver_opt := cfg.lookup receiver_loc
  match sender_opt with
  | some sender =>
    match receiver_opt with
    | some receiver =>
      do
      IO.println s!"{sender_loc} sends to {receiver_loc}"
      epp l cfg rest
    | none => do
      IO.println s!"cant find {receiver_loc}"
      epp l cfg rest
  | none => do
    IO.println s!"cant find {sender_loc}"
    epp l cfg rest
| .done final_io res_loc =>
  if(l == res_loc) then
    do
    let res <- final_io
    return .some res
  else
    return .none

def test_choreo: Choreo Nat :=
  Choreo.send_recv "client" "server" 2

#check Except Nat Nat

def NetM (a:Type):Type := IO a
deriving Monad

def testProg: NetM Unit := do
  IO.println ""


instance: Monad Network IO where
  bind := bind_with_logs
  pure := fun x => {value := x, logs := []}

def net_to_prog: Network α → IO a
| .recv => IO.println "help"
| .send a msg => a.send msg
| .run comp => IO.println "todo"


def bind_network: Network m α → (α → Network β) → Network β
| .send a => _
| .recv => _
| .run comp => _

def bind_choreo: Choreo α → (α → Choreo β) → Choreo β
| send_recv a =>
|
#check IO
#check MonadReader
#check Network (IO Nat


instance: Monad Choreo where
  bind := bind_with_logs
  pure := fun x => {value := x, logs := []}



def locally (loc: String):  IO a -> Choreo (a @ loc)
| comp => do
  let comp_res <- comp
  Choreo.Choreo comp_res

#check IO (Nat)@"client"

def testProg: IO ((Nat)@"client") := do
  IO.println "done"
  return (2, LocTy.named "client")

def toType: Type 1 := String -> Type

def testf (s: String): Type 1 := s

#check toType

#check LocValue.Wrap  (LocTy.named "a")

def Unwrap l := forall a, (LocValue.Wrap) -> a

#check Lean.ParserDescr
#check Type 6

def nat_to_type (n: Nat):= Type 100

def F.{u} (α : Type u) : Type u := Prod α α

#check F    -- Type u → Type u
#check #[3,4,5,6]
