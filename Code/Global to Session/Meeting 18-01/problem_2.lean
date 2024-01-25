-- HasChor macht ziemlich ähnliche Sachen wie was ich bisher versucht habe
-- bloß besser und nützlicher.
-- Hauptsächlich durch die Verwendbarkeit von lokalen Berechnungen
-- ("locally"). die Verstehe ich noch nicht ganz.

-- bei mir werden Sequenzen über die Inductive verschachtelungen
-- eines inductive, bei Haschor über die Effekte einer Monade.
-- deren Variante ist deutlich eleganter, und choreos sehen fast
-- aus wie programme.
-- sie benutzen Freer Monaden, soweit ich das verstanden habe kann
-- ich aber genauso gut auch einen Monadentransformer für IO
-- verwenden (mal zusammen probieren ich bin daran gescheitert)
-- vlt machen Freer Monads die EPP aber einfacher?


import Lean.Elab.Term


#eval do return toString (←Lean.Elab.Term.elabTerm (← `(String -> String)) none)

inductive limitedIOEffect: Type -> Type where
| print_nat  : Nat -> limitedIOEffect Unit


inductive limitedIO (a:Type) where
| effect  : limitedIOEffect b -> (b -> limitedIO a ) -> limitedIO a
| done: a->  limitedIO a

def limitedIOEffect.run : limitedIOEffect a -> IO a
| .print_nat n => do
    IO.println ("nat: " ++ toString n)


def limitedIO.run : limitedIO a -> IO a
| effect eff next => do
  let res <- eff.run
  (next res).run
| done v => do
  return v

def limitedIO.bind : limitedIO α → (α → limitedIO β) → limitedIO β
  | .effect eff next, next' => .effect eff (fun x => bind (next x) next')
  | .done v, next' => next' v

instance: Monad limitedIO where
  pure x := limitedIO.done x
  bind  := limitedIO.bind

instance: MonadLift limitedIO IO where
  monadLift := limitedIO.run


def toLimitedIO (eff: limitedIOEffect a): limitedIO a :=
  limitedIO.effect eff (limitedIO.done)

def print_nat (n:Nat) := toLimitedIO (limitedIOEffect.print_nat n)


def finish (n:Nat): limitedIO Nat:= limitedIO.done n

def limited_prog: limitedIO Nat := do
  print_nat 244
  print_nat 333
  finish 2

def unlimited_prog: IO Nat := do
  let _ <-limited_prog
  return 4

#eval unlimited_prog



inductive ChoreoIO (a:Type): Type where
| print_nat (n:Nat)  (cont: Unit -> ChoreoIO a ) : ChoreoIO a
| id (n:Nat)  (cont: Nat -> ChoreoIO a ) : ChoreoIO a
| done (v:a):  ChoreoIO a



def ChoreoIO.run : ChoreoIO a -> IO a
| print_nat n next => do
  IO.println ("nat: " ++ toString n)
  (next ()).run
| id n next => do
  (next n).run
| done v => do
  return v

instance: MonadLift ChoreoIO (IO) where
  monadLift := ChoreoIO.run


def main_fun: IO Unit := do
  (ChoreoIO.print_nat 3 (fun _ => ChoreoIO.done ())).run

#eval main_fun


def ChoreoIO.bind (chor: ChoreoIO α) (next: α → ChoreoIO β):  (ChoreoIO β):=
  let res := chor.run
  let io_res := EStateM.bind res
  match io_res with
  |

  let



instance: Monad ChoreoIO where
  pure := fun x => ChoreoIO.done x
  bind := ChoreoIO.bind


def choreo_m: ChoreoIO Unit := do
  print_nat 3


def test_chor1 := ChoreoIO.print_nat 2 ( fun _ => ChoreoIO.done ())

-- def chorIO_Bind: ChoreoIO α → (α → ChoreoIO β) → ChoreoIO β
-- | c, fn => do
--   let v <- c
--   fn

-- instance: Monad ChoreoIO where
--   pure x := fun _ => pure x
--   bind := _

def ConfigIO (α : Type) : Type :=
  String → IO α

def ConfigIO.run (action : ConfigIO α) (cfg : String) : IO α :=
  action cfg

instance : Monad ConfigIO where
  pure x := fun _ => pure x
  bind result next := fun cfg => do
    let v ← result cfg
    next v cfg

def runIO (action : IO α) : ConfigIO α :=
  fun _ => action

def pprint (s:String): ConfigIO Nat := do

  return 2

def test_comp: ConfigIO Nat := do
  let v <- runIO (IO.println "hello")
  return 2

class restricted (a) extends Monad a where
  print_nat: Nat -> a Unit
  get_nat: Nat -> a Nat


instance: restricted Option where
  print_nat := fun x => ()


def myFunc: restricted m -> m Unit  := do
  let temp <- print_nat 32
  return ()

inductive myMonad m (a:Type) [restricted m] :=
| done: a -> myMonad m a
| print: Nat -> myMonad m a

instance: Monad (myMonad IO)  where
  bind := _
  pure := _

inductive LocTy: String → Type where
| named n: LocTy n

def toLocTm : LocTy l -> String
| LocTy.named l => l

inductive locVal (a:Type) (l:String) where
| Wrap: a  -> locVal a l
| Empty: locVal a l

class Unwrap (l:String) where
  unwrap: locVal x l -> x

#check ∀ (x), locVal x l -> x
#check fun l => Type -> locVal x l-> x
#check fun l => ∀ x, locVal x l -> x


#check (LocTy.named "cliient")
#check toLocTm (LocTy.named "cliient")
--#eval  (LocTy.named "cliient")
#eval toLocTm (LocTy.named "cliient")

-- gibt es eine Methode einen Typ auf seinen Bezeichner als String abzubilden?
-- Nat => "Nat"


-- effect signature
inductive ChorEffect a
| print_string: String -> (Unit -> ChorEffect a) -> ChorEffect a
| print_nat: Nat -> (Unit -> ChorEffect a) ->ChorEffect a
| id: b -> (b -> ChorEffect a) -> ChorEffect a
| done: a -> ChorEffect a
#check 3
#check Nat

def ChorM (α: Type): Type :=
  (ChorEffect α) -> IO α

-- less free Monadic type
inductive Choreo a where
| done: a -> Choreo a
--| comp: ChorEffect -> (b -> Choreo a) -> Choreo a
| comp_print_string: String -> (Unit -> Choreo a) -> Choreo a
| comp_print_nat: Nat -> (Unit -> Choreo a) -> Choreo a
| comp_id: b -> (b -> Choreo a) -> Choreo a



def ChorEffect.run: ChorEffect α -> IO α
| id a r =>do
  (r a).run
| print_string s r => do
  IO.println s
  (r ()).run
| print_nat n r => do
  IO.println n
  (r ()).run
| done v => do
  return v

instance : Monad ChorM where
  pure x := fun _ => pure x
  bind chor next := fun eff => do
    let v ← chor
    next v cfg


def my_chor1: Choreo IO Nat :=
  Choreo.comp_id 22 (Choreo.done)

def my_chor: Choreo IO String :=
  Choreo.comp_id "" (fun x => my_chor1)

def pureChoreo m (v: a) [restricted m]: Choreo m :=
  .done v


-- def bindChoreo: (Choreo m) -> (a -> (Choreo b)) -> IO (Choreo b)
-- | .done r, f => do
--   return (f r)
-- | .comp_print_string s r, fn => do
--     IO.println s
--     bindChoreo (r ()) fn

-- | .comp_print_nat n r, fn => do
--     IO.println n
--     bindChoreo (r ()) fn
-- | .comp_id v r, fn => do
--   IO.println "compute"
--   bindChoreo (r v) fn

--   def print_nat (n: Nat) (c: Nat -> Choreo a): Choreo a :=
--     Choreo.comp_print_nat n (c n)


instance: Monad (Choreo (IO))  where
  bind := bindNet
  pure := pureNet
-- Hier will ich IO Effekte ausführen - MonadTransformer🧐 ---
-- instance: Monad (IO (Choreo)) where
--   bind := bindChoreo
--   pure := pureChoreo

def main: IO Unit := do
  IO.println "start"
  let test_chor := Choreo.done 2
  bindChoreo test_chor
  return ()

#eval main

-- effect signature
inductive NetEffect (a:Type)
| print_string: String -> NetEffect a
| print_nat: Nat -> NetEffect a
| id: a -> NetEffect a

-- less free Monadic type
inductive Network (a:Type) where
| done: a -> Network a
| comp: NetEffect b -> (b -> Network a) -> Network a

def pureNet (v: a): Network a :=
  .done v

def bindNet: Network a -> (a -> Network b) -> Network b
| .done r, f => f r
| .comp eff, f => match eff with -- kann Typ Network a nicht ableiten?
  | .print_string _ => f  -- hier soll nun IO passieren, muss also ein IO. Transformer sein?
  | .print_nat _ => f
  | .id v => v

-- Hier will ich IO Effekte ausführen - MonadTransformer🧐 ---
instance: Monad (Network) where
  bind := bindNet
  pure := pureNet



instance: restricted (Network) where
  print_nat n :=  (IO.println "")
  get_nat a := return a
