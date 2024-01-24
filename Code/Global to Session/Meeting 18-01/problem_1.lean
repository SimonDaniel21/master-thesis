

-- meine Intention ist es eine Session als Typ zu spezifizieren
-- sodass dieser "SessionType" ein Kommunikationsprotokoll beschreibt.
-- abhängig von diesem Typ gibt es zu jedem Zeitpunkt in einem Programm
-- nur eine mögliche Aktion in dieser Session.
-- eine Funktion soll nun den SessionType auf die nächste Session
-- Aktion abbilden (send oder recv z.b), welche mit entsprechenden
-- argumenten auf ein IO Programm abgebildet werdern können


mutual
  inductive A: (Type) -> Type 1 where
  | Send_recv [ToString a]:  A a
  | Local [ToString a]: String -> ((a -> a) -> IO a) -> ChorEff a
  --| Cond [Serialize b]: LocVal b loc2 -> (b -> Choreo a) -> ChorEff a

  inductive B  where
  | Do :  ChorEff b -> (b -> Choreo a) -> Choreo a
  | Return: a -> Choreo a
end

def Location := String

def do_send (α:Type): α -> Location -> IO Unit := fun _ _ => do
  IO.println "sending"

def do_recv (α:Type): α -> Location -> IO α := fun v _ => do
  IO.println "receiving"
  return v

inductive SessionType where
| send (t: Type): Location -> SessionType -> SessionType
| receive (t: Type): Location -> SessionType -> SessionType
| done: SessionType

def test_type: SessionType := .send Nat "client" .done

inductive SessionStep where
| send (t:Type ): (t -> IO Unit) -> SessionStep
| receive (t:Type ): (t -> IO t) -> SessionStep
| done: SessionStep

def SessionType.next (s: SessionType): SessionStep := match s with
| SessionType.send t l n =>
  SessionStep.send t (fun x => (do_send t x l))
| SessionType.receive t l n =>
  SessionStep.receive t (fun x => (do_recv t x l))
| SessionType.done => SessionStep.done


-- what i want
def prog: IO Unit := do
  IO.println "start"
  let session := SessionType.send Nat "client" (.receive String "client" (.done))
  let step := session.next
  -- receive "client"
  -- IO programm
  -- send 2 "client"
  -- when calling next i have the type info of the next step, so i dont want to pattern match


mutual
  inductive I1 (a:Type) [i : ToString a]  where
  | some: I2 a -> I1 a

  inductive I2 (a:Type) [i : ToString a] where
  | other: I2 a
end

inductive I3 (a:Type) [i : ToString a] where
  | other: I3 a


def fn (a b:Nat) (p : (a!=b) := by decide) :=
  a + b

#check fn 2 4
#eval fn 2 2 -- this should not

mutual
  inductive A: Type -> Type 1 where
  | one: B α -> A α

  inductive B: Type -> Type 1 where
  | two (other:Type) : A other -> B α
end
