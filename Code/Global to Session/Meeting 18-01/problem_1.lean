

-- meine Intention ist es eine Session als Typ zu spezifizieren
-- sodass dieser "SessionType" ein Kommunikationsprotokoll beschreibt.
-- abhängig von diesem Typ gibt es zu jedem Zeitpunkt in einem Programm
-- nur eine mögliche Aktion in dieser Session.
-- eine Funktion soll nun den SessionType auf die nächste Session
-- Aktion abbilden (send oder recv z.b), welche mit entsprechenden
-- argumenten auf ein IO Programm abgebildet werdern können

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
  receive "client"
  IO programm
  send 2 "client"
  -- when calling next i have the type info of the next step, so i dont want to pattern match
