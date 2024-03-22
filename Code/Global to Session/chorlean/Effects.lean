import chorlean.utils
import chorlean.Freer


namespace Effect


  inductive Log: Type -> Type 1
  | warning: String -> Log Unit
  | info: String -> Log Unit
  | error: String -> Log Unit
  deriving Repr

  instance: MonadLift (Log) IO where
    monadLift m := match m with
      | .info msg => IO.println     s!"[info]    {msg}"
      | .warning msg => IO.println  s!"[warning] {msg}"
      | .error msg => IO.eprintln   s!"[error]   {msg}"

  inductive CmdInput: Type -> Type 1
  | readString (msg: Option String := none): CmdInput String
  | readNat (msg: Option String := none): CmdInput Nat
  | readBool (msg: Option String := none): CmdInput Bool

  instance: MonadLift (CmdInput) IO where
    monadLift m := match m with
      | .readString msg => do
        if h:(msg.isSome) then
          IO.println (msg.get h)
        return <- IO.getLine
      | .readNat  msg => do
        if h:(msg.isSome) then
          IO.println (msg.get h)
        return (<-IO.getLine).toNat!
      | .readBool msg => do
        if h:(msg.isSome) then
          IO.println ((msg.get h) ++ " (y/n)")
        return (<-IO.getLine) == "y"

  inductive Sleep: Type -> Type 1
  | sleep (ms: UInt32): Sleep Unit

  instance: MonadLift (Sleep) IO where
    monadLift m := match m with
      | .sleep d => do
        IO.sleep d

  inductive Timer: Type -> Type 1
  | getTime: Timer Nat

  instance: MonadLift (Timer) IO where
    monadLift m := match m with
      | .getTime => do
        IO.monoNanosNow

  inductive Rand: Type -> Type 1
  | rand (hi lo: Nat): Rand Nat

  instance: MonadLift (Rand) IO where
    monadLift m := match m with
      | .rand hi lo => do
        IO.rand hi lo


  def Timer.NanosToSec: Nat -> Float :=  fun x => x.toFloat / 1000000000


end Effect


def generate_random_list_rec: (l: List Nat) -> Nat -> Freer Effect.Rand (List Nat)
| _, 0 =>  return []
| remaining, len+1 =>  do
  let index <- Effect.Rand.rand 0 (remaining.length-1)
  let rest_list <- generate_random_list_rec (remaining.eraseIdx index) len
  return rest_list.concat remaining[index]!

def descending_list: Nat -> List Nat
| 0 => []
| x+1 => [x+1] ++ descending_list (x)

def generate_random_list (n:Nat): Freer Effect.Rand (List Nat) := do
  let sorted := descending_list n
  generate_random_list_rec sorted n
