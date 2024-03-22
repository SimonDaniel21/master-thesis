import Test.my_utils

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

end Effect
