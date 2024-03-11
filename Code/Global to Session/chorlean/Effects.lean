import Test.my_utils

inductive LogEff: Type -> Type 1
| warning: String -> LogEff Unit
| info: String -> LogEff Unit
| error: String -> LogEff Unit

instance: MonadLift (LogEff) IO where
  monadLift m := match m with
    | .info msg => IO.println     s!"[info]    {msg}"
    | .warning msg => IO.println  s!"[warning] {msg}"
    | .error msg => IO.eprintln   s!"[error]   {msg}"

inductive CmdInputEff: Type -> Type 1
| readString (msg: Option String := none): CmdInputEff String
| readNat (msg: Option String := none): CmdInputEff Nat
| readBool (msg: Option String := none): CmdInputEff Bool

instance: MonadLift (CmdInputEff) IO where
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
