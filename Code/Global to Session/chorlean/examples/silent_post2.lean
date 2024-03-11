import chorlean.Choreo2
import chorlean.Effects

inductive Location
| alice | bob | eve
deriving Repr
open Location

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location

instance sig: LocSig Location IO where
  sig x := match x with
    | alice =>  CmdInputEff ⨳ LogEff
    | bob =>  LogEff
    | eve => LogEff ⨳ IOEff
  liftable x := match x with
    | alice => inferInstance
    | bob => inferInstance
    | eve => inferInstance
  liftable2 x := match x with
    | _ => inferInstance

open LogEff
open CmdInputEff

def silent_post (ep:Location): Choreo ep ((List String) @alice # ep) (m:=IO):= do

  have: MonadLiftT (LogEff) (LocalM (CmdInputEff ⨳ LogEff)) := inferInstance
  have: MonadLiftT (CmdInputEff) (LocalM (CmdInputEff ⨳ LogEff)) := inferInstance
  have: MonadLiftT (LogEff) (LocalM (LogEff ⨳ IOEff)) := inferInstance
  have: MonadLiftT (IOEff) (LocalM (LogEff ⨳ IOEff)) := inferInstance


  let input: String @ alice <- locally alice do
    info "enter a message"
    return <- readString

  let msg <- input ~> bob
  let msg <- locally bob do
    info s!"received from alice: {⤉msg}"
    return [(⤉msg), "bob"]

  let msg <- msg ~> eve
  let msg <- locally eve do
    info s!"received from bob: {⤉msg}"
    return (⤉msg).concat "eve"

  let msg <- send_recv msg alice

  let _ <- locally alice do
    info s!"finished with string from eve: {msg}"

  return msg


def main (args : List String): IO Unit := do
  let mode := args.get! 0

  let ep_opt := FinEnum.ofString? mode
  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h
    let net <-  init_network ep

    have := (sig.liftable ep)
    let res <- ((silent_post ep).epp net.toNet)
    IO.println (s!"res: {res}")

    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()
