import chorlean.Choreo
import chorlean.Effects

inductive Location
| alice | bob | eve
deriving Repr
open Location

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location

instance sig: LocSig Location where
  sig x := match x with
    | alice =>  CmdInputEff ⨳ LogEff
    | bob =>  LogEff
    | eve => LogEff
  executable x := match x with
    | alice => inferInstance
    | bob => inferInstance
    | eve => inferInstance

open LogEff
open CmdInputEff

def silent_post (ep:Location): Choreo ep ((List String) @alice # ep):= do

  have: MonadLiftT (LogEff) (CmdInputEff ⨳ LogEff) := inferInstance
  have: MonadLiftT (CmdInputEff)  (CmdInputEff ⨳ LogEff) := inferInstance
  have: MonadLiftT (LogEff) (LogEff ⨳ IOEff) := inferInstance
  have: MonadLiftT (IOEff) (LogEff ⨳ IOEff) := inferInstance


  let input <- locally alice do
    info "enter a message"
    return <- readString

  let msg: String @ bob <- input ~> bob
  let msg <- locally bob do return [(⤉msg), "bob"]

  let msg <- msg ~> eve
  let msg <- locally eve do return (⤉msg).concat "eve"

  let msg <- send_recv msg alice
  locally alice do info s!"finished with string from eve: {msg}"

  return msg


def main (args : List String): IO Unit := do
  let mode := args.get! 0

  let ep_opt := FinEnum.ofString? mode
  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h
    let net <-  init_network ep
    have := EPP ep net
    let res <- silent_post ep
    IO.println (s!"res: {res}")

    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()
