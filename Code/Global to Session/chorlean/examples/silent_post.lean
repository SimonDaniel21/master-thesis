import chorlean.Choreo
import chorlean.Effects
open Effect
open Effect (CmdInput)
open Effect.CmdInput
open Effect.Log

inductive Location
| alice | bob | eve
deriving Repr, Fintype

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location

instance sig: LocSig Location where
  sig x := match x with
    | alice =>  CmdInput ⨳ Log
    | bob =>  CmdInput ⨳ Log
    | eve => CmdInput ⨳ Log
  executable x := match x with
    | alice => inferInstance
    | bob => inferInstance
    | eve => inferInstance


def silent_post (ep:Location): Choreo ep ((List String) @ alice#ep):= do

  have: MonadLiftT (Log) (CmdInput ⨳ Log) := inferInstance
  have: MonadLiftT (CmdInput)  (CmdInput ⨳ Log) := inferInstance
  have: MonadLiftT (Log) (Log ⨳ IO) := inferInstance
  have: MonadLiftT (IO) (Log ⨳ IO) := inferInstance


  let input <- locally alice do
    info "enter a message"
    return <- CmdInput.readString

  let msg: String @ bob <- input ~> bob
  let msg <- locally bob do return [(⤉msg), "bob"]

  let msg <- msg ~> eve
  let msg <- locally eve do return (⤉msg).concat (<- CmdInput.readString)

  let msg <- send_recv msg alice
  locally alice do info s!"finished with chain: {msg}"

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
