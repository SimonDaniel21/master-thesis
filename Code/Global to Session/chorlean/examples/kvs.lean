import chorlean.Choreo
import chorlean.Effects

inductive Location
| client | server
deriving Repr, Fintype

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location
open Effect

#check IO.println

instance sig: LocSig Location where
  sig x := match x with
    | client =>  CmdInput ⨳ Log
    | server =>  Log
  executable x := match x with
    | client =>  inferInstance
    | server =>  inferInstance


partial def kv (ep: Location) (store:(List (String × String)) @ server # ep := GVal.wrap server ep []): Choreo ep Unit := do
  have: MonadLift CmdInput  (CmdInput ⨳ Log):= inferInstance
  have: MonadLift Log  (CmdInput ⨳ Log):= inferInstance

  let input <- locally client (CmdInput.readString "Put/Get/q")

  branch input fun
  | "Put" => do
    let key <- (CmdInput.readString "enter key") @ client ~~> server
    let value <- (CmdInput.readString "enter value") @ client ~~> server
    let store <- locally server do return (⤉store).insert (⟨⤉key, ⤉value⟩)
    kv ep store

  | "Get" => do
    let key <- (CmdInput.readString "enter key") @ client ~~> server
    let response <- (return (⤉store).lookup (⤉key)) @ server ~~> client
    locally client do Log.info (toString ⤉response)
    kv ep store
  | "q" | _ => return ()
  return ()




def main (args : List String): IO Unit := do
  let mode := args.get! 0

  let ep_opt := FinEnum.ofString? mode

  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h
    let net <- init_network ep
    let epp := EPP ep net

    let r <- (kv ep)
    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()
