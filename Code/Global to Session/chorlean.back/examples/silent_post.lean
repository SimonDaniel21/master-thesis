import chorlean.Choreo

inductive Location
| alice | bob | eve
deriving Repr
open Location

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

def silent_post (ep:Location): Choreo ep ((List String) @alice # ep):= do

  let input: String @ alice <- locally alice  do
    IO.println "enter a message"
    return <- IO.getLine


  send input to eve

  let msg <- eve ~> bob # do return [(⤉input), "eve"]
  let msg <- locally bob do return (⤉msg).concat "bob"

  let msg <- send_recv msg alice
  return msg


def main (args : List String): IO Unit := do
  let mode := args.get! 0

  let ep_opt := FinEnum.ofString? mode
  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h
    let net <-  init_network ep
    have: Network ep := net.toNet

    let res <- ((silent_post ep).epp)
    IO.println (s!"res: {res}")

    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()
