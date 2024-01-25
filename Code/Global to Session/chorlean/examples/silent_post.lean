import chorlean.Choreo

def silent_post: Choreo (String @"alice"):= do

  let input: LocVal String "alice" <- locally "alice" (fun un => do
    IO.println "enter a message"
    let stdin <- IO.getStdin
    return <- stdin.getLine
  )

  let msg <- locally "alice" fun un => return (un input) ++ "-alice_mut"

  let msg <- send_recv msg "eve"
  let msg <- locally "eve" fun un => return (un msg) ++ "-eve"

  let msg <- send_recv msg "bob"
  let msg <- locally "bob" fun un => return (un msg) ++ "-bob"

  let msg <- send_recv msg "alice"
  return msg

def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network test_cfg mode
  let res <- ((silent_post).epp mode).run mode net
  IO.println (s!"res: {res}")
  return ()
