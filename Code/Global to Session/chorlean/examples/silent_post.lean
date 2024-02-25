import chorlean.Choreo_nomut


def silent_post: Choreo ((List String) @"alice"):= do

  let input: String @ "alice" <- locally "alice" (fun _ => do
    IO.println "enter a message"
    return <- IO.getLine
  )

  let msg <- input ~> "eve"
  let msg <- locally "eve" fun un => return [(un msg), "eve"]

  let msg <- send_recv msg "bob"
  let msg <- locally "bob" fun un => return (un msg).concat "bob"

  let msg <- send_recv msg "alice"
  return msg


def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network test_cfg mode
  let res <- ((silent_post).epp mode (by sorry)).run mode net
  IO.println (s!"res: {res}")
  return ()
