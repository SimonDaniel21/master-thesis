import chorlean.Choreo_nomut

def bookseller_cfg := gen_fullmesh_cfg ["buyer", "seller"]


def book_seller: Choreo (Option (String @"buyer")):= do

  let budget := wrap 150 "buyer"


  let title <- locally "buyer" (fun _ => do
    IO.println "enter a book title:"
    return <- IO.getLine
  )
  let title' <- title ~> "seller"

  let price <- compute "seller" fun un => if (un title') == "Faust" then 100 else 200
  let price <- price ~> "buyer"

  let _ <- locally "seller" (fun un => do
    IO.println s!"got book title: {un title'}"
  )

  let decision: LocVal Bool "buyer" <- compute "buyer" fun un => (un budget >= un price)

  branch decision fun
  | true => do
    let date <- locally "seller" (fun _ => do
      IO.println "enter the delivery date:"
      return <- IO.getLine
    )
    let date <- date ~> "buyer"
    return some date
  | false => do

    let _ <- locally "seller" (fun _un => do
      IO.println s!"the customer declined the purchase"
    )
    let _ <- locally "buyer" (fun un => do
      IO.println s!"{un title} has a price of {un price} exceeding your budget of {un budget}!"
    )
    return none



def ping: Choreo (Unit):= do
  let data := wrap [4424, 424, 22, 4] "buyer"
  while true do
    let data <- data ~> "seller"
    let data <- data ~> "buyer"
    let data <- data ~> "seller"


def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network bookseller_cfg mode
  let res <- ((ping).epp mode (by sorry)).run mode net
  IO.println (s!"res: {res}")
  return ()
