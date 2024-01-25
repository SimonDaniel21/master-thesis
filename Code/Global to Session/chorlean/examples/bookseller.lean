import chorlean.Choreo

def bookseller_cfg := local_cfg ["buyer", "seller"] 3333


def book_seller: Choreo (Option (String @"buyer")):= do

  let budget := wrap 150 "buyer"

  let title <- locally "buyer" (fun _ => do
    IO.println "enter a book title:"
    let stdin <- IO.getStdin
    let str <-stdin.getLine
    return str.dropRight 1
  )
  let title' <- title ~> "seller"
  let price <- compute "seller" fun un => if (un title') == "Faust" then 100 else 200
  let price <- price ~> "buyer"

  let _ <- locally "seller" (fun un => do
    IO.println s!"got book title: {un title'}"

  )
  let decision: LocVal Bool "buyer" <- compute "buyer" fun un => (un budget >= un price)

  branch decision (fun x => match x with
  | true => do
    let date <- locally "seller" (fun _ => do
      IO.println "enter the delivery date:"
      let stdin <- IO.getStdin
      return <- stdin.getLine
    )
    let date <- date ~> "buyer"
    return some date
  | false => do

    let _ <- locally "seller" (fun un => do
      IO.println s!"the customer declined the purchase"
    )
    let _ <- locally "buyer" (fun un => do
      IO.println s!"{un title} has a price of {un price} exceeding your budget of {un budget}!"
    )
    return none
  )


def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network bookseller_cfg mode
  let res <- ((book_seller).epp mode).run mode net
  IO.println (s!"res: {res}")
  return ()
