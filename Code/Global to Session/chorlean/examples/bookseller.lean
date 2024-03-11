import chorlean.Choreo

inductive Location
| buyer | seller
deriving Repr, Fintype

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location

def book_seller (ep: Location) (budget: GVal buyer ep Nat): Choreo ep (Option (GVal buyer ep String)):= do

  let title <- locally buyer do
    IO.println "enter a book title:"
    return <- IO.getLine

  let title' <- title ~> seller

  let price <- compute seller (if (⤉ title') == "Faust" then 100 else 200)
  let price <- price ~> buyer

  let _ <- locally seller do
    IO.println s!"got book title: { ⤉ title'}"

  let d: GVal  buyer ep Bool <- compute buyer ((⤉budget) >= (⤉price))

  branch d fun
  | true => do
    let date <- locally seller do
      IO.println "enter the delivery date:"
      return <- IO.getLine

    let date <- date ~> buyer
    return some date
  | false => do

    let _ <- locally seller do
      IO.println s!"the customer declined the purchase"

    let _ <- locally buyer do
      IO.println s!"{⤉ title} has a price of {⤉ price} exceeding your budget of {⤉ budget}!"

    return none

def main (args : List String): IO Unit := do
  let mode := args.get! 0

  let ep_opt := FinEnum.ofString? mode
  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h

    let net <-  init_network ep

    have: Network ep := net.toNet

    let budget := GVal.wrap buyer ep (args.get! 1).toNat!

    let res <- ((book_seller ep budget).epp)
    IO.println (s!"res: {res}")

    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()
