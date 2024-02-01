import chorlean.Choreo

def bookseller_cfg := local_cfg ["buyer", "seller", "friend"] 3333


-- budget -> price -> decision

def negT2 {l1: String}:=  Nat @ l1 -> Nat @ l1 -> Choreo (Bool @ l1)

def negT := Nat @ "buyer" -> Nat @ "buyer" -> Choreo (Bool @ "buyer")

def budget := wrap 150 "buyer"
def book_price: String -> Nat
| "hello" => 400
| "Faust" => 100
| _ => 200

def split_50_50 (borrower lender: String) (j:borrower != lender :=by decide) (j2: lender != borrower :=by simp): negT2 (l1:=borrower) := fun budget price => do

  let share <- compute borrower fun un => un price / 2
  let exceeds_budget: Bool @ borrower <- compute borrower fun un => (un budget) < (un share)

  branch exceeds_budget fun
  | true =>
    return wrap false borrower
  | false => do
    let share <- send_recv share lender j
    let accepts <- locally lender fun un => do
      IO.println s!"the buyer wants you to pay a share of {un share} for his book.\nDo you accept?(y/n):"
      let str <- IO.getLine
      return str == "y"

    let accepts <- send_recv accepts borrower j2
    return accepts



def pay_rest: negT  := fun budget price => do

  let missing <- compute "buyer" fun un => un price - un budget

  branch missing fun
  | 0 => do
    return wrap true "buyer"
  | x => do
    let accepts <- locally "friend" fun _ => do
      IO.println s!"the buyer wants you to pay a share of {x} for his book.\nDo you accept?(y/n):"
      let str <- IO.getLine
      return str == "y"

    let accepts <- accepts ~> "buyer"
    return accepts


def book_seller (negotiate: negT) : Choreo (Option (String @"buyer")):= do

  let title <- locally "buyer" (fun _ => do
    IO.println "enter a book title:"
    return <- IO.getLine
  )
  let title' <- title ~> "seller"

  let nor_title := unwrap title'

  let price <- compute "seller" fun un => book_price (un title')
  let price <- price ~> "buyer"

  let _ <- locally "seller" (fun un => do
    IO.println s!"got book title: {un title'}"

  )
  let decision <- negotiate budget price -- calls another choreo :)

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


def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network bookseller_cfg mode
  IO.println (s!"starting bookseller 50 50")
  let res <- ((book_seller (split_50_50 "buyer" "friend")).epp mode).run mode net
  IO.println (s!"res: {res}")
  IO.println (s!"\n\nstarting bookseller pay rest")
  let res <- ((book_seller pay_rest).epp mode).run mode net
  IO.println (s!"res: {res}")
  return ()
