import chorlean.Choreo

def bookseller_cfg := gen_fullmesh_cfg ["buyer", "seller", "friend"]


-- budget -> price -> decision

def negT2 {l1: String} {endpoint:String}:=  GVal Nat l1 endpoint -> GVal Nat l1 endpoint -> Choreo endpoint (GVal Bool l1 endpoint)

--def negT {endpoint: String} := GVal Nat "buyer" endpoint -> Nat @ "buyer" -> Choreo (GVal Bool "buyer" endpoint)

def book_price: String -> Nat
| "hello" => 400
| "Faust" => 100
| _ => 200

def split_50_50 (borrower lender endpoint: String) (j:borrower != lender :=by decide) (j2: lender != borrower :=by decide): negT2 (l1:=borrower) (endpoint:= endpoint) := fun budget price => do

  let share <- compute borrower ((⤉price) / 2)

  let exceeds_budget: GVal Bool borrower endpoint <- compute borrower ((⤉budget) < (share))

  branch exceeds_budget fun
  | true =>
    return GVal.wrap borrower endpoint false
  | false => do
    let share <- send_recv share lender
    let accepts <- locally lender do
      IO.println s!"the buyer wants you to pay a share of {⤉share} for his book.\nDo you accept?(y/n):"
      let str <- IO.getLine
      return str == "y"

    let accepts <- send_recv accepts borrower
    return accepts



def pay_rest (borrower lender endpoint: String) : negT2 (l1:=borrower) (endpoint:= endpoint) := fun budget price => do

  let missing <- compute borrower ((⤉price) - (⤉budget))

  branch missing fun
  | 0 => do
    return GVal.wrap borrower endpoint true
  | x => do
    let accepts <- locally lender do
      IO.println s!"the buyer wants you to pay a share of {x} for his book.\nDo you accept?(y/n):"
      let str <- IO.getLine
      return str == "y"

    let accepts <- accepts ~> borrower
    return accepts

def send_recv_comp2 {a:Type} {chor: Choreo endpoint x} [Serialize b] (sender receiver: String) (comp: [∀ x, Coe (GVal x sender endpoint) x] -> IO b)  :=
  do
  let gv <- locally sender comp
  toChoreo endpoint (ChorEff.Send_recv gv receiver)

def book_seller (endpoint: String) (negotiate: negT2  (l1:="buyer") (endpoint:=endpoint)) : Choreo endpoint (Option (GVal String "buyer" endpoint)):= do

  let title <- locally "buyer" do
    IO.println "enter a book title:"
    return <- IO.getLine
  --connect "buyer" to "seller"
  let temnop <- send_recv_comp2 endpoint "buyer" "seller" (do
    IO.println "enter a book title:"
    return <- IO.getLine)


  let title' <- "buyer" ~> "seller" # do

    IO.println "enter a book title:"
    return <- IO.getLine

    -- geht nicht
  --close "buyer" to "seller"

  let price <- compute "seller" (book_price (title'))
  let price <- price ~> "buyer"

  let _ <- locally "seller" do
    IO.println s!"got book title: {⤉title'}"

   let _ <- locally "buyer" do
    IO.println s!"the price is {⤉price}, negotiate with friend"

  let decision <- negotiate (GVal.wrap "buyer" endpoint 150) price -- calls another choreo :)

  -- have (x:Type) (loc:String) : Coe (Choreo endpoint (GVal x loc endpoint)) (GVal x loc endpoint) := ⟨fun chor =>
  --   chor.bind⟩
  branch decision fun
  | true => do
    let date <- locally "seller" do
      IO.println "enter the delivery date:"
      return <- IO.getLine

    let date <- date ~> "buyer"
    return some date
  | false => do

    let _ <- locally "seller" do
      IO.println s!"the customer declined the purchase"

    let _ <- locally "buyer" do
      IO.println s!"{⤉title} has a price of {⤉price} exceeding your budget of {150}!"

    return none


def someCalc (v: Nat ⊕ UInt8): Nat := match v with
| .inl n => n+1
| .inr ui => ui.toNat +1

#eval someCalc (.inl 3)

def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network bookseller_cfg mode
  IO.println (s!"starting bookseller 50 50")
  let res <- ((book_seller mode (split_50_50 "buyer" "friend" mode)).epp).run mode net

  IO.println (s!"\n\nstarting bookseller pay rest")
  let res <- ((book_seller mode (pay_rest "buyer" "friend" mode)).epp).run mode net

  return ()
