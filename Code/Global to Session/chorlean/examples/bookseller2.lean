import chorlean.Choreo

inductive Location
| buyer | seller | friend
deriving Repr

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location

def negT2  {l1 ep:δ}:=  GVal l1 ep Nat -> GVal l1 ep Nat -> Choreo ep (Bool @ l1 # ep)

--def negT {endpoint: String} := GVal Nat "buyer" endpoint -> Nat @ "buyer" -> Choreo (GVal Bool "buyer" endpoint)

def book_price: String -> Nat
| "hello" => 400
| "Faust" => 100
| _ => 200


def split_50_50 (borrower lender ep: Location) (j:borrower != lender :=by decide) (j2: lender != borrower :=by decide): negT2 (l1:=borrower) (ep:= ep) := fun budget price => do


  let share <- compute borrower ((⤉price) / 2)

  let exceeds_budget: Bool @ borrower <- compute borrower ((⤉budget) < (share))

  branch exceeds_budget fun
  | true =>
    return GVal.wrap borrower ep false
  | false => do
    let share <- send_recv share lender
    let accepts <- locally lender do
      IO.println s!"the buyer wants you to pay a share of {⤉share} for his book.\nDo you accept?(y/n):"
      let str <- IO.getLine
      return str == "y"

    send accepts to borrower
    return accepts



def pay_rest (borrower lender ep: Location) : negT2 (l1:=borrower) (ep:= ep) := fun budget price => do

  let missing <- compute borrower ((⤉price) - (⤉budget))

  branch missing fun
  | 0 => do
    return GVal.wrap borrower ep true
  | x => do
    let accepts <- locally lender do
      IO.println s!"the buyer wants you to pay a share of {x} for his book.\nDo you accept?(y/n):"
      let str <- IO.getLine
      return str == "y"

    send accepts to borrower
    return accepts



def book_seller (negotiate: negT2  (l1:=buyer) (ep:=ep))
  : Choreo ep (Option (String @ buyer # ep)):= do

  let title <- locally buyer do
    IO.println "enter a book title:"
    return <- IO.getLine

  let title' <- (title ~> seller)
  let price <- compute seller (book_price (⤉title'))
  let price <- price ~> buyer

  let _ <- locally seller do
    IO.println s!"got book title: {⤉title'}"

   let _ <- locally buyer do
    IO.println s!"the price is {⤉price}, negotiate with friend"

  let d <- negotiate (GVal.wrap buyer ep 150) price -- calls another choreo :)

  -- have (x:Type) (loc:String) : Coe (Choreo endpoint (GVal x loc endpoint)) (GVal x loc endpoint) := ⟨fun chor =>
  --   chor.bind⟩
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
      IO.println s!"{⤉title} has a price of {⤉price} exceeding your budget of {150}!"

    return none


def someCalc (v: Nat ⊕ UInt8): Nat := match v with
| .inl n => n+1
| .inr ui => ui.toNat +1

#eval someCalc (.inl 3)

def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let ep_opt := FinEnum.fromString? mode
  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h

    let net <-  init_network ep default_adress

    have: Network ep := net.toNet

    IO.println (s!"starting bookseller 50 50")
    let res <- ((book_seller (split_50_50 buyer friend ep)).epp)

    IO.println (s!"\n\nstarting bookseller pay rest")
    let res <- ((book_seller (pay_rest buyer friend ep)).epp)

    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()
