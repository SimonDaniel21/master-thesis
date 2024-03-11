import chorlean.Choreo2
import chorlean.Effects


class ExecutableLocation (δ:Type) where
  m : δ -> (Type u -> Type b)

inductive Location
| buyer | seller | friend
deriving Repr, Fintype

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location

inductive BuyerEff: Type -> Type 1
| get_budget: BuyerEff Nat
| get_title: BuyerEff String

inductive FriendEff: Type -> Type 1
| credit_decision: Nat -> FriendEff Bool


instance: MonadLift (FriendEff) CmdInputEff where
  monadLift m := match m with
    | .credit_decision share =>
      CmdInputEff.readBool (.some s!"the buyer wants you to pay a share of {share} for his book.\nDo you accept?")

open BuyerEff

instance: MonadLiftT (BuyerEff) CmdInputEff where
  monadLift m := match m with
    | .get_budget => CmdInputEff.readNat (.some "enter your budget")
    | .get_title => CmdInputEff.readString (.some "enter your title")


inductive SellerEff: Type -> Type 1
| lookup_price: String -> SellerEff Nat
| deliveryDate:  SellerEff String
open SellerEff

instance si: MonadLift (SellerEff) IO where
  monadLift m := match m with
    | .lookup_price title => do
      IO.println "looked up title"
      return  (if (title) == "Faust" then 100 else 200)
    | .deliveryDate => do
      IO.println "enter the delivery date:"
      return (<-IO.getLine)

instance sig: LocSig Location IO where
  sig x := match x with
    | buyer =>  BuyerEff ⨳ LogEff
    | seller =>  SellerEff ⨳ LogEff
    | friend => FriendEff ⨳ LogEff
  liftable x := match x with
    | buyer => inferInstance
    | seller => inferInstance
    | friend => inferInstance
  liftable2 x := match x with
    | _ => inferInstance


open LogEff

-- Type of Negotiation Choreo where l1 is the Location of the borrower
def negT  {l1 ep:Location}:=  GVal l1 ep Nat -> GVal l1 ep Nat -> Choreo ep (Bool @ l1 # ep) (m:=IO)


-- b - borrower - l - lender
def split_50_50 (b l ep: Location) [MonadLiftT FriendEff (sig.sig l)]: negT (l1:=b) (ep:= ep) :=
  fun budget price => do
    let share <- compute b ((⤉price) / 2)
    let exceeds_budget: Bool @ b <- compute b ((⤉budget) < (⤉share))

    branch exceeds_budget fun
    | true =>
      return GVal.wrap b ep false
    | false => do
      let share <- send_recv share l
      let accepts <- locally l do FriendEff.credit_decision (⤉share)
      let accepts <- accepts ~> b
      return accepts


def pay_rest (b l ep: Location) [MonadLiftT FriendEff (sig.sig l)]: negT (l1:=b) (ep:= ep) := fun budget price => do

  let missing <- compute b ((⤉price) - (⤉budget))

  branch missing fun
  | 0 => do
    return GVal.wrap b ep true
  | x => do
    let accepts <- locally l do FriendEff.credit_decision (x)

    let accepts <- accepts ~> b
    return accepts


def book_seller (negotiate: negT  (l1:=buyer) (ep:=ep))
  : Choreo ep (Option (String @ buyer # ep)) (m:=IO):= do

  have: MonadLiftT BuyerEff  (BuyerEff ⨳ LogEff) := inferInstance
  have: MonadLiftT LogEff (BuyerEff ⨳ LogEff) := inferInstance

  have: MonadLiftT (FriendEff) (FriendEff ⨳ LogEff) := inferInstance
  have: MonadLiftT (LogEff)  (FriendEff ⨳ LogEff):= inferInstance

  have: MonadLiftT (SellerEff) (SellerEff ⨳ LogEff) := inferInstance
  have: MonadLiftT (LogEff) (SellerEff ⨳ LogEff) := inferInstance

  let budget <- locally buyer do BuyerEff.get_budget
  let title <- locally buyer do BuyerEff.get_title

  let title' <- (title ~> seller)
  let price <- locally seller do SellerEff.lookup_price (⤉title')
  let price <- price ~> buyer

  let _ <- locally seller do
    LogEff.info s!"got book title: {⤉title'}"

   let _ <- locally buyer do
    LogEff.info s!"the price is {⤉price}, negotiate with friend"

  let d <- negotiate budget price -- calls another choreo :)

  branch d fun
  | true => do
    let date <- locally seller do SellerEff.deliveryDate
    let date <- date ~> buyer
    return some date
  | false => do
    let _ <- locally seller do
      warning s!"the customer declined the purchase"

    let _ <- locally buyer do
      error s!"{⤉title} has a price of {⤉price} exceeding your budget of {150}!"

    return none


def main (args : List String): IO Unit := do
  let mode := args.get! 0

  let ep_opt := FinEnum.ofString? mode

  let bobby : LocalM BuyerEff Unit := do
    let temp := BuyerEff.get_title
    return ()
  let bres <- MonadLiftT.monadLift bobby

  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h

    let net <-  init_network ep

    have: Network ep := net.toNet

    let budget := GVal.wrap buyer ep (args.get! 1).toNat!

    have := (sig.liftable ep)

    --IO.println (s!"res: {res}")

    IO.println (s!"starting bookseller 50 50")

    have: MonadLiftT (FriendEff) (FriendEff ⨳ LogEff) := inferInstance

    let res <- ((book_seller (split_50_50 buyer friend ep)).epp  net.toNet)

    IO.println (s!"\n\nstarting bookseller pay rest")
    let res <- ((book_seller (pay_rest buyer friend ep)).epp  net.toNet)
    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()