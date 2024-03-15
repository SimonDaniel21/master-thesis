import chorlean.Choreo
import chorlean.Effects

inductive Location
| buyer | seller
deriving Repr, Fintype

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location

inductive BuyerEff: Type -> Type 1
| get_budget: BuyerEff Nat
| get_title: BuyerEff String
| print2: String -> BuyerEff Unit

open BuyerEff

instance bi: MonadLift (BuyerEff) IO where
  monadLift m := match m with
    | .get_budget => do
      IO.println "enter your budget"
      return (<-IO.getLine).toNat!
    | .get_title => do
      IO.println "enter your title"
      return (<-IO.getLine)
    | .print2 s => do
      IO.print s



inductive SellerEff: Type -> Type 1
| lookup_price: String -> SellerEff Nat
| deliveryDate:  SellerEff String
open SellerEff

open LogEff


instance: MonadLift (SellerEff) IO where
  monadLift m := match m with
    | .lookup_price title => do
      IO.println "looked up title"
      return  (if (title) == "Faust" then 100 else 200)
    | .deliveryDate => do
      IO.println "enter the delivery date:"
      return (<-IO.getLine)


instance sig: LocSig Location where
  sig x := match x with
    | buyer =>  BuyerEff ⨳ LogEff
    | seller =>  SellerEff ⨳ LogEff
  executable x := match x with
    | buyer => inferInstance
    | seller => inferInstance



def book_seller (ep: Location): Choreo ep (Option (GVal buyer ep String)):= do

  have: MonadLift BuyerEff (BuyerEff ⨳ LogEff) := inferInstance
  have: MonadLift LogEff (BuyerEff ⨳ LogEff) := inferInstance

  have: MonadLift (SellerEff) (SellerEff ⨳ LogEff) := inferInstance
  have: MonadLift (LogEff)  (SellerEff ⨳ LogEff):= inferInstance

  let budget <- locally buyer get_budget
  let title <- locally buyer get_title

  let title' <- title ~> seller

  let price <- (lookup_price (⤉ title')) @ seller ~~> buyer

  let d: Bool @ buyer <- locally buyer do return ((⤉budget) >= (⤉price))

  locally buyer (
    print2 s!"budget {⤉budget} -- {⤉price}")

  branch d fun
  | true => do
    let date <- deliveryDate @ seller ~~> buyer
    return some date
  | false => do

    locally seller do
      LogEff.warning s!"the customer declined the purchase"

    locally buyer do
      LogEff.error s!"{⤉ title} has a price of {⤉ price} exceeding your budget of {⤉ budget}!"

     return none


def main (args : List String): IO Unit := do
  let mode := args.get! 0

  let ep_opt := FinEnum.ofString? mode

  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h
    let net <- init_network ep
    let epp := EPP ep net

    let r <- (book_seller ep)
    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()
