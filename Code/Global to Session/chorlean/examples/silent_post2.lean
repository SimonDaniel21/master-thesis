import chorlean.Choreo2

class ExecutableLocation (δ:Type) where
  m : δ -> (Type u -> Type b)

inductive Location
| buyer | seller
deriving Repr, Fintype

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location

inductive BuyerEff: Type -> Type 1
| get_budget: BuyerEff Nat
| get_title: BuyerEff String

open BuyerEff

instance bi: MonadLift (BuyerEff) IO where
  monadLift m := match m with
    | .get_budget => do
      IO.println "enter your budget"
      return (<-IO.getLine).toNat!
     | .get_title => do
      IO.println "enter your title"
      return (<-IO.getLine)


inductive SellerEff: Type -> Type 1
| lookup_price: String -> SellerEff Nat
| deliveryDate:  SellerEff String
open SellerEff

instance si: MonadLift (SellerEff) IO where
  monadLift m := match m with
    | .lookup_price title =>
      return  (if (title) == "Faust" then 100 else 200)
    | .deliveryDate => do
      IO.println "enter the delivery date:"
      return (<-IO.getLine)

@[reducible] def effect_of: Location -> (Type -> Type 1)
| buyer => BuyerEff
| seller => SellerEff

instance sig: LocSig Location IO where
  sig x := match x with
    | buyer =>  BuyerEff
    | seller =>  SellerEff
  liftable x := match x with
    | buyer => inferInstance
    | seller => inferInstance


def seller_prog: LocalM SellerEff Nat :=do
  (lookup_price "he")

def book_seller (ep: Location): Choreo ep (Option (GVal buyer ep String)) (m:=IO):= do

  let budget <- locally buyer (do
    let temp <- get_budget
    return 3)
  let title <- locally buyer get_title

  let title': GVal seller ep String <- title ~> seller

  let price <- locally seller do lookup_price (⤉ title')
  let price <- price ~> buyer


  let d: GVal  buyer ep Bool <- compute buyer ((⤉budget) >= (⤉price))

  branch d fun
  | true => do
    let date <- locally seller deliveryDate
    let date <- date ~> buyer
    return some date
  | false => do

    -- let _ <- locally seller do
    --   IO.println s!"the customer declined the purchase"

    -- let _ <- locally buyer do
    --   IO.println s!"{⤉ title} has a price of {⤉ price} exceeding your budget of {⤉ budget}!"

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
    let res <-  ((book_seller ep).epp net.toNet)
    --IO.println (s!"res: {res}")

    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()
