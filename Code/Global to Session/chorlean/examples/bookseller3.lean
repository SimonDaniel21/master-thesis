import chorlean.Choreo2
import chorlean.Effects


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

abbrev summy := (SellerEff ⨳ LogEff ⨳ CmdInputEff)
open LogEff

def myProg: Freer summy Nat := do
  let temp <- deliveryDate
  let lift: MonadLiftT LogEff (Freer summy) := inferInstance
  lift.monadLift (warning "this is dangerous")

  info "this is info"
  error "this is error"
  return 22

instance si: MonadLift (SellerEff) IO where
  monadLift m := match m with
    | .lookup_price title => do
      IO.println "looked up title"
      return  (if (title) == "Faust" then 100 else 200)
    | .deliveryDate => do
      IO.println "enter the delivery date:"
      return (<-IO.getLine)


def myMain: IO Unit := do
  let temp <- myProg
  return ()

#eval myMain



instance sig: LocSig Location IO where
  sig x := match x with
    | buyer =>  BuyerEff
    | seller =>  summy
  liftable x := match x with
    | buyer => inferInstance
    | seller => inferInstance
  liftable2 x := match x with
    | buyer => inferInstance
    | seller => inferInstance


-- Versuch Unit Lokale Programme ohne let schreiben zu können
instance: CoeOut (GVal o ep Unit) Unit where
  coe _ := ()

def book_seller (ep: Location): Choreo ep (Option (GVal buyer ep String)) (m:=IO):= do

  let budget <- locally buyer get_budget
  let title <- locally buyer get_title

  let title': GVal seller ep String <- title ~> seller


  let lifter: MonadLiftT (summy) IO := inferInstance
  let lifter: MonadLiftT (BuyerEff) IO := inferInstance

  let lifter: MonadLiftT (LogEff) (LocalM summy) := inferInstance

  let lifter: MonadLiftT (SellerEff) (LocalM summy) := inferInstance

  let price <- locally seller (MonadLiftT.monadLift (lookup_price (⤉ title')))

  let _ <-locally seller ((LogEff.info ("")))
  let price <- price ~> buyer


  let d: GVal  buyer ep Bool <- compute buyer ((⤉budget) >= (⤉price))

  let _ <- locally buyer (
    print2 s!"budget {⤉budget} -- {⤉price}")

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
