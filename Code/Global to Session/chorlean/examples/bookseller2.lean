import chorlean.Choreo
import chorlean.Effects

open Effect

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


instance: MonadLift (FriendEff) CmdInput where
  monadLift m := match m with
    | .credit_decision share =>
      CmdInput.readBool (.some s!"the buyer wants you to pay a share of {share} for his book.\nDo you accept?")

open BuyerEff

instance: MonadLiftT (BuyerEff) CmdInput where
  monadLift m := match m with
    | .get_budget => CmdInput.readNat (.some "enter your budget")
    | .get_title => CmdInput.readString (.some "enter your title")


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

instance sig: LocSig Location where
  sig x := match x with
    | buyer =>  BuyerEff ⨳ Log
    | seller =>  SellerEff ⨳ Log
    | friend => FriendEff ⨳ Log
  executable x := match x with
    | buyer => inferInstance
    | seller => inferInstance
    | friend => inferInstance


open Effect.Log

-- Type of Negotiation Choreo where l1 is the Location of the borrower
def negT  {l1 ep:Location}:=  GVal l1 ep Nat -> GVal l1 ep Nat -> Choreo ep (Bool @ l1 # ep)


-- b - borrower - l - lender
def split_50_50 (b l ep: Location) [MonadLiftT FriendEff (sig.sig l)]: negT (l1:=b) (ep:= ep) :=
  fun budget price => do
    let share <- locally b do return ((⤉price) / 2)
    let exceeds_budget: Bool @ b#ep <- locally b do return ((⤉budget) < (⤉share))

    branch exceeds_budget fun
    | true =>
      return GVal.wrap b ep false
    | false => do
      let share <- send_recv share l
      let accepts <- locally l do FriendEff.credit_decision (⤉share)
      let accepts <- accepts ~> b
      return accepts

abbrev friends := {l:Location // l = friend || l = buyer}
abbrev b2: friends := ⟨buyer, by decide⟩
abbrev f2: friends := ⟨friend, by decide⟩

instance {δ:Type} [S: LocSig δ] {p: δ -> Prop}: LocSig (Subtype p (α:=δ)) where
  sig x := match x with
    | ⟨w, _⟩ => S.sig w
  executable x := match x with
     | ⟨w, _⟩ => S.executable w

def split_50_502 (ep: friends): GVal b2 ep Nat -> GVal b2 ep Nat -> Choreo ep (GVal b2 ep Bool) :=
  fun budget price => do

    have: MonadLiftT FriendEff  (FriendEff ⨳ Log) := inferInstance
    let share <- locally b2 do return ((⤉price) / 2)
    let exceeds_budget: Bool @ b2#ep <- locally b2 do return ((⤉budget) < (⤉share))

    branch exceeds_budget fun
    | true =>
      return GVal.wrap b2 ep false
    | false => do
      let share <- share ~> f2
      let accepts <- locally f2 do FriendEff.credit_decision (⤉share)
      let accepts <- accepts ~> b2
      return accepts


def pay_rest (b l ep: Location) [MonadLiftT FriendEff (sig.sig l)]: negT (l1:=b) (ep:= ep) := fun budget price => do

  let missing <- locally b do return ((⤉price) - (⤉budget))

  branch missing fun
  | 0 => do
    return GVal.wrap b ep true
  | x => do

    let accepts <- (FriendEff.credit_decision x) @ l ~~> b
    return accepts


def book_seller (negotiate: negT  (l1:=buyer) (ep:=ep))
  : Choreo ep (Option (String @buyer#ep)) := do

  have: MonadLiftT BuyerEff  (BuyerEff ⨳ Log) := inferInstance
  have: MonadLiftT Log (BuyerEff ⨳ Log) := inferInstance

  have: MonadLiftT (FriendEff) (FriendEff ⨳ Log) := inferInstance
  have: MonadLiftT (Log)  (FriendEff ⨳ Log):= inferInstance

  have: MonadLiftT (SellerEff) (SellerEff ⨳ Log) := inferInstance
  have: MonadLiftT (Log) (SellerEff ⨳ Log) := inferInstance

  let budget <- locally buyer do BuyerEff.get_budget
  let title <- locally buyer do BuyerEff.get_title

  let title' <- (title ~> seller)
  let price <- (lookup_price (⤉title')) @ seller ~~> buyer
  locally seller do info s!"got book title: {⤉title'}"
  locally buyer do info s!"the price is {⤉price}, negotiate with friend"

  let d <- negotiate budget price -- calls another choreo :)

  let d <- split_50_502 

  branch d fun
  | true => do
    let date <- deliveryDate @ seller ~~> buyer
    return some date
  | false => do
    locally seller do warning s!"the customer declined the purchase"
    locally buyer do error s!"{⤉title} has a price of {⤉price} exceeding your budget of {⤉budget}!"
    return none


--instance (ep:Location): MonadLiftT (Choreo ep) IO := EPP ep


def main (args : List String): IO Unit := do
  let mode := args.get! 0

  let ep_opt := FinEnum.ofString? mode

  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h

    let net <-  init_network ep
    let _epp := EPP ep net

    IO.println (s!"starting bookseller 50 50")

    have: MonadLiftT (FriendEff) (FriendEff ⨳ Log) := inferInstance

    let _res <- (book_seller (split_50_50 buyer friend ep))

    IO.println (s!"\n\nstarting bookseller pay rest")
    let res <- (book_seller (pay_rest buyer friend ep))
    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()
