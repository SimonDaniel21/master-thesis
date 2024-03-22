import chorlean.Choreo
import chorlean.Effects

open Effect

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

open Effect.Log


--variable (A B C: Type -> Type) [Monad M] [Monad N] [Monad C]
variable (eff1 eff2 eff3: Type -> Type)

def plus (e1: Type -> Type) (e2: Type -> Type): Type -> Type := sorry

instance: MonadLift e1 (plus e1 e2) := sorry
instance: MonadLift e2 (plus e1 e2) := sorry

-- transitively lifts an sum Effect into a Monad (or Effect) m if both Effect Signatures can be lifted into m
instance [MonadLiftT e1 m] [MonadLiftT e2 m]: MonadLiftT (plus e1 e2) m := sorry

class Sig where
  sig: (Type -> Type)

def e1: Type -> Type := sorry
def e2: Type -> Type := sorry

instance: MonadLiftT e1 e2 := sorry

variable (Free: (Type  -> Type) -> (Type -> Type ))
instance: Monad (Free e) := sorry
instance (e:Type -> Type): MonadLift (e) (Free e) := sorry


instance s: Sig where
  sig := e2

def test: Free (s.sig) Unit := do
  let test_e2: e2 Unit := sorry
  let e1_val <- test_e2 -- lifts just fine
  let test_e1: e1 Unit := sorry
  have lifter: MonadLiftT e1 e2 := inferInstance
  let e1_val <- test_e1 -- does not lift

  return



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
    | buyer =>  BuyerEff ⨳ Log
    | seller =>  SellerEff ⨳ Log
  executable x := match x with
    | buyer =>  inferInstance
    | seller =>  inferInstance

variable (ep3: Location)

--instance [sig: LocSig Location]: MonadLiftT (sig.sig l) IO := sig.executable l

variable (t:Type)

instance ins (eff1 eff2 sum: Type -> Type) [MonadLift (SumEff eff1 eff2) (Freer sum)]: MonadLiftT eff1 (Freer sum) where
  monadLift x := sorry
instance (eff1 eff2 sum: Type -> Type) [MonadLift (SumEff eff1 eff2) (Freer sum)]: MonadLiftT eff2 (Freer sum) where
  monadLift x := sorry

class A where
  M:  (Type -> Type 1)
  executable: MonadLiftT M IO := sorry




#eval true && ! true


--set_option trace.Meta.synthInstance true


def book_seller (ep: Location): Choreo ep (Option (String @ buyer#ep)):= do


  let test: MonadLiftT BuyerEff (BuyerEff ⨳ Log) := inferInstance
  have: MonadLift Log (BuyerEff ⨳ Log) := inferInstance
  have: MonadLift (SellerEff) (SellerEff ⨳ Log) := inferInstance
  have: MonadLift (Log)  (SellerEff ⨳ Log):= inferInstance
  let budget <- locally buyer (info "2")
  let budget <- locally buyer get_budget
  let title <- locally buyer get_title


  let title' <- title ~> seller

  let price <- (lookup_price (⤉ title')) @ seller ~~> buyer

  let d: Bool @ buyer#ep <- locally buyer do return ((⤉budget) >= (⤉price))

  locally buyer (
    print2 s!"budget {⤉budget} -- {⤉price}")

  branch d fun
  | true => do
    let date <- deliveryDate @ seller ~~> buyer
    return some date
  | false => do

    locally seller do
      warning s!"the customer declined the purchase"

    locally buyer do
      error s!"{⤉ title} has a price of {⤉ price} exceeding your budget of {⤉ budget}!"

     return none

abbrev net := NetEff buyer

abbrev send_b (r:Location) (v: μ) (p: r ≠ buyer := by decide) [Serialize μ] := NetEff.send r p v
abbrev recv_b (r:Location) (μ:Type) (p: r ≠ buyer := by decide) [Serialize μ] := NetEff.recv r p μ
abbrev send_s (r:Location) (v: μ) (p: r ≠ seller := by decide) [Serialize μ] := NetEff.send r p v
abbrev recv_s (r:Location) (μ:Type) (p: r ≠ seller := by decide) [Serialize μ] := NetEff.recv r p μ

abbrev send (s r:Location) (v: μ) (p: r ≠ s := by decide) [Serialize μ] := NetEff.send r p v
abbrev recv (s r:Location) (μ:Type) (p: r ≠ s := by decide) [Serialize μ] := NetEff.recv r p μ

def buyer': LocalM buyer (Option (String)):= do

  let test: MonadLiftT BuyerEff (BuyerEff ⨳ Log) := inferInstance

  let budget <- get_budget
  let title <- get_title
  send_b seller title
  let price <- recv buyer seller Nat

  if budget >= price then
    let date <- recv buyer seller String
    return some date
  else
    return none

def seller': LocalM seller Unit:= do
  let test: MonadLiftT SellerEff (SellerEff ⨳ Log) := inferInstance
  let title' <- recv seller buyer String
  let price <- (lookup_price  title')
  send_s buyer price
  let choice <- recv seller buyer Bool
  if choice then
    let date <- deliveryDate
    send seller buyer date



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
