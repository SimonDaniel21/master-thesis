import Test.my_utils
import chorlean.Effects
import chorlean.Network
import Std.Data.Option.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Finmap
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.IntervalCases
variable {α β: Type} -- alpha beta als normaler Type
variable {δ: Type} [DecidableEq δ]  -- delta als Location Type
variable {μ: Type} [Serialize μ]  -- mu wegen msg Type


-- class Network {δ:Type} (ep: δ) where
--   com {μ} [Serialize μ]: {s: δ} -> GVal s ep μ -> (r: δ) -> NetM (GVal r ep μ)


structure SockChannel (sender receiver ep: δ ) where
  recv_sock: GVal receiver ep Socket
  send_sock: GVal sender ep Socket

def init_sending_channel (sender ep:δ) (addr: Address):  IO (GVal sender ep Socket) := do
  if h:(sender = ep) then
    let sock <- addr.connect_to
    return GVal.Wrap h sock
  else
    return GVal.Empty h

def init_receiving_channel  (receiver ep: δ) (addr: Address):  IO (GVal receiver ep Socket) := do
  if h:(receiver = ep) then
    let sock <- addr.listen_on
    return GVal.Wrap h sock
  else
    return GVal.Empty h

-- epp for initializing one network socket
def init_channel [Repr δ] (sender receiver ep: δ) (addr: Address):  IO (SockChannel sender receiver ep) := do
  if(dbg_print_init_sockets ∧ sender = ep) then
    IO.println s!"connecting out {reprStr sender} -> {reprStr receiver}"
  if(dbg_print_init_sockets ∧ receiver = ep) then
    IO.println s!"connecting in  {reprStr sender} -> {reprStr receiver}"
  let recv_sock <- init_receiving_channel receiver ep addr
  let send_sock <- init_sending_channel sender ep addr
  return ⟨recv_sock, send_sock⟩

structure SockNet {δ:Type} [DecidableEq δ] (ep: δ) [DecidableEq δ] where
  channels: List (Σ (id: δ×δ), SockChannel id.1 id.2 ep)
  complete: ∀ (k : δ×δ), (k.1 ≠ k.2) -> (channels.dlookup k).isSome

def SockNet.getChannel {δ:Type} [DecidableEq δ]  {ep: δ} (net:SockNet ep) (k:δ×δ) (not_self: k.1 ≠ k.2) : SockChannel k.1 k.2 ep :=
  (net.channels.dlookup k).get (by simp [net.complete, not_self])

def init_network [DecidableEq δ] [Repr δ] [FinEnum δ] (ep: δ) (as:  (k:δ×δ) -> (k.1 ≠ k.2) -> Address := default_adress) : IO (SockNet ep) := do

  let filtered := (FinEnum.toList (δ×δ)).filter (fun k => k.1 ≠ k.2)
  let progs: List (Σ (k: (δ×δ)), Address)  := filtered.map (fun k => ⟨k, as k (by sorry)⟩ )
  let channels_prog: IO (List (Σ (k: δ×δ), SockChannel k.1 k.2 ep)):= progs.mapM (fun x => do
    let id := x.1
    let chan: SockChannel id.1 id.2 ep <-  init_channel id.1 id.2 ep x.2
    return ⟨id, chan⟩ )
  let cs <- channels_prog

  if(dbg_print_init_sockets) then
    IO.println ""
  return {
            channels := cs
            complete := fun k => by
              simp [List.dlookup_isSome, List.keys]
              sorry
              done
          }


#check LocalM


-- type with effect signature
class LocSig (δ:Type) where
  sig: δ -> (Type -> Type 1)
  executable: ∀ (l:δ), MonadLiftT (sig l) IO

inductive ChorEff (ep:δ) [LocSig δ]: Type -> Type 1 where
| Send_recv {μ} [Serialize μ] : {s:δ} -> GVal s ep μ  -> (r:δ) -> ChorEff ep (GVal r ep μ)
| Local {α} [DecidableEq δ] : (loc:δ) -> ([∀ x, Unpack loc ep x] -> LocalM δ (LocSig.sig loc) α) -> ChorEff ep (GVal loc ep α)
--| Cond2 {decider:δ}: GVal decider ep Bool -> (Freer (ChorEff ep) a) -> (Freer (ChorEff ep) a) -> ChorEff ep a

abbrev Choreo (ep:δ) [LocSig δ] := Freer (ChorEff ep)


-- def ChorEff.epp [LocSig δ m]: ChorEff ep a (δ:=δ) (m:=m) -> (Network ep) -> (LocalM (LocSig.sig m ep)) a
-- | ChorEff.Send_recv gv receiver, net => do
--   (net.com gv receiver)
-- | ChorEff.Local loc comp, net => do
--     if h:( loc = ep) then
--       have (x:Type) : Unpack loc ep x := ⟨fun gv => gv.unwrap h⟩
--       let res <- cast (by simp [h]) comp
--       return GVal.Wrap h res
--     else

instance EPP (ep:δ) [sig: LocSig δ]: MonadLiftT (ChorEff ep) (LocalM δ (LocSig.sig ep)) where
  monadLift e := match e with
  | ChorEff.Send_recv gv r => do
    let s := gv.owner
    if h:( s = ep) then
      let v := gv.unwrap h
      if h2:(r = ep) then
        return GVal.Wrap h2 v
      else

        let v := gv.unwrap h
        -- if dbg_print_net_msgs then
        --   IO.println s!"--> {reprName r} --> {Serialize.pretty v}"
        NetEff.send r v

        return GVal.Empty h2
    else
      if h2:(r = ep) then
        let v <- NetEff.recv s gv.dataType
        -- if dbg_print_net_msgs then
        --   IO.println s!"<-- {reprName s} <-- {Serialize.pretty v}"
        return GVal.Wrap h2 v
      else
        return GVal.Empty h2
  | ChorEff.Local loc comp => do
      if h:( loc = ep) then
        have (x:Type) : Unpack loc ep x := ⟨fun gv => gv.unwrap h⟩
        let res <- cast (by simp [h]) comp
        return GVal.Wrap h res
      else
        return  GVal.Empty h




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

instance: MonadLiftT (BuyerEff) IO where
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
    | buyer =>  BuyerEff
    | seller =>  SellerEff
  executable x := match x with
    | buyer => inferInstance
    | seller => inferInstance

notation:55 lv "~>" receiver => ChorEff.send_recv lv receiver
notation:55 "⤉" gv => (Unpack.unpack gv)

abbrev locally (loc: δ) [LocSig δ]
  (comp: [∀ x, Unpack loc ep x ] ->
    (LocalM δ (LocSig.sig loc) ) α):
      Choreo ep (GVal loc ep α) :=do
  let temp: (GVal loc ep α) <- (ChorEff.Local loc comp (ep:=ep))
  return temp


def myProg (ep: Location): Choreo ep Nat := do

  let budget <- locally buyer (BuyerEff.get_budget)
  let title <- locally  buyer do BuyerEff.get_title

  let title' <- ChorEff.Send_recv title seller
  let price <- locally seller do
    SellerEff.lookup_price (⤉title')
  let price <- ChorEff.Send_recv price buyer

  -- let _ <- locally seller do
  --   LogEff.info s!"got book title: {⤉title'}"

  --  let _ <- locally buyer do
  --   LogEff.info s!"the price is {⤉price}, negotiate with friend"
  return 22

-- instance EPP3 {δ:Type} (ep:δ) [sig: LocSig δ] [net: Network ep]: MonadLiftT (ChorEff ep) IO where
--   monadLift x := match x with
--   | ChorEff.Send_recv gv receiver => do
--     (net.com gv receiver)
--   | ChorEff.Local loc comp => do
--       if h:( loc = ep) then
--         have (x:Type) : Unpack loc ep x := ⟨fun gv => gv.unwrap h⟩
--         let res <- (sig.executable ep) comp
--         return GVal.Wrap h res
--       else
--         return  GVal.Empty h

def main33 (args : List String): IO Unit := do
  let mode := args.get! 0

  let ep_opt := FinEnum.ofString? mode

  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h
    --have: Network ep := net.toNet
    have := (sig.executable ep)
    IO.println (s!"starting bookseller 50 50")
    have test5: MonadLiftT (Choreo ep) (LocalM Location (LocSig.sig ep)) := inferInstance
    have test3: MonadLiftT (NetEff Location) IO := NetEPP ep
    --have test3: MonadLiftT (Choreo ep) IO:= inferInstance
    have localprog := test5.monadLift (myProg ep)
    let res <- localprog

    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()


#eval main33

-- def send_recv_comp (s r: δ) [LocSig δ m] [Serialize μ]
--   (comp: [∀ x, Unpack s ep x] -> (LocalM (LocSig.sig m loc)) μ):
--     Choreo ep (GVal r ep μ) (δ:=δ) (m:=m) :=
--   do
--   let gv <- locally s comp
--   toChoreo (ChorEff.Send_recv gv r) (a:= GVal r ep μ)



--axiom net2: ∀ (o ep:δ) (p: o = ep) (gv: GVal o ep μ) (chor: Choreo ep α), gv.unwrap (p) =





-- notation:55 sender "~>" receiver "#" comp => send_recv_comp sender receiver comp

-- notation:55 sender "~~>" receiver comp => send_recv_comp sender receiver comp

def cast_gv {owner ep:δ}  (gv: GVal owner ep α ) [k:∀ x, Coe (GVal owner ep x) x]: α :=
  let c := k α
  c.coe gv

-- works similiar to normal coersion arrow ↑ but always casts to the underlying type
notation:55 "⤉" gv => (Unpack.unpack gv)

-- syntax "send " ident (" from " ident)? " to " term (" as " ident)?: doElem

-- macro_rules
-- | `(doElem|send $i to $r) => `(doElem| let $i:ident := <- (send_recv $i $r))
-- | `(doElem|send $i to $r as $y) => `(doElem| let $y:ident := <- (send_recv $i $r))
-- | `(doElem|send $i from $i2 to $r) => `(doElem| let $i:ident := <- (send_recv (sender:=$i2) $i $r))
-- --| `(doElem|send $i from $i2 to $r as $y) => `(doElem| let $i := <- (send_recv $i $r (sender:=$i2)) )

syntax "decision " ident term " else " term: term

macro_rules
| `(decision $i $t1 else $t2) => `(Choreo.Cond2 $i ($t1) ($t2))

inductive Example_Location
| alice | eve | bob
deriving Repr, Fintype

open Example_Location


instance : FinEnum Example_Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Example_Location).symm


inductive BobEff: Type -> Type 1
| Print: String -> BobEff Unit




-- def bobprint (s: String): (Freer BobEff) Unit := Effect.ToFreer (BobEff.Print s)

-- def multiMonad: Choreo ep F Nat := do
--   let lv: LVal bob Nat <- locally .bob do
--     let lst: List Nat := []
--     let temp2 <- monadLift (bobprint "heyoo2")
--     let temp2 <- monadLift (recv (sorry) Nat)
--     return 2
--   return 3


-- def multiMonad2: Choreo ep F Nat := do
--   let lv: LVal alice Nat <- locally .alice do
--     let lst: List Nat := []
--     let temp2 <- monadLift (print "heyoo2")

--     return 2
--   return 3
