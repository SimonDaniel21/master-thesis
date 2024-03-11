import Test.my_utils
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


class Network {δ:Type} (ep: δ) where
  com {μ} [Serialize μ]: {s: δ} -> GVal s ep μ -> (r: δ) -> NetM (GVal r ep μ)

def Network.broadcast [FinEnum δ] (net: Network ep) {s: δ} (gv:GVal s ep μ): NetM μ := do

  let progs: List (Σ (r: δ), NetM (GVal r ep μ)) :=
    (FinEnum.toList δ).map (fun x => ⟨x, net.com gv x⟩)

  let mut gvs: List (Σ (r: δ), (GVal r ep μ)) := []
  -- mapM sollte eigentlich auch gehen
  for p in progs do
    let gv <- p.2
    gvs := gvs.concat ⟨p.1, gv⟩

  return GVal.reduce gvs (by sorry)

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

def SockNet.toNet {δ:Type} [Repr δ] [DecidableEq δ] {ep:δ} (snet: SockNet ep): Network ep :=
  ⟨fun gv r => do
    let s := gv.owner
    if h:( s = ep) then
      let v := gv.unwrap h
      if h2:(r = ep) then
        return GVal.Wrap h2 v
      else
        let h3: r != s := sorry
        let sock := (snet.getChannel (s, r) (by sorry)).send_sock.unwrap h
        let v := gv.unwrap h
        -- if dbg_print_net_msgs then
        --   IO.println s!"--> {reprName r} --> {Serialize.pretty v}"
        NetEff.send sock v
        return GVal.Empty h2
    else
      if h2:(r = ep) then
        let sock := (snet.getChannel (s, r) (by simp [h, h2])).recv_sock.unwrap h2
        let v <- NetEff.recv sock gv.dataType
        -- if dbg_print_net_msgs then
        --   IO.println s!"<-- {reprName s} <-- {Serialize.pretty v}"
        return GVal.Wrap h2 v
      else
        return GVal.Empty h2⟩
instance  {δ:Type} [DecidableEq δ] {ep:δ} (snet: SockNet ep): Network ep where
  com gv r := do
    let s:= gv.owner
    if h:( s = ep) then
      let v := gv.unwrap h
      if h2:(r = ep) then
        return GVal.Wrap h2 v
      else
        let h3: r != s := sorry
        let sock := (snet.getChannel (s, r) (by sorry)).send_sock.unwrap h
        let v := gv.unwrap h
        NetEff.send sock v
        return GVal.Empty h2
    else
      if h2:(r = ep) then
        let sock := (snet.getChannel (s, r) (by simp [h, h2])).recv_sock.unwrap h2
        let v <- NetEff.recv sock gv.dataType
        return GVal.Wrap h2 v
      else
        return GVal.Empty h2


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

class LocSig (δ:Type)  (m: Type -> Type) where
  sig: δ -> (Type -> Type 1)
  liftable: ∀ (l:δ), MonadLift (sig l) m

inductive ChorEff (ep:δ) [LocSig δ m]: Type -> Type 1 where
| Send_recv {μ} [Serialize μ] : {s:δ} -> GVal s ep μ  -> (r:δ) -> ChorEff ep (GVal r ep μ)
| Local {α} [DecidableEq δ] : (loc:δ) -> ([∀ x, Unpack loc ep x] -> LocalM (LocSig.sig m loc) α) -> ChorEff ep (GVal loc ep α)
| Calc {α} [DecidableEq δ] : (loc:δ) -> ([∀ x, Unpack loc ep x] -> α) -> ChorEff ep (GVal loc ep α)

inductive Choreo (ep:δ) [LocSig δ m]: Type -> Type 1  where
| Cond {μ} {α} {decider:δ} [DecidableEq δ] [FinEnum δ] [Serialize μ]: GVal decider ep μ -> (μ -> Choreo ep α) -> Choreo ep α
--| Cond2 {decider:δ}: GVal Bool decider ep -> (Choreo a) -> (Choreo a) -> Choreo a
| Do {α β} :  ChorEff ep β (m:=m) -> (β -> Choreo ep α) -> Choreo ep α
| Return {α}: α -> Choreo ep α

def Choreo.bind {ep:δ} [LocSig δ m] {α β: Type} :
  Choreo ep α (m:=m) → (α → Choreo ep β (m:=m)) → Choreo ep β (m:=m)
| Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
| Choreo.Cond lv next, next' =>
  Choreo.Cond lv (fun x => bind (next x) next')
-- | Choreo.Cond2 lv opt_a opt_b, next' =>
--   Choreo.Cond2 lv (bind opt_a next') (bind opt_b next')
| Choreo.Return v, next' => next' v

instance {δ:Type} [DecidableEq δ] {ep:δ} [LocSig δ m] : Monad (Choreo ep (m:=m)) where
  pure x := Choreo.Return x
  bind  := Choreo.bind


def toChoreo [LocSig δ m]  (eff: ChorEff ep a (δ := δ) (m:=m)) : Choreo ep a (m:=m):=
   Choreo.Do eff (Choreo.Return)

def send_recv {s:δ} (gv: GVal s ep μ) (r: δ) [LocSig δ m]: Choreo ep (GVal r ep μ) (m:=m) :=
  toChoreo (ChorEff.Send_recv gv r )

abbrev locally (loc: δ) [LocSig δ m]
  (comp: [∀ x, Unpack loc ep x ] ->
    (LocalM (LocSig.sig m loc)) α):
      Choreo ep (GVal loc ep α) (m:=m)  :=
  toChoreo (ChorEff.Local loc comp) (a:=GVal loc ep α)


--toChoreo (ChorEff.Local loc comp) (a:=GVal loc ep α)

def compute (loc: δ)  [LocSig δ m] (comp: [∀ x, Unpack loc ep x] -> α): Choreo ep (GVal loc ep α) (δ:=δ) (m:=m) :=
  toChoreo (ChorEff.Calc loc comp) (a:=GVal loc ep α)

def branch {decider:δ} [LocSig δ m] (gv: GVal decider ep μ) (cont: μ -> Choreo ep α (δ:=δ) (m:=m)) [FinEnum δ]:
  Choreo ep α (δ:=δ) (m:=m):=
    Choreo.Cond gv cont

-- def send_recv_comp (s r: δ) [LocSig δ m] [Serialize μ]
--   (comp: [∀ x, Unpack s ep x] -> (LocalM (LocSig.sig m loc)) μ):
--     Choreo ep (GVal r ep μ) (δ:=δ) (m:=m) :=
--   do
--   let gv <- locally s comp
--   toChoreo (ChorEff.Send_recv gv r) (a:= GVal r ep μ)



--axiom net2: ∀ (o ep:δ) (p: o = ep) (gv: GVal o ep μ) (chor: Choreo ep α), gv.unwrap (p) =

def ChorEff.epp [LocSig δ m]: ChorEff ep a (δ:=δ) (m:=m) -> (Network ep) -> (LocalM (LocSig.sig m ep)) a
| ChorEff.Send_recv gv receiver, net => do
  (net.com gv receiver)
| ChorEff.Local loc comp, net => do
    if h:( loc = ep) then
      have (x:Type) : Unpack loc ep x := ⟨fun gv => gv.unwrap h⟩
      let res <- cast (by simp [h]) comp
      return GVal.Wrap h res
    else
      return  GVal.Empty h
| ChorEff.Calc loc comp, net => do
    if h:( loc = ep) then
      have (x:Type) : Unpack loc ep x := ⟨fun gv => gv.unwrap h⟩
      let res := comp
      return GVal.Wrap h res
    else
      return  GVal.Empty h

def  Choreo.epp  [LocSig δ m] {a:Type} :
   Choreo ep a (δ:=δ) (m:=m) -> ( Network ep) -> (LocalM (LocSig.sig m ep)) a
| Choreo.Return v, _ => return v
| Choreo.Do eff next, net => do
  let res <- (eff.epp net)
  Choreo.epp (next res) net
| Choreo.Cond gv cont, net => do
  let choice <- (net.broadcast gv)
  (cont choice).epp net




notation:55 lv "~>" receiver => send_recv lv receiver

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


abbrev F : Example_Location → (Type -> Type 1) --also needs [Monad r] of result?
| .alice => PrintEff
| .bob => BobEff
| .eve => PrintEff





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
