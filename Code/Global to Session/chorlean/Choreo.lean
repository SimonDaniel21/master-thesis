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



#check LocalM


-- type with effect signature
class LocSig (δ:Type) where
  sig: δ -> (Type -> Type 1)
  executable: ∀ (l:δ), MonadLiftT (sig l) IO


inductive ChorEff (ep:δ) [LocSig δ]: Type -> Type 1 where
| Send_recv {μ} [Serialize μ] : {s:δ} -> GVal s ep μ  -> (r:δ) -> ChorEff ep (GVal r ep μ)
| Local {α} [DecidableEq δ] : (loc:δ) -> ([∀ x, Unpack loc ep x] -> Freer (LocSig.sig loc) α) -> ChorEff ep (GVal loc ep α)
--| Cond2 {decider:δ}: GVal decider ep Bool -> (Freer (ChorEff ep) a) -> (Freer (ChorEff ep) a) -> ChorEff ep a

inductive Choreo (ep:δ) [LocSig δ]: Type -> Type 1  where
| Cond {μ} {α} {decider:δ} [DecidableEq δ] [FinEnum δ] [Serialize μ]: GVal decider ep μ -> (μ -> Choreo ep α) -> Choreo ep α
| Do {α β} :  ChorEff ep β -> (β -> Choreo ep α) -> Choreo ep α
| Return {α}: α -> Choreo ep α


def Choreo.bind {ep:δ} [LocSig δ]{α β: Type} :
  Choreo ep α → (α → Choreo ep β) → Choreo ep β
| Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
| Choreo.Cond lv next, next' =>
  Choreo.Cond lv (fun x => bind (next x) next')
| Choreo.Return v, next' => next' v

instance {δ:Type} [DecidableEq δ]  [LocSig δ]{ep:δ}: Monad (Choreo (δ := δ) (ep := ep)) where
  pure x := Choreo.Return x
  bind  := Choreo.bind


-- projects a communication operation to a NetM
def com {s: δ} (gv:GVal s ep μ) (r: δ): NetM ep (GVal r ep μ) := do
   let s := gv.owner
    if h:( s = ep) then
      let v := gv.unwrap h
      if h2:(r = ep) then
        return GVal.Wrap h2 v
      else
        let v := gv.unwrap h
        NetEff.send r (h2) v
        return GVal.Empty h2
    else
      if h2:(r = ep) then
        let v <- NetEff.recv s h μ
        return GVal.Wrap h2 v
      else
        return GVal.Empty h2

-- projects a broadcast operation to a NetM
def broadcast [FinEnum δ] {s: δ} (gv:GVal s ep μ): NetM ep μ := do

  let progs: List (Σ (r: δ), NetM ep (GVal r ep μ)) :=
    (FinEnum.toList δ).map (fun x => ⟨x, com gv x⟩)

  let mut gvs: List (Σ (r: δ), (GVal r ep μ)) := []
  -- mapM sollte eigentlich auch gehen
  for p in progs do
    let gv <- p.2
    gvs := gvs.concat ⟨p.1, gv⟩

  return GVal.reduce gvs (by sorry)


-- projects a ChorEff to a LocalM by adding the neccesarry NetEffects
def ChorEff.epp' (ep:δ) [LocSig δ] {α : Type}: ChorEff ep α → LocalM ep (LocSig.sig ep) α
| ChorEff.Send_recv gv r => com gv r
| ChorEff.Local loc comp (α := α ) => do
  if h:( loc = ep) then
    have (x:Type) : Unpack loc ep x := ⟨fun gv => gv.unwrap h⟩
    let local_prog: Freer (LocSig.sig ep) α  := cast (by simp [h]) comp
    let res <- local_prog
    return GVal.Wrap h res
  else
    return  GVal.Empty h

-- instance EPP2 (ep:δ) [LocSig δ]: MonadLiftT (ChorEff ep) (LocalM δ (LocSig.sig ep)) where
--   monadLift := ChorEff.epp' ep

-- projects a Choreo to a LocalM by broadcasting choices and projecting the Choreffects
def Choreo.epp' (ep:δ) [LocSig δ] {α : Type}: Choreo ep α → LocalM ep (LocSig.sig ep) α
 | Choreo.Cond gv cont => do
    let choice <- broadcast gv
    Choreo.epp' ep (cont choice)
  | Choreo.Return v => return v

  | Choreo.Do eff cont => do
    let res <- eff.epp' ep
    Choreo.epp' ep (cont res)


-- Lifts a Choreo into the localM Program with the endpoint signature.
-- to be liftable into IO however a Lift instance for NetEff needs to be provided aswell
instance ChoreoEPP (ep:δ) [LocSig δ]: MonadLiftT (Choreo ep) (LocalM ep (LocSig.sig ep)) where
  monadLift := Choreo.epp' ep

--(as: δ × δ -> Address := default_adress)
instance EPP  [FinEnum δ] [Repr δ] [LocSig δ]
  (ep:δ) (net: SockNet ep) : MonadLiftT (Choreo ep) IO where
  monadLift x :=
    let _netlift := NetEPP ep net
    let _ep_io_lift := LocSig.executable ep
    ((Choreo.epp' ep) x)


notation:55 "⤉" gv => (Unpack.unpack gv)

def toChoreo  [LocSig δ] (eff: ChorEff ep a (δ:=δ)): Choreo ep a:=
   Choreo.Do eff (Choreo.Return)

def send_recv {s:δ} (gv: GVal s ep μ) (r: δ)  [LocSig δ]:=
  toChoreo (ChorEff.Send_recv gv r )

def locally  [LocSig δ] (loc: δ)  (comp: [∀ x, Unpack loc ep x] -> Freer (LocSig.sig loc) α):=
  toChoreo (ChorEff.Local loc comp) (a:= α @ loc # ep)

def branch {decider:δ} [LocSig δ] (gv: GVal decider ep μ) (cont: μ -> Choreo ep α) [FinEnum δ] :=
    Choreo.Cond gv cont

def send_recv_comp [LocSig δ] (s r: δ)  [Serialize μ] (comp: [∀ x, Unpack s ep x] -> Freer (LocSig.sig s) μ):=
  do
  let gv <- locally s comp
  toChoreo (ChorEff.Send_recv gv r) (a:= GVal r ep μ)


notation:55 lv "~>" receiver => send_recv lv receiver


notation:55 comp "@" sender "~~>" receiver  => send_recv_comp sender receiver comp


-- coerces GVal Unit types into Unit
-- lets you omit variable assignement with let in do notation for Unit Choreos
instance: CoeOut (GVal o ep Unit) Unit where
  coe _ := ()



-- def runChoreo {δ:Type} {α:Type} [FinEnum δ] [LocSig δ] [Repr δ] (s: String) (chor: (ep:δ) ->  Choreo ep α): (IO (Option α))  := do

--     let ep_opt: Option δ := FinEnum.ofString? s

--     if h: (ep_opt.isSome) then

--       let ep := ep_opt.get h
--       let _epp := EPP ep

--       let r <- (chor ep)
--       return r
--     else
--       IO.println s!"{s} is no valid endpoint"
--       return none
