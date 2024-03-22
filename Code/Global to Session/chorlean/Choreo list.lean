import chorlean.Effects
import chorlean.Network
import Std.Data.Option.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Finmap
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.IntervalCases
variable {α β: Type} -- alpha beta als normaler Type
variable {δ: Type} [DecidableEq δ]  -- delta als Location Type
variable {μ: Type} [Serialize μ]  -- mu wegen msg Type


-- class Network {δ:Type} (ep: δ) where
--   com {μ} [Serialize μ]: {s: δ} -> GVal' s ep μ -> (r: δ) -> NetM (GVal' r ep μ)

inductive GVal' (owners: Finset δ) (endpoint: δ) (α: Type)   where
| Wrap:  (endpoint ∈ owners) -> α -> GVal' owners endpoint α
| Empty: ¬ (endpoint ∈ owners) -> GVal' owners endpoint α

@[reducible] def GVal'.owner {δ} {o:Finset δ} {ep:δ} [DecidableEq δ] (_gv:GVal' o ep α (δ:=δ)) : List δ := o
@[reducible] def GVal'.dataType {δ} {o: Finset δ} {ep:δ} (_gv:GVal' o ep α (δ:=δ)) : Type := α


variable {δ: Type} [DecidableEq δ]  -- delta als Location Type

def GVal'.wrap (loc: δ) (endpoint: δ) (v:α) : GVal' {loc} endpoint α :=
  let owners: Finset δ := ⟨Multiset.ofList [loc], by simp⟩
  if h:(endpoint ∈ owners) then
    GVal'.Wrap h v
  else
    GVal'.Empty h

def GVal'.unwrap {owners: Finset δ} {endpoint: δ}: GVal' owners endpoint α -> (endpoint ∈ owners) -> α
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction

def GVal'.reduce {α:Type}  (gv: GVal' owners ep α ) (complete: ∀ (loc : δ),  (loc ∈ owners)):  α :=
  gv.unwrap (complete ep)

instance {owners: Finset δ} {ep: δ} [ToString μ]: ToString (GVal' owners ep μ) where
  toString x :=
    if h:(ep ∈ owners) then
      let val := x.unwrap h
      toString val
    else
      "Empty"

@[reducible] def LVal' {ep:δ} (α:Type) (owners :Finset δ)  := GVal' owners ep α

class Unpack' (owners: Finset δ) (ep: δ) (α : Type) where
  unpack : GVal' loc ep α → α

notation:55 α " @ " owner " # " ep  => GVal' owner ep α

variable (ep: δ)

notation:55 α "@" owner =>  LVal' owner α

abbrev tempp' (owner: Finset δ) (α:Type) := GVal' owner ep α

notation:55 α "@@" owner =>  tempp' α owner


#check LocalM


-- type with effect signature
class LocSig (δ:Type) where
  sig: δ -> (Type -> Type 1)
  executable: ∀ (l:δ), MonadLiftT (sig l) IO


abbrev LV {owners: Finset δ} (o ep: δ) (α:Type) (_:o ∈ owners) := GVal' owners ep α

instance [sig: LocSig δ]: MonadLiftT (sig.sig l) IO := sig.executable l

inductive ChorEff (ep:δ) [LocSig δ]: Type -> Type 1 where
--| Send_recv {μ} [Serialize μ] : {s:δ} -> (ex: s ∈ owners) -> LV s ep μ ex  -> (r:δ) -> ChorEff ep (GVal' (owners ∪ {r}) ep μ)
| Local {μ:Type} [DecidableEq δ] [Serialize μ] : (loc:δ) -> (confidants: Finset δ) ->  ([∀ x, Unpack loc ep x] -> Freer (LocSig.sig loc)  μ) -> ChorEff ep (GVal' confidants ep  μ)


inductive Choreo (ep:δ) [LocSig δ]: Type -> Type 1  where
| Cond {μ} {α} {decider:δ} {owners: Finset δ} (ex: decider ∈ owners) [DecidableEq δ] [FinEnum δ] [Serialize μ]: GVal decider ep μ -> (μ -> Choreo ep α) -> Choreo ep α
| Do {α β} :  ChorEff ep β -> (β -> Choreo ep α) -> Choreo ep α
| Return {α}: α -> Choreo ep α

def Choreo.bind {ep:δ} [LocSig δ]{α β: Type} :
  Choreo ep α → (α → Choreo ep β) → Choreo ep β
| Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
| Choreo.Cond ex lv next, next' =>
  Choreo.Cond ex lv (fun x => bind (next x) next')
| Choreo.Return v, next' => next' v

instance {δ:Type} [DecidableEq δ]  [LocSig δ]{ep:δ}: Monad (Choreo (δ := δ) (ep := ep)) where
  pure x := Choreo.Return x
  bind  := Choreo.bind



def com {s: δ} (v: μ) (r: Finset δ): NetM ep (GVal' r ep μ) := do
  let progs: List (Σ (r: δ), NetM ep (GVal r ep μ)) :=
      (r.toList).map (fun x => ⟨x, do
        if h2:(x = s) then

          return GVal.Wrap sorry ep res
        else
          NetEff.send x h2 v (ep:= ep)
          se
        elsecom gv x⟩)
  if h:( s = ep) then
    NetEff.send r (h2) v
    if h2:(ep ∈ r) then
      return GVal'.Wrap h2 v
    else
      --
      return GVal'.Empty h2
  else
    if h2:(r = ep) then
      let v <- NetEff.recv s h μ
      return GVal.Wrap h2 v
    else
      return GVal.Empty h2


-- projects a ChorEff to a LocalM by adding the neccesarry NetEffects
def ChorEff.epp' (ep:δ) [LocSig δ] [FinEnum δ] {α : Type}: ChorEff ep α → LocalM ep (LocSig.sig ep) α
| ChorEff.Local loc confidants comp (μ := μ ) => do


  if h:( loc = ep) then
    have (x:Type) : Unpack loc ep x := ⟨fun gv => gv.unwrap h⟩
    let local_prog: Freer (LocSig.sig ep) μ := cast (by simp [h]) comp
    let res <- local_prog


    let progs: List (Σ (r: δ), NetM ep (GVal r ep μ)) :=
      (confidants.toList).map (fun x => ⟨x, do

        if h2:(x = loc) then
          return GVal.Wrap sorry ep res
        else
          se
        elsecom gv x⟩)
    sorry




  if h: (ep ∈ confidants) then
    if h2: (loc = ep) then
      have (x:Type) : Unpack loc ep x := ⟨fun gv => gv.unwrap h2⟩
      let local_prog: Freer (LocSig.sig ep) α  := cast (by simp [h2]) comp
      let res <- local_prog
      return GVal'.Wrap h res
    else
      let m <- NetEff.recv loc h2 α
      return GVal'.Wrap h m
  else
      return GVal'.Empty h



-- instance EPP2 (ep:δ) [LocSig δ]: MonadLiftT (ChorEff ep) (LocalM δ (LocSig.sig ep)) where
--   monadLift := ChorEff.epp' ep

-- projects a Choreo to a LocalM by broadcasting choices and projecting the Choreffects
def Choreo.epp' (ep:δ) [LocSig δ] [FinEnum δ] {α : Type}: Choreo ep α → LocalM ep (LocSig.sig ep) α
 | Choreo.Cond gv cont => do
    let choice <- broadcast' gv
    Choreo.epp' ep (cont choice)
  | Choreo.Return v => return v

  | Choreo.Do eff cont => do
    let res <- eff.epp' ep
    Choreo.epp' ep (cont res)


-- Lifts a Choreo into the localM Program with the endpoint signature.
-- to be liftable into IO however a Lift instance for NetEff needs to be provided aswell
instance ChoreoEPP (ep:δ) [LocSig δ] [FinEnum δ]: MonadLiftT (Choreo ep) (LocalM ep (LocSig.sig ep)) where
  monadLift := Choreo.epp' ep

--(as: δ × δ -> Address := default_adress)
instance EPP  [FinEnum δ] [Repr δ] [LocSig δ]
  (ep:δ) (net: SockNet ep) : MonadLiftT (Choreo ep) IO where
  monadLift x :=
    let _netlift := NetEPP ep net
    let _ep_io_lift := LocSig.executable ep
    ((Choreo.epp' ep) x)

notation:max "⤉" gv:40 => Unpack.unpack gv

def toChoreo  [LocSig δ] (eff: ChorEff ep a (δ:=δ)): Choreo ep a:=
   Choreo.Do eff (Choreo.Return)

def send_recv {s:δ} (gv: GVal' s ep μ) (r: δ)  [LocSig δ]:=
  toChoreo (ChorEff.Send_recv gv r )

def locally  [LocSig δ] (loc: δ)  (comp: [∀ x, Unpack loc ep x] -> Freer (LocSig.sig loc) α):=
  toChoreo (ChorEff.Local loc comp) (a:= α @ loc # ep)


def branch {decider:δ} [LocSig δ] (gv: GVal' decider ep μ) (cont: μ -> Choreo ep α) [FinEnum δ] :=
    Choreo.Cond gv cont

def broadcast {s:δ}  (gv: GVal' s ep μ) [LocSig δ] [FinEnum δ] :=
  toChoreo (ChorEff.Broadcast gv)

def scatter {s:δ}  (gl: GVal' s ep (List μ)) [LocSig δ] [FinEnum δ] :=
  toChoreo (ChorEff.Scatter gl)

-- def collect (v:  μ) (r:δ) [LocSig δ] [FinEnum δ] [Repr δ]: Choreo ep (GVal' r ep (List μ)) :=
--   toChoreo (ChorEff.Gather gl r)

def gather (gl: List μ) (r:δ) [LocSig δ] [FinEnum δ] [Repr δ]: Choreo ep (GVal' r ep (List μ)) :=
  toChoreo (ChorEff.Gather gl r)

-- structure ScatterResult (sender ep:δ) (data: (List μ)) [Serialize μ] [FinEnum δ] where
--   chunks: List (Σ (loc: δ), GVal' loc ep (List μ))
--   complete:  ∀ (l: δ), (chunks.dlookup l).isSome
--   scattered: ∀ (l1: δ), (h: l1 = ep) ->
--     let chunk := (((chunks.dlookup l1).get (complete l1)).unwrap h)

--   equal_sizes: ∀ (l1: δ), (h: l1 = ep) -> (((chunks.dlookup l1).get (complete l1)).unwrap h).length = data.length / (FinEnum.card δ)

#eval [1,2,3,4,5,6].split




-- def only [LocSig δ] {ep:δ} (p: δ -> Prop) [Decidable (p ep)] {owner:{l:δ // p l}} (schor: (ep': {l:δ // p l}) ->  Choreo ep' (GVal' owner ep' α) (δ:={l:δ // p l}))  [FinEnum δ] :Choreo ep (GVal' owner.val ep α) := do
--   if h:(p ep) then do
--     let ep2: {l:δ // p l} := ⟨ep, h⟩
--     let temp := schor ep2
--     let temp2: Choreo ep (GVal' owner.val ep α) := cast (by simp[h]) temp
--     temp2
--   else
--     sorry


def send_recv_comp [LocSig δ] (s r: δ)  [Serialize μ] (comp: [∀ x, Unpack s ep x] -> Freer (LocSig.sig s) μ):=
  do
  let gv <- locally s comp
  toChoreo (ChorEff.Send_recv gv r) (a:= GVal' r ep μ)


notation:55 lv "~>" receiver => send_recv lv receiver


notation:55 comp "@" sender "~~>" receiver  => send_recv_comp sender receiver comp


-- coerces GVal' Unit types into Unit
-- lets you omit variable assignement with let in do notation for Unit Choreos
instance: CoeOut (GVal' o ep Unit) Unit where
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
