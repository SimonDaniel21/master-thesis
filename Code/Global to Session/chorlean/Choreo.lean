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

def f (v:μ) := Serialize.to_bytes v

class Test where
  t: Type -> Type
  [m: Monad t]

def testing: Unit :=
  let t: Test := ⟨IO⟩

  have: Monad t.t := t.m

  let prog: t.t Nat := do
    return 3
  ()

structure Chunk(ep:δ) (μ:Type) [Serialize μ] [FinEnum δ] where
  data: (List (Σ (l:δ), GVal l ep μ))
  complete: ∀ (l:δ), (data.dlookup l).isSome


instance {l:δ} (ep:δ) [FinEnum δ] : Coe (Chunk ep μ) (GVal l ep μ) where
  coe x :=
    (x.data.dlookup l).get (x.complete l)

instance {l:δ} (ep:δ) [FinEnum δ] : CoeOut (Chunk ep μ) μ where
  coe x :=
    GVal.reduce x.data (x.complete)


--instance [sig: LocSig δ]: MonadLiftT (sig.sig l) IO := sig.executable l

inductive ChorEff (ep:δ) [LocSig δ]: Type -> Type 1 where
| Send_recv {μ} [Serialize μ] : {s:δ} -> GVal s ep μ  -> (r:δ) -> ChorEff ep (GVal r ep μ)
| Local {α} [DecidableEq δ] : (loc:δ) -> ([∀ x, Unpack loc ep x] -> Freer (LocSig.sig loc) α) -> ChorEff ep (GVal loc ep α)
| Broadcast {μ} [Serialize μ] : {s:δ} -> GVal s ep μ -> ChorEff ep μ
| Scatter {μ} [Serialize μ] : {s:δ} -> GVal s ep (List μ)  -> ChorEff ep (List μ)
| Gather {μ} [Serialize μ] [Repr δ]: List μ -> (r:δ) -> ChorEff ep (GVal r ep (List μ))


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
        NetEff.send r (h2) v
        return GVal.Empty h2
    else
      if h2:(r = ep) then
        let v <- NetEff.recv s h μ
        return GVal.Wrap h2 v
      else
        return GVal.Empty h2


#eval [4,1,5,2,5].fromTo 3 2


  -- scatters a List of Data evenly across all δ Locations. The last δ gets fewer items if gl.length is not devidable by the location number
def com_scatter {s: δ} (gl:GVal s ep (List μ)) (r: δ) [FinEnum δ]: NetM ep (GVal r ep (List μ)) := do
  let id := FinEnum.equiv r
  let s := gl.owner
  if h:( s = ep) then
    let l := gl.unwrap h
    let chunk_size := l.length / (FinEnum.card δ)
    let rest := l.length % (FinEnum.card δ)
    dbg_trace s!"rest: {rest}"


    let chunk_start := (id.val * chunk_size) + (min rest id.val)

    let chunk_size :=
      if id < rest then
        chunk_size + 1
      else
        chunk_size


    dbg_trace s!"chunk_start {chunk_start}"
    dbg_trace s!"chunk_size {chunk_size}"

    let chunk: List μ :=
       l.fromTo chunk_start chunk_size

    if h2:(r = ep) then
      return GVal.Wrap h2 chunk
    else
      NetEff.send r (h2) chunk
      return GVal.Empty h2
  else
    if h2:(r = ep) then
      let v <- NetEff.recv s h (List μ)
      return GVal.Wrap h2 v
    else
      return GVal.Empty h2


-- projects a broadcast operation to a NetM
def broadcast' [FinEnum δ] {s: δ} (gv:GVal s ep μ): NetM ep μ := do

  let progs: List (Σ (r: δ), NetM ep (GVal r ep μ)) :=
    (FinEnum.toList δ).map (fun x => ⟨x, com gv x⟩)

  let mut gvs: List (Σ (r: δ), (GVal r ep μ)) := []
  -- mapM sollte eigentlich auch gehen
  for p in progs do
    let gv <- p.2
    gvs := gvs.concat ⟨p.1, gv⟩

  return GVal.reduce gvs (by sorry)

def scatter' {μ} [Serialize μ] {sender ep:δ} (gl: GVal sender ep (List μ)) [FinEnum δ] [LocSig δ]: NetM ep (List μ) := do
  let progs: List (Σ (r: δ), NetM ep (GVal r ep (List μ))) :=
  (FinEnum.toList δ).map (fun x => ⟨x, com_scatter gl x⟩)

  let mut gls: List (Σ (r: δ), (GVal r ep (List μ))) := []
  -- mapM sollte eigentlich auch gehen
  for p in progs do
    let gv <- p.2
    gls := gls.concat ⟨p.1, gv⟩

  return GVal.reduce gls (by sorry)

def gather' {μ} [Serialize μ] {ep:δ} (ls: List μ) (r:δ) [FinEnum δ] [LocSig δ] [Repr δ]: NetM ep (GVal r ep  (List μ)) := do

  let progs: List (NetM ep (GVal r ep (List μ))) :=
   (FinEnum.toList δ).map (fun x =>
    let gl := GVal.wrap x ep ls
    com gl r)


  if h:(r = ep) then

    let mut gls: List μ := []

    for p in progs do
      let gl <- p
      let l' := gl.unwrap h
      gls := gls.append l'

    return GVal.Wrap h gls

  else
    for p in progs do
      let _ <- p
    return GVal.Empty h

-- projects a ChorEff to a LocalM by adding the neccesarry NetEffects
def ChorEff.epp' (ep:δ) [LocSig δ] [FinEnum δ] {α : Type}: ChorEff ep α → LocalM ep α
| ChorEff.Send_recv gv r => com gv r
| ChorEff.Broadcast gv => broadcast' gv
| ChorEff.Scatter gl => scatter' gl
| ChorEff.Gather gl r => gather' gl r (ep:=ep)
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
def Choreo.epp' (ep:δ) [LocSig δ] [FinEnum δ] {α : Type}: Choreo ep α → LocalM ep α
 | Choreo.Cond gv cont => do
    let choice <- broadcast' gv
    Choreo.epp' ep (cont choice)
  | Choreo.Return v => return v

  | Choreo.Do eff cont => do
    let res <- eff.epp' ep
    Choreo.epp' ep (cont res)


-- Lifts a Choreo into the localM Program with the endpoint signature.
-- to be liftable into IO however a Lift instance for NetEff needs to be provided aswell
instance ChoreoEPP (ep:δ) [LocSig δ] [FinEnum δ]: MonadLiftT (Choreo ep) (LocalM ep) where
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

def send_recv {s:δ} (gv: GVal s ep μ) (r: δ)  [LocSig δ]:=
  toChoreo (ChorEff.Send_recv gv r )

def locally  [LocSig δ] (loc: δ)  (comp: [∀ x, Unpack loc ep x] -> Freer (LocSig.sig loc) α):=
  toChoreo (ChorEff.Local loc comp) (a:= α @ loc # ep)


def branch {decider:δ} [LocSig δ] (gv: GVal decider ep μ) (cont: μ -> Choreo ep α) [FinEnum δ] :=
    Choreo.Cond gv cont

def broadcast {s:δ}  (gv: GVal s ep μ) [LocSig δ] [FinEnum δ] :=
  toChoreo (ChorEff.Broadcast gv)

def scatter {s:δ}  (gl: GVal s ep (List μ)) [LocSig δ] [FinEnum δ] :=
  toChoreo (ChorEff.Scatter gl)

-- def collect (v:  μ) (r:δ) [LocSig δ] [FinEnum δ] [Repr δ]: Choreo ep (GVal r ep (List μ)) :=
--   toChoreo (ChorEff.Gather gl r)

def gather (gl: List μ) (r:δ) [LocSig δ] [FinEnum δ] [Repr δ]: Choreo ep (GVal r ep (List μ)) :=
  toChoreo (ChorEff.Gather gl r)

-- structure ScatterResult (sender ep:δ) (data: (List μ)) [Serialize μ] [FinEnum δ] where
--   chunks: List (Σ (loc: δ), GVal loc ep (List μ))
--   complete:  ∀ (l: δ), (chunks.dlookup l).isSome
--   scattered: ∀ (l1: δ), (h: l1 = ep) ->
--     let chunk := (((chunks.dlookup l1).get (complete l1)).unwrap h)

--   equal_sizes: ∀ (l1: δ), (h: l1 = ep) -> (((chunks.dlookup l1).get (complete l1)).unwrap h).length = data.length / (FinEnum.card δ)

#eval [1,2,3,4,5,6].split




-- def only [LocSig δ] {ep:δ} (p: δ -> Prop) [Decidable (p ep)] {owner:{l:δ // p l}} (schor: (ep': {l:δ // p l}) ->  Choreo ep' (GVal owner ep' α) (δ:={l:δ // p l}))  [FinEnum δ] :Choreo ep (GVal owner.val ep α) := do
--   if h:(p ep) then do
--     let ep2: {l:δ // p l} := ⟨ep, h⟩
--     let temp := schor ep2
--     let temp2: Choreo ep (GVal owner.val ep α) := cast (by simp[h]) temp
--     temp2
--   else
--     sorry


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


-- weiß gerade nicht ob das nützlich ist
instance: Coe α (GVal ep ep α) where
  coe x := GVal.Wrap (by trivial) x

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
