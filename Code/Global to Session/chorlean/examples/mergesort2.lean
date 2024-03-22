import chorlean.Choreo
import chorlean.Effects
open Effect

inductive Location (n:Nat)
| Master | Worker: Fin n -> Location n
deriving Repr, Fintype



instance (n:Nat) : FinEnum (Location n) :=
  FinEnum.ofEquiv _ (proxy_equiv% (Location n)).symm

abbrev Workers (n:Nat) := {l: Location n // l ≠ Location.Master}

#eval FinEnum.toList (Workers 2)

open Location

inductive MasterEff: Type -> Type 1 where
| gen:  MasterEff (List Nat)


instance: MonadLift MasterEff IO where
  monadLift m := match m with
    | .gen => do
      let n <- CmdInput.readNat (.some "enter the random List length")
      return (<-generate_random_list n)

instance sig: LocSig (Location n) where
  sig x := match x with
    | Master =>  MasterEff ⨳ Timer ⨳ Sleep ⨳ Log
    | Worker _ =>  Log ⨳ Sleep
  executable x := match x with
    | Master => inferInstance
    | Worker _ => inferInstance

instance {δ:Type} [S: LocSig δ] {p: δ -> Prop}: LocSig (Subtype p (α:=δ)) where
  sig x := match x with
    | ⟨w, _⟩ => S.sig w
  executable x := match x with
     | ⟨w, _⟩ => S.executable w

instance wsig: LocSig (Workers n) := inferInstance

def temp: Location 2 := Worker 1
#eval (FinEnum.card (Location 2))
#eval (FinEnum.equiv (temp) )
#eval ((FinEnum.equiv (temp) +1) == FinEnum.card (Location 2))

instance: MonadLift MasterEff IO where
  monadLift m := match m with
    | .gen => do
      let n <- CmdInput.readNat (.some "enter the random List length")
      return (<-generate_random_list n)


instance (l:Workers n): MonadLiftT Sleep (sig.sig l.val) := match l.val, l.prop with
    | Worker _, _ =>
      have: MonadLiftT Sleep (Log ⨳ Sleep) := inferInstance
      inferInstance

instance (l:Location n): MonadLiftT Sleep (sig.sig l) := match l with
    | Master =>
      have: MonadLiftT Sleep (MasterEff ⨳ Timer ⨳ Sleep ⨳ Log) := inferInstance
      inferInstance
    | Worker _ =>
      have: MonadLiftT Sleep (Log ⨳ Sleep) := inferInstance
      inferInstance

-- takes two sorted lists as an input and produces a sorted list of all numbers
def merge: List Nat -> List Nat -> List Nat
| a::as2, b::bs =>
  if a < b then
    [a] ++ merge as2 ([b] ++ bs)
  else
    [b] ++ merge ([a] ++ as2) bs
| [], [] => []
| as2, [] => as2
| [], bs => bs


def te: Fin 3 := 1
def te2: Fin 3 := (te.val + 3)



def sort_serial: List Nat -> List Nat
| [] => []
| x::[] => [x]
| l => do
  let size := l.length
  let pivot := (Float.floor ((size).toFloat / 2)).toUInt16.toNat
  let ls := l.seperate (pivot)
  let l1 := ls.1
  let l2 := ls.2
  have: sizeOf (List.seperate l (UInt16.toNat (Float.toUInt16 (Float.floor (Nat.toFloat (List.length l) / 2))))).1 < sizeOf l:= sorry
  have: sizeOf (List.seperate l (UInt16.toNat (Float.toUInt16 (Float.floor (Nat.toFloat (List.length l) / 2))))).2 < sizeOf l := sorry
  let l1_sorted := sort_serial l1

  let l2_sorted := sort_serial l2

  merge l1_sorted l2_sorted



#eval sort_serial [1,2,5325,5,2,43,623,62,63426,4634,23,5425,325,3]


abbrev W  {n:Nat} (f: Fin n): Workers n := ⟨Worker f, by simp⟩

-- def sort {n:Nat} (ep: Workers n) (shift: Fin n)
--   (l: GVal (Worker shift) ep (List Nat) ) (iter: Nat := 100) (indents: Nat:= 0):
--   Choreo ep (GVal (Worker shift ) ep (List Nat)) := do

--   have: MonadLiftT Effect.Sleep  (Log ⨳ Sleep) := inferInstance

--   have: MonadLiftT Effect.Sleep  (Freer (LocSig.sig (ep))) := sorry
--   match iter with
--   | i + 1 =>
--     let m := Worker shift
--     let w1: Fin n := ⟨ (shift.val + 1) % n, by sorry⟩

--     let w2: Fin n := ⟨ (shift.val + 2) % n, by sorry⟩

--     let size: Nat @ m # ep <- locally m do return (⤉l).length
--     branch l fun
--     | [] | _::[] =>
--       return l
--     | a::as2 => do
--       --let sizef: Float @ "M" <- locally "M" f⤉⤉=> (⤉size).toFloat
--       let pivot <- locally m do return (Float.floor ((⤉size).toFloat / 2)).toUInt16.toNat
--       let ls: (List ℕ × List ℕ) @ m # ep <- locally m do return  (⤉l).seperate (⤉pivot)
--       let l1 <- locally m do return (⤉ls).fst
--       let l2 <- locally m do return (⤉ls).snd


--       --let _ <- locally m do
--         --LogEff.info s!"{repeat_string "  " indents}splitting {⤉l1}{⤉l2}"

--       --have h: l1 < l.length := by sorry

--       let l1: (List ℕ) @ (W w1) # ep <- l1 ~> (W w1)
--       let l2: (List ℕ) @ (W w2) # ep <- l2 ~> (W w2)
--       let l1_sorted:  (List ℕ) @ (W w1) # ep <- cast (by sorry) (sort ep w1 (cast (by sorry) l1) (indents+1))
--       let l2_sorted:  (List ℕ) @ (W w2) # ep <- cast (by sorry) (sort ep w2 (cast (by sorry) l2) (indents+1))

--       --let l2_sorted <- sort ep w2_index (cast (by sorry) l2) i (indents+1)

--       let l1_sorted: (List Nat) @ m # ep <- cast (by sorry) l1_sorted ~> m
--       let l2_sorted: (List Nat) @ m # ep <- cast (by sorry) l2_sorted ~> m


--       let temp <- locally m (Sleep.sleep 5000)


--       let res <- locally m do return  merge (⤉l1_sorted) (⤉l2_sorted)

--       -- let _ <- locally m do return  do
--       --     IO.println s!"{repeat_string "  " indents}merged {⤉res}"
--       return res

--   | 0 => sorry




def sort (n:Nat) (ep: Location n) (nodes : List (Location n)) (notEmpty: 0 < nodes.length)
  (l: GVal (nodes[0]'(by simp [notEmpty])) ep (List Nat) ) (iter: Nat := 100) (indents: Nat:= 0):

  Choreo ep (GVal (nodes[0]'(by simp [notEmpty])) ep (List Nat)) := do

  match iter with
  | i + 1 =>
    let m := nodes[0]'(by done)
    let w1 := nodes[1 % nodes.length]'(by exact Nat.mod_lt 1 notEmpty)
    let w2 := nodes[2 % nodes.length]'(by exact Nat.mod_lt 2 notEmpty)

    let size <- locally m do return (⤉l).length
    branch l fun
    | [] | _::[] =>
      return l
    | a::as2 => do
      --let sizef: Float @ "M" <- locally "M" f⤉⤉=> (⤉size).toFloat
      let pivot <- locally m do return (Float.floor ((⤉size).toFloat / 2)).toUInt16.toNat
      let ls <- locally m do return  (⤉l).seperate (⤉pivot)
      let l1 <- locally m do return (⤉ls).fst
      let l2 <- locally m do return (⤉ls).snd


      --let _ <- locally m do
        --LogEff.info s!"{repeat_string "  " indents}splitting {⤉l1}{⤉l2}"

      --have h: l1 < l.length := by sorry

      --let temp <- locally m (Sleep.sleep 5000)

      let l1 <- l1 ~> w1
      let l2 <- l2 ~> w2

      let l1_workers := nodes.shuffle 1
      let l2_workers := nodes.shuffle 2

      let l1_sorted <- sort n ep l1_workers (by sorry) (cast (by sorry) l1) i (indents+1)

      let l2_sorted <- sort n ep l2_workers (by simp [List.shuffle, notEmpty]) (cast (by sorry) l2) i (indents+1)

      let l1_sorted <- l1_sorted ~> m
      let l2_sorted <- l2_sorted ~> m

      let res <- locally m do return  merge (⤉l1_sorted) (⤉l2_sorted)

      let _ <- locally m do return  do
          IO.println s!"{repeat_string "  " indents}merged {⤉res}"
      return res

  | 0 => sorry




-- def sort (n:Nat) (ep: Location n) (nodes : List (Location n)) (notEmpty: 0 < nodes.length)
--   (l: GVal (nodes[0]'(by simp [notEmpty])) ep (List Nat) ) (iter: Nat := 100) (indents: Nat:= 0):

--   Choreo ep (GVal (nodes[0]'(by simp [notEmpty])) ep (List Nat)) := do

--   match iter with
--   | i + 1 =>
--     let m := nodes[0]'(by done)
--     let w1 := nodes[1 % nodes.length]'(by exact Nat.mod_lt 1 notEmpty)
--     let w2 := nodes[2 % nodes.length]'(by exact Nat.mod_lt 2 notEmpty)

--     let size <- locally m do return (⤉l).length
--     branch l fun
--     | [] | _::[] =>
--       return l
--     | a::as2 => do
--       --let sizef: Float @ "M" <- locally "M" f⤉⤉=> (⤉size).toFloat
--       let pivot <- locally m do return (Float.floor ((⤉size).toFloat / 2)).toUInt16.toNat
--       let ls <- locally m do return  (⤉l).seperate (⤉pivot)
--       let l1 <- locally m do return (⤉ls).fst
--       let l2 <- locally m do return (⤉ls).snd


--       --let _ <- locally m do
--         --LogEff.info s!"{repeat_string "  " indents}splitting {⤉l1}{⤉l2}"

--       --have h: l1 < l.length := by sorry

--       let temp <- locally m (Sleep.sleep 5000)

--       let l1 <- l1 ~> w1
--       let l2 <- l2 ~> w2

--       let l1_workers := nodes.shuffle 1
--       let l2_workers := nodes.shuffle 2

--       let l1_sorted <- sort n ep l1_workers (by sorry) (cast (by sorry) l1) i (indents+1)

--       let l2_sorted <- sort n ep l2_workers (by simp [List.shuffle, notEmpty]) (cast (by sorry) l2) i (indents+1)

--       let l1_sorted <- l1_sorted ~> m
--       let l2_sorted <- l2_sorted ~> m

--       let res <- locally m do return  merge (⤉l1_sorted) (⤉l2_sorted)

--       let _ <- locally m do return  do
--           IO.println s!"{repeat_string "  " indents}merged {⤉res}"
--       return res

--   | 0 => sorry



def testing_ (n:Nat): IO Unit := do
  let data  <- generate_random_list n
  let start <- Timer.getTime
  let _serial <- ComputeEff.compute (sort_serial (data))
  Sleep.sleep 2331
  let delta <- Timer.getTime

  let delta := delta - start
  Log.info (s!"serial duration: {Timer.NanosToSec (delta)} sec.")

#eval testing_ 2000

def test: IO Unit:= do


  return ()

def main (args : List String): IO Unit := do

  let mode := args.get! 0

  let ep_opt: Option (Location 1) := FinEnum.ofString? mode
  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h
    let net <-  init_network ep
    let epp := EPP ep net
    have: MonadLiftT MasterEff (MasterEff ⨳ Timer ⨳ Sleep ⨳ Log) := inferInstance
    have: MonadLiftT Timer (MasterEff ⨳ Timer ⨳ Sleep ⨳ Log) := inferInstance
    have: MonadLiftT Log (MasterEff ⨳ Timer ⨳ Sleep ⨳ Log) := inferInstance
    let data <- epp.monadLift (locally Master do
      let res <- MasterEff.gen
      let start <- Timer.getTime
      --let serial <- ComputeEff.compute (sort_serial (res))
      let delta <- Timer.getTime
      let delta := delta - start
      Log.info (s!"serial duration: {Timer.NanosToSec (delta)} sec.")
      return res
      )
    --let temp := (sort n ep (FinEnum.toList (Location n)) (by sorry) data)

    let start <- epp.monadLift (locally Master do Timer.getTime)
    let res <- (sort 1 ep (FinEnum.toList (Location 1)) (by sorry) data)
    let delta <- epp.monadLift (locally Master do
      let now <-Timer.getTime
      return now  - (⤉start))
    --IO.println (s!"res: {res}")
    let _ <- epp.monadLift (locally Master do Log.info (s!"duration: {Timer.NanosToSec (⤉delta)} sec."))
    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()
