import chorlean.Choreo

def bookseller_cfg := gen_fullmesh_cfg ["N1", "N2", "N3"]


-- budget -> price -> decision


def sort (M S1 S2: String) (l: (List Nat) @ M): Choreo ((List Nat) @ M) := do
  let size <- compute M fun un => (un l).length
  branch size fun
  | 0 | 1 =>
    return l
  | _ => do
    --let sizef: Float @ "M" <- compute "M" fun un => (un size).toFloat
    let pivot <- compute M fun un => (Float.floor ((un size).toFloat / 2)).toUInt16.toNat
    let ls <- compute M fun un => (un l).split (un pivot)
    let l1 <- compute M fun un => (un ls).fst
    let l2 <- compute M fun un => (un ls).snd

    let l1 <- l1 ~> S1
    let l1_sorted <- sort S1 M S2 l1
    let _ <- locally M fun un => do
      IO.println s!"splitting list of size {un size} at pivot {un pivot} to \n{un l1}{un l2}"
    return l

def sort2 (M S1 S2: String) (l: (List Nat) @ M): Choreo ((List Nat) @ M) := do
  let size <- compute M fun un => (un l).length
  branch size fun
  | 0 | 1 =>
    return l
  | _ => do
    --let sizef: Float @ "M" <- compute "M" fun un => (un size).toFloat
    let pivot <- compute M fun un => (Float.floor ((un size).toFloat / 2)).toUInt16.toNat
    let ls <- compute M fun un => (un l).split (un pivot)
    let l1 <- compute M fun un => (un ls).fst
    let l2 <- compute M fun un => (un ls).snd

    let l1 <- l1 ~> S1
    let l1_sorted <- sort S1 M S2 l1
    let _ <- locally M fun un => do
      IO.println s!"splitting list of size {un size} at pivot {un pivot} to \n{un l1}{un l2}"
    return l


def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network bookseller_cfg mode
  IO.println (s!"mergesort")

  let input := wrap [1,2,3,4,56,26,236,123,4,3,523,56,21,2,53,5235,23] "M"

  let res <- ((sort input).epp mode).run mode net
  IO.println (s!"res: {unwrap res}")
  return ()
