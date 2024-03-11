import chorlean.Choreo2
import chorlean.Effects

inductive Location
| N1 | N2 | N3 | N4
deriving Repr, Fintype

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location

instance sig: LocSig Location IO where
  sig x := match x with
    | N1 =>  EmptyEff
    | N2 =>  EmptyEff
    | N3 =>  EmptyEff
    | N4 =>  EmptyEff
  liftable x := match x with
    | N1 => inferInstance
    | N2 => inferInstance
    | N3 => inferInstance
    | N4 => inferInstance
  liftable2 x := match x with
    | _ => inferInstance



def generate_random_list_rec: (l: List Nat) -> Nat -> IO (List Nat)
| _, 0 =>  return []
| remaining, len+1 =>  do
  let index <- IO.rand 0 (remaining.length-1)
  let rest_list <- generate_random_list_rec (remaining.eraseIdx index) len
  return rest_list.concat remaining[index]!

def descending_list: Nat -> List Nat
| 0 => []
| x+1 => [x+1] ++ descending_list (x)


def generate_random_list (n:Nat): IO (List Nat) := do
  let sorted := descending_list n
  generate_random_list_rec sorted n


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

partial def sort2 (m w1 w2: String) (others : List String) (l: (List Nat) @ m) (indents: Nat:= 0): Choreo ((List Nat) @ m) := do
  let size <- compute m fun un => (un l).length
  branch l fun
  | [] | _::[] =>
    return l
  | a::as2 => do
    --let sizef: Float @ "M" <- compute "M" fun un => (un size).toFloat
    let pivot <- compute m fun un => (Float.floor ((un size).toFloat / 2)).toUInt16.toNat
    let ls <- compute m fun un => (un l).seperate (un pivot)
    let l1 <- compute m fun un => (un ls).fst
    let l2 <- compute m fun un => (un ls).snd

    let node_list_w1 := others ++ [m, w2]
    let node_list_w2 := others ++ [m, w1]
    let (w1_workers, w1_others) := node_list_w1.seperate 2
    let (w2_workers, w2_others) := node_list_w2.seperate 2

    let _ <- locally m fun un => do
      IO.println s!"{repeat_string "  " indents}splitting {un l1}{un l2}"

    --have h: l1 < l.length := by sorry
    let l1_sorted <- sort2 w1 w1_workers[0]! w1_workers[1]! w1_others l1 (indents+1)

    let l2 <- l2 ~> w2
    let l2_sorted <- sort2 w2 w2_workers[0]! w2_workers[1]! w2_others l2 (indents+1)

    let l1_sorted <- l1_sorted ~> m
    let l2_sorted <- l2_sorted ~> m

    let res <- compute m fun un => merge (un l1_sorted) (un l2_sorted)

    let _ <- locally m fun un => do
        IO.println s!"{repeat_string "  " indents}merged {un res}"
    return res

def sort (m w1 w2: Location) (others : List Location) (l: GVal m ep (List Nat)) (indents: Nat:= 0): Choreo ep (GVal m ep (List Nat)) := do
  let size <- compute m ((⤉l).length)
  branch size fun
  | 0 | 1 =>
    return l
  | _ => do
    --let sizef: Float @ "M" <- compute "M" fun un => (un size).toFloat
    let pivot <- compute m (Float.floor ((⤉ size).toFloat / 2)).toUInt16.toNat
    let ls <- compute m ((⤉ l).seperate (⤉ pivot))
    let l1 <- compute m (⤉ ls).fst
    let l2 <- compute m (⤉ ls).snd

    let node_list_w1 := others ++ [m, w2]
    let node_list_w2 := others ++ [m, w1]
    let (w1_workers, w1_others) := node_list_w1.seperate 2
    let (w2_workers, w2_others) := node_list_w2.seperate 2

    let _ <- locally m do
      IO.println s!"{repeat_string "  " indents}splitting {⤉l1}{⤉l2}"

    let l1 <- l1 ~> w1
    let l1_sorted <- sort w1 w1_workers[0]! w1_workers[1]! w1_others l1 (indents+1)


    let l2 <- l2 ~> w2
    let l2_sorted <- sort w2 w2_workers[0]! w2_workers[1]! w2_others l2 (indents+1)

    let l1_sorted <- l1_sorted ~> m
    let l2_sorted <- l2_sorted ~> m

    let res <- compute m fun un => merge (un l1_sorted) (un l2_sorted)

    let _ <- locally m fun un => do
        IO.println s!"{repeat_string "  " indents}merged {un res}"
    return res
decreasing_by simp

def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network merge_cfg mode
  IO.println (s!"mergesort")

  let main_node := Workers[0]

  let input_size_chor: Choreo ((List Nat) @ main_node) := do
    return <- locally main_node fun un => do
      IO.println "enter the size of the List to sort:"
      let len := (<-IO.getLine).toNat!
      let lst <- generate_random_list len
      return lst

  let input <- ((input_size_chor).epp mode ( by sorry)).run mode net

  let res <- ((sort main_node Workers[1] Workers[2] (Workers.seperate 3).snd input).epp mode ( by sorry)).run mode net
  IO.println (s!"res: {unwrap res}")
  return ()
