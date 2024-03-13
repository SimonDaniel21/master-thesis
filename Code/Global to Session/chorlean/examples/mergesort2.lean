import chorlean.Choreo2
import chorlean.Effects

inductive Location (n:Nat)
| Master | Worker: Fin n -> Location n
deriving Repr, Fintype

instance (n:Nat) : FinEnum (Location n) :=
  FinEnum.ofEquiv _ (proxy_equiv% (Location n)).symm

open Location

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

inductive MasterEff: Type -> Type 1 where
| gen:  MasterEff (List Nat)


instance: MonadLift MasterEff IO where
  monadLift m := match m with
    | .gen => do
      let n <- CmdInputEff.readNat (.some "enter the random List length")
      return (<-generate_random_list n)

instance sig: LocSig (Location n) where
  sig x := match x with
    | Master =>  MasterEff
    | Worker _ =>  LogEff
  executable x := match x with
    | Master => inferInstance
    | Worker _ => inferInstance



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



def main (args : List String): IO Unit := do
  let n := (args.get! 0).toNat!
  let mode := args.get! 1
  let ep_opt := FinEnum.ofString? mode

  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h

    --let net <-  init_network ep

    have:= NetEPP ep
    have := (sig.executable ep)
    let e := EPP ep

    IO.println (s!"starting bookseller 50 50")
    IO.println (s!"\n\nstarting bookseller pay rest")


    --let data <- e.monadLift (locally Master do MasterEff.gen)
    let data := GVal.wrap Master ep [1]
    let temp := (sort n ep (FinEnum.toList (Location n)) (by sorry) data)

    let res := e.monadLift (sort n ep (FinEnum.toList (Location n)) (by sorry) sorry)
    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()
