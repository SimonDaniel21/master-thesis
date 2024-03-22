import chorlean.Choreo
import chorlean.Effects

open Effect

abbrev Loc (n:Nat) := {f: Fin n // n >= 1 }

open Effect

inductive Location
| Master | W1 | W2
deriving Repr, Fintype

instance : FinEnum (Location) :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location

open Effect.Log


instance sig: LocSig (Location ) where
  sig x := match x with
    | Master =>  CmdInput ⨳ Rand ⨳ Timer ⨳ Sleep ⨳ Log
    | W1 =>  Log ⨳ Sleep
    | W2 =>  Log ⨳ Sleep
  executable x := match x with
    | Master => inferInstance
    | W1 => inferInstance
    | W2 => inferInstance

--instance [sig: LocSig Location]: MonadLiftT (sig.sig l) IO := sig.executable l

def dot_product: List UInt64 -> List UInt64 -> UInt64
| [], [] => 0
| _::_, [] => 0
| [], _::_ => 0
| a::as, b::bs => a*b + dot_product as bs

#eval dot_product [1,2,3] [2,3,4]

def vec_op (ep: Location) (A:(List (List UInt64)) @ Master#ep) (b:(List UInt64) @ Master#ep): Choreo ep ((List UInt64) @ Master#ep):= do

  have: MonadLiftT CmdInput  (CmdInput ⨳ Rand ⨳ Timer ⨳ Sleep ⨳ Log) := inferInstance
  have: MonadLiftT Rand  (CmdInput ⨳ Rand ⨳ Timer ⨳ Sleep ⨳ Log) := inferInstance
  have: MonadLiftT Log  (CmdInput ⨳ Rand ⨳ Timer ⨳ Sleep ⨳ Log) := inferInstance
  have: MonadLiftT Log  ( Log ⨳ Sleep) := inferInstance
   --have: MonadLiftT CmdInput  (Freer (CmdInput ⨳ 2)) := inferInstance

  let b <- broadcast b
  let chunk <- scatter A
  let chunk := chunk.map (fun x => dot_product x b)


  --let other :=GVal.wrap W1 ep chunk

  --let other <- other  ~> Master

  let all <- gather chunk Master
  -- locally Master do
  --   info s!"transformed: {⤉all}"


  --let all: List (Location n) := (FinEnum.toList (Location n))
  return all

  -- for i in all do

  --   locally i do
  --     info s!"my chunk: {chunk}"


def experiment (ep: Location): Choreo ep ((List UInt64) @ Master#ep):= do

  have: MonadLiftT CmdInput  (CmdInput ⨳ Rand ⨳ Timer ⨳ Sleep ⨳ Log) := inferInstance
  have: MonadLiftT Rand  (CmdInput ⨳ Rand ⨳ Timer ⨳ Sleep ⨳ Log) := inferInstance
  have: MonadLiftT Log  (CmdInput ⨳ Rand ⨳ Timer ⨳ Sleep ⨳ Log) := inferInstance
  have: MonadLiftT Timer  (CmdInput ⨳ Rand ⨳ Timer ⨳ Sleep ⨳ Log) := inferInstance
  have: MonadLiftT Log  ( Log ⨳ Sleep) := inferInstance

  while (true = true) do
    let _ <- locally Master do info "hello"

  let size <- locally Master do CmdInput.readNat ("enter vector size")

  let A <- locally Master do
    let mut A: List (List UInt64) := []
    for _ in [:⤉size] do
      let data <- generate_random_list ⤉size
      let data := data.map (fun x => x.toUInt64)
      A := A.concat data
    --info s!"global data: {A}"
    return A
  let b <- locally Master do return (<-generate_random_list ⤉size).map (fun x => x.toUInt64)

  let start <- locally Master Timer.getTime
  let res <- vec_op ep A b
  let duration <- locally Master do
    let t <-Timer.getTime
    info s!"duration {Timer.NanosToSec (t-⤉start)}"
    return t - (⤉start)

  return res


def main (args : List String): IO Unit := do
  let mode := args.get! 0

  let ep_opt: Option (Location) := FinEnum.ofString? mode

  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h
    let net <- init_network ep
    let epp := EPP ep net

    let r <- (experiment ep )
    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()
