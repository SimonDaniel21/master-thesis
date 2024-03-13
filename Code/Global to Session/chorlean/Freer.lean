
#check ReaderT

-- class EffectHandler (eff: Type u → Type v) (m: Type u → Type v) [Monad m] where
--   run: eff α → m α

inductive Freer (Eff:Type u → Type v) (α:Type w) where
| Do: Eff β → (β → Freer Eff α) → Freer Eff α
| Return: α → Freer Eff α



def Freer.lift  {m: Type → Type} [Monad m] [MonadLift eff m]: Freer eff α → m α
| .Return v => return v
| .Do e cont => do
  let res <- MonadLift.monadLift e
  Freer.lift (cont res)


@[reducible] def Freer.toFreer {α: Type u} {Eff: Type u → Type v} (e: Eff α): Freer Eff α :=
  .Do e (fun x =>  .Return x)

-- Lift instance that lifts an Effect into Freer tha only does this single effect
instance: MonadLift (Eff) (Freer Eff) where
  monadLift e := Freer.Do e (fun x =>  .Return x)


def Freer.bind {α β : Type} : Freer Eff α → (α → Freer Eff β) → Freer Eff β
| Return v, next => next v
| Do eff cont, next =>
  Freer.Do eff (fun  x => bind (cont x) next)

instance: Monad (Freer Eff) where
  pure x := .Return x
  bind := Freer.bind

def Freer.monadLift {α : Type}  [Monad m] [MonadLiftT eff m]:  Freer eff α → m α
| .Do e cont => do
  let res <- MonadLiftT.monadLift e
  Freer.monadLift (cont res)
| .Return v => do return v


-- the Freer eff Lift instance for a Effect eff with existing Lifting instance (transitive)
instance [MonadLiftT eff m] [Monad m]: MonadLiftT (Freer eff) m where
  monadLift := Freer.monadLift

-- product freer
--def Freer.product (eff1)

inductive SumEff (eff1: Type u → Type v1) (eff2: Type u → Type v2) (α:Type u) where
| eff1: eff1 α → SumEff eff1 eff2 α
| eff2: eff2 α → SumEff eff1 eff2 α

-- Lifts the first Effect alternative into an SumEff
instance: MonadLift eff1 (SumEff eff1 eff2) where
  monadLift x := SumEff.eff1 x

-- Lifts the sedcond Effect alternative into an SumEff
instance: MonadLift eff2 (SumEff eff1 eff2) where
  monadLift x := SumEff.eff2 x

-- transitively lifts an sum Effect into a Monad (or Effect) m if both Effect Signatures can be lifted into m
instance [MonadLiftT eff1 m] [MonadLiftT eff2 m]: MonadLiftT (SumEff eff1 eff2) m where
  monadLift x := match x with
    | .eff1 e1 => MonadLiftT.monadLift e1
    | .eff2 e2 => MonadLiftT.monadLift e2

-- short notation for SumEffs
infixl:65 "⨳" => SumEff


inductive EmptyEff: Type → Type 1

inductive ComputeEff: Type → Type 1
| compute: α -> ComputeEff α

instance: MonadLift ComputeEff IO where
  monadLift x := match x with
  | .compute v => return v

abbrev FIO := Freer IO

--- Examples

inductive PrintEff: Type → Type
| Print1: String → PrintEff Unit



inductive LogEff1: Type → Type 1
| Print2: Nat → LogEff1 Unit

inductive LogEff2: Type → Type 1
| Print3: Nat → LogEff2 Unit

@[reducible] def LogPrintEff := Freer (SumEff PrintEff LogEff1)
@[reducible] def LogPrintEff2 := Freer (SumEff LogPrintEff LogEff2)

open PrintEff
open LogEff1

instance: MonadLift PrintEff IO where
  monadLift x := match x with
    | .Print1 s => IO.println s

instance: MonadLift LogEff1 IO where
  monadLift x := match x with
    | .Print2 s => IO.println ("n: " ++ toString s)

instance: MonadLift LogEff2 IO where
  monadLift x := match x with
    | .Print3 s => IO.println ("n: " ++ toString s)

def prog: Freer PrintEff Unit :=do
  Print1 "Hello"
  Print1 "a"
  return ()

def prog1: Freer LogPrintEff Unit :=do
  Print1 "Hello"
  Print2 23
  return ()

def prog2: Freer LogPrintEff2 Unit :=do
  Print1 "Hello"
  (LogEff1.Print2 23)
  LogEff2.Print3 23
  return ()

def Main: IO Unit := do
  MonadLiftT.monadLift prog1
  prog1
  prog2
  let temp <- (Print1 "e e e e")
  return ()

#eval Main
