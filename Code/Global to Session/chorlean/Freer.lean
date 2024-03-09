
#check ReaderT

-- class EffectHandler (eff: Type u -> Type v) (m: Type u -> Type v) [Monad m] where
--   run: eff α -> m α

inductive Freer (Eff:Type u -> Type v) (α:Type) where
| Do: Eff β -> (β -> Freer Eff α) -> Freer Eff α
| Return: α -> Freer Eff α

def Freer.lift  {m: Type -> Type} [Monad m] [MonadLift eff m]: Freer eff α -> m α
| .Return v => return v
| .Do e cont => do
  let res <- MonadLift.monadLift e
  Freer.lift (cont res)

def Effect.ToFreer {Eff: Type -> Type} (e: Eff α): Freer Eff α :=
  .Do e (fun x =>  .Return x)


def Freer.bind {α β : Type} : Freer Eff α → (α → Freer Eff β) → Freer Eff β
| Return v, next => next v
| Do eff cont, next =>
  Freer.Do eff (fun  x => bind (cont x) next)

instance: Monad (Freer Eff) where
  pure x := .Return x
  bind := Freer.bind

def Freer.monadLift {α : Type}  [Monad m] [MonadLift eff m]:  Freer eff α → m α
| .Do e cont => do
  let res <- MonadLift.monadLift e
  Freer.monadLift (cont res)
| .Return v => do return v

instance [Monad m] [MonadLift eff m]: MonadLift (Freer eff) m where
  monadLift := Freer.monadLift

--- Examples

inductive PrintEff: Type -> Type
| Print: String -> PrintEff Unit

instance: MonadLift PrintEff IO where
  monadLift x := match x with
    | .Print s => IO.println s

abbrev PrintIO := Freer PrintEff

def print (s: String): PrintIO Unit := Effect.ToFreer (PrintEff.Print s)

def prog: PrintIO Unit :=do
  print "Hello"

def Main: IO Unit := do
  prog
  return ()

#eval Main
