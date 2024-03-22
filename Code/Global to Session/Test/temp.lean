
def expensive (x: Nat) := x

def test (n:Nat): IO Unit := do
  let start <- IO.monoNanosNow
  let _ := expensive n
  let delta := (<-IO.monoNanosNow) - start

  IO.println (s!"duration: {delta} ns.")
