structure with_logs (l: Type) (t: Type) where
  value: t
  logs: List l

instance: ToString (with_logs String Nat) where
  toString := fun v_with_logs => "value => " ++ toString v_with_logs.value ++ "\nLogs =>" ++ toString v_with_logs.logs

def append (s: List String): with_logs String PUnit :=
  {value:= (), logs:= s}


def my_add2(v: Nat) : with_logs String Nat :=
  {value := v+2, logs := ["+2 (" ++ toString v ++ ") "]}

def my_mult3(v: Nat) : with_logs String Nat :=
  {value := v*3, logs := ["*3 (" ++ toString v ++ ") "]}

def bind_with_logs:  with_logs String α → (α → with_logs String β) → with_logs String β :=
  fun x f =>
    let result := f x.value
    {value := result.value, logs := x.logs.append result.logs}

instance: Monad (with_logs String) where
  bind := bind_with_logs
  pure := fun x => {value := x, logs := []}


#check (with_logs Nat)


def test: with_logs String Nat := (do
  let x <- my_add2 2
  let y <- my_mult3 x
  return y)

#eval test
def faraway := 2
