def list_to_string_seperated_by (l: List String) (s: String): String :=
  match l with
  |   a::_::as => a ++ s ++ (list_to_string_seperated_by as s)
  |   a::_ => a
  | _ => ""

def list_to_continuos_string (l: List String): String :=
  list_to_string_seperated_by l ""

def repeat_string (s: String) (n: Nat): String :=
  if n > 0 then
    repeat_string s (n -1) ++ s
  else
    ""

def newLine (i: Nat): String :=
  "\n" ++ repeat_string "  " i

def pad_until (s: String) (i: Nat): String :=
  s ++ repeat_string " " (i - s.length)

/-

def combine {α: Type} (lst: List (List α)): List α :=
  let combine_two: List α -> List α -> List α := fun x y =>
    (x.append y).eraseDups
  match lst with
  | [] => []
  | x::xs => combine_two x (combine xs)
-/
