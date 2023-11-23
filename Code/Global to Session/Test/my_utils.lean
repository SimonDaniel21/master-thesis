def list_to_string_seperated_by (l: List String) (s: String): String :=
  match l with
  | List.cons a as => a ++ s ++ (list_to_string_seperated_by as s)
  | _ => ""

def list_to_continuos_string (l: List String): String :=
  list_to_string_seperated_by l ""

def repeat_string (s: String) (n: Nat): String :=
  if n > 0 then
    repeat_string s (n -1) ++ s
  else
    ""
