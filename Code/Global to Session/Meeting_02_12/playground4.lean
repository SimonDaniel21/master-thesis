import Test.my_utils
import chorlean.Network
--import Mathlib



inductive M: Type -> Type 1  where
| Do_A :  M Unit -> (Unit -> M a) -> M a
| Do_B :  M Nat -> (Nat -> M a) -> M a
-- possibly many effects
| Return: a -> M a

@[reducible] def Store := List ((a:Type) × a)

@[reducible] def GVal (a:Type) (loc: String) := Nat


structure Valid (a:Type) (loc:String) (s:Store) where
  gv: GVal a loc
  p1: gv < s.length := by decide
  p2: (s[gv]' p1).fst  = a := by simp

def valid2 (a:Type) (loc:String) (s:Store) := {gv: {gv2: GVal a loc // gv2 < s.length} // (s[gv.val]'(gv.property)).fst  = a}


def Store.unwrap {a:Type} {loc:String}  (s: Store) (v: Valid a loc s): a :=
  cast v.p2 (s[v.gv]'(v.p1)).snd

#check Subtype

infixl:55 "@" => GVal

-- instance [Serialize a]: ToString (a @ l) where
--   toString := fun x => match x with
--     | .Wrap v => toString v ++ "@" ++ toString l
--     | .Empty => "Empty"

def wrap {a} (v:a) (l: String) (s:Store): Valid a l (s.concat ⟨a, v⟩) :=
  let i := s.length
  let ns := s.concat ⟨a, v⟩
  Valid.mk i (by sorry) (by sorry) -- first sorry solved by mathlib

def notEmpty {a:Type} {l:String}: GVal a l -> (s:Store) -> Prop := fun _ _ =>false


def Unwrap (l:String)  :=   {a:Type} -> a @ l -> a


def local_func (a:Type) (l:String):= (Unwrap l -> a)
def local_prog (a:Type) (l:String):= (Unwrap l -> IO a)


inductive Choreo': Type -> Type 1 where
| Send_recv [Serialize a]: {sender:String} -> a @ sender -> (receiver:String) -> (a @ receiver -> Choreo' n) -> Choreo' n
| Local : (loc:String) -> (Unwrap loc -> IO a)  -> (a @ loc -> Choreo' n) -> Choreo' n
--| Calc : (loc:String) -> (Unwrap loc -> a)  -> (a @ loc -> Choreo' n) -> Choreo' n
--| Cond [Serialize a] {decider:String} : a @ decider -> (a -> Choreo' b) -> (b -> Choreo' n) -> Choreo' n
| Return: a -> Choreo' a



def Choreo'.bind: Choreo' α → (α → Choreo' β) → Choreo' β
| Choreo'.Send_recv v receiver next, next' => Choreo'.Send_recv v receiver (fun x => bind (next x) next')
| Choreo'.Local loc comp next, next' => Choreo'.Local loc comp (fun x => bind (next x) next')
--| Choreo'.Calc loc comp next, next' => Choreo'.Calc loc comp (fun x => bind (next x) next')
--| Choreo'.Cond lv d next, next' => Choreo'.Cond lv d (fun x => bind (next x) next')
| Choreo'.Return v, next' => next' v

instance: Monad Choreo' where
  pure x := Choreo'.Return x
  bind  := Choreo'.bind

--def send_recv {a:Type} [Serialize a] (vl: a @ sender) (receiver:String) (_dont_send_to_yourself: sender != receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def send_recv {a:Type} {sender:String} [Serialize a] (vl: a @ sender) (receiver:String) := Choreo'.Send_recv vl receiver (fun x => Choreo'.Return x)
def locally (loc: String) (comp: (Unwrap loc) -> IO b) := Choreo'.Local loc comp (fun x => Choreo'.Return x)
--def compute (loc: String) (comp: (Unwrap loc) -> b) := Choreo'.Calc loc comp (fun x => Choreo'.Return x)
-- def branch {a:Type} {decider:String} [Serialize a] (lv: a @ decider) (cont: a -> Choreo' b) :=
--   let temp:= (fun x => Choreo'.Return x (a:=b))
--   Choreo'.Cond (a:=a) (b:=b) lv cont temp


def Choreo'.epp: Choreo' a -> (l:String) -> (s:Store) ->
  (pr: (lv: x @ l) -> (lv < s.length) -> Valid x l s)
   -> Network a
| Choreo'.Send_recv lv receiver (sender:=sender) next, l, s, pr => do
  if (sender == receiver) then
    let temp := pr lv
    let temp := wrap (unwrap lv (by sorry)) receiver
    (next temp).epp l

  else if (sender == l) then
    send receiver (unwrap lv)
    (next .Empty).epp l
  else if (receiver == l) then
    let response <- (recv sender)
    let temp := wrap response receiver
    (next temp).epp l
  else
    (next .Empty).epp l
| Choreo'.Local l1 comp next, l2, s, pr => do
  if j:( l1 == l2) then
    let t := pr
    let un := s.unwrap
    let res <- run (comp (un))
    let temp := wrap res l1
    (next temp).epp l2
  else
    (next .Empty).epp l2



-- | Choreo'.Calc l1 comp next, l2 => do
--   if j:( l1 == l2) then
--     let temp :=  wrap (comp (unwrap)) l1
--     (next temp).epp l2
--   else
--     (next .Empty).epp l2
-- | Choreo'.Cond lv fn next (decider:=decider), loc => do
--   if (loc == decider) then
--     let choice := (unwrap lv)
--     broadcast choice
--     let temp <- (fn choice).epp loc
--     (next temp).epp loc
--   else
--     let choice <- (recv decider)
--     --(fn choice).epp loc
--     let temp <- (fn choice).epp loc
--     (next temp).epp loc
| Choreo'.Return v, _, _ => Network.Return v


def test_store: Store := []

def wrapped := wrap "jello" "bob" test_store

def unwrapped := (wrapped.snd).unwrap



#eval unwrapped



notation:55 lv "~>" receiver => send_recv lv receiver

-- notation:55 sender "~>" receiver "##" comp => send_recv_locally sender receiver comp
-- notation:55 sender "~>" receiver "pure" comp => send_recv_pure sender receiver comp
