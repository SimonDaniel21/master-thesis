import Test.my_utils
import Std.Data.Option.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.FinEnum
import Mathlib.Data.Finmap
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib
--import Mathlib.Combinatorics.SimpleGraph.Basic

inductive GVal (α: Type) (owner endpoint: δ)   where
| Wrap:  (owner = endpoint) -> α -> GVal α owner endpoint
| Empty: (owner ≠ endpoint) -> GVal α owner endpoint

def GVal.wrap (owner endpoint: δ) (v:α) : GVal α owner endpoint :=
  if h:(owner = endpoint) then
    GVal.Wrap h v
  else
    GVal.Empty h

def GVal.unwrap {owner endpoint: δ}: GVal α owner endpoint -> (owner = endpoint) -> α
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction

instance {loc ep: δ} [DecidableEq δ]  [Fintype δ] [ToString t]: ToString (GVal t loc ep) where
  toString x :=
    if h:(loc = ep) then
      let val := x.unwrap h
      toString val
    else
      "Empty"

infixl:55 "@" => fun {endpoint:String} (a:Type) (loc:String) => GVal a loc endpoint

class Network {δ:Type} (ep: δ) where
  com {t:Type} [Serialize t]: (s: δ) -> GVal t s ep -> (r: δ) -> IO (GVal t r ep)


def Network.broadcast {δ:Type} [FinEnum δ] {ep: δ} (net: Network ep) {t:Type} [Serialize t] (s: δ) (gv:GVal t s ep): IO t := do
  let gv <- com s gv ep
  let v := gv.unwrap (by simp)
  return v


structure SockChannel {δ:Type} [DecidableEq δ] (sender receiver ep: δ ) where
  recv_sock: GVal Socket receiver ep
  send_sock: GVal Socket sender ep

def init_sending_channel {δ:Type} [DecidableEq δ] (sender ep:δ) (addr: Address):  IO (GVal Socket sender ep) := do
  if h:(sender = ep) then
    IO.println s!"waiting for"-- {sender} -> {receiver}"
    let sock <- addr.connect_to
    return GVal.Wrap h sock
  else
    return GVal.Empty h

def init_receiving_channel {δ:Type} [DecidableEq δ] (receiver ep: δ) (addr: Address):  IO (GVal Socket receiver ep) := do
  if h:(receiver = ep) then
    IO.println s!"waiting for"-- {sender} -> {receiver}"
    let sock <- addr.listen_on
    return GVal.Wrap h sock
  else
    return GVal.Empty h

-- epp for initializing one network socket
def init_channel {δ:Type} [DecidableEq δ] (sender receiver ep: δ) (addr: Address):  IO (SockChannel sender receiver ep) := do
  let recv_sock <- init_receiving_channel receiver ep addr
  let send_sock <- init_sending_channel sender ep addr
  return ⟨recv_sock, send_sock⟩

structure SockNet {δ:Type} [DecidableEq δ] (ep: δ) [DecidableEq δ] where
  channels: List (Σ (id: δ×δ), SockChannel id.1 id.2 ep)
  complete: ∀ (k : δ×δ), (k.1 ≠ k.2) -> (channels.dlookup k).isSome

def SockNet.getChannel {δ:Type} [DecidableEq δ]  {ep: δ} (net:SockNet ep) (k:δ×δ) (not_self: k.1 ≠ k.2) : SockChannel k.1 k.2 ep :=
  (net.channels.dlookup k).get (by simp [net.complete, not_self])

def SockNet.toNet {δ:Type} [DecidableEq δ] {ep:δ} (snet: SockNet ep): Network ep :=
  ⟨fun s gv r => do

    if h:( s = ep) then
      let v := gv.unwrap h
      if h2:(r = ep) then
        return GVal.Wrap h2 v
      else
        let h3: r != s := sorry
        let sock := (snet.getChannel (s, r) (by sorry)).send_sock.unwrap h
        let v := gv.unwrap h
        sock.send_val2 v
        return GVal.Empty h2
    else
      if h2:(r = ep) then
        let sock := (snet.getChannel (s, r) (by simp [h, h2])).recv_sock.unwrap h2
        let v <- sock.recv_val2
        return GVal.Wrap h2 v
      else
        return GVal.Empty h2⟩
instance  {δ:Type} [DecidableEq δ] {ep:δ} (snet: SockNet ep): Network ep where
  com s gv r := do

    if h:( s = ep) then
      let v := gv.unwrap h
      if h2:(r = ep) then
        return GVal.Wrap h2 v
      else
        let h3: r != s := sorry
        let sock := (snet.getChannel (s, r) (by sorry)).send_sock.unwrap h
        let v := gv.unwrap h
        sock.send_val2 v
        return GVal.Empty h2
    else
      if h2:(r = ep) then
        let sock := (snet.getChannel (s, r) (by simp [h, h2])).recv_sock.unwrap h2
        let v <- sock.recv_val2
        return GVal.Wrap h2 v
      else
        return GVal.Empty h2

def init_network [DecidableEq δ] [FinEnum δ] (ep: δ) (as:  (k:δ×δ) -> (k.1 ≠ k.2) -> Address) : IO (SockNet ep) := do

  let filtered := (FinEnum.toList (δ×δ)).filter (fun k => k.1 ≠ k.2)
  let progs: List (Σ (k: (δ×δ)), Address)  := filtered.map (fun k => ⟨k, as k (by sorry)⟩ )
  let channels_prog: IO (List (Σ (k: δ×δ), SockChannel k.1 k.2 ep)):= progs.mapM (fun x => do
    IO.println "hello"
    let id := x.1
    let chan: SockChannel id.1 id.2 ep <-  init_channel id.1 id.2 ep x.2
    return ⟨id, chan⟩ )
    let cs <- channels_prog
    pure {
              channels := cs
              complete := fun k => by
                simp [List.dlookup_isSome, List.keys]
                sorry
                done
            }



inductive ChorEff {δ:Type} {ep:δ}: Type -> Type 1 where
| Send_recv [ser:Serialize a]: {sender:δ} -> GVal a sender ep  -> (receiver:δ) -> ChorEff (GVal a receiver ep)
| Local : (loc:δ) -> ([∀ x, Coe (GVal x loc ep) x] -> IO a) -> ChorEff (GVal a loc ep)
| Calc : (loc:δ) -> ([∀ x, Coe (GVal x loc ep) x] -> a) -> ChorEff (GVal a loc ep)

inductive Choreo {δ:Type} {ep:δ}: Type -> Type 1  where
| Cond [Serialize a] {decider:δ}: GVal a decider ep -> (a -> Choreo b) -> Choreo b
| Cond2 {decider:δ}: GVal Bool decider ep -> (Choreo a) -> (Choreo a) -> Choreo a
| Do :  ChorEff b (ep:=ep) -> (b -> Choreo a) -> Choreo a
| Return: a -> Choreo a

def Choreo.bind {δ:Type} [DecidableEq δ] {ep:δ} {α β: Type}:
  Choreo α (δ := δ) (ep := ep)→ (α → Choreo β (δ := δ) (ep := ep)) → Choreo β (δ := δ) (ep := ep)
| Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
| Choreo.Cond lv next, next' =>
  Choreo.Cond lv (fun x => bind (next x) next')
| Choreo.Cond2 lv opt_a opt_b, next' =>
  Choreo.Cond2 lv (bind opt_a next') (bind opt_b next')
| Choreo.Return v, next' => next' v

instance {δ:Type} [DecidableEq δ] {ep:δ}: Monad (Choreo (δ := δ) (ep := ep)) where
  pure x := Choreo.Return x
  bind  := Choreo.bind

def toChoreo {δ:Type} [DecidableEq δ] {ep:δ} (eff: ChorEff a (δ := δ) (ep := ep)) : Choreo a (δ := δ) (ep := ep):=
   Choreo.Do eff (Choreo.Return)

def send_recv  {δ:Type} [DecidableEq δ] {ep:δ}
  {a:Type} [Serialize a] {sender:δ} (gv: GVal a sender ep ) (receiver: δ) :=
  toChoreo (ChorEff.Send_recv gv receiver ) (a:=GVal a receiver ep)

def locally  {δ:Type} [DecidableEq δ] {ep:δ}
  (loc: δ) (comp: [∀ x, Coe (GVal x loc ep) x] -> IO b) :=
  toChoreo (ChorEff.Local loc comp) (a:=GVal b loc ep)

def compute {δ:Type} [DecidableEq δ] {ep:δ}
  (loc: δ) (comp: [∀ x, Coe (GVal x loc ep) x] -> b) :=
  toChoreo (ChorEff.Calc loc comp) (a:=GVal b loc ep)

def branch {δ:Type} [DecidableEq δ] {ep:δ}
    {a:Type} [Serialize a] {decider:δ} (gv: GVal a decider ep) (cont: a -> Choreo b (δ:=δ)):=
    Choreo.Cond gv cont

def branch' {δ:Type} [DecidableEq δ] {ep:δ}
  {a:Type} {decider:δ} [Serialize b] (comp: [∀ x , Coe (GVal x decider ep ) x] -> IO b) (cont: b -> Choreo a (δ:=δ)):=
  do
  let gv <- locally decider comp (δ:=δ) (ep:=ep)
  Choreo.Cond gv cont

def send_recv_comp {δ:Type} [DecidableEq δ] {ep:δ}
  {a:Type} (endpoint: String) [Serialize b] (sender receiver: δ) (comp: [∀ x, Coe (GVal x sender ep) x] -> IO b):=
  do
  let gv <- locally sender comp
  toChoreo (ChorEff.Send_recv gv receiver) (a:= GVal b receiver ep)


def ChorEff.epp {δ:Type} [DecidableEq δ] {ep:δ} [net: Network ep]:
  ChorEff a (δ:=δ) (ep:=ep)-> IO a
| ChorEff.Send_recv gv receiver (sender := sender) => do
  net.com sender gv receiver

| ChorEff.Local loc comp => do
    if h:( loc = ep) then

      have (x:Type) : Coe (GVal x loc ep) x := ⟨fun gv => gv.unwrap h⟩
      let res <- comp
      return GVal.Wrap h res
    else
      return  GVal.Empty h

| ChorEff.Calc loc comp => do
    if h:( loc = ep) then
      have (x:Type) : Coe (GVal x loc ep) x := ⟨fun gv => gv.unwrap h⟩
      return GVal.Wrap h (comp)
    else
      return  GVal.Empty h


partial def  Choreo.epp {δ:Type} [DecidableEq δ] {ep:δ} [net: Network ep]:
   Choreo a (δ:=δ) (ep:=ep) -> IO a
| Choreo.Return v => return v
| Choreo.Do eff next => do
  let res <- (eff.epp)
  --have h: sizeOf (next res) < 1 + sizeOf eff := by sorry
  Choreo.epp (next res)
| Choreo.Cond gv cont (decider:= decider) (ep:=ep) => do
  let endpoint_choice <- net.com decider gv ep
  let choice := endpoint_choice.unwrap (by simp)
  (cont choice).epp
| Choreo.Cond2 gv opt_a opt_b (decider:= decider) (ep:=ep) => do
  let endpoint_choice <- net.com decider gv ep
  let choice := endpoint_choice.unwrap (by simp)
  if choice then
    opt_a.epp
  else
    opt_b.epp


notation:55 lv "~>" receiver => send_recv lv receiver

notation:55 sender "~>" receiver "#" comp => send_recv_comp sender receiver comp
--notation:55 sender "~>" receiver "pure" comp => send_recv_pure sender receiver comp


def cast_gv {δ:Type} {owner ep:δ}  [DecidableEq δ] (gv: GVal a owner ep) [k:∀ x, Coe (GVal x owner ep (δ:=δ)) x]: a :=
  let c := k a
  c.coe gv

-- works similiar to normal coersion arrow ↑ but always casts to the underlying type
notation:55 "⤉" gv => cast_gv gv

syntax "send " ident (" from " ident)? " to " term (" as " ident)?: doElem

macro_rules
| `(doElem|send $i to $r) => `(doElem| let $i:ident := <- (send_recv $i $r))
| `(doElem|send $i to $r as $y) => `(doElem| let $y:ident := <- (send_recv $i $r))
| `(doElem|send $i from $i2 to $r) => `(doElem| let $i:ident := <- (send_recv (sender:=$i2) $i $r))
--| `(doElem|send $i from $i2 to $r as $y) => `(doElem| let $i := <- (send_recv $i $r (sender:=$i2)) )

syntax "decision " ident term " else " term: term

macro_rules
| `(decision $i $t1 else $t2) => `(Choreo.Cond2 $i ($t1) ($t2))


inductive Location
| alice | eve | bob
deriving Repr, Fintype

open Location

def Location.ofString: String -> Option Location
| "alice" => .some alice
| "eve" => .some eve
| "bob" => .some bob
| _ => .none





def adresses (k:Location × Location)  (p: k.1 ≠ k.2):  Address :=
match k, p with
| (alice, bob), _ => .v4  (.mk 127 0 0 1) 2222
| (alice, eve), _ => .v4  (.mk 127 0 0 1) 2223
| (bob, alice), _ => .v4  (.mk 127 0 0 1) 2224
| (bob, eve), _ => .v4  (.mk 127 0 0 1) 2225
| (eve, bob), _ => .v4  (.mk 127 0 0 1) 2226
| (eve, alice), _ => .v4  (.mk 127 0 0 1) 2227


instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

def fff: Fin (FinEnum.card Location) := (FinEnum.equiv Location.eve)


#eval (FinEnum.equiv Location.eve)


def silent_post (ep: Location):

  Choreo (ep:=ep) (GVal (List String) alice ep) := do

  let input: GVal String alice ep <- locally alice do
    IO.println "enter a message"
    return <- IO.getLine

  send input to eve

  let choice: GVal Bool alice ep <- compute alice true

  let temp <-
  decision choice
    return "hello"
  else
    return "nothello"

  let msg <- locally eve do
    return [↑input, "eve"]

  let msg <- send_recv msg bob

  let msg <- locally bob do
    let test:= msg
    return (⤉msg).concat "bob"

  let msg <- send_recv msg alice
  let _a <- locally alice do
    IO.println s!"alice ended with {⤉msg}"

  return msg


def main (args : List String): IO Unit := do
  let mode := args.get! 0

  let ep_opt := Location.ofString mode
  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h

    let net <-  init_network ep adresses

    have: Network ep := net.toNet

    let res <- ((silent_post ep).epp)
    IO.println (s!"res: {res}")

    let te := ["hello", "world"]
    let te2 <- te.mapM (fun x => IO.println x)
    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()
