import Test.my_utils
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.List.Sigma
import Mathlib.Data.FinEnum

inductive Example_Location
| alice | eve | bob
deriving Repr, Fintype
open Example_Location

variable {α β: Type} -- alpha beta als normaler Type
variable {δ: Type} [DecidableEq δ]  -- delta als Location Type
variable {μ: Type} [Serialize μ]  -- mu wegen msg Type

inductive GVal (owner endpoint: δ) (α: Type)   where
| Wrap:  (owner = endpoint) -> α -> GVal owner endpoint α
| Empty: (owner ≠ endpoint) -> GVal owner endpoint α

inductive LVal (owner: δ) (α:Type)

#check ReaderT

--def LVal {δ:Type}  := δ -> Type

def GVal.wrap (owner:δ) (endpoint: δ) (v:α) : GVal owner endpoint α :=
  if h:(owner = endpoint) then
    GVal.Wrap h v
  else
    GVal.Empty h

def GVal.unwrap {owner endpoint: δ}: GVal owner endpoint α -> (owner = endpoint) -> α
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction



class Network (ep: δ) (M : ( Type -> Type) ) where
  com {μ:Type} [Serialize μ]: {s: δ} -> GVal s ep μ -> (r: δ) -> M (GVal r ep μ)




structure SockChannel {δ:Type} [DecidableEq δ] (sender receiver ep: δ ) where
  recv_sock: GVal receiver ep Socket
  send_sock: GVal sender ep Socket

def init_sending_channel {δ:Type} [DecidableEq δ] (sender ep:δ) (addr: Address):  IO (GVal sender ep Socket) := do
  if h:(sender = ep) then
    let sock <- addr.connect_to
    return GVal.Wrap h sock
  else
    return GVal.Empty h

def init_receiving_channel {δ:Type} [DecidableEq δ] (receiver ep: δ) (addr: Address):  IO (GVal receiver ep Socket) := do
  if h:(receiver = ep) then
    let sock <- addr.listen_on
    return GVal.Wrap h sock
  else
    return GVal.Empty h

-- epp for initializing one network socket
def init_channel {δ:Type} [DecidableEq δ] [Repr δ] (sender receiver ep: δ) (addr: Address):  IO (SockChannel sender receiver ep) := do
  if(dbg_print_init_sockets ∧ sender = ep) then
    IO.println s!"connecting out {reprStr sender} -> {reprStr receiver}"
  if(dbg_print_init_sockets ∧ receiver = ep) then
    IO.println s!"connecting in  {reprStr sender} -> {reprStr receiver}"
  let recv_sock <- init_receiving_channel receiver ep addr
  let send_sock <- init_sending_channel sender ep addr
  return ⟨recv_sock, send_sock⟩




structure SockNet {δ:Type} [DecidableEq δ] (ep: δ) [DecidableEq δ] where
  channels: List (Σ (id: δ×δ), SockChannel id.1 id.2 ep)
  complete: ∀ (k : δ×δ), (k.1 ≠ k.2) -> (channels.dlookup k).isSome

def SockNet.getChannel {δ:Type} [DecidableEq δ]  {ep: δ} (net:SockNet ep) (k:δ×δ) (not_self: k.1 ≠ k.2) : SockChannel k.1 k.2 ep :=
  (net.channels.dlookup k).get (by simp [net.complete, not_self])

def SockNet.toNet {δ:Type} [Repr δ] [DecidableEq δ] {ep:δ} (snet: SockNet ep): Network ep IO :=
  ⟨fun s gv r => do

    if h:( s = ep) then
      let v := gv.unwrap h
      if h2:(r = ep) then
        return GVal.Wrap h2 v
      else
        let h3: r != s := sorry
        let sock := (snet.getChannel (s, r) (by sorry)).send_sock.unwrap h
        let v := gv.unwrap h
        if dbg_print_net_msgs then
          IO.println s!"send to   {reprStr r} -> {Serialize.pretty v}"
        sock.send_val2 v
        return GVal.Empty h2
    else
      if h2:(r = ep) then
        let sock := (snet.getChannel (s, r) (by simp [h, h2])).recv_sock.unwrap h2
        let v <- sock.recv_val2
        if dbg_print_net_msgs then
          IO.println s!"recv from {reprStr s} -> {Serialize.pretty v}"
        return GVal.Wrap h2 v
      else
        return GVal.Empty h2⟩
instance  {δ:Type} [DecidableEq δ] {ep:δ} (snet: SockNet ep): Network ep IO where
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

def init_network [DecidableEq δ] [Repr δ] [FinEnum δ] (ep: δ) (as:  (k:δ×δ) -> (k.1 ≠ k.2) -> Address) : IO (SockNet ep) := do

  let filtered := (FinEnum.toList (δ×δ)).filter (fun k => k.1 ≠ k.2)
  let progs: List (Σ (k: (δ×δ)), Address)  := filtered.map (fun k => ⟨k, as k (by sorry)⟩ )
  let channels_prog: IO (List (Σ (k: δ×δ), SockChannel k.1 k.2 ep)):= progs.mapM (fun x => do
    let id := x.1
    let chan: SockChannel id.1 id.2 ep <-  init_channel id.1 id.2 ep x.2
    return ⟨id, chan⟩ )
  let cs <- channels_prog

  if(dbg_print_init_sockets) then
    IO.println ""
  return {
            channels := cs
            complete := fun k => by
              simp [List.dlookup_isSome, List.keys]
              sorry
              done
          }


instance: Network ep IO where
  com :=


inductive ChorEff (ep:δ) (LM: δ ->  (m: Type -> Type) × Monad m): Type -> Type 1 where
| Send_recv {μ:Type} [Serialize μ]: {sender:δ} -> GVal sender ep μ -> (receiver:δ) -> ChorEff ep LM (GVal receiver ep μ)
| Local {α:Type}: (loc:δ) -> ((LM ep).1 α) -> ChorEff ep LM (GVal loc ep α)

inductive Choreo (ep:δ) (LM: δ -> (m:Type -> Type) × Monad m := (fun _ => ⟨IO, inferInstance⟩)) : Type u -> Type (u+1)  where
| Do :  ChorEff ep LM b -> (b -> Choreo ep LM a) -> Choreo ep LM a
| Return: a -> Choreo ep LM a

def Choreo.bind {α β: Type}:
  Choreo LM ep α → (α  → Choreo LM ep β) → Choreo LM ep β
| Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
| Choreo.Return v, next' => next' v

instance: Monad (Choreo LM ep) where
  pure x := Choreo.Return x
  bind := Choreo.bind

def ChorEff.epp (eff: ChorEff ep LM a (δ:=δ)) [net:Network ep (LM ep)]: (LM ep).1 a :=
  have: Monad (LM ep).1 := (LM ep).2
  match eff with
  | ChorEff.Send_recv gv receiver =>
    net.com gv receiver
  | ChorEff.Local loc op => do
    let res <- op
    let gv := GVal.wrap loc ep res
    return gv



def Choreo.epp {α:Type} (chor:Choreo ep LM α (δ:=δ)) [Network ep (LM ep)]: (LM ep).1 α :=
  have: Monad (LM ep).1 := (LM ep).2
  match chor with
  | Choreo.Do eff next => do
    let e <- eff.epp
    let rest := next e
    rest.epp
  | Choreo.Return v => return v


def locally (loc: δ) (op: (LM ep).1 a) [Monad (LM ep).1]: Choreo ep LM (GVal loc ep a) :=
  have: Monad (LM ep).1 := (LM ep).2
  Choreo.Do (ChorEff.Local loc op) (fun x => Choreo.Return x)

def send_recv {sender:δ} (gv: GVal sender ep μ) (receiver:δ): Choreo ep LM (GVal receiver ep μ) :=
  Choreo.Do (ChorEff.Send_recv gv receiver) (fun x => Choreo.Return x)

def F : Nat → (m : Type -> Type) × Monad m
  | 0 => ⟨IO, inferInstance⟩
  | 1 => ⟨ReaderM Nat, inferInstance⟩
  | _ => ⟨Option, inferInstance⟩

-- this line is a bit of a hack
attribute [local instance] Sigma.snd in
def multiMonad : (n : Nat) → (F n).1 Unit
  | 0 => do
    -- in IO
    IO.println "hello"
    return ()
  | 1 => do
    let temp <- pure
    return ()
  | _ => do
    -- in Option
    return ()


-- this line is a bit of a hack
attribute [local instance] Sigma.snd in
def multiMonad : (n : Nat) → (F n).1 Unit
  | 0 => do
    -- in IO
    return ()
  | _ => do
    -- in Option
    return ()


def LocalProgs: Example_Location ->  (m: Type -> Type) × Monad m
| bob => ⟨IO, inferInstance⟩
| alice => ⟨ReaderM Nat, inferInstance⟩
| eve => ⟨IO, inferInstance⟩

--attribute [local instance] Sigma.snd in
def dist_prog2 (ep: Example_Location): (Choreo ep LocalProgs) Nat :=
  have: Monad (LocalProgs bob).fst := (LocalProgs bob).snd
  do

  let temp <- locally bob (do
    IO.println "hello"
    return "")
  let temp <- locally alice (do
    let bla <- read
    return "")
  let tt2 <- send_recv temp bob
  return 23
