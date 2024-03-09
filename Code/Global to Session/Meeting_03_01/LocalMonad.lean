import Test.my_utils
import Mathlib.Data.List.Sigma

variable {m : Type u → Type v}
variable [Monad m]
variable {δ:Type} [DecidableEq δ]


inductive L
| alice | eve | bob
deriving Repr, DecidableEq
open L

inductive GVal (owner endpoint: δ) (α: Type)   where
| Wrap:  (owner = endpoint) -> α -> GVal owner endpoint α
| Empty: (owner ≠ endpoint) -> GVal owner endpoint α


def GVal.wrap [DecidableEq δ] (owner endpoint: δ) (v:α) : GVal owner endpoint α :=
  if h:(owner = endpoint) then
    GVal.Wrap h v
  else
    GVal.Empty h

def GVal.unwrap  [DecidableEq δ] {owner endpoint: δ}: GVal owner endpoint α  -> (owner = endpoint) -> α
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction

class Network (ep: δ) (M : ( Type -> Type) ) where
  com {μ:Type} [Serialize μ]: {s: δ} -> GVal s ep μ -> (r: δ) -> M (GVal r ep μ)


structure LocalChannel (sender receiver: δ ) where
  messages: (List ((t:Type) × t))

def LocalChannel.write {α:Type} (v:α) (ch: LocalChannel s r (δ:=δ)): LocalChannel s r (δ:=δ) :=
  {ch with messages := ch.messages.concat ⟨α, v⟩}

def LocalChannel.read {α:Type} (ch: LocalChannel s r (δ:=δ)):  (α ×  LocalChannel s r (δ:=δ)) :=
  if h(ch.messages[0])let temp := ch.messages[0]
  {ch with messages := ch.messages.concat ⟨α, v⟩}


structure LocalNet (δ:Type)  [DecidableEq δ] where
  channels: List (Σ (id: δ×δ), LocalChannel id.1 id.2)
  complete: ∀ (k : δ×δ), (channels.dlookup k).isSome


-- def NetM (δ:Type) [DecidableEq δ] (α : Type) :=
--    LocalNet δ → (LocalNet δ × α)

-- def NetM.bind {α β : Type} [DecidableEq δ] (n: NetM δ α)  (next: α → NetM δ β) :  NetM δ β :=
--   fun x =>
--     let temp := n x
--     let temp2 := next temp.2
--     let temp3 := temp2
--     sorry

-- instance[DecidableEq δ]: Monad (NetM δ) where
--   pure x:= fun s => ⟨s, x⟩
--   bind :=  fun s =>


def NetM := StateM (LocalNet δ)

def funky: StateM (List (Σ (l:δ) (α:Type), List α))  (Σ (α:Type), α)  := do
  let state <- get
  let temp := state.dlookup
  return ⟨Nat, 0⟩

def funky2: StateM (List (Σ (l:L) (α:Type), List α))  (Σ (α:Type), α)  := do
  let state <- get
  let temp := state.dlookup alice
  return ⟨Nat, 0⟩


def com2 {s ep: δ} (gv: GVal s ep α ) (r:δ) : StateM (LocalNet δ) (Σ (α:Type), GVal receiver ep α):= do
  let state <- get
  if h:(s = ep) then
    let v := gv.unwrap h
    let channel := (state.channels.dlookup (s,r)).get (state.complete (s,r))
    sorry
  else
    sorry

def com {sender: δ} (gv: GVal s ep α ) (r:δ) [DecidableEq δ]: NetM δ (GVal r ep α):=
  if h:(sender = ep) then
    sorry
  else
    sorry
