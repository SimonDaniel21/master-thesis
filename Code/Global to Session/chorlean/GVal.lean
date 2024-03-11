import Mathlib.Data.List.Sigma

inductive GVal (owner endpoint: δ) (α: Type)   where
| Wrap:  (owner = endpoint) -> α -> GVal owner endpoint α
| Empty: (owner ≠ endpoint) -> GVal owner endpoint α

@[reducible] def GVal.owner {δ} {o ep:δ} (_gv:GVal o ep α (δ:=δ)) : δ := o
@[reducible] def GVal.dataType {δ} {o ep:δ} (_gv:GVal o ep α (δ:=δ)) : Type := α


variable {δ: Type} [DecidableEq δ]  -- delta als Location Type

def GVal.wrap (owner:δ) (endpoint: δ) (v:α) : GVal owner endpoint α :=
  if h:(owner = endpoint) then
    GVal.Wrap h v
  else
    GVal.Empty h

def GVal.unwrap {owner endpoint: δ}: GVal owner endpoint α -> (owner = endpoint) -> α
| Wrap _ v  => fun _ => v
| Empty q => fun x => by contradiction

def GVal.reduce {α:Type}  (gvs: List (Σ (loc: δ), GVal loc ep α )) (complete: ∀ (loc : δ),  (gvs.dlookup loc).isSome):  α :=
  let local_gv := (gvs.dlookup ep).get (complete ep)
  let v := local_gv.unwrap (by simp)
  v

instance {loc ep: δ} [ToString μ]: ToString (GVal loc ep μ) where
  toString x :=
    if h:(loc = ep) then
      let val := x.unwrap h
      toString val
    else
      "Empty"

@[reducible] def LVal {ep:δ} (owner: δ) (α:Type) := GVal owner ep α

class Unpack (loc ep: δ) (α : Type) where
  unpack : GVal loc ep α → α

notation:55 α " @ " owner " # " ep  => GVal owner ep α
notation:55 α "@" owner =>  LVal owner α
