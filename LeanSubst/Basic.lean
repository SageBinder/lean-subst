
import Lilac
open Lilac

namespace LeanSubst

universe u1 u2 u3
variable {S : Type} {T : Type} {U : Type}

structure Ren (T : Type) : Type where
  act : Nat -> Nat

class RenMap {n : Nat} (S : Type) (V : Vec (Type) n) where
  rmap : V -> S -> S
  self : Option (V -> Ren S)

export RenMap (rmap)

macro:max t:term noWs "⟨" r:term "⟩" : term => `(rmap $r $t)

@[app_unexpander rmap]
def unexpand_rmap : Lean.PrettyPrinter.Unexpander
| `($_ $r $t) => `($t⟨$r⟩)
| _ => throw ()

def test1 : Ren Nat -> Nat -> Nat := sorry
def test2 : Ren Nat × Ren Bool -> Nat -> Nat := sorry

instance : RenMap Nat #(Ren Nat) where
  rmap := test1
  self := sorry

instance : RenMap Nat #(Ren Nat, Ren Bool) where
  rmap := test2
  self := sorry

theorem test3 (r1 : Ren Nat) (r2 : Ren Bool) (x : Nat) : x⟨r1::r2::#⟨⟩⟩ = x := sorry

theorem test4 (r1 : Ren Nat) (x : Nat) : x⟨r1::#⟨⟩⟩ = x := sorry

inductive Action (T : Type) where
| re : Nat -> Action T
| su : T -> Action T
deriving Repr

export Action (re su)

instance {n} {S : Type} {V : Vec Type n} [i : RenMap S V] : RenMap (Action S) V where
  self := none
  rmap := λ r a =>
    match a with
    | re x =>
      match i.self with
      | some p => re ((p r).act x)
      | none => re x
    | su t => su t⟨r⟩

-- structure Subst (T : Type u2) where
--   inner : Nat -> Action T

-- class SubstAction (T : Type u1) (A : Type u2) (U : outParam (Type u3)) where
--   act (σ : Subst T) : A -> U

-- def Subst.act [SubstAction S T U] (σ : Subst S) : T -> U := SubstAction.act σ

-- instance : SubstAction T Nat (Action T) where
--   act := Subst.inner

-- class SubstMap {n} (S : Type u1) (V : Vec (Type u2) n) where
--   smap : V.map Subst -> S -> S

-- export SubstMap (smap)

-- macro:max t:term noWs "[" σ:term "]" : term => `(smap $σ $t)

-- @[app_unexpander smap]
-- def unexpand_smap : Lean.PrettyPrinter.Unexpander
-- | `($_ $σ $t) => `($t[$σ])
-- | _ => throw ()


end LeanSubst
