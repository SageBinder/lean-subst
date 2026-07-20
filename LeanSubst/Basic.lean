
import Lilac
open Lilac

namespace LeanSubst

universe u

universe u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}

set_option linter.unusedVariables false in
abbrev Var (T : Type u2) := Nat

structure Ren (T : Type u2) where
  act : Var T -> Var T

@[simp]
def List.RenMapType (S : Type u) : List (Type u) -> Type u
| [] => S
| .cons x xs => Ren x -> List.RenMapType S xs

class RenMap (S : Type u) (V : List (Type u)) where
  rmap : List.RenMapType (S -> S) V

export RenMap (rmap)

def test1 : Ren Nat -> Nat -> Nat := sorry

instance : RenMap Nat [Nat] where
  rmap := test1

def test2 : Ren Nat -> Ren Bool -> Nat -> Nat := sorry

instance : RenMap Nat [Nat, Bool] where
  rmap := test2

theorem test3 {r1 : Ren Nat} {r2 : Ren Bool} {x : Nat} : @rmap _ [Nat, Bool] _ r1 r2 x = x := sorry


macro:max (name := «term_⟨_,⟩») t:term noWs "⟨" r:term ",⟩" : term => `(rmap $r $t)
syntax:max (name := «term_⟨_,+⟩») term noWs "⟨" term ,+ "⟩" : term

open Lean in
macro_rules
  | `($t⟨ $elems,* ⟩) => do
    let rec expand_ren_lit (i : Nat) (skip : Bool) (result : TSyntax `term) : MacroM Syntax := do
      match i, skip with
      | 0,     _     => pure result
      | i + 1, true  => expand_ren_lit i false result
      | i + 1, false => expand_ren_lit i true  (<- ``(Tuple.cons $(⟨elems.elemsAndSeps[i]!⟩) $result))
    let size := elems.elemsAndSeps.size
    let arg <- expand_ren_lit size (size % 2 == 0) (<- ``(Tuple.nil))
    let arg : TSyntax `term := .mk arg
    `(rmap $arg $t)

@[app_unexpander rmap]
def unexpand_rmap : Lean.PrettyPrinter.Unexpander
| `($_ $r $t) => `($t⟨$r⟩)
| _ => throw ()

inductive Action (T : Type u2) where
| re : Var T -> Action T
| su : T -> Action T
deriving Repr

export Action (re su)

structure Subst (T : Type u2) where
  inner : Var T -> Action T

class SubstAction (T : Type u1) (A : Type u2) (U : outParam (Type u3)) where
  act (σ : Subst T) : A -> U

def Subst.act [SubstAction S T U] (σ : Subst S) : T -> U := SubstAction.act σ

instance : SubstAction T Nat (Action T) where
  act := Subst.inner

class SubstMap {n} (S : Type u2) (V : Vec (Type u2) n) where
  smap : V -> S -> S

export SubstMap (smap)

macro:max (name := «term_[_,]») t:term noWs "[" σ:term ",]" : term => `(smap $σ $t)
syntax:max (name := «term_[_,+]») term noWs "[" term ,+ "]" : term

open Lean in
macro_rules
  | `($t[ $elems,* ]) => do
    let rec expand_subst_lit (i : Nat) (skip : Bool) (result : TSyntax `term) : MacroM Syntax := do
      match i, skip with
      | 0,     _     => pure result
      | i + 1, true  => expand_subst_lit i false result
      | i + 1, false => expand_subst_lit i true  (<- ``(Tuple.cons $(⟨elems.elemsAndSeps[i]!⟩) $result))
    let size := elems.elemsAndSeps.size
    let arg <- expand_subst_lit size (size % 2 == 0) (<- ``(Tuple.nil))
    let arg : TSyntax `term := .mk arg
    `(smap $arg $t)

@[app_unexpander smap]
def unexpand_smap : Lean.PrettyPrinter.Unexpander
| `($_ $σ $t) => `($t[$σ])
| _ => throw ()

end LeanSubst
