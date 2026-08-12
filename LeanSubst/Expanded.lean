
import LeanSubst.Basic
import LeanSubst.Ops
import LeanSubst.Class

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T T1 T2 T3 : Type u2} {U : Type u3}
variable {V : List (Type u2)}


@[grind =_]
theorem RenVec.get_eta1 {r : RenVec [T1]} : r = (r.get T1 0, .unit) := sorry

@[grind =_]
theorem RenVec.get_eta2 {r : RenVec [T1, T2]} : r = (r.get T1 0, r.get T2 1, .unit) := sorry

@[grind =_]
theorem SubstVec.get_eta1 {σ : SubstVec [T1]} : σ = (σ.get T1 0, .unit) := sorry

@[grind =_]
theorem SubstVec.get_eta2 {σ : SubstVec [T1, T2]} : σ = (σ.get T1 0, σ.get T2 1, .unit) := sorry


-- @[simp]
-- theorem subst_tuple_eta1 [SubstMap S [T]] {s : S} {σ : List.Tuple Subst [T]} : s[σ,] = s[σ.1] := by
--   rcases σ with ⟨σ, u⟩; rcases u; simp

-- @[simp]
-- theorem subst_tuple_eta2 [SubstMap S [T1, T2]] {s : S} {σ : List.Tuple Subst [T1, T2]}
--   : s[σ,] = s[σ.1, σ.2.1]
-- := by
--   rcases σ with ⟨σ1, σ2, u⟩; rcases u; simp

end LeanSubst
