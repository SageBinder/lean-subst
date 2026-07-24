
namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}

@[implicit_reducible, simp]
def List.Tuple (F : Type u1 -> Type u2) : List (Type u1) -> Type u2
| [] => ULift Unit
| .cons x xs => F x × List.Tuple F xs

class List.TuplePred (P : Type u2 -> List (Type u2) -> Type u1) (V : List $ Type u2) where
  pred : ∀ (i : Fin V.length), P V[i] [V[i]]

end LeanSubst
