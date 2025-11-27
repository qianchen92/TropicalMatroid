import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Basic

namespace TropicalMatroid


variable (α : Type*) [Fintype α]

class PowersetSetoid extends Setoid α where
  setEquiv : Set α → Set α → Prop
  setEquiv_Equiv : Equivalence setEquiv
  singleton_consistency : ∀ x y : α, setEquiv {x} {y} ↔ r x y
  insert_congruence : ∀ (S₁ S₂ : Set α) (x y : α),
    setEquiv S₁ S₂ → r x y → setEquiv (S₁ ∪ {x}) (S₂ ∪ {y})
  substitutivity : ∀ (S : Set α) (x y : α),
    x ∈ S → r x y → setEquiv ((S \ {x}) ∪ {y}) S

infix:50 " ≈ " => PowersetSetoid.setEquiv
end TropicalMatroid
