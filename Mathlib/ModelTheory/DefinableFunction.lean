/-
Copyright (c) 2024 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.ModelTheory.Algebra.Field.IsAlgClosed

universe u v w x

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory) {α : Type w} {β : Type x}

def IsDefFunc (φ : L.Formula (α ⊕ β)) : Prop :=
  ∀ (M : Type (max u v)) [L.Structure M] [T.Model M],
      ∃ f : (α → M) → (β → M), ∀ x : α → M, ∀ y : β → M,
        (f x = y) ↔ φ.Realize (Sum.elim x y)
#print Formula.or
theorem isDefFunc_iff_of_finite [Fintype α] [Fintype β] {φ : L.Formula (α ⊕ β)} :
    T.IsDefFunc φ ↔ T ⊨ᵇ
      (Formula.iAlls (β := Empty) Sum.inr
        (Formula.iExs Sum.swap φ)) ⊓
      BoundedFormula.iInf (Finset.univ : Finset α) _ := by sorry

/-- A definable  -/
def DefFunc (α : Type w) (β : Type x) : Type _ :=
  { φ : L.Formula (α ⊕ β) // ∀ (M : Type (max u v)) [L.Structure M] [T.Model M],
      ∃ f : (α → M) → (β → M), ∀ x : α → M, ∀ y : β → M,
        (f x = y) ↔ φ.Realize (Sum.elim x y) }

namespace DefFunc



end DefFunc

end Theory

end Language

end FirstOrder
