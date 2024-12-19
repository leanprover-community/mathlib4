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
  ∀ (M : Theory.ModelType.{_, _, max u v} T),
      ∃ f : (α → M) → (β → M), ∀ x : α → M, ∀ y : β → M,
        (f x = y) ↔ φ.Realize (Sum.elim x y)
#print ModelsBoundedFormula
theorem isDefFunc_iff [DecidableEq (α ⊕ β)] {φ : L.Formula (α ⊕ β)} :
    T.IsDefFunc φ ↔
      (∃ (h : Finite β),
        T ⊨ᵇ (Formula.iExsUnique (γ := β) id φ)) ∨
    (T ⊨ᵇ (∀' ∀' ((Term.var (Sum.inr 0)) =' (Term.var (Sum.inr 1))) : L.Formula Empty) ∧
      T ⊨ᵇ φ) := by
  by_cases hM : T ⊨ᵇ ∀' ∀' ((var (Sum.inr 0) : L.Term (Empty ⊕ Fin 2)) =' var (Sum.inr 1)) ∧ T ⊨ᵇ φ
  · refine iff_of_true ?_ (Or.inr hM)
    intro M
    let m : M := Classical.choice inferInstance
    use fun _ _ => m
    intro x y
    have h1 : ∀ a b : M, a = b :=
      by simpa [Sentence.Realize, Formula.Realize] using hM.1.realize_sentence M
    exact iff_of_true (funext (fun _ => h1 _ _)) (hM.2.realize_formula M)
  · rw [or_iff_left hM]
    simp only [IsDefFunc, ModelsBoundedFormula, BoundedFormula.realize_iExsUnique, id_eq,
      forall_const, exists_prop]
    refine ⟨?_, ?_⟩
    · intro h
      admit
    · intro h M
      simp only [Classical.skolem, ExistsUnique] at h
      rcases h.2 with ⟨f, hf⟩
      use f M
      intro x y







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
