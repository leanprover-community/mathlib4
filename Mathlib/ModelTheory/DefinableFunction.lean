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

theorem finite_or_subsingleton_of_isDefFunc {φ : L.Formula (α ⊕ β)}
    (h : T.IsDefFunc φ) : (Finite β) ∨
    (∀ M : Theory.ModelType.{_, _, max u v} T, Subsingleton M) := by
  refine or_iff_not_imp_right.2 (fun h => ?_)
  simp only [subsingleton_iff, not_forall] at h
  rcases h with ⟨M, x, y, hxy⟩
  rcases h M with ⟨f, hf⟩
  by_contra hβ
  simp only [not_finite_iff_infinite] at hβ
  classical
  rcases Infinite.exists_not_mem_finset φ.freeVarFinset.toRight with ⟨b, hb⟩
  have h1 := (hf (fun _ => x) (f (fun _ => x))).1 rfl
  have k : { m : M // m ≠ f (fun _ => x) b } :=
    ⟨if f (fun _ => x) b = y then x else y, by split_ifs <;> simp_all [eq_comm]⟩
  have h2 := ((hf (fun _ => x)) (fun b' => if b' = b then k.val else f (fun _ => x) b')).2
    (by
      rwa [Formula.Realize, ← BoundedFormula.realize_restrictFreeVar' (Set.Subset.refl _),
        BoundedFormula.realize_restrictFreeVar (Sum.elim (fun _ => x) (f (fun _ => x)))]
      simp only [Finset.coe_sort_coe, Subtype.coe_eta, Function.comp_apply, Subtype.forall,
        Sum.forall, Sum.elim_inl, implies_true, Sum.elim_inr, ite_eq_right_iff, true_and]
      rintro b' hb' rfl
      simp_all)
  have := congr_fun h2 b
  simp only [↓reduceIte] at this
  exact k.2 this.symm

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
    refine ⟨?_, ?_⟩
    · intro h
      have : Finite β := by
        refine (finite_or_subsingleton_of_isDefFunc T h).resolve_right ?_
        simp
        simp [ModelsBoundedFormula, Fin.snoc] at hM
    · intro h M
      rcases h with ⟨_, h⟩
      have := fun v => h.realize_formula M (v := v)
      simp [Classical.skolem, Formula.realize_iExsUnique, ExistsUnique] at this
      rcases this with ⟨f, hf⟩
      use f
      intro x y
      refine ⟨?_, ?_⟩
      · rintro rfl
        exact (hf x).1
      · intro h
        exact ((hf x).2 y h).symm

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
