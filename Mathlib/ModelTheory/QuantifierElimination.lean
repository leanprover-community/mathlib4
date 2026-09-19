/-
Copyright (c) 2026 Yağız Kaan Aydoğdu, Yusuf Demir, Salih Erdem Koçak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yağız Kaan Aydoğdu, Yusuf Demir, Salih Erdem Koçak
-/
module

public import Mathlib.Data.Finite.Sum
public import Mathlib.ModelTheory.Complexity
public import Mathlib.ModelTheory.Satisfiability

/-!
# Quantifier Elimination

This file defines quantifier elimination for first-order theories and reduces it to the
elimination of a single existential quantifier from quantifier-free formulas.

## Main Definitions

- `FirstOrder.Language.Theory.IsQFEquivalent` says that a formula is equivalent over a theory to a
  quantifier-free formula.
- `FirstOrder.Language.Theory.HasQuantifierElimination` says that every formula in finitely many
  free variables is equivalent over the theory to a quantifier-free formula.

## Main Results

- `FirstOrder.Language.Theory.hasQuantifierElimination_iff_finite_isQFEquivalent` characterizes
  quantifier elimination by quantifier-free equivalence for every formula over a finite index type
  of variables.
- `FirstOrder.Language.Theory.hasQuantifierElimination_iff_ex_isQFEquivalent_of_isQF` characterizes
  quantifier elimination by elimination of one existential quantifier from quantifier-free
  formulas. This corresponds to [Theorem 3.1.5][marker2002].

## References

- [D. Marker, *Model Theory: An Introduction*][marker2002]
-/

@[expose] public section

universe u v w u'

namespace FirstOrder

namespace Language

namespace Theory

open Structure
variable {L : Language.{u, v}}
variable {M : Type w} {N A : Type*} [L.Structure M] [L.Structure N] [L.Structure A]

/-- A formula is equivalent to a quantifier-free formula over a theory. -/
def IsQFEquivalent (T : L.Theory) {α : Type*} (φ : L.Formula α) : Prop :=
  ∃ ψ : L.Formula α, ψ.IsQF ∧ φ ⇔[T] ψ

/-- A theory has quantifier elimination if every formula is equivalent, over the theory, to a
quantifier-free formula. -/
def HasQuantifierElimination (T : L.Theory) : Prop :=
  ∀ {α : Type} (φ : L.Formula α), T.IsQFEquivalent φ

/-- Promote the single-bound-variable elimination hypothesis to any number of bound variables: if
existential closures of quantifier-free formulas over one bound variable are quantifier-free
equivalent over `T`, then so are existential closures of quantifier-free formulas with `n + 1`
bound variables, reduced to the last bound variable. -/
private theorem exists_qf_equiv_ex_of_isQF
    {T : L.Theory}
    (h :
      ∀ {α : Type u'} [Finite α] (θ : L.BoundedFormula α 1), θ.IsQF →
        ∃ ψ : L.Formula α, ψ.IsQF ∧ θ.ex ⇔[T] ψ)
    {α : Type u'} [Finite α] {n : ℕ} {θ : L.BoundedFormula α (n + 1)} (hθ : θ.IsQF) :
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧ θ.ex ⇔[T] ψ := by
  -- Keep the last of the `n + 1` bound variables as the single bound variable handled by `h`, and
  -- move the other `n` bound variables into the free index type `α ⊕ Fin n`.
  let toOne : α ⊕ Fin (n + 1) → (α ⊕ Fin n) ⊕ Fin 1 :=
    Sum.elim (fun i => Sum.inl (Sum.inl i))
      (Fin.lastCases (Sum.inr 0) fun i => Sum.inl (Sum.inr i))
  let θ' : L.BoundedFormula (α ⊕ Fin n) 1 := BoundedFormula.relabel toOne θ.toFormula
  -- Apply the one-variable hypothesis, then relabel the result back; the rest checks the bound
  -- variable lines up on both sides of the equivalence.
  obtain ⟨ψ', hψ', hθψ'⟩ := h θ' (hθ.toFormula.relabel _)
  refine ⟨BoundedFormula.relabel (id : α ⊕ Fin n → α ⊕ Fin n) ψ',
    hψ'.relabel _, fun M v xs => ?_⟩
  let v' : α ⊕ Fin n → M := Sum.elim v xs
  rw [BoundedFormula.realize_iff, BoundedFormula.realize_ex]
  simp only [BoundedFormula.realize_relabel, Function.comp_id,
    Fin.castAdd_zero, Fin.cast_refl]
  rw [Subsingleton.elim (xs ∘ Fin.natAdd n : Fin 0 → M) default]
  refine (exists_congr fun a => ?_).trans
    (BoundedFormula.realize_ex.symm.trans (BoundedFormula.realize_iff.mp (hθψ' M v' default)))
  change θ.Realize v (Fin.snoc xs a) ↔
    (BoundedFormula.relabel toOne θ.toFormula).Realize v' (Fin.snoc default a)
  rw [BoundedFormula.realize_relabel,
    show (Fin.snoc default a ∘ Fin.natAdd 1 : Fin 0 → M) = default from Subsingleton.elim _ _]
  change _ ↔ θ.toFormula.Realize _
  rw [BoundedFormula.realize_toFormula]
  refine iff_of_eq <| congrArg₂ _ ?_ ?_
  · funext i; simp [toOne, v']
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [toOne, v', Fin.snoc]
    · simp [toOne, v']

/-- A theory has quantifier elimination iff every formula over a finite index type of variables is
equivalent over the theory to a quantifier-free formula: any formula has only finitely many free
variables, so the general case reduces to the finite-index case by restricting to the
free-variable subtype. -/
theorem hasQuantifierElimination_iff_finite_isQFEquivalent {T : L.Theory} :
    T.HasQuantifierElimination ↔
      ∀ {α : Type} [Finite α] (φ : L.Formula α), T.IsQFEquivalent φ := by
  refine ⟨fun h _ _ φ => h φ, fun h α φ => ?_⟩
  classical
  let S : Set α := ↑φ.freeVarFinset
  haveI : Finite S := φ.freeVarFinset.finite_toSet.to_subtype
  obtain ⟨ψ', hψ'QF, hψ'eq⟩ := h (φ.restrictFreeVar (Set.inclusion subset_rfl))
  refine ⟨ψ'.relabel ((↑) : S → α), hψ'QF.relabel _, fun M v xs => ?_⟩
  rw [BoundedFormula.realize_iff,
    ← BoundedFormula.realize_restrictFreeVar' (subset_rfl : S ⊆ S)
      (v := v) (xs := xs),
    Subsingleton.elim xs (default : Fin 0 → M)]
  exact (BoundedFormula.realize_iff.mp (hψ'eq M (v ∘ (↑)) default)).trans
    Formula.realize_relabel.symm

/-- A theory has quantifier elimination iff for every quantifier-free formula `θ` with one bound
variable, the formula `θ.ex` is equivalent over the theory to a quantifier-free formula.

This corresponds to [Theorem 3.1.5][marker2002]. -/
theorem hasQuantifierElimination_iff_ex_isQFEquivalent_of_isQF {T : L.Theory} :
    T.HasQuantifierElimination ↔
      ∀ {α : Type} [Finite α] (θ : L.BoundedFormula α 1), θ.IsQF → T.IsQFEquivalent θ.ex := by
  refine ⟨fun h _ _ θ _ => h θ.ex, fun h => ?_⟩
  refine hasQuantifierElimination_iff_finite_isQFEquivalent.mpr (fun {α} _ φ => ?_)
  -- Induct on formula structure: quantifier-free equivalence is preserved by negation, by the
  -- existential step (handled by `exists_qf_equiv_ex_of_isQF`), and along semantic equivalence.
  refine φ.induction_on_exists_not
    (P := fun {_} φ => ∃ ψ, ψ.IsQF ∧ φ ⇔[T] ψ)
    (fun hψ => ⟨_, hψ, Theory.Iff.refl _⟩) ?_ ?_ ?_
  · rintro _ φ ⟨ψ, hψ, hφψ⟩
    exact ⟨ψ.not, hψ.not, hφψ.not⟩
  · rintro _ φ ⟨ψ, hψ, hφψ⟩
    obtain ⟨χ, hχ, hψχ⟩ := exists_qf_equiv_ex_of_isQF h hψ
    exact ⟨χ, hχ, hφψ.ex.trans hψχ⟩
  · intro _ φ₁ φ₂ hφ₁φ₂
    have hφ₁φ₂T : φ₁ ⇔[T] φ₂ := fun M v xs =>
      hφ₁φ₂ (Theory.ModelType.of (∅ : L.Theory) M) v xs
    exact ⟨fun ⟨ψ, hψ, hφ₁ψ⟩ => ⟨ψ, hψ, hφ₁φ₂T.symm.trans hφ₁ψ⟩,
      fun ⟨ψ, hψ, hφ₂ψ⟩ => ⟨ψ, hψ, hφ₁φ₂T.trans hφ₂ψ⟩⟩

end Theory

end Language

end FirstOrder
