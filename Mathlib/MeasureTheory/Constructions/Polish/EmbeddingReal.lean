/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# A Polish Borel space is measurably equivalent to a set of reals
-/

open Set Function PolishSpace PiNat TopologicalSpace Bornology Metric Filter Topology MeasureTheory

namespace MeasureTheory
variable (α : Type*) [MeasurableSpace α] [StandardBorelSpace α]

theorem exists_nat_measurableEquiv_range_coe_fin_of_finite [Finite α] :
    ∃ n : ℕ, Nonempty (α ≃ᵐ range ((↑) : Fin n → ℝ)) := by
  obtain ⟨n, ⟨n_equiv⟩⟩ := Finite.exists_equiv_fin α
  refine ⟨n, ⟨PolishSpace.Equiv.measurableEquiv (n_equiv.trans ?_)⟩⟩
  exact Equiv.ofInjective _ (Nat.cast_injective.comp Fin.val_injective)

theorem measurableEquiv_range_coe_nat_of_infinite_of_countable [Infinite α] [Countable α] :
    Nonempty (α ≃ᵐ range ((↑) : ℕ → ℝ)) := by
  have : PolishSpace (range ((↑) : ℕ → ℝ)) :=
    Nat.isClosedEmbedding_coe_real.isClosedMap.isClosed_range.polishSpace
  refine ⟨PolishSpace.Equiv.measurableEquiv ?_⟩
  refine (nonempty_equiv_of_countable.some : α ≃ ℕ).trans ?_
  exact Equiv.ofInjective ((↑) : ℕ → ℝ) Nat.cast_injective

/-- Any standard Borel space is measurably equivalent to a subset of the reals. -/
theorem exists_subset_real_measurableEquiv : ∃ s : Set ℝ, MeasurableSet s ∧ Nonempty (α ≃ᵐ s) := by
  by_cases hα : Countable α
  · cases finite_or_infinite α
    · obtain ⟨n, h_nonempty_equiv⟩ := exists_nat_measurableEquiv_range_coe_fin_of_finite α
      refine ⟨_, ?_, h_nonempty_equiv⟩
      letI : MeasurableSpace (Fin n) := borel (Fin n)
      haveI : BorelSpace (Fin n) := ⟨rfl⟩
      apply MeasurableEmbedding.measurableSet_range (mα := by infer_instance)
      exact continuous_of_discreteTopology.measurableEmbedding
        (Nat.cast_injective.comp Fin.val_injective)
    · refine ⟨_, ?_, measurableEquiv_range_coe_nat_of_infinite_of_countable α⟩
      apply MeasurableEmbedding.measurableSet_range (mα := by infer_instance)
      exact continuous_of_discreteTopology.measurableEmbedding Nat.cast_injective
  · refine
      ⟨univ, MeasurableSet.univ,
        ⟨(PolishSpace.measurableEquivOfNotCountable hα ?_ : α ≃ᵐ (univ : Set ℝ))⟩⟩
    rw [countable_coe_iff]
    exact Cardinal.not_countable_real

/-- Any standard Borel space embeds measurably into the reals. -/
theorem exists_measurableEmbedding_real : ∃ f : α → ℝ, MeasurableEmbedding f := by
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_subset_real_measurableEquiv α
  exact ⟨(↑) ∘ e, (MeasurableEmbedding.subtype_coe hs).comp e.measurableEmbedding⟩

/-- A measurable embedding of a standard Borel space into `ℝ`. -/
noncomputable
def embeddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : Ω → ℝ :=
  (exists_measurableEmbedding_real Ω).choose

lemma measurableEmbedding_embeddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] :
    MeasurableEmbedding (embeddingReal Ω) :=
  (exists_measurableEmbedding_real Ω).choose_spec

@[fun_prop]
lemma measurable_embeddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] :
    Measurable (embeddingReal Ω) :=
  (measurableEmbedding_embeddingReal Ω).measurable

end MeasureTheory
