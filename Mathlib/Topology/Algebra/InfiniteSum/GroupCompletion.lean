/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Infinite sums in the completion of a topological group
-/

open UniformSpace UniformSpace.Completion

variable {α β : Type*} [AddCommGroup α] [UniformSpace α] [UniformAddGroup α]

/-- A function `f` has a sum in an uniform additive group `α` if and only if it has that sum in the
completion of `α`. -/
theorem UniformSpace.Completion.hasSum_coe_comp_iff (f : β → α) (a : α) :
    HasSum ((coe : α → Completion α) ∘ f) a ↔ HasSum f a :=
    (isDenseInducing_coeAddHom α).hasSum_iff f a

@[deprecated (since := "2025-01-05")] alias hasSum_iff_hasSum_compl :=
  UniformSpace.Completion.hasSum_coe_comp_iff

/-- A function `f` is summable in a uniform additive group `α` if and only if it is summable in
`Completion α` and its sum in `Completion α` lies in the range of `coe : α → Completion α`. -/
theorem summable_iff_summable_compl_and_tsum_mem (f : β → α) :
    Summable f ↔
      Summable ((coe : α → Completion α) ∘ f) ∧ ∑' i, (f i : Completion α) ∈ Set.range coe :=
  (isDenseInducing_coeAddHom α).summable_iff_tsum_comp_mem_range f

/-- A function `f` is summable in a uniform additive group `α` if and only if the net of its partial
sums is Cauchy and its sum in `Completion α` lies in the range of `coe : α → Completion α`.
(The condition that the net of partial sums is Cauchy can be checked using
`cauchySeq_finset_iff_sum_vanishing` or `cauchySeq_finset_iff_tsum_vanishing`.) -/
theorem summable_iff_cauchySeq_finset_and_tsum_mem (f : β → α) :
    Summable f ↔ CauchySeq (fun s : Finset β ↦ ∑ b in s, f b) ∧
      ∑' i, (f i : Completion α) ∈ Set.range coe := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨ha.cauchySeq, ((summable_iff_summable_compl_and_tsum_mem f).mp ⟨a, ha⟩).2⟩
  · rintro ⟨h_cauchy, h_tsum⟩
    apply (summable_iff_summable_compl_and_tsum_mem f).mpr
    constructor
    · apply summable_iff_cauchySeq_finset.mpr
      simp_rw [Function.comp_apply, ← coeAddHom_eq_coe, ← map_sum]
      exact h_cauchy.map (uniformContinuous_coe α)
    · exact h_tsum

/-- If a function `f` is summable in a uniform additive group `α`, then its sum in `α` is the same
as its sum in `Completion α`. -/
theorem Summable.tsum_coe_completion {f : β → α} (hf : Summable f) :
    ∑' i, (f i : Completion α) = ∑' i, f i :=
  (hf.map_tsum coeAddHom (continuous_coe α)).symm

@[deprecated (since := "2025-01-05")] alias Summable.toCompl_tsum := Summable.tsum_coe_completion
