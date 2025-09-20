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

open UniformSpace.Completion

variable {α β : Type*} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α]
  {L : Filter (Finset β)}


/-- A function `f` has a sum in an uniform additive group `α` if and only if it has that sum in the
completion of `α`. -/
theorem hasSumFilter_iff_hasSumFilter_compl (f : β → α) (a : α) :
    HasSumFilter L (toCompl ∘ f) a ↔ HasSumFilter L f a :=
  (isDenseInducing_toCompl α).hasSumFilter_iff f a

/-- A function `f` is summable in a uniform additive group `α` if and only if it is summable in
`Completion α` and its sum in `Completion α` lies in the range of `toCompl : α →+ Completion α`. -/
theorem summableFilter_iff_summableFilter_compl_and_tsumFilter_mem [L.NeBot] (f : β → α) :
    SummableFilter L f ↔ SummableFilter L (toCompl ∘ f) ∧
    ∑'[L] i, toCompl (f i) ∈ Set.range toCompl :=
  (isDenseInducing_toCompl α).summableFilter_iff_tsumFilter_comp_mem_range f

/-- A function `f` is summable in a uniform additive group `α` if and only if the net of its partial
sums is Cauchy and its sum in `Completion α` lies in the range of `toCompl : α →+ Completion α`.
(The condition that the net of partial sums is Cauchy can be checked using
`cauchySeq_finset_iff_sum_vanishing` or `cauchySeq_finset_iff_tsum_vanishing`.) -/
theorem summable_iff_cauchySeq_finset_and_tsum_mem (f : β → α) :
    Summable f ↔ CauchySeq (fun s : Finset β ↦ ∑ b ∈ s, f b) ∧
      ∑' i, toCompl (f i) ∈ Set.range toCompl := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨ha.cauchySeq,
      ((summableFilter_iff_summableFilter_compl_and_tsumFilter_mem f).mp ⟨a, ha⟩).2⟩
  · rintro ⟨h_cauchy, h_tsum⟩
    apply (summableFilter_iff_summableFilter_compl_and_tsumFilter_mem f).mpr
    constructor
    · apply summable_iff_cauchySeq_finset.mpr
      simp_rw [Function.comp_apply, ← map_sum]
      exact h_cauchy.map (uniformContinuous_coe α)
    · exact h_tsum

/-- If a function `f` is summable in a uniform additive group `α`, then its sum in `α` is the same
as its sum in `Completion α`. -/
theorem SummableFilter.toCompl_tsumFilter [L.NeBot] {f : β → α} (hf : SummableFilter L f) :
    ∑'[L] i, toCompl (f i) = ∑'[L] i, f i :=
  (hf.map_tsumFilter toCompl (continuous_coe α)).symm
