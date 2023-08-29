/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.MeasurableSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

#align_import measure_theory.function.ae_measurable_sequence from "leanprover-community/mathlib"@"d003c55042c3cd08aefd1ae9a42ef89441cdaaf3"

/-!
# Sequence of measurable functions associated to a sequence of a.e.-measurable functions

We define here tools to prove statements about limits (infi, supr...) of sequences of
`AEMeasurable` functions.
Given a sequence of a.e.-measurable functions `f : ι → α → β` with hypothesis
`hf : ∀ i, AEMeasurable (f i) μ`, and a pointwise property `p : α → (ι → β) → Prop` such that we
have `hp : ∀ᵐ x ∂μ, p x (fun n ↦ f n x)`, we define a sequence of measurable functions `aeSeq hf p`
and a measurable set `aeSeqSet hf p`, such that
* `μ (aeSeqSet hf p)ᶜ = 0`
* `x ∈ aeSeqSet hf p → ∀ i : ι, aeSeq hf hp i x = f i x`
* `x ∈ aeSeqSet hf p → p x (fun n ↦ f n x)`
-/


open MeasureTheory

open Classical

variable {ι : Sort*} {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : ι → α → β}
  {μ : Measure α} {p : α → (ι → β) → Prop}

/-- If we have the additional hypothesis `∀ᵐ x ∂μ, p x (fun n ↦ f n x)`, this is a measurable set
whose complement has measure 0 such that for all `x ∈ aeSeqSet`, `f i x` is equal to
`(hf i).mk (f i) x` for all `i` and we have the pointwise property `p x (fun n ↦ f n x)`. -/
def aeSeqSet (hf : ∀ i, AEMeasurable (f i) μ) (p : α → (ι → β) → Prop) : Set α :=
  (toMeasurable μ { x | (∀ i, f i x = (hf i).mk (f i) x) ∧ p x fun n => f n x }ᶜ)ᶜ
#align ae_seq_set aeSeqSet

/-- A sequence of measurable functions that are equal to `f` and verify property `p` on the
measurable set `aeSeqSet hf p`. -/
noncomputable def aeSeq (hf : ∀ i, AEMeasurable (f i) μ) (p : α → (ι → β) → Prop) : ι → α → β :=
  fun i x => ite (x ∈ aeSeqSet hf p) ((hf i).mk (f i) x) (⟨f i x⟩ : Nonempty β).some
#align ae_seq aeSeq

namespace aeSeq

section MemAESeqSet

theorem mk_eq_fun_of_mem_aeSeqSet (hf : ∀ i, AEMeasurable (f i) μ) {x : α} (hx : x ∈ aeSeqSet hf p)
    (i : ι) : (hf i).mk (f i) x = f i x :=
  haveI h_ss : aeSeqSet hf p ⊆ { x | ∀ i, f i x = (hf i).mk (f i) x } := by
    rw [aeSeqSet, ← compl_compl { x | ∀ i, f i x = (hf i).mk (f i) x }, Set.compl_subset_compl]
    -- ⊢ {x | ∀ (i : ι), f i x = AEMeasurable.mk (f i) (_ : AEMeasurable (f i)) x}ᶜ ⊆ …
    refine' Set.Subset.trans (Set.compl_subset_compl.mpr fun x h => _) (subset_toMeasurable _ _)
    -- ⊢ x ∈ {x | ∀ (i : ι), f i x = AEMeasurable.mk (f i) (_ : AEMeasurable (f i)) x}
    exact h.1
    -- 🎉 no goals
  (h_ss hx i).symm
#align ae_seq.mk_eq_fun_of_mem_ae_seq_set aeSeq.mk_eq_fun_of_mem_aeSeqSet

theorem aeSeq_eq_mk_of_mem_aeSeqSet (hf : ∀ i, AEMeasurable (f i) μ) {x : α}
    (hx : x ∈ aeSeqSet hf p) (i : ι) : aeSeq hf p i x = (hf i).mk (f i) x := by
  simp only [aeSeq, hx, if_true]
  -- 🎉 no goals
#align ae_seq.ae_seq_eq_mk_of_mem_ae_seq_set aeSeq.aeSeq_eq_mk_of_mem_aeSeqSet

theorem aeSeq_eq_fun_of_mem_aeSeqSet (hf : ∀ i, AEMeasurable (f i) μ) {x : α}
    (hx : x ∈ aeSeqSet hf p) (i : ι) : aeSeq hf p i x = f i x := by
  simp only [aeSeq_eq_mk_of_mem_aeSeqSet hf hx i, mk_eq_fun_of_mem_aeSeqSet hf hx i]
  -- 🎉 no goals
#align ae_seq.ae_seq_eq_fun_of_mem_ae_seq_set aeSeq.aeSeq_eq_fun_of_mem_aeSeqSet

theorem prop_of_mem_aeSeqSet (hf : ∀ i, AEMeasurable (f i) μ) {x : α} (hx : x ∈ aeSeqSet hf p) :
    p x fun n => aeSeq hf p n x := by
  simp only [aeSeq, hx, if_true]
  -- ⊢ p x fun n => AEMeasurable.mk (f n) (_ : AEMeasurable (f n)) x
  rw [funext fun n => mk_eq_fun_of_mem_aeSeqSet hf hx n]
  -- ⊢ p x fun n => f n x
  have h_ss : aeSeqSet hf p ⊆ { x | p x fun n => f n x } := by
    rw [← compl_compl { x | p x fun n => f n x }, aeSeqSet, Set.compl_subset_compl]
    refine' Set.Subset.trans (Set.compl_subset_compl.mpr _) (subset_toMeasurable _ _)
    exact fun x hx => hx.2
  have hx' := Set.mem_of_subset_of_mem h_ss hx
  -- ⊢ p x fun n => f n x
  exact hx'
  -- 🎉 no goals
#align ae_seq.prop_of_mem_ae_seq_set aeSeq.prop_of_mem_aeSeqSet

theorem fun_prop_of_mem_aeSeqSet (hf : ∀ i, AEMeasurable (f i) μ) {x : α} (hx : x ∈ aeSeqSet hf p) :
    p x fun n => f n x := by
  have h_eq : (fun n => f n x) = fun n => aeSeq hf p n x :=
    funext fun n => (aeSeq_eq_fun_of_mem_aeSeqSet hf hx n).symm
  rw [h_eq]
  -- ⊢ p x fun n => aeSeq hf p n x
  exact prop_of_mem_aeSeqSet hf hx
  -- 🎉 no goals
#align ae_seq.fun_prop_of_mem_ae_seq_set aeSeq.fun_prop_of_mem_aeSeqSet

end MemAESeqSet

theorem aeSeqSet_measurableSet {hf : ∀ i, AEMeasurable (f i) μ} : MeasurableSet (aeSeqSet hf p) :=
  (measurableSet_toMeasurable _ _).compl
#align ae_seq.ae_seq_set_measurable_set aeSeq.aeSeqSet_measurableSet

theorem measurable (hf : ∀ i, AEMeasurable (f i) μ) (p : α → (ι → β) → Prop) (i : ι) :
    Measurable (aeSeq hf p i) :=
  Measurable.ite aeSeqSet_measurableSet (hf i).measurable_mk <| measurable_const' fun _ _ => rfl
#align ae_seq.measurable aeSeq.measurable

theorem measure_compl_aeSeqSet_eq_zero [Countable ι] (hf : ∀ i, AEMeasurable (f i) μ)
    (hp : ∀ᵐ x ∂μ, p x fun n => f n x) : μ (aeSeqSet hf p)ᶜ = 0 := by
  rw [aeSeqSet, compl_compl, measure_toMeasurable]
  -- ⊢ ↑↑μ {x | (∀ (i : ι), f i x = AEMeasurable.mk (f i) (_ : AEMeasurable (f i))  …
  have hf_eq := fun i => (hf i).ae_eq_mk
  -- ⊢ ↑↑μ {x | (∀ (i : ι), f i x = AEMeasurable.mk (f i) (_ : AEMeasurable (f i))  …
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at hf_eq
  -- ⊢ ↑↑μ {x | (∀ (i : ι), f i x = AEMeasurable.mk (f i) (_ : AEMeasurable (f i))  …
  exact Filter.Eventually.and hf_eq hp
  -- 🎉 no goals
#align ae_seq.measure_compl_ae_seq_set_eq_zero aeSeq.measure_compl_aeSeqSet_eq_zero

theorem aeSeq_eq_mk_ae [Countable ι] (hf : ∀ i, AEMeasurable (f i) μ)
    (hp : ∀ᵐ x ∂μ, p x fun n => f n x) : ∀ᵐ a : α ∂μ, ∀ i : ι, aeSeq hf p i a = (hf i).mk (f i) a :=
  haveI h_ss : aeSeqSet hf p ⊆ { a : α | ∀ i, aeSeq hf p i a = (hf i).mk (f i) a } := fun x hx i =>
    by simp only [aeSeq, hx, if_true]
       -- 🎉 no goals
  le_antisymm
    (le_trans (measure_mono (Set.compl_subset_compl.mpr h_ss))
      (le_of_eq (measure_compl_aeSeqSet_eq_zero hf hp)))
    (zero_le _)
#align ae_seq.ae_seq_eq_mk_ae aeSeq.aeSeq_eq_mk_ae

theorem aeSeq_eq_fun_ae [Countable ι] (hf : ∀ i, AEMeasurable (f i) μ)
    (hp : ∀ᵐ x ∂μ, p x fun n => f n x) : ∀ᵐ a : α ∂μ, ∀ i : ι, aeSeq hf p i a = f i a :=
  haveI h_ss : { a : α | ¬∀ i : ι, aeSeq hf p i a = f i a } ⊆ (aeSeqSet hf p)ᶜ := fun _ =>
    mt fun hx i => aeSeq_eq_fun_of_mem_aeSeqSet hf hx i
  measure_mono_null h_ss (measure_compl_aeSeqSet_eq_zero hf hp)
#align ae_seq.ae_seq_eq_fun_ae aeSeq.aeSeq_eq_fun_ae

theorem aeSeq_n_eq_fun_n_ae [Countable ι] (hf : ∀ i, AEMeasurable (f i) μ)
    (hp : ∀ᵐ x ∂μ, p x fun n => f n x) (n : ι) : aeSeq hf p n =ᵐ[μ] f n :=
  ae_all_iff.mp (aeSeq_eq_fun_ae hf hp) n
#align ae_seq.ae_seq_n_eq_fun_n_ae aeSeq.aeSeq_n_eq_fun_n_ae

theorem iSup [CompleteLattice β] [Countable ι] (hf : ∀ i, AEMeasurable (f i) μ)
    (hp : ∀ᵐ x ∂μ, p x fun n => f n x) : ⨆ n, aeSeq hf p n =ᵐ[μ] ⨆ n, f n := by
  simp_rw [Filter.EventuallyEq, ae_iff, iSup_apply]
  -- ⊢ ↑↑μ {a | ¬⨆ (i : ι), aeSeq hf p i a = ⨆ (i : ι), f i a} = 0
  have h_ss : aeSeqSet hf p ⊆ { a : α | ⨆ i : ι, aeSeq hf p i a = ⨆ i : ι, f i a } := by
    intro x hx
    congr
    exact funext fun i => aeSeq_eq_fun_of_mem_aeSeqSet hf hx i
  exact measure_mono_null (Set.compl_subset_compl.mpr h_ss) (measure_compl_aeSeqSet_eq_zero hf hp)
  -- 🎉 no goals
#align ae_seq.supr aeSeq.iSup

end aeSeq
