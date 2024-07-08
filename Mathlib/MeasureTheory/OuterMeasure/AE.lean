/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov
-/
import Mathlib.MeasureTheory.OuterMeasure.Basic

/-!
# The “almost everywhere” filter of co-null sets.

If `μ` is an outer measure or a measure on `α`,
then `MeasureTheory.ae μ` is the filter of co-null sets: `s ∈ ae μ ↔ μ sᶜ = 0`.

In this file we define the filter and prove some basic theorems about it.

## Notation

- `∀ᵐ x ∂μ, p x`: the predicate `p` holds for `μ`-a.e. all `x`;
- `∃ᶠ x ∂μ, p x`: the predicate `p` holds on a set of nonzero measure;
- `f =ᵐ[μ] g`: `f x = g x` for `μ`-a.e. all `x`;
- `f ≤ᵐ[μ] g`: `f x ≤ g x` for `μ`-a.e. all `x`.

## Implementation details

All notation introduced in this file
reducibly unfolds to the corresponding definitions about filters,
so generic lemmas about `Filter.Eventually`, `Filter.EventuallyEq` etc apply.
However, we restate some lemmas specifically for `ae`.

## Tags

outer measure, measure, almost everywhere
-/

open Filter Set
open scoped ENNReal

namespace MeasureTheory

variable {α β F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] {μ : F} {s t : Set α}

/-- The “almost everywhere” filter of co-null sets. -/
def ae (μ : F) : Filter α :=
  .ofCountableUnion (μ · = 0) (fun _S hSc ↦ (measure_sUnion_null_iff hSc).2) fun _t ht _s hs ↦
    measure_mono_null hs ht
#align measure_theory.measure.ae MeasureTheory.ae

/-- `∀ᵐ a ∂μ, p a` means that `p a` for a.e. `a`, i.e. `p` holds true away from a null set.

This is notation for `Filter.Eventually p (MeasureTheory.ae μ)`. -/
notation3 "∀ᵐ "(...)" ∂"μ", "r:(scoped p => Filter.Eventually p <| MeasureTheory.ae μ) => r

/-- `∃ᵐ a ∂μ, p a` means that `p` holds `∂μ`-frequently,
i.e. `p` holds on a set of positive measure.

This is notation for `Filter.Frequently p (MeasureTheory.ae μ)`. -/
notation3 "∃ᵐ "(...)" ∂"μ", "r:(scoped P => Filter.Frequently P <| MeasureTheory.ae μ) => r

/-- `f =ᵐ[μ] g` means `f` and `g` are eventually equal along the a.e. filter,
i.e. `f=g` away from a null set.

This is notation for `Filter.EventuallyEq (MeasureTheory.ae μ) f g`. -/
notation:50 f " =ᵐ[" μ:50 "] " g:50 => Filter.EventuallyEq (MeasureTheory.ae μ) f g

/-- `f ≤ᵐ[μ] g` means `f` is eventually less than `g` along the a.e. filter,
i.e. `f ≤ g` away from a null set.

This is notation for `Filter.EventuallyLE (MeasureTheory.ae μ) f g`. -/
notation:50 f " ≤ᵐ[" μ:50 "] " g:50 => Filter.EventuallyLE (MeasureTheory.ae μ) f g

theorem mem_ae_iff {s : Set α} : s ∈ ae μ ↔ μ sᶜ = 0 :=
  Iff.rfl
#align measure_theory.mem_ae_iff MeasureTheory.mem_ae_iff

theorem ae_iff {p : α → Prop} : (∀ᵐ a ∂μ, p a) ↔ μ { a | ¬p a } = 0 :=
  Iff.rfl
#align measure_theory.ae_iff MeasureTheory.ae_iff

theorem compl_mem_ae_iff {s : Set α} : sᶜ ∈ ae μ ↔ μ s = 0 := by simp only [mem_ae_iff, compl_compl]
#align measure_theory.compl_mem_ae_iff MeasureTheory.compl_mem_ae_iff

theorem frequently_ae_iff {p : α → Prop} : (∃ᵐ a ∂μ, p a) ↔ μ { a | p a } ≠ 0 :=
  not_congr compl_mem_ae_iff
#align measure_theory.frequently_ae_iff MeasureTheory.frequently_ae_iff

theorem frequently_ae_mem_iff {s : Set α} : (∃ᵐ a ∂μ, a ∈ s) ↔ μ s ≠ 0 :=
  not_congr compl_mem_ae_iff
#align measure_theory.frequently_ae_mem_iff MeasureTheory.frequently_ae_mem_iff

theorem measure_zero_iff_ae_nmem {s : Set α} : μ s = 0 ↔ ∀ᵐ a ∂μ, a ∉ s :=
  compl_mem_ae_iff.symm
#align measure_theory.measure_zero_iff_ae_nmem MeasureTheory.measure_zero_iff_ae_nmem

theorem ae_of_all {p : α → Prop} (μ : F) : (∀ a, p a) → ∀ᵐ a ∂μ, p a :=
  eventually_of_forall
#align measure_theory.ae_of_all MeasureTheory.ae_of_all

instance instCountableInterFilter : CountableInterFilter (ae μ) := by
  unfold ae; infer_instance
#align measure_theory.measure.ae.countable_Inter_filter MeasureTheory.instCountableInterFilter

theorem ae_all_iff {ι : Sort*} [Countable ι] {p : α → ι → Prop} :
    (∀ᵐ a ∂μ, ∀ i, p a i) ↔ ∀ i, ∀ᵐ a ∂μ, p a i :=
  eventually_countable_forall
#align measure_theory.ae_all_iff MeasureTheory.ae_all_iff

theorem all_ae_of {ι : Sort*} {p : α → ι → Prop} (hp : ∀ᵐ a ∂μ, ∀ i, p a i) (i : ι) :
    ∀ᵐ a ∂μ, p a i := by
  filter_upwards [hp] with a ha using ha i

lemma ae_iff_of_countable [Countable α] {p : α → Prop} : (∀ᵐ x ∂μ, p x) ↔ ∀ x, μ {x} ≠ 0 → p x := by
  rw [ae_iff, measure_null_iff_singleton]
  exacts [forall_congr' fun _ ↦ not_imp_comm, Set.to_countable _]

theorem ae_ball_iff {ι : Type*} {S : Set ι} (hS : S.Countable) {p : α → ∀ i ∈ S, Prop} :
    (∀ᵐ x ∂μ, ∀ i (hi : i ∈ S), p x i hi) ↔ ∀ i (hi : i ∈ S), ∀ᵐ x ∂μ, p x i hi :=
  eventually_countable_ball hS
#align measure_theory.ae_ball_iff MeasureTheory.ae_ball_iff

theorem ae_eq_refl (f : α → β) : f =ᵐ[μ] f :=
  EventuallyEq.rfl
#align measure_theory.ae_eq_refl MeasureTheory.ae_eq_refl

theorem ae_eq_symm {f g : α → β} (h : f =ᵐ[μ] g) : g =ᵐ[μ] f :=
  h.symm
#align measure_theory.ae_eq_symm MeasureTheory.ae_eq_symm

theorem ae_eq_trans {f g h : α → β} (h₁ : f =ᵐ[μ] g) (h₂ : g =ᵐ[μ] h) : f =ᵐ[μ] h :=
  h₁.trans h₂
#align measure_theory.ae_eq_trans MeasureTheory.ae_eq_trans

theorem ae_le_of_ae_lt {β : Type*} [Preorder β] {f g : α → β} (h : ∀ᵐ x ∂μ, f x < g x) :
    f ≤ᵐ[μ] g :=
  h.mono fun _ ↦ le_of_lt
#align measure_theory.ae_le_of_ae_lt MeasureTheory.ae_le_of_ae_lt

@[simp]
theorem ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0 :=
  eventuallyEq_empty.trans <| by simp only [ae_iff, Classical.not_not, setOf_mem_eq]
#align measure_theory.ae_eq_empty MeasureTheory.ae_eq_empty

-- Porting note: The priority should be higher than `eventuallyEq_univ`.
@[simp high]
theorem ae_eq_univ : s =ᵐ[μ] (univ : Set α) ↔ μ sᶜ = 0 :=
  eventuallyEq_univ
#align measure_theory.ae_eq_univ MeasureTheory.ae_eq_univ

theorem ae_le_set : s ≤ᵐ[μ] t ↔ μ (s \ t) = 0 :=
  calc
    s ≤ᵐ[μ] t ↔ ∀ᵐ x ∂μ, x ∈ s → x ∈ t := Iff.rfl
    _ ↔ μ (s \ t) = 0 := by simp [ae_iff]; rfl
#align measure_theory.ae_le_set MeasureTheory.ae_le_set

theorem ae_le_set_inter {s' t' : Set α} (h : s ≤ᵐ[μ] t) (h' : s' ≤ᵐ[μ] t') :
    (s ∩ s' : Set α) ≤ᵐ[μ] (t ∩ t' : Set α) :=
  h.inter h'
#align measure_theory.ae_le_set_inter MeasureTheory.ae_le_set_inter

theorem ae_le_set_union {s' t' : Set α} (h : s ≤ᵐ[μ] t) (h' : s' ≤ᵐ[μ] t') :
    (s ∪ s' : Set α) ≤ᵐ[μ] (t ∪ t' : Set α) :=
  h.union h'
#align measure_theory.ae_le_set_union MeasureTheory.ae_le_set_union

theorem union_ae_eq_right : (s ∪ t : Set α) =ᵐ[μ] t ↔ μ (s \ t) = 0 := by
  simp [eventuallyLE_antisymm_iff, ae_le_set, union_diff_right,
    diff_eq_empty.2 Set.subset_union_right]
#align measure_theory.union_ae_eq_right MeasureTheory.union_ae_eq_right

theorem diff_ae_eq_self : (s \ t : Set α) =ᵐ[μ] s ↔ μ (s ∩ t) = 0 := by
  simp [eventuallyLE_antisymm_iff, ae_le_set, diff_diff_right, diff_diff,
    diff_eq_empty.2 Set.subset_union_right]
#align measure_theory.diff_ae_eq_self MeasureTheory.diff_ae_eq_self

theorem diff_null_ae_eq_self (ht : μ t = 0) : (s \ t : Set α) =ᵐ[μ] s :=
  diff_ae_eq_self.mpr (measure_mono_null inter_subset_right ht)
#align measure_theory.diff_null_ae_eq_self MeasureTheory.diff_null_ae_eq_self

theorem ae_eq_set {s t : Set α} : s =ᵐ[μ] t ↔ μ (s \ t) = 0 ∧ μ (t \ s) = 0 := by
  simp [eventuallyLE_antisymm_iff, ae_le_set]
#align measure_theory.ae_eq_set MeasureTheory.ae_eq_set

open scoped symmDiff in
@[simp]
theorem measure_symmDiff_eq_zero_iff {s t : Set α} : μ (s ∆ t) = 0 ↔ s =ᵐ[μ] t := by
  simp [ae_eq_set, symmDiff_def]
#align measure_theory.measure_symm_diff_eq_zero_iff MeasureTheory.measure_symmDiff_eq_zero_iff

@[simp]
theorem ae_eq_set_compl_compl {s t : Set α} : sᶜ =ᵐ[μ] tᶜ ↔ s =ᵐ[μ] t := by
  simp only [← measure_symmDiff_eq_zero_iff, compl_symmDiff_compl]
#align measure_theory.ae_eq_set_compl_compl MeasureTheory.ae_eq_set_compl_compl

theorem ae_eq_set_compl {s t : Set α} : sᶜ =ᵐ[μ] t ↔ s =ᵐ[μ] tᶜ := by
  rw [← ae_eq_set_compl_compl, compl_compl]
#align measure_theory.ae_eq_set_compl MeasureTheory.ae_eq_set_compl

theorem ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') :
    (s ∩ s' : Set α) =ᵐ[μ] (t ∩ t' : Set α) :=
  h.inter h'
#align measure_theory.ae_eq_set_inter MeasureTheory.ae_eq_set_inter

theorem ae_eq_set_union {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') :
    (s ∪ s' : Set α) =ᵐ[μ] (t ∪ t' : Set α) :=
  h.union h'
#align measure_theory.ae_eq_set_union MeasureTheory.ae_eq_set_union

theorem union_ae_eq_univ_of_ae_eq_univ_left (h : s =ᵐ[μ] univ) : (s ∪ t : Set α) =ᵐ[μ] univ :=
  (ae_eq_set_union h (ae_eq_refl t)).trans <| by rw [univ_union]
#align measure_theory.union_ae_eq_univ_of_ae_eq_univ_left MeasureTheory.union_ae_eq_univ_of_ae_eq_univ_left

theorem union_ae_eq_univ_of_ae_eq_univ_right (h : t =ᵐ[μ] univ) : (s ∪ t : Set α) =ᵐ[μ] univ := by
  convert ae_eq_set_union (ae_eq_refl s) h
  rw [union_univ]
#align measure_theory.union_ae_eq_univ_of_ae_eq_univ_right MeasureTheory.union_ae_eq_univ_of_ae_eq_univ_right

theorem union_ae_eq_right_of_ae_eq_empty (h : s =ᵐ[μ] (∅ : Set α)) : (s ∪ t : Set α) =ᵐ[μ] t := by
  convert ae_eq_set_union h (ae_eq_refl t)
  rw [empty_union]
#align measure_theory.union_ae_eq_right_of_ae_eq_empty MeasureTheory.union_ae_eq_right_of_ae_eq_empty

theorem union_ae_eq_left_of_ae_eq_empty (h : t =ᵐ[μ] (∅ : Set α)) : (s ∪ t : Set α) =ᵐ[μ] s := by
  convert ae_eq_set_union (ae_eq_refl s) h
  rw [union_empty]
#align measure_theory.union_ae_eq_left_of_ae_eq_empty MeasureTheory.union_ae_eq_left_of_ae_eq_empty

theorem inter_ae_eq_right_of_ae_eq_univ (h : s =ᵐ[μ] univ) : (s ∩ t : Set α) =ᵐ[μ] t := by
  convert ae_eq_set_inter h (ae_eq_refl t)
  rw [univ_inter]
#align measure_theory.inter_ae_eq_right_of_ae_eq_univ MeasureTheory.inter_ae_eq_right_of_ae_eq_univ

theorem inter_ae_eq_left_of_ae_eq_univ (h : t =ᵐ[μ] univ) : (s ∩ t : Set α) =ᵐ[μ] s := by
  convert ae_eq_set_inter (ae_eq_refl s) h
  rw [inter_univ]
#align measure_theory.inter_ae_eq_left_of_ae_eq_univ MeasureTheory.inter_ae_eq_left_of_ae_eq_univ

theorem inter_ae_eq_empty_of_ae_eq_empty_left (h : s =ᵐ[μ] (∅ : Set α)) :
    (s ∩ t : Set α) =ᵐ[μ] (∅ : Set α) := by
  convert ae_eq_set_inter h (ae_eq_refl t)
  rw [empty_inter]
#align measure_theory.inter_ae_eq_empty_of_ae_eq_empty_left MeasureTheory.inter_ae_eq_empty_of_ae_eq_empty_left

theorem inter_ae_eq_empty_of_ae_eq_empty_right (h : t =ᵐ[μ] (∅ : Set α)) :
    (s ∩ t : Set α) =ᵐ[μ] (∅ : Set α) := by
  convert ae_eq_set_inter (ae_eq_refl s) h
  rw [inter_empty]
#align measure_theory.inter_ae_eq_empty_of_ae_eq_empty_right MeasureTheory.inter_ae_eq_empty_of_ae_eq_empty_right

@[to_additive]
theorem _root_.Set.mulIndicator_ae_eq_one {M : Type*} [One M] {f : α → M} {s : Set α} :
    s.mulIndicator f =ᵐ[μ] 1 ↔ μ (s ∩ f.mulSupport) = 0 := by
  simp [EventuallyEq, eventually_iff, ae, compl_setOf]; rfl
#align set.mul_indicator_ae_eq_one Set.mulIndicator_ae_eq_one
#align set.indicator_ae_eq_zero Set.indicator_ae_eq_zero

/-- If `s ⊆ t` modulo a set of measure `0`, then `μ s ≤ μ t`. -/
@[mono]
theorem measure_mono_ae (H : s ≤ᵐ[μ] t) : μ s ≤ μ t :=
  calc
    μ s ≤ μ (s ∪ t) := measure_mono subset_union_left
    _ = μ (t ∪ s \ t) := by rw [union_diff_self, Set.union_comm]
    _ ≤ μ t + μ (s \ t) := measure_union_le _ _
    _ = μ t := by rw [ae_le_set.1 H, add_zero]
#align measure_theory.measure_mono_ae MeasureTheory.measure_mono_ae

alias _root_.Filter.EventuallyLE.measure_le := measure_mono_ae
#align filter.eventually_le.measure_le Filter.EventuallyLE.measure_le

/-- If two sets are equal modulo a set of measure zero, then `μ s = μ t`. -/
theorem measure_congr (H : s =ᵐ[μ] t) : μ s = μ t :=
  le_antisymm H.le.measure_le H.symm.le.measure_le
#align measure_theory.measure_congr MeasureTheory.measure_congr

alias _root_.Filter.EventuallyEq.measure_eq := measure_congr
#align filter.eventually_eq.measure_eq Filter.EventuallyEq.measure_eq

theorem measure_mono_null_ae (H : s ≤ᵐ[μ] t) (ht : μ t = 0) : μ s = 0 :=
  nonpos_iff_eq_zero.1 <| ht ▸ H.measure_le
#align measure_theory.measure_mono_null_ae MeasureTheory.measure_mono_null_ae
