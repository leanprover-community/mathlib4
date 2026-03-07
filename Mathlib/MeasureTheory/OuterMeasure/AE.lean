/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Basic

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
so generic lemmas about `Filter.Eventually`, `Filter.EventuallyEq` etc. apply.
However, we restate some lemmas specifically for `ae`.

## Tags

outer measure, measure, almost everywhere
-/

@[expose] public section

open Filter Set
open scoped ENNReal

namespace MeasureTheory

variable {α β F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] {μ : F} {s t : Set α}

/-- The “almost everywhere” filter of co-null sets. -/
def ae (μ : F) : Filter α :=
  .ofCountableUnion {s | μ s = 0} (fun _S hSc ↦ (measure_sUnion_null_iff hSc).2) fun _t ht _s hs ↦
    measure_mono_null hs ht

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

notation:50 s " =ᵐˢ[" μ:50 "] " t:50 => Filter.EventuallyEqSet (MeasureTheory.ae μ) s t

/-- `f ≤ᵐ[μ] g` means `f` is eventually less than `g` along the a.e. filter,
i.e. `f ≤ g` away from a null set.

This is notation for `Filter.EventuallyLE (MeasureTheory.ae μ) f g`. -/
notation:50 f " ≤ᵐ[" μ:50 "] " g:50 => Filter.EventuallyLE (MeasureTheory.ae μ) f g

notation:50 s " ⊆ᵐ[" μ:50 "] " t:50 => Filter.EventuallySubset (MeasureTheory.ae μ) s t

theorem mem_ae_iff {s : Set α} : s ∈ ae μ ↔ μ sᶜ = 0 :=
  Iff.rfl

theorem ae_iff {p : α → Prop} : (∀ᵐ a ∂μ, p a) ↔ μ { a | ¬p a } = 0 :=
  Iff.rfl

theorem compl_mem_ae_iff {s : Set α} : sᶜ ∈ ae μ ↔ μ s = 0 := by simp only [mem_ae_iff, compl_compl]

theorem frequently_ae_iff {p : α → Prop} : (∃ᵐ a ∂μ, p a) ↔ μ { a | p a } ≠ 0 :=
  not_congr compl_mem_ae_iff

theorem frequently_ae_mem_iff {s : Set α} : (∃ᵐ a ∂μ, a ∈ s) ↔ μ s ≠ 0 :=
  not_congr compl_mem_ae_iff

theorem measure_eq_zero_iff_ae_notMem {s : Set α} : μ s = 0 ↔ ∀ᵐ a ∂μ, a ∉ s :=
  compl_mem_ae_iff.symm

@[deprecated (since := "2025-08-26")]
alias measure_zero_iff_ae_notMem := measure_eq_zero_iff_ae_notMem
theorem ae_of_all {p : α → Prop} (μ : F) : (∀ a, p a) → ∀ᵐ a ∂μ, p a :=
  Eventually.of_forall

instance instCountableInterFilter : CountableInterFilter (ae μ) := by
  unfold ae; infer_instance

theorem ae_all_iff {ι : Sort*} [Countable ι] {p : α → ι → Prop} :
    (∀ᵐ a ∂μ, ∀ i, p a i) ↔ ∀ i, ∀ᵐ a ∂μ, p a i :=
  eventually_countable_forall

theorem all_ae_of {ι : Sort*} {p : α → ι → Prop} (hp : ∀ᵐ a ∂μ, ∀ i, p a i) (i : ι) :
    ∀ᵐ a ∂μ, p a i := by
  filter_upwards [hp] with a ha using ha i

lemma ae_iff_of_countable [Countable α] {p : α → Prop} : (∀ᵐ x ∂μ, p x) ↔ ∀ x, μ {x} ≠ 0 → p x := by
  rw [ae_iff, measure_null_iff_singleton]
  exacts [forall_congr' fun _ ↦ not_imp_comm, Set.to_countable _]

theorem ae_ball_iff {ι : Type*} {S : Set ι} (hS : S.Countable) {p : α → ∀ i ∈ S, Prop} :
    (∀ᵐ x ∂μ, ∀ i (hi : i ∈ S), p x i hi) ↔ ∀ i (hi : i ∈ S), ∀ᵐ x ∂μ, p x i hi :=
  eventually_countable_ball hS

lemma ae_eq_refl (f : α → β) : f =ᵐ[μ] f := EventuallyEq.rfl
lemma ae_eq_rfl {f : α → β} : f =ᵐ[μ] f := EventuallyEq.rfl
lemma ae_eq_comm {f g : α → β} : f =ᵐ[μ] g ↔ g =ᵐ[μ] f := eventuallyEq_comm

theorem ae_eq_symm {f g : α → β} (h : f =ᵐ[μ] g) : g =ᵐ[μ] f :=
  h.symm

theorem ae_eq_trans {f g h : α → β} (h₁ : f =ᵐ[μ] g) (h₂ : g =ᵐ[μ] h) : f =ᵐ[μ] h :=
  h₁.trans h₂

lemma aeEq_iff {f g : α → β} : f =ᵐ[μ] g ↔ μ {x | f x ≠ g x} = 0 := by rfl

lemma _root_.Set.EqOn.aeEq {f g : α → β} (h : s.EqOn f g) (h2 : μ sᶜ = 0) : f =ᵐ[μ] g :=
  eventuallyEq_of_mem h2 h

@[simp] lemma ae_eq_top : ae μ = ⊤ ↔ ∀ a, μ {a} ≠ 0 := by
  simp only [Filter.ext_iff, mem_ae_iff, mem_top, ne_eq]
  refine ⟨fun h a ha ↦ by simpa [ha] using (h {a}ᶜ).1, fun h s ↦ ⟨fun hs ↦ ?_, ?_⟩⟩
  · rw [← compl_empty_iff, ← not_nonempty_iff_eq_empty]
    rintro ⟨a, ha⟩
    exact h _ <| measure_mono_null (singleton_subset_iff.2 ha) hs
  · rintro rfl
    simp

theorem ae_le_of_ae_lt {β : Type*} [Preorder β] {f g : α → β} (h : ∀ᵐ x ∂μ, f x < g x) :
    f ≤ᵐ[μ] g :=
  h.mono fun _ ↦ le_of_lt

@[simp]
theorem ae_eq_empty : s =ᵐˢ[μ] (∅ : Set α) ↔ μ s = 0 :=
  eventuallyEqSet_empty.trans <| by simp only [ae_iff, Classical.not_not, setOf_mem_eq]

-- The priority should be higher than `eventuallyEq_univ`.
@[simp high]
theorem ae_eq_univ : s =ᵐˢ[μ] (univ : Set α) ↔ μ sᶜ = 0 :=
  eventuallyEqSet_univ

theorem ae_le_set : s ⊆ᵐ[μ] t ↔ μ (s \ t) = 0 :=
  calc
    s ⊆ᵐ[μ] t ↔ ∀ᵐ x ∂μ, x ∈ s → x ∈ t := Iff.rfl
    _ ↔ μ (s \ t) = 0 := by simp [ae_iff]; rfl

theorem ae_le_set_inter {s' t' : Set α} (h : s ⊆ᵐ[μ] t) (h' : s' ⊆ᵐ[μ] t') :
    (s ∩ s' : Set α) ⊆ᵐ[μ] (t ∩ t' : Set α) :=
  h.inter h'

theorem ae_le_set_union {s' t' : Set α} (h : s ⊆ᵐ[μ] t) (h' : s' ⊆ᵐ[μ] t') :
    (s ∪ s' : Set α) ⊆ᵐ[μ] (t ∪ t' : Set α) :=
  h.union h'

theorem union_ae_eq_right : (s ∪ t : Set α) =ᵐˢ[μ] t ↔ μ (s \ t) = 0 := by
  simp [eventuallySubset_antisymm_iff, ae_le_set, union_diff_right,
    diff_eq_empty.2 Set.subset_union_right]

theorem diff_ae_eq_self : (s \ t : Set α) =ᵐˢ[μ] s ↔ μ (s ∩ t) = 0 := by
  simp [eventuallySubset_antisymm_iff, ae_le_set]

theorem diff_null_ae_eq_self (ht : μ t = 0) : (s \ t : Set α) =ᵐˢ[μ] s :=
  diff_ae_eq_self.mpr (measure_mono_null inter_subset_right ht)

theorem ae_eq_set {s t : Set α} : s =ᵐˢ[μ] t ↔ μ (s \ t) = 0 ∧ μ (t \ s) = 0 := by
  simp [eventuallySubset_antisymm_iff, ae_le_set]

open scoped symmDiff in
@[simp]
theorem measure_symmDiff_eq_zero_iff {s t : Set α} : μ (s ∆ t) = 0 ↔ s =ᵐˢ[μ] t := by
  simp [ae_eq_set, symmDiff_def]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem ae_eq_set_compl_compl {s t : Set α} : sᶜ =ᵐˢ[μ] tᶜ ↔ s =ᵐˢ[μ] t := by
  simp only [← measure_symmDiff_eq_zero_iff, compl_symmDiff_compl]

theorem ae_eq_set_compl {s t : Set α} : sᶜ =ᵐˢ[μ] t ↔ s =ᵐˢ[μ] tᶜ := by
  rw [← ae_eq_set_compl_compl, compl_compl]

theorem ae_eq_set_inter {s' t' : Set α} (h : s =ᵐˢ[μ] t) (h' : s' =ᵐˢ[μ] t') :
    (s ∩ s' : Set α) =ᵐˢ[μ] (t ∩ t' : Set α) :=
  h.inter h'

theorem ae_eq_set_union {s' t' : Set α} (h : s =ᵐˢ[μ] t) (h' : s' =ᵐˢ[μ] t') :
    (s ∪ s' : Set α) =ᵐˢ[μ] (t ∪ t' : Set α) :=
  h.union h'

theorem ae_eq_set_diff {s' t' : Set α} (h : s =ᵐˢ[μ] t) (h' : s' =ᵐˢ[μ] t') :
    s \ s' =ᵐˢ[μ] t \ t' :=
  h.diff h'

open scoped symmDiff in
theorem ae_eq_set_symmDiff {s' t' : Set α} (h : s =ᵐˢ[μ] t) (h' : s' =ᵐˢ[μ] t') :
    s ∆ s' =ᵐˢ[μ] t ∆ t' :=
  h.symmDiff h'

theorem union_ae_eq_univ_of_ae_eq_univ_left (h : s =ᵐˢ[μ] univ) : (s ∪ t : Set α) =ᵐˢ[μ] univ :=
  (ae_eq_set_union h .rfl).trans <| by rw [univ_union]

theorem union_ae_eq_univ_of_ae_eq_univ_right (h : t =ᵐˢ[μ] univ) : (s ∪ t : Set α) =ᵐˢ[μ] univ := by
  rw [union_comm]
  exact union_ae_eq_univ_of_ae_eq_univ_left h

theorem union_ae_eq_right_of_ae_eq_empty (h : s =ᵐˢ[μ] (∅ : Set α)) : (s ∪ t : Set α) =ᵐˢ[μ] t := by
  convert ae_eq_set_union h .rfl
  rw [empty_union]

theorem union_ae_eq_left_of_ae_eq_empty (h : t =ᵐˢ[μ] (∅ : Set α)) : (s ∪ t : Set α) =ᵐˢ[μ] s := by
  convert ae_eq_set_union .rfl h
  rw [union_empty]

theorem inter_ae_eq_right_of_ae_eq_univ (h : s =ᵐˢ[μ] univ) : (s ∩ t : Set α) =ᵐˢ[μ] t := by
  convert ae_eq_set_inter h .rfl
  rw [univ_inter]

theorem inter_ae_eq_left_of_ae_eq_univ (h : t =ᵐˢ[μ] univ) : (s ∩ t : Set α) =ᵐˢ[μ] s := by
  convert ae_eq_set_inter .rfl h
  rw [inter_univ]

theorem inter_ae_eq_empty_of_ae_eq_empty_left (h : s =ᵐˢ[μ] (∅ : Set α)) :
    (s ∩ t : Set α) =ᵐˢ[μ] (∅ : Set α) := by
  convert ae_eq_set_inter h .rfl
  rw [empty_inter]

theorem inter_ae_eq_empty_of_ae_eq_empty_right (h : t =ᵐˢ[μ] (∅ : Set α)) :
    (s ∩ t : Set α) =ᵐˢ[μ] (∅ : Set α) := by
  convert ae_eq_set_inter .rfl h
  rw [inter_empty]

theorem ae_eq_set_biInter {s : Set β} (hs : s.Countable) {t t' : β → Set α}
    (h : ∀ b ∈ s, t b =ᵐ[μ] t' b) :
    (⋂ b ∈ s, t b : Set α) =ᵐ[μ] (⋂ b ∈ s, t' b : Set α) :=
  .countable_bInter hs h

theorem ae_eq_set_biUnion {s : Set β} (hs : s.Countable) {t t' : β → Set α}
    (h : ∀ b ∈ s, t b =ᵐ[μ] t' b) :
    (⋃ b ∈ s, t b : Set α) =ᵐ[μ] (⋃ b ∈ s, t' b : Set α) :=
  .countable_bUnion hs h

@[to_additive]
theorem _root_.Set.mulIndicator_ae_eq_one {M : Type*} [One M] {f : α → M} {s : Set α} :
    s.mulIndicator f =ᵐ[μ] 1 ↔ μ (s ∩ f.mulSupport) = 0 := by
  simp [EventuallyEq, eventually_iff, ae, compl_setOf]; rfl

/-- If `s ⊆ t` modulo a set of measure `0`, then `μ s ≤ μ t`. -/
@[mono]
theorem measure_mono_ae (H : s ⊆ᵐ[μ] t) : μ s ≤ μ t :=
  calc
    μ s ≤ μ (s ∪ t) := measure_mono subset_union_left
    _ = μ (t ∪ s \ t) := by rw [union_diff_self, Set.union_comm]
    _ ≤ μ t + μ (s \ t) := measure_union_le _ _
    _ = μ t := by rw [ae_le_set.1 H, add_zero]

alias _root_.Filter.EventuallySubset.measure_le := measure_mono_ae

/-- If two sets are equal modulo a set of measure zero, then `μ s = μ t`. -/
theorem measure_congr (H : s =ᵐˢ[μ] t) : μ s = μ t :=
  le_antisymm H.subset.measure_le H.superset.measure_le

alias _root_.Filter.EventuallyEqSet.measure_eq := measure_congr

theorem measure_mono_null_ae (H : s ⊆ᵐ[μ] t) (ht : μ t = 0) : μ s = 0 :=
  nonpos_iff_eq_zero.1 <| ht ▸ H.measure_le

end MeasureTheory
