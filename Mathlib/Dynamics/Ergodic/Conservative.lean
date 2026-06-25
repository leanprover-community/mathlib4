/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Damien Thomine
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Combinatorics.Pigeonhole

/-!
# Measure-theoretic recurrence and conservative systems
In this file, we implement notions of measure-theoretic recurrence of sets as weel as conservative
dynamical systems.

## Main definitions
- `IsRecurrent`: given a map `f : α → α` and a measure `μ`, a set `s` is said to be *recurrent* if
  `μ`-almost every point in `s` returns to `s` after some number of iterations of `f`.
- `Conservative`: a map `f : α → α` is said to be a *conservative* system with respect to a measure
  `μ` if `f` is non-singular (`QuasiMeasurePreserving`) and all measurable sets are recurrent.

## Main results
There are several properties that look like they are stronger than recurrence but actually
follow from it for non-singular maps:
- `IsRecurrent.frequently_measure_inter_ne_zero`: if a subset `t ⊆ s` has positive measure, then
  for infinitely many `n`, the measure of `t ∩ f^[n] ⁻¹' s` is positive.
- `IsRecurrent.ae_mem_imp_frequently_image_mem`: `μ`-almost every every point of `s` visits `s`
  infinitely many times.
- `isRecurrent_iff_ae_sub_limsup_preimage`: `μ`-almost everywhere, if a point visits `s`, then it
  visits `s` infinitely many times.

Another definition of conservative systems is that any measurable set `s` of positive measure
contains a point which returns to `s` after some number of iterations of `f`. The equivalence
between these definitions is proven in lemma `conservative_iff_exists_mem_iterate_mem`.

We also prove:
- `MeasurePreserving.conservative`: a map preserving a finite measure is conservative.
- `Conservative.iterate`: iterates of conservative maps are conservative.
- `Conservative.ae_frequently_mem_of_mem_nhds`: the topological Poincaré recurrence theorem. Let
  `f : α → α` be a conservative dynamical system on a topological space with second countable
  topology and measurable open sets. Then almost every point `x : α` is topologically recurrent: it
  visits every neighborhood `s ∈ 𝓝 x` infinitely many times.

## Tags
recurrent set, conservative dynamical system, Poincare recurrence theorem
-/

public section

noncomputable section

namespace MeasureTheory

open Filter Function Measure Set

variable {α : Type*} [MeasurableSpace α] {f : α → α} {μ : Measure α} {s : Set α}

/-! ### Recurrent sets -/

/-- A set `s` is recurrent for a transformation `f` and a measure `μ` if almost every point in `s`
returns to `s` under some iteration of `f`. -/
def IsRecurrent (f : α → α) (μ : Measure α) (s : Set α) :=
    s ≤ᵐ[μ] ⋃ n ≠ 0, f^[n] ⁻¹' s

lemma isRecurrent_def :
    IsRecurrent f μ s ↔ ∀ᵐ (x : α) ∂μ, x ∈ s → ∃ n ≠ 0, f^[n] x ∈ s := by
  change (∀ᵐ x ∂μ, x ∈ s → x ∈ ⋃ n ≠ 0, f^[n] ⁻¹' s) ↔ ∀ᵐ (x : α) ∂μ, x ∈ s → ∃ n ≠ 0, f^[n] x ∈ s
  apply eventually_congr <| Eventually.of_forall fun x ↦ imp_congr_right fun hx ↦ ?_
  simp

lemma isRecurrent_iff_ae_iUnion :
    IsRecurrent f μ s ↔ (sᶜ ∪ ⋃ n ≠ 0, f^[n] ⁻¹' s : Set α) =ᵐ[μ] univ := by
  rw [isRecurrent_def, ae_iff, ae_eq_univ]
  apply Eq.congr _ (Eq.refl 0)
  congr 2
  simp

lemma isRecurrent_iff_restrict (f : α → α) (hs : NullMeasurableSet s μ) :
    IsRecurrent f μ s ↔ ∀ᵐ (x : α) ∂μ.restrict s, ∃ n ≠ 0, f^[n] x ∈ s := by
  rw [isRecurrent_def, ae_restrict_iff'₀ hs]

lemma IsRecurrent.congr_ae {ν : Measure α} (hs : IsRecurrent f μ s) (h : ae μ = ae ν) :
    IsRecurrent f ν s := by
  rwa [IsRecurrent, ← h]

theorem IsRecurrent.of_absolutelyContinuous {ν : Measure α} (hν : ν ≪ μ) (hs : IsRecurrent f μ s) :
    IsRecurrent f ν s :=
  hs.filter_mono hν.ae_le

lemma isRecurrent_of_null (hs : μ s = 0) : IsRecurrent f μ s :=
  (measure_eq_zero_iff_ae_notMem.1 hs).mono fun x _ _ ↦ by contradiction

lemma isRecurrent_of_mapsTo (hs : MapsTo f s s) : IsRecurrent f μ s :=
  isRecurrent_def.2 (Eventually.of_forall fun _ x_s ↦ ⟨1, one_ne_zero, hs x_s⟩)

lemma isRecurrent_univ : IsRecurrent f μ univ :=
  isRecurrent_of_mapsTo (mapsTo_univ f univ)

lemma isRecurrent_iUnion {ι : Type*} [Countable ι] {s : ι → Set α}
    (hs : ∀ i, IsRecurrent f μ (s i)) :
    IsRecurrent f μ (⋃ i, s i) := by
  simp only [isRecurrent_def] at hs ⊢
  apply (eventually_countable_forall.2 hs).mono
  intro x x_rec x_s
  obtain ⟨i, x_i⟩ := mem_iUnion.1 x_s
  obtain ⟨n, n_0, x_n⟩ := x_rec i x_i
  exact ⟨n, n_0, mem_iUnion.2 ⟨i, x_n⟩⟩

lemma IsRecurrent.exists_mem_iterate_mem (hs : μ s ≠ 0) (hf : IsRecurrent f μ s) :
    ∃ x ∈ s, ∃ m ≠ 0, f^[m] x ∈ s := by
  rw [← frequently_ae_mem_iff] at hs
  obtain ⟨x, x_s, hx⟩ := (hs.and_eventually (isRecurrent_def.1 hf)).exists
  exact ⟨x, x_s, hx x_s⟩

lemma isRecurrent_congr_set {t : Set α} (hf : QuasiMeasurePreserving f μ μ) (h : s =ᵐ[μ] t) :
    IsRecurrent f μ s ↔ IsRecurrent f μ t := by
  suffices h' : (⋃ n ≠ 0, f^[n] ⁻¹' s : Set α) =ᵐ[μ] (⋃ n ≠ 0, f^[n] ⁻¹' t : Set α) by
    exact eventuallyLE_congr h h'
  apply Filter.EventuallyEq.countable_iUnion fun n ↦ ?_
  exact Filter.EventuallyEq.countable_iUnion fun _ ↦ (hf.iterate n).preimage_ae_eq h

lemma isRecurrent_of_ae (hf : QuasiMeasurePreserving f μ μ) (hs : s ∈ ae μ) :
    IsRecurrent f μ s := by
  rw [mem_ae_iff, ← ae_eq_univ] at hs
  rw [isRecurrent_congr_set hf hs]
  exact isRecurrent_univ

lemma IsRecurrent.preimage (n : ℕ) (hf : QuasiMeasurePreserving f μ μ) (hs : IsRecurrent f μ s) :
    IsRecurrent f μ (f^[n] ⁻¹' s) := by
  apply ((hf.iterate n).preimage_mono_ae hs).congr ae_eq_rfl (Eq.eventuallyEq _)
  rw [preimage_iUnion₂]
  apply iUnion₂_congr fun m _ ↦ ?_
  rw [← preimage_comp, ← iterate_add, add_comm, iterate_add, preimage_comp]

lemma isRecurrent_iff_isReccurent_iUnion_preimage (s : Set α) (hf : QuasiMeasurePreserving f μ μ) :
    IsRecurrent f μ s ↔ IsRecurrent f μ (⋃ n, f^[n] ⁻¹' s) := by
  constructor <;> intro hs
  · exact isRecurrent_iUnion fun n ↦ hs.preimage n hf
  rw [isRecurrent_def] at hs ⊢
  refine hs.mono fun x hx x_s ↦ ?_
  simp only [mem_iUnion, Set.mem_preimage, forall_exists_index] at hx
  specialize hx 0
  simp only [iterate_zero, id_eq, x_s, forall_const, ← iterate_add_apply] at hx
  obtain ⟨n, n_0, m, x_m⟩ := hx
  exact ⟨m + n, add_ne_zero.2 (Or.inr n_0), x_m⟩

lemma isRecurrent_of_ae_iUnion_preimage (hf : QuasiMeasurePreserving f μ μ)
    (hs : ⋃ n, f^[n] ⁻¹' s ∈ ae μ) :
    IsRecurrent f μ s :=
  (isRecurrent_iff_isReccurent_iUnion_preimage s hf).2 (isRecurrent_of_ae hf hs)

lemma IsRecurrent.frequently_measure_inter_ne_zero {t : Set α}
    (hf : QuasiMeasurePreserving f μ μ) (hs : IsRecurrent f μ s) (ht : t ⊆ s) (h₀ : μ t ≠ 0) :
    ∃ᶠ n in atTop, μ (t ∩ f^[n] ⁻¹' s) ≠ 0 := by
  rw [Nat.frequently_atTop_iff_infinite]
  have t_nemp : { n | μ (t ∩ f^[n] ⁻¹' s) ≠ 0 }.Nonempty := ⟨0, by simp [inter_eq_left.2 ht, h₀]⟩
  refine (infinite_iff_exists_gt_mem t_nemp).2 fun n hn ↦ ?_
  let r := t ∩ f^[n] ⁻¹' s ∩ f^[n] ⁻¹' (sᶜ ∪ ⋃ m ≠ 0, f^[m] ⁻¹' s)
  have r_μ : μ r ≠ 0 := by
    suffices h : r =ᵐ[μ] (t ∩ f^[n] ⁻¹' s : Set α) by rwa [measure_congr h]
    apply inter_ae_eq_left_of_ae_eq_univ
    rw [← preimage_univ (f := f^[n])]
    apply (hf.iterate n).preimage_ae_eq (isRecurrent_iff_ae_iUnion.1 hs)
  have r_sub : r ⊆ ⋃ m ≠ 0, t ∩ f^[n+m] ⁻¹' s := by
    intro x
    simp only [mem_inter_iff, Set.mem_preimage, Set.mem_union, mem_iUnion, ← iterate_add_apply, r]
    grind
  obtain ⟨m, hm⟩ := exists_measure_pos_of_not_measure_iUnion_null
    (pos_mono r_sub (pos_of_ne_zero r_μ)).ne.symm
  obtain ⟨m_0, hm⟩ := exists_measure_pos_of_not_measure_iUnion_null hm.ne.symm
  exact ⟨n + m, hm.ne.symm, lt_add_of_pos_right n (pos_of_ne_zero m_0)⟩

lemma IsRecurrent.ae_mem_imp_frequently_image_mem (hf : QuasiMeasurePreserving f μ μ)
    (hs : IsRecurrent f μ s) :
    ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s := by
  simp only [ae_iff, Classical.not_imp, not_frequently, eventually_atTop]
  let t := ⋃ n, s ∩ ⋂ m ≥ n, f^[m] ⁻¹' sᶜ
  suffices h : μ t = 0 by rw [← h]; congr 1; ext x; simp [t]
  refine measure_iUnion_null_iff.2 fun n ↦ ?_
  apply not_imp_not.1 <| hs.frequently_measure_inter_ne_zero hf (t := s ∩ ⋂ m ≥ n, f^[m] ⁻¹' sᶜ)
    inter_subset_left
  simp only [Set.preimage_compl, not_ne_iff, eventually_atTop]
  refine ⟨n, fun m n_m ↦ ae_eq_empty.1 <| Eq.eventuallyEq ?_⟩
  suffices h : ((⋂ k ≥ n, (f^[k] ⁻¹' s)ᶜ) ∩ f^[m] ⁻¹' s : Set α) = ∅ by simp [inter_assoc, h]
  rw [iInter_inter]
  apply iInter_eq_empty_of_eq_empty (i := m)
  simp [n_m]

lemma preimage_limsup_preimage {α : Type*} {s : Set α} {f : α → α} {n : ℕ} :
    f^[n] ⁻¹' limsup (fun k ↦ f^[k] ⁻¹' s) atTop = limsup (fun k ↦ f^[k] ⁻¹' s) atTop := by
  ext x
  simp only [limsup_eq_iInf_iSup_of_nat, iSup_eq_iUnion, iInf_eq_iInter, mem_preimage, mem_iInter,
    mem_iUnion, exists_prop]
  constructor <;> intro h m
  · obtain ⟨k, k_m, f_k⟩ := h m
    refine ⟨n + k, by linarith, ?_⟩
    rwa [add_comm, Function.iterate_add_apply]
  · obtain ⟨k, k_m, f_k⟩ := h (m + n)
    refine ⟨k - n, Nat.le_sub_of_add_le k_m, ?_⟩
    rwa [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_add_left_le k_m)]

lemma isRecurrent_iff_ae_sub_limsup_preimage (s : Set α) (hf : QuasiMeasurePreserving f μ μ) :
    IsRecurrent f μ s ↔ ⋃ n, f^[n] ⁻¹' s =ᵐ[μ] (limsup (fun n ↦ f^[n] ⁻¹' s) atTop : Set α) := by
  have hl : (limsup (fun n ↦ f^[n] ⁻¹' s) atTop : Set α) ≤ᵐ[μ] ⋃ n ≠ 0, f^[n] ⁻¹' s := by
    refine (eventuallyLE_of_subset fun x hx ↦ ?_)
    simp only [limsup_eq_iInf_iSup_of_nat, iSup_eq_iUnion, iInf_eq_iInter, mem_iInter,
      mem_iUnion, Set.mem_preimage, exists_prop] at hx ⊢
    obtain ⟨n, n_0, x_n⟩ := hx 1
    exact ⟨n, Nat.one_le_iff_ne_zero.1 n_0, x_n⟩
  constructor <;> intro h
  · apply EventuallyLE.antisymm
    · refine EventuallyLE.countable_iUnion' fun n ↦ ?_
      rw [← preimage_limsup_preimage (n := n)]
      apply (hf.iterate n).preimage_mono_ae
      apply (h.ae_mem_imp_frequently_image_mem hf).mono fun x hx ↦ ?_
      simp only [limsup_eq_iInf_iSup_of_nat, iSup_eq_iUnion, iInf_eq_iInter]
      refine fun x_s ↦ mem_iInter.2 fun n ↦ mem_iUnion₂.2 ?_
      simp [frequently_atTop.1 (hx x_s) n]
    · exact hl.trans (eventuallyLE_of_subset (iUnion₂_subset_iUnion _ _))
  · apply EventuallyLE.trans _ (h.trans_le hl)
    exact eventuallyLE_of_subset (subset_iUnion_of_subset 0 (by simp))

lemma MeasurePreserving.isRecurrent [IsFiniteMeasure μ] (hf : MeasurePreserving f μ μ)
    (hs : NullMeasurableSet s μ) :
    IsRecurrent f μ s :=
  isRecurrent_def.2 (hf.ae_mem_exists_iterate_mem hs)

lemma isRecurrent_id :
    IsRecurrent id μ s :=
  Eventually.of_forall fun x x_s ↦ mem_iUnion₂.2 ⟨1, one_ne_zero, by simpa⟩

/-! ### Conservative systems -/

/-- We say that a non-singular (`MeasureTheory.QuasiMeasurePreserving`) self-map is
*conservative* if any measurable set `s` is recurrent, i.e. almost every point `x` returns to `s`
under some iteration of `f`. -/
structure Conservative (f : α → α) (μ : Measure α) : Prop extends QuasiMeasurePreserving f μ μ where
  /-- If `f` is a conservative self-map and `s` is a measurable set of nonzero measure,
  then there exists a point `x ∈ s` that returns to `s` under a non-zero iteration of `f`. -/
  isRecurrent : ∀ ⦃s⦄, MeasurableSet s → IsRecurrent f μ s

namespace Conservative

theorem nullMeasurableSet_isRecurrent (hf : Conservative f μ) (hs : NullMeasurableSet s μ) :
    IsRecurrent f μ s := by
  obtain ⟨t, _, ht, s_t⟩ := hs.exists_measurable_subset_ae_eq
  exact (isRecurrent_congr_set hf.toQuasiMeasurePreserving s_t).1 (hf.isRecurrent ht)

theorem _root_.MeasureTheory.conservative_iff_exists_mem_iterate_mem
    (hf : QuasiMeasurePreserving f μ μ) :
    Conservative f μ ↔ ∀ ⦃s⦄, MeasurableSet s → μ s ≠ 0 → ∃ x ∈ s, ∃ m ≠ 0, f^[m] x ∈ s := by
  refine ⟨fun h s s_m s_0 ↦ (h.isRecurrent s_m).exists_mem_iterate_mem s_0, fun h ↦ ?_⟩
  refine ⟨hf, fun s hs ↦ ae_le_set.2 ?_⟩
  suffices ht : μ (s ∩ ⋂ n ≠ 0, f^[n] ⁻¹' sᶜ) = 0 by
    rw [← ht]; congr; ext x
    simp only [Set.mem_sdiff, mem_iUnion, not_exists, preimage_compl, mem_inter_iff, mem_iInter,
      mem_compl_iff]
  by_contra t_0
  have t_m : MeasurableSet (s ∩ ⋂ n ≠ 0, f^[n] ⁻¹' sᶜ) := by
    refine MeasurableSet.inter hs (MeasurableSet.iInter fun n ↦ ?_)
    exact MeasurableSet.iInter fun _ ↦ ((hf.iterate n).measurable hs).compl
  obtain ⟨x, x_t, n, n_0, x_n⟩ := h t_m t_0
  exact notMem_of_mem_compl (mem_iInter₂.1 x_t.2 n n_0) x_n.1

/-- If `f` is a conservative self-map and `s` is a null measurable set of nonzero measure,
then there exists a point `x ∈ s` that returns to `s` under a non-zero iteration of `f`. -/
theorem exists_mem_iterate_mem (hf : Conservative f μ) (hsm : NullMeasurableSet s μ)
    (hs₀ : μ s ≠ 0) :
    ∃ x ∈ s, ∃ m ≠ 0, f^[m] x ∈ s :=
  (hf.nullMeasurableSet_isRecurrent hsm).exists_mem_iterate_mem hs₀

theorem of_absolutelyContinuous {ν : Measure α} (h : Conservative f μ) (hν : ν ≪ μ)
    (h' : QuasiMeasurePreserving f ν ν) :
    Conservative f ν :=
  ⟨h', fun _ hs ↦ (h.isRecurrent hs).of_absolutelyContinuous hν⟩

theorem congr_ae {ν : Measure α} (hf : Conservative f μ) (h : ae μ = ae ν) :
    Conservative f ν :=
  hf.of_absolutelyContinuous h.ge.absolutelyContinuous_of_ae
    (hf.toQuasiMeasurePreserving.of_eq_ae h)

theorem _root_.MeasureTheory.conservative_congr {ν : Measure α} (h : ae μ = ae ν) :
    Conservative f μ ↔ Conservative f ν :=
  ⟨(congr_ae · h), (congr_ae · h.symm)⟩

/-- Restriction of a conservative system to an invariant set is a conservative system,
formulated in terms of the restriction of the measure. -/
theorem measureRestrict (h : Conservative f μ) (hs : MapsTo f s s) :
    Conservative f (μ.restrict s) :=
  h.of_absolutelyContinuous (absolutelyContinuous_of_le restrict_le_self) <|
    h.toQuasiMeasurePreserving.restrict hs

/-- A self-map preserving a finite measure is conservative. -/
protected theorem _root_.MeasurePreserving.conservative [IsFiniteMeasure μ]
    (h : MeasurePreserving f μ μ) :
    Conservative f μ :=
  ⟨h.quasiMeasurePreserving, fun _ hs ↦ h.isRecurrent hs.nullMeasurableSet⟩

/-- The identity map is conservative with respect to any measure. -/
protected theorem id (μ : Measure α) : Conservative id μ :=
  { toQuasiMeasurePreserving := QuasiMeasurePreserving.id μ
    isRecurrent := fun _ _ ↦ isRecurrent_id }

/-- If `f` is a conservative map and `s` is a measurable set of nonzero measure, then
for infinitely many values of `m` a positive measure of points `x ∈ s` returns back to `s`
after `m` iterations of `f`. -/
theorem frequently_measure_inter_ne_zero (hf : Conservative f μ) (hs : NullMeasurableSet s μ)
    (h0 : μ s ≠ 0) : ∃ᶠ m in atTop, μ (s ∩ f^[m] ⁻¹' s) ≠ 0 :=
  (hf.nullMeasurableSet_isRecurrent hs).frequently_measure_inter_ne_zero hf.toQuasiMeasurePreserving
    (subset_refl s) h0

/-- If `f` is a conservative map and `s` is a measurable set of nonzero measure, then
for an arbitrarily large `m` a positive measure of points `x ∈ s` returns back to `s`
after `m` iterations of `f`. -/
theorem exists_gt_measure_inter_ne_zero (hf : Conservative f μ) (hs : NullMeasurableSet s μ)
    (h0 : μ s ≠ 0) (N : ℕ) : ∃ m > N, μ (s ∩ f^[m] ⁻¹' s) ≠ 0 := by
  obtain ⟨m, N_m, hm⟩ := (hf.frequently_measure_inter_ne_zero hs h0).forall_exists_of_atTop (N + 1)
  exact ⟨m, by linarith, hm⟩

/-- Poincaré recurrence theorem: given a conservative map `f` and a measurable set `s`,
almost every point `x ∈ s` returns back to `s` infinitely many times. -/
theorem ae_mem_imp_frequently_image_mem (hf : Conservative f μ) (hs : NullMeasurableSet s μ) :
    ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s :=
  (hf.nullMeasurableSet_isRecurrent hs).ae_mem_imp_frequently_image_mem hf.toQuasiMeasurePreserving

/-- Poincaré recurrence theorem: given a conservative map `f` and a measurable set `s`, the set
of points `x ∈ s` such that `x` does not return to `s` after `≥ n` iterations has measure zero. -/
theorem measure_mem_forall_ge_image_notMem_eq_zero (hf : Conservative f μ)
    (hs : NullMeasurableSet s μ) (n : ℕ) :
    μ ({ x ∈ s | ∀ m ≥ n, f^[m] x ∉ s }) = 0 := by
  apply measure_mono_null _ (ae_iff.1 (hf.ae_mem_imp_frequently_image_mem hs))
  simp only [Classical.not_imp, not_frequently, eventually_atTop, setOf_subset_setOf, and_imp]
  exact fun x x_s hx ↦ ⟨x_s, n, fun m m_n ↦ hx m m_n⟩

theorem inter_frequently_image_mem_ae_eq (hf : Conservative f μ) (hs : NullMeasurableSet s μ) :
    (s ∩ { x | ∃ᶠ n in atTop, f^[n] x ∈ s } : Set α) =ᵐ[μ] s :=
  inter_eventuallyEq_left.2 <| hf.ae_mem_imp_frequently_image_mem hs

theorem measure_inter_frequently_image_mem_eq (hf : Conservative f μ) (hs : NullMeasurableSet s μ) :
    μ (s ∩ { x | ∃ᶠ n in atTop, f^[n] x ∈ s }) = μ s :=
  measure_congr (hf.inter_frequently_image_mem_ae_eq hs)

/-- Poincaré recurrence theorem: if `f` is a conservative dynamical system and `s` is a measurable
set, then for `μ`-a.e. `x`, if the orbit of `x` visits `s` at least once, then it visits `s`
infinitely many times. -/
theorem ae_forall_image_mem_imp_frequently_image_mem (hf : Conservative f μ)
    (hs : NullMeasurableSet s μ) : ∀ᵐ x ∂μ, ∀ k, f^[k] x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s := by
  refine ae_all_iff.2 fun k => ?_
  refine (hf.ae_mem_imp_frequently_image_mem
    (hs.preimage <| hf.toQuasiMeasurePreserving.iterate k)).mono fun x hx hk => ?_
  rw [← map_add_atTop_eq_nat k, frequently_map]
  refine (hx hk).mono fun n hn => ?_
  rwa [add_comm, iterate_add_apply]

/-- If `f` is a conservative self-map and `s` is a measurable set of positive measure, then
`ae μ`-frequently we have `x ∈ s` and `s` returns to `s` under infinitely many iterations of `f`. -/
theorem frequently_ae_mem_and_frequently_image_mem (hf : Conservative f μ)
    (hs : NullMeasurableSet s μ) (h0 : μ s ≠ 0) : ∃ᵐ x ∂μ, x ∈ s ∧ ∃ᶠ n in atTop, f^[n] x ∈ s :=
  ((frequently_ae_mem_iff.2 h0).and_eventually (hf.ae_mem_imp_frequently_image_mem hs)).mono
    fun _ hx => ⟨hx.1, hx.2 hx.1⟩

/-- Iteration of a conservative system is a conservative system. -/
protected theorem iterate (hf : Conservative f μ) (n : ℕ) : Conservative f^[n] μ := by
  -- Discharge the trivial case `n = 0`
  rcases n with - | n
  · exact Conservative.id μ
  apply (conservative_iff_exists_mem_iterate_mem (hf.toQuasiMeasurePreserving.iterate (n + 1))).2
  intro s hs hs0
  obtain ⟨x, _, hx⟩ :=
    (hf.frequently_ae_mem_and_frequently_image_mem hs.nullMeasurableSet hs0).exists
  /- We take a point `x ∈ s` such that `f^[k] x ∈ s` for infinitely many values of `k`,
    then we choose two of these values `k < l` such that `k ≡ l [MOD (n + 1)]`.
    Then `f^[k] x ∈ s` and `f^[n + 1]^[(l - k) / (n + 1)] (f^[k] x) = f^[l] x ∈ s`. -/
  rw [Nat.frequently_atTop_iff_infinite] at hx
  obtain ⟨k, hk, l, hl, hkl, hn⟩ := Nat.exists_lt_modEq_of_infinite hx n.succ_pos
  set m := (l - k) / (n + 1)
  have : (n + 1) * m = l - k := Nat.mul_div_cancel' ((Nat.modEq_iff_dvd' hkl.le).1 hn)
  refine ⟨f^[k] x, hk, m, ?_, ?_⟩
  · intro hm
    rw [hm, mul_zero, eq_comm, tsub_eq_zero_iff_le] at this
    exact this.not_gt hkl
  · rwa [← iterate_mul, this, ← iterate_add_apply, tsub_add_cancel_of_le]
    exact hkl.le

open TopologicalSpace Topology

/-- Poincaré recurrence theorem. Let `f : α → α` be a conservative dynamical system on a topological
space with second countable topology and measurable open sets. Then almost every point `x : α`
is recurrent: it visits every neighborhood `s ∈ 𝓝 x` infinitely many times. -/
theorem ae_frequently_mem_of_mem_nhds [TopologicalSpace α] [SecondCountableTopology α]
    [OpensMeasurableSpace α] {f : α → α} {μ : Measure α} (h : Conservative f μ) :
    ∀ᵐ x ∂μ, ∀ s ∈ 𝓝 x, ∃ᶠ n in atTop, f^[n] x ∈ s := by
  have : ∀ s ∈ countableBasis α, ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s := fun s hs =>
    h.ae_mem_imp_frequently_image_mem (isOpen_of_mem_countableBasis hs).nullMeasurableSet
  refine ((ae_ball_iff <| countable_countableBasis α).2 this).mono fun x hx s hs => ?_
  rcases (isBasis_countableBasis α).mem_nhds_iff.1 hs with ⟨o, hoS, hxo, hos⟩
  exact (hx o hoS hxo).mono fun n hn => hos hn

end Conservative

end MeasureTheory
