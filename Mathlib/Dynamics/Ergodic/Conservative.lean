/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Combinatorics.Pigeonhole

#align_import dynamics.ergodic.conservative from "leanprover-community/mathlib"@"bf6a01357ff5684b1ebcd0f1a13be314fc82c0bf"

/-!
# Conservative systems

In this file we define `f : α → α` to be a *conservative* system w.r.t a measure `μ` if `f` is
non-singular (`MeasureTheory.QuasiMeasurePreserving`) and for every measurable set `s` of
positive measure at least one point `x ∈ s` returns back to `s` after some number of iterations of
`f`. There are several properties that look like they are stronger than this one but actually follow
from it:

* `MeasureTheory.Conservative.frequently_measure_inter_ne_zero`,
  `MeasureTheory.Conservative.exists_gt_measure_inter_ne_zero`: if `μ s ≠ 0`, then for infinitely
  many `n`, the measure of `s ∩ f^[n] ⁻¹' s` is positive.

* `MeasureTheory.Conservative.measure_mem_forall_ge_image_not_mem_eq_zero`,
  `MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`: a.e. every point of `s` visits `s`
  infinitely many times (Poincaré recurrence theorem).

We also prove the topological Poincaré recurrence theorem
`MeasureTheory.Conservative.ae_frequently_mem_of_mem_nhds`. Let `f : α → α` be a conservative
dynamical system on a topological space with second countable topology and measurable open
sets. Then almost every point `x : α` is recurrent: it visits every neighborhood `s ∈ 𝓝 x`
infinitely many times.

## Tags

conservative dynamical system, Poincare recurrence theorem
-/


noncomputable section

open scoped Classical
open Set Filter MeasureTheory Finset Function TopologicalSpace

open scoped Classical
open Topology

variable {ι : Type*} {α : Type*} [MeasurableSpace α] {f : α → α} {s : Set α} {μ : Measure α}

namespace MeasureTheory

open Measure

/-- We say that a non-singular (`MeasureTheory.QuasiMeasurePreserving`) self-map is
*conservative* if for any measurable set `s` of positive measure there exists `x ∈ s` such that `x`
returns back to `s` under some iteration of `f`. -/
structure Conservative (f : α → α) (μ : Measure α) extends QuasiMeasurePreserving f μ μ : Prop where
  /-- If `f` is a conservative self-map and `s` is a measurable set of nonzero measure,
  then there exists a point `x ∈ s` that returns to `s` under a non-zero iteration of `f`. -/
  exists_mem_iterate_mem : ∀ ⦃s⦄, MeasurableSet s → μ s ≠ 0 → ∃ x ∈ s, ∃ m ≠ 0, f^[m] x ∈ s
#align measure_theory.conservative MeasureTheory.Conservative

/-- A self-map preserving a finite measure is conservative. -/
protected theorem MeasurePreserving.conservative [IsFiniteMeasure μ] (h : MeasurePreserving f μ μ) :
    Conservative f μ :=
  ⟨h.quasiMeasurePreserving, fun _ hsm h0 => h.exists_mem_iterate_mem hsm h0⟩
#align measure_theory.measure_preserving.conservative MeasureTheory.MeasurePreserving.conservative

namespace Conservative

/-- The identity map is conservative w.r.t. any measure. -/
protected theorem id (μ : Measure α) : Conservative id μ :=
  { toQuasiMeasurePreserving := QuasiMeasurePreserving.id μ
    exists_mem_iterate_mem := fun _ _ h0 =>
      let ⟨x, hx⟩ := nonempty_of_measure_ne_zero h0
      ⟨x, hx, 1, one_ne_zero, hx⟩ }
#align measure_theory.conservative.id MeasureTheory.Conservative.id

/-- If `f` is a conservative map and `s` is a measurable set of nonzero measure, then
for infinitely many values of `m` a positive measure of points `x ∈ s` returns back to `s`
after `m` iterations of `f`. -/
theorem frequently_measure_inter_ne_zero (hf : Conservative f μ) (hs : MeasurableSet s)
    (h0 : μ s ≠ 0) : ∃ᶠ m in atTop, μ (s ∩ f^[m] ⁻¹' s) ≠ 0 := by
  by_contra H
  simp only [not_frequently, eventually_atTop, Ne, Classical.not_not] at H
  rcases H with ⟨N, hN⟩
  induction' N with N ihN
  · apply h0
    simpa using hN 0 le_rfl
  rw [imp_false] at ihN
  push_neg at ihN
  rcases ihN with ⟨n, hn, hμn⟩
  set T := s ∩ ⋃ n ≥ N + 1, f^[n] ⁻¹' s
  have hT : MeasurableSet T :=
    hs.inter (MeasurableSet.biUnion (to_countable _) fun _ _ => hf.measurable.iterate _ hs)
  have hμT : μ T = 0 := by
    convert (measure_biUnion_null_iff <| to_countable _).2 hN
    rw [← inter_iUnion₂]
    rfl
  have : μ ((s ∩ f^[n] ⁻¹' s) \ T) ≠ 0 := by rwa [measure_diff_null hμT]
  rcases hf.exists_mem_iterate_mem ((hs.inter (hf.measurable.iterate n hs)).diff hT) this with
    ⟨x, ⟨⟨hxs, _⟩, hxT⟩, m, hm0, ⟨_, hxm⟩, _⟩
  refine hxT ⟨hxs, mem_iUnion₂.2 ⟨n + m, ?_, ?_⟩⟩
  · exact add_le_add hn (Nat.one_le_of_lt <| pos_iff_ne_zero.2 hm0)
  · rwa [Set.mem_preimage, ← iterate_add_apply] at hxm
#align measure_theory.conservative.frequently_measure_inter_ne_zero MeasureTheory.Conservative.frequently_measure_inter_ne_zero

/-- If `f` is a conservative map and `s` is a measurable set of nonzero measure, then
for an arbitrarily large `m` a positive measure of points `x ∈ s` returns back to `s`
after `m` iterations of `f`. -/
theorem exists_gt_measure_inter_ne_zero (hf : Conservative f μ) (hs : MeasurableSet s)
    (h0 : μ s ≠ 0) (N : ℕ) : ∃ m > N, μ (s ∩ f^[m] ⁻¹' s) ≠ 0 :=
  let ⟨m, hm, hmN⟩ :=
    ((hf.frequently_measure_inter_ne_zero hs h0).and_eventually (eventually_gt_atTop N)).exists
  ⟨m, hmN, hm⟩
#align measure_theory.conservative.exists_gt_measure_inter_ne_zero MeasureTheory.Conservative.exists_gt_measure_inter_ne_zero

/-- Poincaré recurrence theorem: given a conservative map `f` and a measurable set `s`, the set
of points `x ∈ s` such that `x` does not return to `s` after `≥ n` iterations has measure zero. -/
theorem measure_mem_forall_ge_image_not_mem_eq_zero (hf : Conservative f μ) (hs : MeasurableSet s)
    (n : ℕ) : μ ({ x ∈ s | ∀ m ≥ n, f^[m] x ∉ s }) = 0 := by
  by_contra H
  have : MeasurableSet (s ∩ { x | ∀ m ≥ n, f^[m] x ∉ s }) := by
    simp only [setOf_forall, ← compl_setOf]
    exact
      hs.inter (MeasurableSet.biInter (to_countable _) fun m _ => hf.measurable.iterate m hs.compl)
  rcases (hf.exists_gt_measure_inter_ne_zero this H) n with ⟨m, hmn, hm⟩
  rcases nonempty_of_measure_ne_zero hm with ⟨x, ⟨_, hxn⟩, hxm, -⟩
  exact hxn m hmn.lt.le hxm
#align measure_theory.conservative.measure_mem_forall_ge_image_not_mem_eq_zero MeasureTheory.Conservative.measure_mem_forall_ge_image_not_mem_eq_zero

/-- Poincaré recurrence theorem: given a conservative map `f` and a measurable set `s`,
almost every point `x ∈ s` returns back to `s` infinitely many times. -/
theorem ae_mem_imp_frequently_image_mem (hf : Conservative f μ) (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s := by
  simp only [frequently_atTop, @forall_swap (_ ∈ s), ae_all_iff]
  intro n
  filter_upwards [measure_zero_iff_ae_nmem.1 (hf.measure_mem_forall_ge_image_not_mem_eq_zero hs n)]
  simp
#align measure_theory.conservative.ae_mem_imp_frequently_image_mem MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem

theorem inter_frequently_image_mem_ae_eq (hf : Conservative f μ) (hs : MeasurableSet s) :
    (s ∩ { x | ∃ᶠ n in atTop, f^[n] x ∈ s } : Set α) =ᵐ[μ] s :=
  inter_eventuallyEq_left.2 <| hf.ae_mem_imp_frequently_image_mem hs
#align measure_theory.conservative.inter_frequently_image_mem_ae_eq MeasureTheory.Conservative.inter_frequently_image_mem_ae_eq

theorem measure_inter_frequently_image_mem_eq (hf : Conservative f μ) (hs : MeasurableSet s) :
    μ (s ∩ { x | ∃ᶠ n in atTop, f^[n] x ∈ s }) = μ s :=
  measure_congr (hf.inter_frequently_image_mem_ae_eq hs)
#align measure_theory.conservative.measure_inter_frequently_image_mem_eq MeasureTheory.Conservative.measure_inter_frequently_image_mem_eq

/-- Poincaré recurrence theorem: if `f` is a conservative dynamical system and `s` is a measurable
set, then for `μ`-a.e. `x`, if the orbit of `x` visits `s` at least once, then it visits `s`
infinitely many times.  -/
theorem ae_forall_image_mem_imp_frequently_image_mem (hf : Conservative f μ)
    (hs : MeasurableSet s) : ∀ᵐ x ∂μ, ∀ k, f^[k] x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s := by
  refine ae_all_iff.2 fun k => ?_
  refine (hf.ae_mem_imp_frequently_image_mem (hf.measurable.iterate k hs)).mono fun x hx hk => ?_
  rw [← map_add_atTop_eq_nat k, frequently_map]
  refine (hx hk).mono fun n hn => ?_
  rwa [add_comm, iterate_add_apply]
#align measure_theory.conservative.ae_forall_image_mem_imp_frequently_image_mem MeasureTheory.Conservative.ae_forall_image_mem_imp_frequently_image_mem

/-- If `f` is a conservative self-map and `s` is a measurable set of positive measure, then
`ae μ`-frequently we have `x ∈ s` and `s` returns to `s` under infinitely many iterations of `f`. -/
theorem frequently_ae_mem_and_frequently_image_mem (hf : Conservative f μ) (hs : MeasurableSet s)
    (h0 : μ s ≠ 0) : ∃ᵐ x ∂μ, x ∈ s ∧ ∃ᶠ n in atTop, f^[n] x ∈ s :=
  ((frequently_ae_mem_iff.2 h0).and_eventually (hf.ae_mem_imp_frequently_image_mem hs)).mono
    fun _ hx => ⟨hx.1, hx.2 hx.1⟩
#align measure_theory.conservative.frequently_ae_mem_and_frequently_image_mem MeasureTheory.Conservative.frequently_ae_mem_and_frequently_image_mem

/-- Poincaré recurrence theorem. Let `f : α → α` be a conservative dynamical system on a topological
space with second countable topology and measurable open sets. Then almost every point `x : α`
is recurrent: it visits every neighborhood `s ∈ 𝓝 x` infinitely many times. -/
theorem ae_frequently_mem_of_mem_nhds [TopologicalSpace α] [SecondCountableTopology α]
    [OpensMeasurableSpace α] {f : α → α} {μ : Measure α} (h : Conservative f μ) :
    ∀ᵐ x ∂μ, ∀ s ∈ 𝓝 x, ∃ᶠ n in atTop, f^[n] x ∈ s := by
  have : ∀ s ∈ countableBasis α, ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s := fun s hs =>
    h.ae_mem_imp_frequently_image_mem (isOpen_of_mem_countableBasis hs).measurableSet
  refine ((ae_ball_iff <| countable_countableBasis α).2 this).mono fun x hx s hs => ?_
  rcases (isBasis_countableBasis α).mem_nhds_iff.1 hs with ⟨o, hoS, hxo, hos⟩
  exact (hx o hoS hxo).mono fun n hn => hos hn
#align measure_theory.conservative.ae_frequently_mem_of_mem_nhds MeasureTheory.Conservative.ae_frequently_mem_of_mem_nhds

/-- Iteration of a conservative system is a conservative system. -/
protected theorem iterate (hf : Conservative f μ) (n : ℕ) : Conservative f^[n] μ := by
  cases' n with n
  · exact Conservative.id μ
  -- Discharge the trivial case `n = 0`
  refine ⟨hf.1.iterate _, fun s hs hs0 => ?_⟩
  rcases (hf.frequently_ae_mem_and_frequently_image_mem hs hs0).exists with ⟨x, _, hx⟩
  /- We take a point `x ∈ s` such that `f^[k] x ∈ s` for infinitely many values of `k`,
    then we choose two of these values `k < l` such that `k ≡ l [MOD (n + 1)]`.
    Then `f^[k] x ∈ s` and `f^[n + 1]^[(l - k) / (n + 1)] (f^[k] x) = f^[l] x ∈ s`. -/
  rw [Nat.frequently_atTop_iff_infinite] at hx
  rcases Nat.exists_lt_modEq_of_infinite hx n.succ_pos with ⟨k, hk, l, hl, hkl, hn⟩
  set m := (l - k) / (n + 1)
  have : (n + 1) * m = l - k := by
    apply Nat.mul_div_cancel'
    exact (Nat.modEq_iff_dvd' hkl.le).1 hn
  refine ⟨f^[k] x, hk, m, ?_, ?_⟩
  · intro hm
    rw [hm, mul_zero, eq_comm, tsub_eq_zero_iff_le] at this
    exact this.not_lt hkl
  · rwa [← iterate_mul, this, ← iterate_add_apply, tsub_add_cancel_of_le]
    exact hkl.le
#align measure_theory.conservative.iterate MeasureTheory.Conservative.iterate

end Conservative

end MeasureTheory
