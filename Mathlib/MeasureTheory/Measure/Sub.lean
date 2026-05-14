/-
Copyright (c) 2022 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Subtraction of measures

In this file we define `μ - ν` to be the least measure `τ` such that `μ ≤ τ + ν`.
It is equivalent to `(μ - ν) ⊔ 0` if `μ` and `ν` were signed measures.
Compare with `ENNReal.instSub`.
Specifically, note that if you have `α = {1,2}`, and `μ {1} = 2`, `μ {2} = 0`, and
`ν {2} = 2`, `ν {1} = 0`, then `(μ - ν) {1, 2} = 2`. However, if `μ ≤ ν`, and
`ν univ ≠ ∞`, then `(μ - ν) + ν = μ`.
-/

@[expose] public section

open Set

namespace MeasureTheory

namespace Measure

/-- The measure `μ - ν` is defined to be the least measure `τ` such that `μ ≤ τ + ν`.
It is equivalent to `(μ - ν) ⊔ 0` if `μ` and `ν` were signed measures.
Compare with `ENNReal.instSub`.
Specifically, note that if you have `α = {1,2}`, and `μ {1} = 2`, `μ {2} = 0`, and
`ν {2} = 2`, `ν {1} = 0`, then `(μ - ν) {1, 2} = 2`. However, if `μ ≤ ν`, and
`ν univ ≠ ∞`, then `(μ - ν) + ν = μ`. -/
noncomputable instance instSub {α : Type*} [MeasurableSpace α] : Sub (Measure α) :=
  ⟨fun μ ν => sInf { τ | μ ≤ τ + ν }⟩

variable {α : Type*} {m : MeasurableSpace α} {μ ν ξ : Measure α} {s : Set α}

theorem sub_def : μ - ν = sInf { d | μ ≤ d + ν } := rfl

theorem sub_le_of_le_add {d} (h : μ ≤ d + ν) : μ - ν ≤ d :=
  sInf_le h

theorem sub_eq_zero_of_le (h : μ ≤ ν) : μ - ν = 0 :=
  nonpos_iff_eq_zero'.1 <| sub_le_of_le_add <| by rwa [zero_add]

theorem sub_le : μ - ν ≤ μ :=
  sub_le_of_le_add <| Measure.le_add_right le_rfl

@[simp]
theorem sub_top : μ - ⊤ = 0 :=
  sub_eq_zero_of_le le_top

@[simp]
protected theorem zero_sub : 0 - μ = 0 :=
  sub_eq_zero_of_le μ.zero_le

@[simp]
protected theorem sub_self : μ - μ = 0 :=
  sub_eq_zero_of_le le_rfl

@[simp]
protected theorem sub_zero : μ - 0 = μ := by
  rw [sub_def]
  apply le_antisymm
  · simp [sInf_le]
  · simp

/-- This application lemma only works in special circumstances. Given knowledge of
when `μ ≤ ν` and `ν ≤ μ`, a more general application lemma can be written. -/
theorem sub_apply [IsFiniteMeasure ν] (h₁ : MeasurableSet s) (h₂ : ν ≤ μ) :
    (μ - ν) s = μ s - ν s := by
  -- We begin by defining `measure_sub`, which will be equal to `(μ - ν)`.
  let measure_sub : Measure α := MeasureTheory.Measure.ofMeasurable
    (fun (t : Set α) (_ : MeasurableSet t) => μ t - ν t) (by simp)
    (fun g h_meas h_disj ↦ by
      simp only [measure_iUnion h_disj h_meas]
      rw [ENNReal.tsum_sub _ (h₂ <| g ·)]
      rw [← measure_iUnion h_disj h_meas]
      apply measure_ne_top)
  -- Now, we demonstrate `μ - ν = measure_sub`, and apply it.
  have h_measure_sub_add : ν + measure_sub = μ := by
    ext1 t h_t_measurable_set
    simp only [Pi.add_apply, coe_add]
    rw [MeasureTheory.Measure.ofMeasurable_apply _ h_t_measurable_set, add_comm,
      tsub_add_cancel_of_le (h₂ t)]
  have h_measure_sub_eq : μ - ν = measure_sub := by
    rw [MeasureTheory.Measure.sub_def]
    apply le_antisymm
    · apply sInf_le
      simp [add_comm, h_measure_sub_add]
    apply le_sInf
    intro d h_d
    rw [← h_measure_sub_add, mem_setOf_eq, add_comm d] at h_d
    apply Measure.le_of_add_le_add_left h_d
  rw [h_measure_sub_eq]
  apply Measure.ofMeasurable_apply _ h₁

theorem sub_add_cancel_of_le [IsFiniteMeasure ν] (h₁ : ν ≤ μ) : μ - ν + ν = μ := by
  ext1 s h_s_meas
  rw [add_apply, sub_apply h_s_meas h₁, tsub_add_cancel_of_le (h₁ s)]

@[simp]
protected lemma add_sub_cancel [IsFiniteMeasure ν] : μ + ν - ν = μ := by
  ext1 s hs
  rw [sub_apply hs (Measure.le_add_left (le_refl _)), add_apply,
    ENNReal.add_sub_cancel_right (measure_ne_top ν s)]

theorem restrict_sub_eq_restrict_sub_restrict (h_meas_s : MeasurableSet s) :
    (μ - ν).restrict s = μ.restrict s - ν.restrict s := by
  repeat rw [sub_def]
  have h_nonempty : { d | μ ≤ d + ν }.Nonempty := ⟨μ, Measure.le_add_right le_rfl⟩
  rw [restrict_sInf_eq_sInf_restrict h_nonempty h_meas_s]
  apply le_antisymm
  · refine sInf_le_sInf_of_isCoinitialFor ?_
    intro ν' h_ν'_in
    rw [mem_setOf_eq] at h_ν'_in
    refine ⟨ν'.restrict s, ?_, restrict_le_self⟩
    refine ⟨ν' + (⊤ : Measure α).restrict sᶜ, ?_, ?_⟩
    · rw [mem_setOf_eq, add_right_comm, Measure.le_iff]
      intro t h_meas_t
      repeat rw [← measure_inter_add_diff t h_meas_s]
      refine add_le_add ?_ ?_
      · rw [add_apply, add_apply]
        apply le_add_right _
        rw [← restrict_eq_self μ inter_subset_right,
          ← restrict_eq_self ν inter_subset_right]
        apply h_ν'_in
      · rw [add_apply, restrict_apply (h_meas_t.diff h_meas_s), diff_eq, inter_assoc, inter_self,
          ← add_apply]
        have h_mu_le_add_top : μ ≤ ν' + ν + ⊤ := by simp only [add_top, le_top]
        exact Measure.le_iff'.1 h_mu_le_add_top _
    · ext1 t h_meas_t
      simp [restrict_apply h_meas_t, restrict_apply (h_meas_t.inter h_meas_s), inter_assoc]
  · refine sInf_le_sInf_of_isCoinitialFor ?_
    refine forall_mem_image.2 fun t h_t_in => ⟨t.restrict s, ?_, le_rfl⟩
    rw [Set.mem_setOf_eq, ← restrict_add]
    exact restrict_mono Subset.rfl h_t_in

theorem sub_apply_eq_zero_of_restrict_le_restrict (h_le : μ.restrict s ≤ ν.restrict s)
    (h_meas_s : MeasurableSet s) : (μ - ν) s = 0 := by
  rw [← restrict_apply_self, restrict_sub_eq_restrict_sub_restrict, sub_eq_zero_of_le] <;> simp [*]

instance isFiniteMeasure_sub [IsFiniteMeasure μ] : IsFiniteMeasure (μ - ν) :=
  isFiniteMeasure_of_le μ sub_le

/-- See `sub_le_iff_le_add` for the case where both measures are finite, which does not need the
hypothesis `ν ≤ μ`. -/
lemma sub_le_iff_le_add_of_le [IsFiniteMeasure ν] (h_le : ν ≤ μ) : μ - ν ≤ ξ ↔ μ ≤ ξ + ν := by
  refine ⟨fun h ↦ ?_, Measure.sub_le_of_le_add⟩
  simpa [sub_add_cancel_of_le h_le] using add_le_add_left h ν

end Measure

end MeasureTheory
