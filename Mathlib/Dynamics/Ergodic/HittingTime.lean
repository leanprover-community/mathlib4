/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Combinatorics.Pigeonhole

/-!
# Conservative systems

In this file we define `f : α → α` to be a *conservative* system w.r.t. a measure `μ` if `f` is
non-singular (`MeasureTheory.QuasiMeasurePreserving`) and for every measurable set `s` of
positive measure at least one point `x ∈ s` returns back to `s` after some number of iterations of
`f`. There are several properties that look like they are stronger than this one but actually follow
from it:

* `MeasureTheory.Conservative.frequently_measure_inter_ne_zero`,
  `MeasureTheory.Conservative.exists_gt_measure_inter_ne_zero`: if `μ s ≠ 0`, then for infinitely
  many `n`, the measure of `s ∩ f^[n] ⁻¹' s` is positive.

* `MeasureTheory.Conservative.measure_mem_forall_ge_image_notMem_eq_zero`,
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

public section

noncomputable section

namespace Recurrence

variable {α : Type*} {f : α → α} {s : Set α}

open Nat

/-- `HittingTime f s` is the function which to each point `x` associates the first positive time `n`
at which the iterate `f^[n] x` belongs to `s`. By the convention `sInf ∅ = 0`, if the positive orbit
of `x` never hits `s`, then `HittingTime f s x = 0`. -/
def HittingTime (f : α → α) (s : Set α) :=
    fun x ↦ sInf {n : ℕ | n ≠ 0 ∧ f^[n] x ∈ s}

lemma hittingTime_eq_zero_iff_forall (f : α → α) (s : Set α) (x : α) :
    HittingTime f s x = 0 ↔ ∀ n ≠ 0, f^[n] x ∉ s := by
  simp [HittingTime, Set.eq_empty_iff_forall_notMem]

lemma hittingTime_pos_iff_exists (f : α → α) (s : Set α) (x : α) :
    HittingTime f s x ≠ 0 ↔ ∃ n ≠ 0, f^[n] x ∈ s := by
  rw [← not_iff_not]
  simp [hittingTime_eq_zero_iff_forall]

/-- `HittingMap f s` is the function which to each point `x` associates the point at which the
positive orbit of `x` first hits `s`. By the convention `sInf ∅ = 0`, if the positive orbit
of `x` never hits `s`, then `HittingMap f s x = x`. -/
def HittingMap (f : α → α) (s : Set α) :=
    fun x ↦ f^[HittingTime f s x] x

lemma hittingMap_eq_self_of_hittingTime_zero {f : α → α} {s : Set α} {x : α}
    (h : HittingTime f s x = 0) :
    HittingMap f s x = x := by
  simp [HittingMap, h]

lemma hittingMap_mem_iff {f : α → α} {s : Set α} {x : α} :
    HittingMap f s x ∈ s ↔ HittingTime f s x ≠ 0 ∨ x ∈ s := by
  by_cases h : HittingTime f s x = 0
  · simp [h, hittingMap_eq_self_of_hittingTime_zero h]
  · simp only [ne_eq, h, not_false_eq_true, true_or, iff_true]
    exact (sInf_mem (nonempty_of_pos_sInf (pos_of_ne_zero h))).2

lemma hittingMap_mem_of_hittingTime_pos {f : α → α} {s : Set α} {x : α}
    (h : HittingTime f s x ≠ 0) :
    HittingMap f s x ∈ s :=
  hittingMap_mem_iff.2 (Or.inl h)

lemma hittingMap_mem_of_mem {f : α → α} {s : Set α} {x : α} (h : x ∈ s) :
    HittingMap f s x ∈ s :=
  hittingMap_mem_iff.2 (Or.inr h)

end Recurrence
