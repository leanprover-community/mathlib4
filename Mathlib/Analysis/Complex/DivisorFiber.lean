/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/
import Mathlib.Analysis.Complex.DivisorConvergence
import Mathlib.Analysis.Complex.DivisorUnits
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.Order

/-!
# Fibers of the divisor index type

This file studies the fiber `{p : divisorZeroIndex₀ f univ | divisorZeroIndex₀_val p = z₀}`.
It provides a canonical `Finset` for this fiber and identifies its cardinality with the divisor
multiplicity and (for holomorphic functions) with `analyticOrderNatAt`.
-/

noncomputable section

open Set
open scoped Topology BigOperators

namespace Complex.Hadamard

/-!
## Divisor values vs analytic order (holomorphic functions)
-/

lemma divisor_univ_eq_analyticOrderNatAt_int {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    MeromorphicOn.divisor f (Set.univ : Set ℂ) z = (analyticOrderNatAt f z : ℤ) := by
  have hmero : MeromorphicOn f (Set.univ : Set ℂ) := by
    intro w hw
    exact (Differentiable.analyticAt (f := f) hf w).meromorphicAt
  simp only
    [MeromorphicOn.divisor_apply hmero (by simp : z ∈ (Set.univ : Set ℂ)), analyticOrderNatAt]
  have han : AnalyticAt ℂ f z := Differentiable.analyticAt (f := f) hf z
  cases h : analyticOrderAt f z with
  | top =>
      simp [han.meromorphicOrderAt_eq, h]
  | coe n =>
      simp [han.meromorphicOrderAt_eq, h]

/-!
## The multiplicity fiber is finite and has the expected cardinality
-/

theorem divisorZeroIndex₀_fiber_finite (f : ℂ → ℂ) (z₀ : ℂ) :
    ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} :
      Set _).Finite := by
  classical
  have hsub :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} : Set _)
        ⊆ ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} :
          Set _) := by
    intro p hp
    have : divisorZeroIndex₀_val p = z₀ := hp
    simp [this]
  have hfin :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} :
        Set _).Finite := by
    have : Metric.closedBall (0 : ℂ) ‖z₀‖ ⊆ (Set.univ : Set ℂ) := by simp
    simpa using (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
      (B := ‖z₀‖) this)
  exact hfin.subset hsub

/-- The finite fiber over `z₀` in the divisor-index type `divisorZeroIndex₀`. -/
noncomputable def divisorZeroIndex₀_fiberFinset (f : ℂ → ℂ) (z₀ : ℂ) :
    Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
  (divisorZeroIndex₀_fiber_finite (f := f) z₀).toFinset

@[simp] lemma mem_divisorZeroIndex₀_fiberFinset (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p = z₀ := by
  classical
  simp [divisorZeroIndex₀_fiberFinset]

theorem eventually_atTop_subset_fiberFinset
    (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s := by
  refine (Filter.eventually_atTop.2 ?_)
  refine ⟨divisorZeroIndex₀_fiberFinset (f := f) z₀, ?_⟩
  intro s hs
  exact hs

lemma divisorZeroIndex₀_fiberFinset_card_eq_toNat_divisor (f : ℂ → ℂ) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    (divisorZeroIndex₀_fiberFinset (f := f) z₀).card =
      Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀) := by
  classical
  let S : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := {p | divisorZeroIndex₀_val p = z₀}
  have hS : S.Finite := divisorZeroIndex₀_fiber_finite (f := f) z₀
  set n : ℕ := Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀)
  have hcard : Nat.card S = n := by
    classical
    haveI : Fintype S := hS.fintype
    -- `S` is the fiber over `z₀`, hence equivalent to `Fin (Int.toNat (divisor z₀))`.
    let e : S ≃ Fin n :=
      { toFun := by
          intro x
          rcases x with ⟨p, hp⟩
          rcases p with ⟨⟨z, q⟩, hz⟩
          have hzEq : z = z₀ := by simpa [divisorZeroIndex₀_val] using hp
          subst hzEq
          simpa [n] using q
        invFun := by
          intro q
          refine ⟨⟨⟨z₀, ?_⟩, hz₀⟩, ?_⟩
          · simpa [n] using q
          · simp [S, divisorZeroIndex₀_val]
        left_inv := by
          rintro ⟨p, hp⟩
          rcases p with ⟨⟨z, q⟩, hz⟩
          have hzEq : z = z₀ := by simpa [divisorZeroIndex₀_val] using hp
          subst hzEq
          (ext; rfl)
        right_inv := by
          intro q
          rfl }
    have h := Nat.card_congr (α := S) (β := Fin n) e
    simpa using (h.trans (by simp))
  have hSncard : S.ncard = n := by
    simpa [Nat.card_coe_set_eq] using hcard
  have hto : hS.toFinset = divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
    rfl
  have htoFinset : S.ncard = (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
    have h' : S.ncard = hS.toFinset.card := Set.ncard_eq_toFinset_card S hS
    simpa [hto] using h'
  exact htoFinset.symm.trans hSncard

lemma divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    (divisorZeroIndex₀_fiberFinset (f := f) z₀).card = analyticOrderNatAt f z₀ := by
  classical
  have hdiv :
      MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀ = (analyticOrderNatAt f z₀ : ℤ) :=
    divisor_univ_eq_analyticOrderNatAt_int (f := f) hf z₀
  have htoNat : Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀) =
    analyticOrderNatAt f z₀ := by
    simp [hdiv]
  exact (divisorZeroIndex₀_fiberFinset_card_eq_toNat_divisor (f := f) (z₀ := z₀) hz₀).trans htoNat

lemma mem_divisorZeroIndex₀_fiberFinset_of_val_mem_ball
    {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball : Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ))
    (hp : divisorZeroIndex₀_val p ∈ Metric.ball z₀ ε) :
    p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
  classical
  have : divisorZeroIndex₀_val p = z₀ :=
    divisorZeroIndex₀_val_eq_of_mem_ball (f := f) (z₀ := z₀) (ε := ε) hball p hp
  exact (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).2 this

lemma mem_divisorZeroIndex₀_fiberFinset_iff_val_mem_ball
    {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p ∈ Metric.ball z₀ ε := by
  classical
  constructor
  · intro hp
    have : divisorZeroIndex₀_val p = z₀ :=
      (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hp
    simpa [this] using (Metric.mem_ball_self hε : z₀ ∈ Metric.ball z₀ ε)
  · intro hp
    exact mem_divisorZeroIndex₀_fiberFinset_of_val_mem_ball (f := f) (z₀ := z₀) (ε := ε) hball p hp

lemma not_mem_divisorZeroIndex₀_fiberFinset_iff_val_ne
    {f : ℂ → ℂ} (z₀ : ℂ) (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p ≠ z₀ := by
  classical
  simp [mem_divisorZeroIndex₀_fiberFinset]

lemma val_not_mem_ball_of_not_mem_fiberFinset
    {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ} (hε : 0 < ε) (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ))
    (hp : p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀) :
    divisorZeroIndex₀_val p ∉ Metric.ball z₀ ε := by
  intro hpball
  exact hp ((mem_divisorZeroIndex₀_fiberFinset_iff_val_mem_ball (f := f)
    (z₀ := z₀) (ε := ε) hε hball p).2 hpball)

lemma weierstrassFactor_div_ne_zero_on_ball_of_not_mem_fiberFinset
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ))
    (hp : p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀) :
    ∀ z ∈ Metric.ball z₀ ε, weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 := by
  have hp' : divisorZeroIndex₀_val p ≠ z₀ :=
    (not_mem_divisorZeroIndex₀_fiberFinset_iff_val_ne (f := f) z₀ p).1 hp
  exact weierstrassFactor_div_ne_zero_on_ball_of_val_ne (m := m) (f := f) (z₀ := z₀)
    (ε := ε) hball p hp'

end Complex.Hadamard
