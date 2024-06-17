/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousFunction.Algebra
import Mathlib.Topology.ContinuousFunction.ContinuousMapZero

/-! # Continuous functions as a star-ordered ring -/

open scoped NNReal

namespace ContinuousMap

variable {α : Type*} [TopologicalSpace α]

lemma starOrderedRing_of_sqrt {R : Type*} [PartialOrder R] [NonUnitalRing R] [StarRing R]
    [StarOrderedRing R] [TopologicalSpace R] [ContinuousStar R] [TopologicalRing R]
    (sqrt : R → R) (h_continuousOn : ContinuousOn sqrt {x : R | 0 ≤ x})
    (h_sqrt : ∀ x, 0 ≤ x → star (sqrt x) * sqrt x = x) : StarOrderedRing C(α, R) :=
  StarOrderedRing.of_nonneg_iff' add_le_add_left fun f ↦ by
    constructor
    · intro hf
      use (mk _ h_continuousOn.restrict).comp ⟨_, map_continuous f |>.codRestrict (by exact hf ·)⟩
      ext x
      exact h_sqrt (f x) (hf x) |>.symm
    · rintro ⟨f, rfl⟩
      rw [ContinuousMap.le_def]
      exact fun x ↦ star_mul_self_nonneg (f x)

open scoped ComplexOrder in
open RCLike in
instance (priority := 100) instStarOrderedRingRCLike {𝕜 : Type*} [RCLike 𝕜] :
    StarOrderedRing C(α, 𝕜) :=
  starOrderedRing_of_sqrt ((↑) ∘ Real.sqrt ∘ re) (by fun_prop) fun x hx ↦ by
    simp only [Function.comp_apply,star_def]
    obtain hx' := nonneg_iff.mp hx |>.right
    rw [← conj_eq_iff_im, conj_eq_iff_re] at hx'
    rw [conj_ofReal, ← ofReal_mul, Real.mul_self_sqrt, hx']
    rw [nonneg_iff]
    simpa using nonneg_iff.mp hx |>.left

instance instStarOrderedRingReal : StarOrderedRing C(α, ℝ) :=
  instStarOrderedRingRCLike (𝕜 := ℝ)

open scoped ComplexOrder in
open Complex in
instance instStarOrderedRingComplex : StarOrderedRing C(α, ℂ) :=
  instStarOrderedRingRCLike (𝕜 := ℂ)

open NNReal in
instance instStarOrderedRingNNReal : StarOrderedRing C(α, ℝ≥0) :=
  StarOrderedRing.of_le_iff fun f g ↦ by
    constructor
    · intro hfg
      use .comp ⟨sqrt, by fun_prop⟩ (g - f)
      ext1 x
      simpa using add_tsub_cancel_of_le (hfg x) |>.symm
    · rintro ⟨s, rfl⟩
      exact fun _ ↦ by simp

end ContinuousMap

namespace ContinuousMapZero

variable {α : Type*} [TopologicalSpace α] [Zero α]

instance instStarOrderedRing {R : Type*}
    [TopologicalSpace R] [OrderedCommSemiring R] [NoZeroDivisors R] [StarRing R] [StarOrderedRing R]
    [TopologicalSemiring R] [ContinuousStar R] [StarOrderedRing C(α, R)] :
    StarOrderedRing C(α, R)₀ where
  le_iff f g := by
    constructor
    · rw [le_def, ← ContinuousMap.coe_coe, ← ContinuousMap.coe_coe g, ← ContinuousMap.le_def,
        StarOrderedRing.le_iff]
      rintro ⟨p, hp_mem, hp⟩
      induction hp_mem using AddSubmonoid.closure_induction_left generalizing f g with
      | one => exact ⟨0, zero_mem _, by ext x; congrm($(hp) x)⟩
      | mul_left s s_mem p p_mem hp' =>
        obtain ⟨s, rfl⟩ := s_mem
        simp only at *
        have h₀ : (star s * s + p) 0 = 0 := by simpa using congr($(hp) 0).symm
        rw [← add_assoc] at hp
        have p'₀ : 0 ≤ p 0 := by rw [← StarOrderedRing.nonneg_iff] at p_mem; exact p_mem 0
        have s₉ : (star s * s) 0 = 0 := le_antisymm ((le_add_of_nonneg_right p'₀).trans_eq h₀)
          (star_mul_self_nonneg (s 0))
        have s₀' : s 0 = 0 := by aesop
        let s' : C(α, R)₀ := ⟨s, s₀'⟩
        obtain ⟨p', hp'_mem, rfl⟩ := hp' (f + star s' * s') g hp
        refine ⟨star s' * s' + p', ?_, by rw [add_assoc]⟩
        exact add_mem (AddSubmonoid.subset_closure ⟨s', rfl⟩) hp'_mem
    · rintro ⟨p, hp, rfl⟩
      induction hp using AddSubmonoid.closure_induction' generalizing f with
      | mem s s_mem =>
        obtain ⟨s, rfl⟩ := s_mem
        exact fun x ↦ le_add_of_nonneg_right (star_mul_self_nonneg (s x))
      | one => simp
      | mul g₁ _ g₂ _ h₁ h₂ => calc
          f ≤ f + g₁ := h₁ f
          _ ≤ (f + g₁) + g₂ := h₂ (f + g₁)
          _ = f + (g₁ + g₂) := add_assoc _ _ _

instance instStarOrderedRingReal : StarOrderedRing C(α, ℝ)₀ :=
  instStarOrderedRing (R := ℝ)

open scoped ComplexOrder in
instance instStarOrderedRingComplex : StarOrderedRing C(α, ℂ)₀ :=
  instStarOrderedRing (R := ℂ)

instance instStarOrderedRingNNReal : StarOrderedRing C(α, ℝ≥0)₀ :=
  instStarOrderedRing (R := ℝ≥0)

end ContinuousMapZero
