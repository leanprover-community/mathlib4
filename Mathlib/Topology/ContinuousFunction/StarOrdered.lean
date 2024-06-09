/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousFunction.Algebra
import Mathlib.Topology.ContinuousFunction.ContinuousMapZero

/-! # Continuous functions as a star-ordered ring -/

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

lemma starOrderedRing_of_sqrt {R : Type*} [PartialOrder R] [CommRing R] [StarRing R]
    [StarOrderedRing R] [TopologicalSpace R] [ContinuousStar R] [TopologicalRing R]
    (sqrt : R → R) (h_continuous : Continuous sqrt)
    (sqrt_map_zero : sqrt 0 = 0)
    (h_sqrt : ∀ x, 0 ≤ x → star (sqrt x) * sqrt x = x) : StarOrderedRing C(α, R)₀ := by
  refine StarOrderedRing.of_nonneg_iff' ?_ ?_
  · intro x y hxy z
    rw [ContinuousMapZero.le_def]
    intro i
    simp [hxy i]
  · intro x
    refine ⟨fun hf => ?_, ?_⟩
    · let sqrtC : C(R, R)₀ :=
      { toFun := sqrt
        continuous_toFun := h_continuous
        map_zero' := sqrt_map_zero }
      refine ⟨sqrtC.comp x, ?_⟩
      ext i
      simp [sqrtC, h_sqrt (x i) (hf i)]
    · rintro ⟨f, rfl⟩
      rw [ContinuousMapZero.le_def]
      intro i
      simp [star_mul_self_nonneg (f i)]

open scoped ComplexOrder in
open RCLike in
instance (priority := 100) instStarOrderedRingRCLike {𝕜 : Type*} [RCLike 𝕜] :
    StarOrderedRing C(α, 𝕜)₀ :=
  starOrderedRing_of_sqrt ((↑) ∘ Real.sqrt ∘ re) (by fun_prop) (by simp) <| fun x hx => by
    simp only [Function.comp_apply,star_def]
    obtain hx' := nonneg_iff.mp hx |>.right
    rw [← conj_eq_iff_im, conj_eq_iff_re] at hx'
    rw [conj_ofReal, ← ofReal_mul, Real.mul_self_sqrt, hx']
    rw [nonneg_iff]
    simpa using nonneg_iff.mp hx |>.left

instance instStarOrderedRingReal : StarOrderedRing C(α, ℝ)₀ :=
  instStarOrderedRingRCLike (𝕜 := ℝ)

open scoped ComplexOrder in
open Complex in
instance instStarOrderedRingComplex : StarOrderedRing C(α, ℂ)₀ :=
  instStarOrderedRingRCLike (𝕜 := ℂ)

open NNReal in
instance instStarOrderedRingNNReal : StarOrderedRing C(α, ℝ≥0)₀ :=
  StarOrderedRing.of_le_iff fun f g ↦ by
    refine ⟨fun hfg => ?_, ?_⟩
    · let sqrtC : C(ℝ≥0, ℝ≥0)₀ :=
      { toFun := sqrt
        continuous_toFun := by fun_prop
        map_zero' := by simp }
      let g_sub_f : C(α, ℝ≥0)₀ :=
      { toFun := g - f
        continuous_toFun := Continuous.sub (by fun_prop) (by fun_prop)
        map_zero' := by simp }
      use .comp sqrtC g_sub_f
      ext1 x
      simpa [sqrtC, g_sub_f] using add_tsub_cancel_of_le (hfg x) |>.symm
    · rintro ⟨s, rfl⟩
      exact fun _ ↦ by simp

end ContinuousMapZero
