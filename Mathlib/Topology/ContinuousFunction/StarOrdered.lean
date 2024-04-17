/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousFunction.Algebra

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
