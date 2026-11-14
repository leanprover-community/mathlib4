/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Coalgebra.Graded
public import Mathlib.RingTheory.Coalgebra.PointwiseNilpotent
public import Mathlib.RingTheory.GradedAlgebra.Connected
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Graded connected bialgebras are Hopf algebras

Every connected graded bialgebra admits an antipode, given by Takeuchi's formula: `uε - id` is
pointwise nilpotent for the convolution product, so `id = uε - (uε - id)` is inverted by the
geometric series `∑ k, (uε - id) ^ k`.

## Main declarations

* `HopfAlgebra.takeuchiAntipode`: the antipode `∑ k, (uε - id) ^ k` of a connected graded
  bialgebra.
* `HopfAlgebra.ofGradedConnected`: every connected graded bialgebra is a Hopf algebra.

## TODO

* Show that `takeuchiAntipode` is a graded map.

## References

* [Grinberg, D. and Reiner, V., *Hopf Algebras in Combinatorics*][GrinbergReiner2020],
  Proposition 1.4.16 (existence) and Proposition 1.4.24 (Takeuchi's formula).
-/

public section

/-- In a connected graded bialgebra, every element of degree zero is its counit times the unit. -/
theorem GradedAlgebra.IsConnected.eq_counit_smul_one {ι R A : Type*} [CommSemiring R]
    [Semiring A] [Bialgebra R A] [Zero ι] (𝒜 : ι → Submodule R A) [IsConnected 𝒜] {a : A}
    (ha : a ∈ 𝒜 0) : a = Coalgebra.counit (R := R) a • 1 := by
  obtain ⟨r, rfl⟩ := (mem_zero_iff 𝒜).mp ha
  simp

namespace HopfAlgebra

open Coalgebra DirectSum LinearMap TensorProduct WithConv

variable {R A : Type*} [CommSemiring R] [Ring A] [Bialgebra R A]

variable (𝒜 : ℕ → Submodule R A) [SetLike.GradedComul 𝒜] {m k : ℕ} {x : A}

/-- If `f` vanishes on the degree-zero part, then `f ^ k` vanishes on `𝒜 m` for `m < k`. -/
lemma convPow_apply_eq_zero_of_lt {f : WithConv (A →ₗ[R] A)} (hf : ∀ a ∈ 𝒜 0, f a = 0)
    (hmk : m < k) (hx : x ∈ 𝒜 m) : (f ^ k) x = 0 := by
  induction k generalizing m x with
  | zero => omega
  | succ k' ih =>
    rw [pow_succ', convMul_apply]
    refine (TensorProduct.grade_le (S := ker (mul' R A ∘ₗ map f.ofConv (f ^ k').ofConv))).2
      (fun p q hpq a ha b hb ↦ ?_) (SetLike.GradedComul.comul_mem hx)
    rw [mem_ker, comp_apply, TensorProduct.map_tmul, mul'_apply]
    obtain rfl | hp := Nat.eq_zero_or_pos p
    · rw [hf a ha, zero_mul]
    · rw [ih (show q < k' by omega) hb, mul_zero]

variable [GradedAlgebra.IsConnected 𝒜]

/-- In a connected graded bialgebra, `(uε - id) ^ k` vanishes on `𝒜 m` for `m < k`. The case
`k = 1` is connectedness. -/
lemma convPow_one_sub_id_apply_eq_zero_of_lt (hmk : m < k) (hx : x ∈ 𝒜 m) :
    ((1 - toConv LinearMap.id : WithConv (A →ₗ[R] A)) ^ k) x = 0 :=
  convPow_apply_eq_zero_of_lt 𝒜 (fun a ha ↦ by
    rw [ofConv_sub, LinearMap.sub_apply, convOne_apply, ofConv_toConv, LinearMap.id_apply,
      Algebra.algebraMap_eq_smul_one, ← GradedAlgebra.IsConnected.eq_counit_smul_one 𝒜 ha,
      sub_self]) hmk hx

variable [DirectSum.Decomposition 𝒜]

include 𝒜 in
/-- In a connected graded bialgebra, `uε - id` is pointwise nilpotent for the convolution
product. -/
theorem isPointwiseConvNilpotent_one_sub_id :
    IsPointwiseConvNilpotent (1 - toConv LinearMap.id : WithConv (A →ₗ[R] A)) := by
  refine isPointwiseConvNilpotent_iff.2 fun x ↦ ?_
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => exact ⟨0, fun k _ ↦ map_zero _⟩
  | @homogeneous i x =>
    exact ⟨i + 1, fun k hk ↦ convPow_one_sub_id_apply_eq_zero_of_lt 𝒜 (by omega) x.2⟩
  | add a b ha hb =>
    obtain ⟨Na, ha⟩ := ha
    obtain ⟨Nb, hb⟩ := hb
    exact ⟨max Na Nb, fun k hk ↦ by rw [map_add, ha k (by omega), hb k (by omega), add_zero]⟩

/-- The Takeuchi antipode `∑ k, (uε - id) ^ k` of a connected graded bialgebra. -/
noncomputable def takeuchiAntipode : A →ₗ[R] A :=
  (isPointwiseConvNilpotent_one_sub_id 𝒜).geomSeries.ofConv

/-- The Hopf algebra structure on a connected graded bialgebra, with antipode given by
Takeuchi's formula.

See note [reducible non-instances]. -/
noncomputable abbrev ofGradedConnected : HopfAlgebra R A :=
  ofConvInverse (takeuchiAntipode 𝒜)
    (by simpa [takeuchiAntipode] using
      (isPointwiseConvNilpotent_one_sub_id 𝒜).geomSeries_mul_one_sub)
    (by simpa [takeuchiAntipode] using
      (isPointwiseConvNilpotent_one_sub_id 𝒜).one_sub_mul_geomSeries)

end HopfAlgebra
