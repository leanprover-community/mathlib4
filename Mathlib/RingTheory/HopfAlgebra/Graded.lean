/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Graded
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Graded connected bialgebras are Hopf algebras

Every connected graded bialgebra admits an antipode, given by Takeuchi's formula.

## Main declarations

* `HopfAlgebra.takeuchiAntipode`: the antipode of a connected graded bialgebra, defined on `𝒜 n`
  as the truncated Takeuchi series `∑_{k=0}^{n} (uε - id)^k` in the convolution algebra.
* `HopfAlgebra.ofGradedConnected`: every connected graded bialgebra is a Hopf algebra.

## TODO

* Show that `takeuchiAntipode` is a graded map.

## References

* [Grinberg, D. and Reiner, V., *Hopf Algebras in Combinatorics*][GrinbergReiner2020],
  Proposition 1.4.16 (existence) and Proposition 1.4.24 (Takeuchi's formula).
-/

public section

namespace HopfAlgebra

open Coalgebra DirectSum LinearMap TensorProduct WithConv

variable {R A : Type*} [CommSemiring R] [Ring A] [Bialgebra R A]

/-! ### The truncated Takeuchi series in `WithConv` -/

/-- The truncated Takeuchi series `∑ k ≤ N, (uε - id)^k` in the convolution algebra
`WithConv (A →ₗ[R] A)`; for a connected grading `𝒜 : ℕ → Submodule R A` it computes the
antipode on `𝒜 N` (see `HopfAlgebra.takeuchiAntipode`). -/
noncomputable def takeuchiSeries (N : ℕ) : WithConv (A →ₗ[R] A) :=
  ∑ k ∈ Finset.range (N + 1), (1 - toConv LinearMap.id) ^ k

lemma takeuchiSeries_mul_toConv_id (N : ℕ) :
    (takeuchiSeries N : WithConv (A →ₗ[R] A)) * toConv LinearMap.id =
      1 - (1 - toConv LinearMap.id) ^ (N + 1) := by
  rw [takeuchiSeries]
  nth_rw 2 [← sub_sub_cancel 1 (toConv LinearMap.id)]
  exact geom_sum_mul_neg _ _

lemma toConv_id_mul_takeuchiSeries (N : ℕ) :
    (toConv LinearMap.id : WithConv (A →ₗ[R] A)) * takeuchiSeries N =
      1 - (1 - toConv LinearMap.id) ^ (N + 1) := by
  rw [takeuchiSeries]
  nth_rw 1 [← sub_sub_cancel 1 (toConv LinearMap.id)]
  exact mul_neg_geom_sum _ _

variable (𝒜 : ℕ → Submodule R A)

/-! ### Vanishing of convolution powers -/

section
variable [SetLike.GradedComul 𝒜] {m k : ℕ} {x : A}

/-- If `f` vanishes on the degree-zero part, then `f ^ k` vanishes on `𝒜 m` for `m < k`. -/
lemma convPow_apply_eq_zero_of_lt {f : WithConv (A →ₗ[R] A)} (hf : ∀ a ∈ 𝒜 0, f.ofConv a = 0)
    (hmk : m < k) (hx : x ∈ 𝒜 m) : (f ^ k).ofConv x = 0 := by
  induction k generalizing m x with
  | zero => omega
  | succ k' ih =>
    rw [pow_succ', convMul_apply]
    refine (Submodule.mem_bot R).mp <| SetLike.map_comul_mem
        (mul' R A ∘ₗ TensorProduct.map f.ofConv ((f ^ k').ofConv))
        (fun p q hpq a ha b hb ↦ ?_) hx
    rw [Submodule.mem_bot, comp_apply, TensorProduct.map_tmul, mul'_apply]
    obtain rfl | hp := Nat.eq_zero_or_pos p
    · rw [hf a ha, zero_mul]
    · rw [ih (show q < k' by omega) hb, mul_zero]

variable [GradedAlgebra.IsConnected 𝒜]

/-- The summand `(uε - id) ^ k` of the Takeuchi series vanishes on `𝒜 m` for `m < k`. The case
`k = 1` is connectedness. -/
lemma takeuchiSeries_summand_apply_eq_zero_of_lt (hmk : m < k) (hx : x ∈ 𝒜 m) :
    ((1 - toConv LinearMap.id : WithConv (A →ₗ[R] A)) ^ k).ofConv x = 0 :=
  convPow_apply_eq_zero_of_lt 𝒜 (fun a ha ↦ by
    rw [ofConv_sub, LinearMap.sub_apply, convOne_apply, ofConv_toConv, LinearMap.id_apply,
      Algebra.algebraMap_eq_smul_one, ← GradedAlgebra.IsConnected.eq_counit_smul_one 𝒜 ha,
      sub_self]) hmk hx

end

/-! ### The Takeuchi antipode -/

section
variable [DirectSum.Decomposition 𝒜] {m : ℕ} {a : A}

/-- The Takeuchi antipode: on `𝒜 n` it equals `(takeuchiSeries n).ofConv`, extended to all of
`A` via the direct-sum decomposition `A ≃ ⨁ n, 𝒜 n`. -/
noncomputable def takeuchiAntipode : A →ₗ[R] A :=
  toModule R ℕ A (fun n ↦ (takeuchiSeries n).ofConv ∘ₗ (𝒜 n).subtype) ∘ₗ
    (decomposeLinearEquiv 𝒜).toLinearMap

/-- On `𝒜 m`, the antipode equals `(takeuchiSeries m).ofConv`. -/
lemma takeuchiAntipode_apply_of_mem (ha : a ∈ 𝒜 m) :
    takeuchiAntipode 𝒜 a = (takeuchiSeries (R := R) m).ofConv a := by
  simp [takeuchiAntipode, decomposeLinearEquiv_apply_coe (ℳ := 𝒜) m ⟨a, ha⟩]

variable [SetLike.GradedComul 𝒜] [GradedAlgebra.IsConnected 𝒜]

/-- On `𝒜 m`, the antipode equals `(takeuchiSeries N).ofConv` for any `N ≥ m`: the truncated
series stabilizes once `N ≥ m`, since its summands kill `𝒜 m` beyond degree `m`. -/
lemma takeuchiAntipode_apply_of_le {N : ℕ} (hmN : m ≤ N) (ha : a ∈ 𝒜 m) :
    takeuchiAntipode 𝒜 a = (takeuchiSeries (R := R) N).ofConv a := by
  simp only [takeuchiAntipode_apply_of_mem 𝒜 ha, takeuchiSeries, WithConv.ofConv_sum,
    LinearMap.sum_apply]
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hmN)) fun k _ hk ↦ ?_
  rw [Finset.mem_range, not_lt] at hk
  exact takeuchiSeries_summand_apply_eq_zero_of_lt 𝒜 (Nat.lt_of_succ_le hk) ha

/-- The Takeuchi antipode is a left convolution inverse of the identity map. -/
theorem toConv_takeuchiAntipode_mul_toConv_id :
    (toConv (takeuchiAntipode 𝒜) * toConv LinearMap.id : WithConv (A →ₗ[R] A)) = 1 :=
  congrArg toConv <| decompose_lhom_ext 𝒜 fun i ↦ LinearMap.ext fun a ↦ by
    simp only [comp_apply, Submodule.subtype_apply, Algebra.linearMap_apply]
    rw [SetLike.map_comul_congr
        (g := TensorProduct.map ((takeuchiSeries i).ofConv) LinearMap.id) a.2
        (fun p q hpq b hb c hc ↦ by
          simp [takeuchiAntipode_apply_of_le 𝒜 (show p ≤ i by omega) hb]),
      ← ofConv_toConv (LinearMap.id (M := A)), ← convMul_apply]
    simp [takeuchiSeries_mul_toConv_id, WithConv.ofConv_sub,
      takeuchiSeries_summand_apply_eq_zero_of_lt 𝒜 (Nat.lt_succ_self i) a.2]

/-- The Takeuchi antipode is a right convolution inverse of the identity map. -/
theorem toConv_id_mul_toConv_takeuchiAntipode :
    (toConv LinearMap.id * toConv (takeuchiAntipode 𝒜) : WithConv (A →ₗ[R] A)) = 1 :=
  congrArg toConv <| decompose_lhom_ext 𝒜 fun i ↦ LinearMap.ext fun a ↦ by
    simp only [comp_apply, Submodule.subtype_apply, Algebra.linearMap_apply]
    rw [SetLike.map_comul_congr
        (g := TensorProduct.map LinearMap.id ((takeuchiSeries i).ofConv)) a.2
        (fun p q hpq b hb c hc ↦ by
          simp [takeuchiAntipode_apply_of_le 𝒜 (show q ≤ i by omega) hc]),
      ← ofConv_toConv (LinearMap.id (M := A)), ← convMul_apply]
    simp [toConv_id_mul_takeuchiSeries, WithConv.ofConv_sub,
      takeuchiSeries_summand_apply_eq_zero_of_lt 𝒜 (Nat.lt_succ_self i) a.2]

/-- The Hopf algebra structure on a connected graded bialgebra, with antipode given by
Takeuchi's formula.

See note [reducible non-instances]. -/
noncomputable abbrev ofGradedConnected : HopfAlgebra R A where
  antipode := takeuchiAntipode 𝒜
  mul_antipode_rTensor_comul := congrArg WithConv.ofConv (toConv_takeuchiAntipode_mul_toConv_id 𝒜)
  mul_antipode_lTensor_comul := congrArg WithConv.ofConv (toConv_id_mul_toConv_takeuchiAntipode 𝒜)

end

end HopfAlgebra
