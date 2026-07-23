/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Bialgebra.Graded
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Graded connected bialgebras are Hopf algebras

Every connected graded bialgebra admits an antipode, given by Takeuchi's formula.

## Main declarations

* `HopfAlgebra.takeuchiAntipode`: the antipode of a connected graded bialgebra, defined on `𝒜 n`
  as the truncated Takeuchi series `∑_{k=0}^{n} (-(id - uε))^k` in the convolution algebra.
* `HopfAlgebra.ofGradedConnected`: every connected graded bialgebra is a Hopf algebra.

## TODO

* Show that `takeuchiAntipode` is a graded map.

## References

* [Grinberg, D. and Reiner, V., *Hopf Algebras in Combinatorics*][grinberg-reiner-2020],
  Proposition 1.4.16 (existence) and Proposition 1.4.24 (Takeuchi's formula).
-/

public section

namespace HopfAlgebra

open Coalgebra DirectSum LinearMap TensorProduct WithConv

variable {R A : Type*} [CommSemiring R] [Ring A] [Bialgebra R A]

/-! ### The Takeuchi element and its partial geometric series in `WithConv` -/

/-- The element `id - uε = toConv LinearMap.id - 1` of the convolution algebra
`WithConv (A →ₗ[R] A)`, whose convolution powers enter Takeuchi's antipode formula. -/
noncomputable def takeuchiF : WithConv (A →ₗ[R] A) := toConv LinearMap.id - 1

/-- The truncated Takeuchi series `∑ k ∈ Finset.range (N + 1), (-takeuchiF) ^ k` in
`WithConv (A →ₗ[R] A)`. -/
noncomputable def takeuchiT (N : ℕ) : WithConv (A →ₗ[R] A) :=
  ∑ k ∈ Finset.range (N + 1), (-takeuchiF) ^ k

private lemma toConv_id_eq : (toConv LinearMap.id : WithConv (A →ₗ[R] A)) = 1 - -takeuchiF := by
  unfold takeuchiF; abel

lemma takeuchiT_mul_id (N : ℕ) :
    (takeuchiT N : WithConv (A →ₗ[R] A)) * toConv LinearMap.id = 1 - (-takeuchiF) ^ (N + 1) := by
  rw [takeuchiT, toConv_id_eq]; exact geom_sum_mul_neg _ _

lemma id_mul_takeuchiT (N : ℕ) :
    (toConv LinearMap.id : WithConv (A →ₗ[R] A)) * takeuchiT N = 1 - (-takeuchiF) ^ (N + 1) := by
  rw [takeuchiT, toConv_id_eq]; exact mul_neg_geom_sum _ _

/-! ### Local nilpotence: `(g^k).ofConv` annihilates `𝒜 m` for `m < k` -/

section LocalNilpotence

variable (𝒜 : ℕ → Submodule R A) [GradedCoalgebra 𝒜]

/-- If `g.ofConv` annihilates `𝒜 0`, then `g^k` annihilates `𝒜 m` for `m < k`. -/
private lemma convPow_apply_eq_zero_of_lt (g : WithConv (A →ₗ[R] A))
    (hg : ∀ x ∈ 𝒜 0, g.ofConv x = 0)
    {m k : ℕ} (hmk : m < k) {x : A} (hx : x ∈ 𝒜 m) :
    (g ^ k).ofConv x = 0 := by
  induction k generalizing m x with
  | zero => omega
  | succ k' ih =>
    rw [pow_succ', convMul_apply]
    suffices h : (TensorProduct.map g.ofConv (g^k').ofConv) (comul x) = 0 by
      rw [h, map_zero]
    refine (Submodule.mem_bot R).mp <|
      apply_mem_of_mem_bigradedPart 𝒜 _ ⊥ (fun p q hpq a ha b hb => ?_)
        (GradedCoalgebra.comul_mem hx)
    rw [Submodule.mem_bot, TensorProduct.map_tmul]
    obtain rfl | hp := Nat.eq_zero_or_pos p
    · rw [hg a ha, TensorProduct.zero_tmul]
    · rw [ih (show q < k' by omega) hb, TensorProduct.tmul_zero]

end LocalNilpotence

/-! ### The Takeuchi antipode and its axioms -/

section Connected

variable (𝒜 : ℕ → Submodule R A)

open Bialgebra

section
variable [GradedAlgebra.IsConnected 𝒜] [GradedCoalgebra 𝒜]

/-- `(-takeuchiF) ^ k` annihilates `𝒜 m` for `m < k`. The case `k = 1` is connectedness: the
Takeuchi element `id - uε` vanishes on `𝒜 0`. -/
private lemma neg_takeuchiF_pow_apply_of_mem {m k : ℕ} (hmk : m < k) {x : A} (hx : x ∈ 𝒜 m) :
    ((-takeuchiF (R := R)) ^ k).ofConv x = 0 := by
  refine convPow_apply_eq_zero_of_lt 𝒜 _ (fun x hx => ?_) hmk hx
  change -(x - algebraMap R A (counit x)) = 0
  rw [Algebra.algebraMap_eq_smul_one,
    ← GradedAlgebra.IsConnected.eq_counit_smul_one (𝒜 := 𝒜) hx, sub_self, neg_zero]

end

section
variable [DirectSum.Decomposition 𝒜]

/-- The Takeuchi antipode: on `𝒜 n` it equals `(takeuchiT n).ofConv`, extended to all of `A` via
the direct-sum decomposition `A ≃ ⨁ n, 𝒜 n`. -/
noncomputable def takeuchiAntipode : A →ₗ[R] A :=
  (toModule R ℕ A
    (fun n => ((takeuchiT n).ofConv).comp (𝒜 n).subtype)).comp
    (decomposeLinearEquiv 𝒜).toLinearMap

/-- On `𝒜 m`, the antipode equals `(takeuchiT m).ofConv`. -/
lemma takeuchiAntipode_apply_of_mem {m : ℕ} {a : A} (ha : a ∈ 𝒜 m) :
    takeuchiAntipode 𝒜 a = (takeuchiT (R := R) m).ofConv a := by
  simp [takeuchiAntipode, decomposeLinearEquiv_apply_coe (ℳ := 𝒜) m ⟨a, ha⟩]

end

section
variable [GradedAlgebra 𝒜] [GradedCoalgebra 𝒜] [GradedAlgebra.IsConnected 𝒜]

/-- On `𝒜 m`, the antipode equals `(takeuchiT N).ofConv` for any `N ≥ m`: the truncated series
stabilizes once `N ≥ m`, since `(-takeuchiF) ^ k` kills `𝒜 m` for every `k > m`. -/
private lemma takeuchiAntipode_apply_eq_takeuchiT_of_le {m N : ℕ} (hmN : m ≤ N)
    {a : A} (ha : a ∈ 𝒜 m) :
    takeuchiAntipode 𝒜 a = (takeuchiT (R := R) N).ofConv a := by
  simp only [takeuchiAntipode_apply_of_mem 𝒜 ha, takeuchiT, WithConv.ofConv_sum,
    LinearMap.sum_apply]
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hmN)) fun k _ hk => ?_
  rw [Finset.mem_range, not_lt] at hk
  exact neg_takeuchiF_pow_apply_of_mem 𝒜 (Nat.lt_of_succ_le hk) ha

/-- Agreement of the piecewise antipode and the uniform truncation on the image of `comul x`
via `rTensor` (controlling the left factor's degree). -/
private lemma takeuchiAntipode_rTensor_comul_eq {n : ℕ} {x : A} (hx : x ∈ 𝒜 n) :
    ((takeuchiAntipode 𝒜).rTensor A) (comul x) =
      (((takeuchiT n).ofConv).rTensor A) (comul x) := by
  refine sub_eq_zero.mp <| (Submodule.mem_bot R).mp <|
    apply_mem_of_mem_bigradedPart 𝒜
      ((takeuchiAntipode 𝒜).rTensor A - ((takeuchiT n).ofConv).rTensor A) ⊥
      (fun p q hpq a ha b hb => (Submodule.mem_bot R).mpr ?_) (GradedCoalgebra.comul_mem hx)
  simp [takeuchiAntipode_apply_eq_takeuchiT_of_le 𝒜 (show p ≤ n by omega) ha]

/-- Agreement on the image of `comul x` via `lTensor` (controlling the right factor's degree). -/
private lemma takeuchiAntipode_lTensor_comul_eq {n : ℕ} {x : A} (hx : x ∈ 𝒜 n) :
    ((takeuchiAntipode 𝒜).lTensor A) (comul x) =
      (((takeuchiT n).ofConv).lTensor A) (comul x) := by
  refine sub_eq_zero.mp <| (Submodule.mem_bot R).mp <|
    apply_mem_of_mem_bigradedPart 𝒜
      ((takeuchiAntipode 𝒜).lTensor A - ((takeuchiT n).ofConv).lTensor A) ⊥
      (fun p q hpq a ha b hb => (Submodule.mem_bot R).mpr ?_) (GradedCoalgebra.comul_mem hx)
  simp [takeuchiAntipode_apply_eq_takeuchiT_of_le 𝒜 (show q ≤ n by omega) hb]

/-- Right antipode axiom for `takeuchiAntipode`. -/
theorem takeuchiAntipode_mul_rTensor_comul :
    mul' R A ∘ₗ (takeuchiAntipode 𝒜).rTensor A ∘ₗ comul = Algebra.linearMap R A ∘ₗ counit := by
  ext x
  refine Decomposition.inductionOn (ℳ := 𝒜) ?_ ?_ ?_ x
  · simp
  · rintro i ⟨a, ha⟩
    change mul' R A (((takeuchiAntipode 𝒜).rTensor A) (comul a)) = algebraMap R A (counit a)
    rw [takeuchiAntipode_rTensor_comul_eq 𝒜 ha]
    change ((takeuchiT i * toConv LinearMap.id :
      WithConv (A →ₗ[R] A))).ofConv a = algebraMap R A (counit a)
    rw [takeuchiT_mul_id, WithConv.ofConv_sub, LinearMap.sub_apply,
      neg_takeuchiF_pow_apply_of_mem 𝒜 (Nat.lt_succ_self i) ha, sub_zero, convOne_apply]
  · intro y₁ y₂ h₁ h₂
    simp only [comp_apply, map_add, h₁, h₂]

/-- Left antipode axiom for `takeuchiAntipode`. -/
theorem takeuchiAntipode_mul_lTensor_comul :
    mul' R A ∘ₗ (takeuchiAntipode 𝒜).lTensor A ∘ₗ comul = Algebra.linearMap R A ∘ₗ counit := by
  ext x
  refine Decomposition.inductionOn (ℳ := 𝒜) ?_ ?_ ?_ x
  · simp
  · rintro i ⟨a, ha⟩
    change mul' R A (((takeuchiAntipode 𝒜).lTensor A) (comul a)) = algebraMap R A (counit a)
    rw [takeuchiAntipode_lTensor_comul_eq 𝒜 ha]
    change ((toConv LinearMap.id * takeuchiT i :
      WithConv (A →ₗ[R] A))).ofConv a = algebraMap R A (counit a)
    rw [id_mul_takeuchiT, WithConv.ofConv_sub, LinearMap.sub_apply,
      neg_takeuchiF_pow_apply_of_mem 𝒜 (Nat.lt_succ_self i) ha, sub_zero, convOne_apply]
  · intro y₁ y₂ h₁ h₂
    simp only [comp_apply, map_add, h₁, h₂]

/-! ### Assembling the Hopf algebra structure -/

/-- Every connected graded bialgebra carries a Hopf algebra structure, with antipode given by
Takeuchi's formula. -/
noncomputable abbrev ofGradedConnected : HopfAlgebra R A where
  antipode := takeuchiAntipode 𝒜
  mul_antipode_rTensor_comul := takeuchiAntipode_mul_rTensor_comul 𝒜
  mul_antipode_lTensor_comul := takeuchiAntipode_mul_lTensor_comul 𝒜

end

end Connected

end HopfAlgebra
