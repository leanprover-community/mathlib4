/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.NumberTheory.Padics.MahlerBasis

/-!
# Additive characters of `ℤ_[p]`

We show that for any normed `ℤ_[p]`-algebra `R`, there is a canonical bijection between continuous
additive characters `ℤ_[p] → R` and topologically nilpotent elements of `R`, given by sending `κ`
to the element `κ 1 - 1`. This is used to define the Mahler transform for `p`-adic measures.

Note that if the norm on `R` is not strictly multiplicative, then the condition that `κ 1 - 1` be
topologically nilpotent is strictly weaker than assuming `‖κ 1 - 1‖ < 1`, although they are of
course equivalent if `NormMulClass R` holds.
-/

open scoped fwdDiff
open Filter Topology

lemma fwdDiff_addChar_eq {M R : Type*} [AddCommMonoid M] [Ring R]
    (φ : AddChar M R) (x h : M) (n : ℕ) : Δ_[h]^[n] φ x = (φ h - 1) ^ n * φ x := by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    simp only [pow_succ, Function.iterate_succ_apply', fwdDiff, IH, ← mul_sub, mul_assoc]
    rw [sub_mul, ← AddChar.map_add_eq_mul, add_comm h x, one_mul]

variable {p : ℕ} [Fact p.Prime]

/-- If two continuous additive characters of `ℤ_[p]` agree at 1, they agree everwhere. -/
lemma AddChar.eq_of_apply_one_eq {M : Type*} [Monoid M] [TopologicalSpace M] [T2Space M]
    {κ₁ κ₂ : AddChar ℤ_[p] M} (hκ₁ : Continuous κ₁) (hκ₂ : Continuous κ₂) (h : κ₁ 1 = κ₂ 1) :
    κ₁ = κ₂ := by
  refine DFunLike.coe_injective <| PadicInt.denseRange_natCast.equalizer hκ₁ hκ₂ (funext fun n ↦ ?_)
  simp only [Function.comp_apply, ← nsmul_one, h, AddChar.map_nsmul_eq_pow]

variable {R : Type*} [NormedRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
  [IsUltrametricDist R]

lemma AddChar.tendsto_apply_one_sub_pow {κ : AddChar ℤ_[p] R} (hκ : Continuous κ) :
    Tendsto (fun n ↦ (κ 1 - 1) ^ n) atTop (𝓝 0) := by
  refine (PadicInt.fwdDiff_tendsto_zero ⟨κ, hκ⟩).congr fun n ↦ ?_
  simpa only [AddChar.map_zero_eq_one, mul_one] using fwdDiff_addChar_eq κ 0 1 n

namespace PadicInt
variable [CompleteSpace R]

/-- The unique continuous additive character of `ℤ_[p]` mapping `1` to `1 + r`. -/
noncomputable def addChar_of_value_at_one (r : R) (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    AddChar ℤ_[p] R where
  toFun := mahlerSeries (r ^ ·)
  map_zero_eq_one' := by
    rw [← Nat.cast_zero, mahlerSeries_apply_nat hr le_rfl, zero_add, Finset.sum_range_one,
      Nat.choose_self, pow_zero, one_smul]
  map_add_eq_mul' a b := by
    let F : C(ℤ_[p], R) := mahlerSeries (r ^ ·)
    show F (a + b) = F a * F b
    -- It is fiddly to show directly that `F (a + b) = F a * F b` for general `a, b`,
    -- so we prove it for `a, b ∈ ℕ` directly, and then deduce it for all `a, b` by continuity.
    have hF (n : ℕ) : F n = (r + 1) ^ n := by
      rw [mahlerSeries_apply_nat hr le_rfl, (Commute.one_right _).add_pow]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [one_pow, mul_one, nsmul_eq_mul, Nat.cast_comm]
    refine congr_fun ((denseRange_natCast.prodMap denseRange_natCast).equalizer
      ((map_continuous F).comp continuous_add)
      (continuous_mul.comp (map_continuous <| F.prodMap F)) (funext fun ⟨m, n⟩ ↦ ?_)) (a, b)
    simp [← Nat.cast_add, hF, ContinuousMap.prodMap_apply, pow_add]

lemma continuous_addChar_of_value_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    Continuous (addChar_of_value_at_one r hr : ℤ_[p] → R) :=
  map_continuous (mahlerSeries (r ^ ·))

lemma coe_addChar_of_value_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    (addChar_of_value_at_one r hr : ℤ_[p] → R) = mahlerSeries (r ^ ·) :=
  rfl

lemma addChar_of_value_at_one_def {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    addChar_of_value_at_one r hr (1 : ℤ_[p]) = 1 + r := by
  show mahlerSeries (r ^ ·) ↑(1 : ℕ) = _
  rw [mahlerSeries_apply_nat hr le_rfl, Finset.sum_range_succ, Finset.sum_range_one,
    Nat.choose_zero_right, Nat.choose_self, one_smul, one_smul, pow_zero, pow_one]

variable (p R) in
/-- Equivalence between continuous additive characters `ℤ_[p] → R`, and `r ∈ R` with `r ^ n → 0`. -/
noncomputable def continuousAddCharEquiv :
    {κ : AddChar ℤ_[p] R // Continuous κ} ≃ {r : R // Tendsto (r ^ ·) atTop (𝓝 0)} where
  toFun := fun ⟨κ, hκ⟩ ↦ ⟨κ 1 - 1, κ.tendsto_apply_one_sub_pow hκ⟩
  invFun := fun ⟨r, hr⟩ ↦ ⟨_, continuous_addChar_of_value_at_one hr⟩
  left_inv := fun ⟨κ, hκ⟩ ↦ by
    apply Subtype.coe_injective
    apply AddChar.eq_of_apply_one_eq (continuous_addChar_of_value_at_one _) hκ
    rw [addChar_of_value_at_one_def (κ.tendsto_apply_one_sub_pow hκ), add_sub_cancel]
  right_inv := fun ⟨r, hr⟩ ↦ by simp [addChar_of_value_at_one_def hr]

@[simp] lemma continuousAddCharEquiv_apply {κ : AddChar ℤ_[p] R} (hκ : Continuous κ) :
    continuousAddCharEquiv p R ⟨κ, hκ⟩ = κ 1 - 1 :=
  rfl

@[simp] lemma continuousAddCharEquiv_symm_apply {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    (continuousAddCharEquiv p R).symm ⟨r, hr⟩ =
    (addChar_of_value_at_one r hr : AddChar ℤ_[p] R) :=
  rfl

end PadicInt
