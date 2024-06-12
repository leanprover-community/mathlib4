/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Ideal.LocalRing


#align_import ring_theory.power_series.basic from "leanprover-community/mathlib"@"2d5739b61641ee4e7e53eca5688a08f66f2e6a60"

/-!
# Formal (multivariate) power series - Inverses

This file defines multivariate formal power series and develops the basic
properties of these objects, when it comes about multiplicative inverses.

For `φ : MvPowerSeries σ R` and `u : Rˣ` is the constant coefficient of `φ`,
`MvPowerSeries.invOfUnit φ u` is a formal power series such,
and `MvPowerSeries.mul_invOfUnit` proves that `φ * invOfUnit φ u = 1`.
The construction of the power series `invOfUnit` is done by writing that
relation and solving and for its coefficients by induction.

Over a field, all power series `φ` have an “inverse” `MvPowerSeries.inv φ`,
which is `0` if and only if the constant coefficient of `φ` is zero
(by `MvPowerSeries.inv_eq_zero`),
and `MvPowerSeries.mul_inv_cancel` asserts the equality `φ * φ⁻¹ = 1` when
the constant coefficient of `φ` is nonzero.

Instances are defined:

* Formal power series over a local ring form a local ring.
* The morphism `MvPowerSeries.map σ f : MvPowerSeries σ A →* MvPowerSeries σ B`
  induced by a local morphism `f : A →+* B` (`IsLocalRingHom f`)
  of commutative rings is a *local* morphism.

-/


noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

section Ring

variable [Ring R]

/-
The inverse of a multivariate formal power series is defined by
well-founded recursion on the coefficients of the inverse.
-/
/-- Auxiliary definition that unifies
 the totalised inverse formal power series `(_)⁻¹` and
 the inverse formal power series that depends on
 an inverse of the constant coefficient `invOfUnit`. -/
protected noncomputable def inv.aux (a : R) (φ : MvPowerSeries σ R) : MvPowerSeries σ R
  | n =>
    letI := Classical.decEq σ
    if n = 0 then a
    else
      -a *
        ∑ x ∈ antidiagonal n, if _ : x.2 < n then coeff R x.1 φ * inv.aux a φ x.2 else 0
termination_by n => n
#align mv_power_series.inv.aux MvPowerSeries.inv.aux

theorem coeff_inv_aux [DecidableEq σ] (n : σ →₀ ℕ) (a : R) (φ : MvPowerSeries σ R) :
    coeff R n (inv.aux a φ) =
      if n = 0 then a
      else
        -a *
          ∑ x ∈ antidiagonal n, if x.2 < n then coeff R x.1 φ * coeff R x.2 (inv.aux a φ) else 0 :=
  show inv.aux a φ n = _ by
    cases Subsingleton.elim ‹DecidableEq σ› (Classical.decEq σ)
    rw [inv.aux]
    rfl
#align mv_power_series.coeff_inv_aux MvPowerSeries.coeff_inv_aux

/-- A multivariate formal power series is invertible if the constant coefficient is invertible. -/
def invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) : MvPowerSeries σ R :=
  inv.aux (↑u⁻¹) φ
#align mv_power_series.inv_of_unit MvPowerSeries.invOfUnit

theorem coeff_invOfUnit [DecidableEq σ] (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (u : Rˣ) :
    coeff R n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff R x.1 φ * coeff R x.2 (invOfUnit φ u) else 0 := by
  convert coeff_inv_aux n (↑u⁻¹) φ
#align mv_power_series.coeff_inv_of_unit MvPowerSeries.coeff_invOfUnit

@[simp]
theorem constantCoeff_invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) :
    constantCoeff σ R (invOfUnit φ u) = ↑u⁻¹ := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invOfUnit, if_pos rfl]
#align mv_power_series.constant_coeff_inv_of_unit MvPowerSeries.constantCoeff_invOfUnit

theorem mul_invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff σ R φ = u) :
    φ * invOfUnit φ u = 1 :=
  ext fun n =>
    letI := Classical.decEq (σ →₀ ℕ)
    if H : n = 0 then by
      rw [H]
      simp [coeff_mul, support_single_ne_zero, h]
    else by
      classical
      have : ((0 : σ →₀ ℕ), n) ∈ antidiagonal n := by rw [mem_antidiagonal, zero_add]
      rw [coeff_one, if_neg H, coeff_mul, ← Finset.insert_erase this,
        Finset.sum_insert (Finset.not_mem_erase _ _), coeff_zero_eq_constantCoeff_apply, h,
        coeff_invOfUnit, if_neg H, neg_mul, mul_neg, Units.mul_inv_cancel_left, ←
        Finset.insert_erase this, Finset.sum_insert (Finset.not_mem_erase _ _),
        Finset.insert_erase this, if_neg (not_lt_of_ge <| le_rfl), zero_add, add_comm, ←
        sub_eq_add_neg, sub_eq_zero, Finset.sum_congr rfl]
      rintro ⟨i, j⟩ hij
      rw [Finset.mem_erase, mem_antidiagonal] at hij
      cases' hij with h₁ h₂
      subst n
      rw [if_pos]
      suffices (0 : _) + j < i + j by simpa
      apply add_lt_add_right
      constructor
      · intro s
        exact Nat.zero_le _
      · intro H
        apply h₁
        suffices i = 0 by simp [this]
        ext1 s
        exact Nat.eq_zero_of_le_zero (H s)
#align mv_power_series.mul_inv_of_unit MvPowerSeries.mul_invOfUnit

end Ring

section CommRing

variable [CommRing R]

/-- Multivariate formal power series over a local ring form a local ring. -/
instance [LocalRing R] : LocalRing (MvPowerSeries σ R) :=
  LocalRing.of_isUnit_or_isUnit_one_sub_self <| by
    intro φ
    rcases LocalRing.isUnit_or_isUnit_one_sub_self (constantCoeff σ R φ) with (⟨u, h⟩ | ⟨u, h⟩) <;>
        [left; right] <;>
      · refine isUnit_of_mul_eq_one _ _ (mul_invOfUnit _ u ?_)
        simpa using h.symm

-- TODO(jmc): once adic topology lands, show that this is complete
end CommRing

section LocalRing

variable {S : Type*} [CommRing R] [CommRing S] (f : R →+* S) [IsLocalRingHom f]

-- Thanks to the linter for informing us that this instance does
-- not actually need R and S to be local rings!
/-- The map between multivariate formal power series over the same indexing set
 induced by a local ring hom `A → B` is local -/
instance map.isLocalRingHom : IsLocalRingHom (map σ f) :=
  ⟨by
    rintro φ ⟨ψ, h⟩
    replace h := congr_arg (constantCoeff σ S) h
    rw [constantCoeff_map] at h
    have : IsUnit (constantCoeff σ S ↑ψ) := isUnit_constantCoeff (↑ψ) ψ.isUnit
    rw [h] at this
    rcases isUnit_of_map_unit f _ this with ⟨c, hc⟩
    exact isUnit_of_mul_eq_one φ (invOfUnit φ c) (mul_invOfUnit φ c hc.symm)⟩
#align mv_power_series.map.is_local_ring_hom MvPowerSeries.map.isLocalRingHom

end LocalRing

section Field

variable {k : Type*} [Field k]

/-- The inverse `1/f` of a multivariable power series `f` over a field -/
protected def inv (φ : MvPowerSeries σ k) : MvPowerSeries σ k :=
  inv.aux (constantCoeff σ k φ)⁻¹ φ
#align mv_power_series.inv MvPowerSeries.inv

instance : Inv (MvPowerSeries σ k) :=
  ⟨MvPowerSeries.inv⟩

theorem coeff_inv [DecidableEq σ] (n : σ →₀ ℕ) (φ : MvPowerSeries σ k) :
    coeff k n φ⁻¹ =
      if n = 0 then (constantCoeff σ k φ)⁻¹
      else
        -(constantCoeff σ k φ)⁻¹ *
          ∑ x ∈ antidiagonal n, if x.2 < n then coeff k x.1 φ * coeff k x.2 φ⁻¹ else 0 :=
  coeff_inv_aux n _ φ
#align mv_power_series.coeff_inv MvPowerSeries.coeff_inv

@[simp]
theorem constantCoeff_inv (φ : MvPowerSeries σ k) :
    constantCoeff σ k φ⁻¹ = (constantCoeff σ k φ)⁻¹ := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_inv, if_pos rfl]
#align mv_power_series.constant_coeff_inv MvPowerSeries.constantCoeff_inv

theorem inv_eq_zero {φ : MvPowerSeries σ k} : φ⁻¹ = 0 ↔ constantCoeff σ k φ = 0 :=
  ⟨fun h => by simpa using congr_arg (constantCoeff σ k) h, fun h =>
    ext fun n => by
      classical
      rw [coeff_inv]
      split_ifs <;>
        simp only [h, map_zero, zero_mul, inv_zero, neg_zero]⟩
#align mv_power_series.inv_eq_zero MvPowerSeries.inv_eq_zero

@[simp]
theorem zero_inv : (0 : MvPowerSeries σ k)⁻¹ = 0 := by
  rw [inv_eq_zero, constantCoeff_zero]
#align mv_power_series.zero_inv MvPowerSeries.zero_inv

-- Porting note (#10618): simp can prove this.
-- @[simp]
theorem invOfUnit_eq (φ : MvPowerSeries σ k) (h : constantCoeff σ k φ ≠ 0) :
    invOfUnit φ (Units.mk0 _ h) = φ⁻¹ :=
  rfl
#align mv_power_series.inv_of_unit_eq MvPowerSeries.invOfUnit_eq

@[simp]
theorem invOfUnit_eq' (φ : MvPowerSeries σ k) (u : Units k) (h : constantCoeff σ k φ = u) :
    invOfUnit φ u = φ⁻¹ := by
  rw [← invOfUnit_eq φ (h.symm ▸ u.ne_zero)]
  apply congrArg (invOfUnit φ)
  rw [Units.ext_iff]
  exact h.symm
#align mv_power_series.inv_of_unit_eq' MvPowerSeries.invOfUnit_eq'

@[simp]
protected theorem mul_inv_cancel (φ : MvPowerSeries σ k) (h : constantCoeff σ k φ ≠ 0) :
    φ * φ⁻¹ = 1 := by rw [← invOfUnit_eq φ h, mul_invOfUnit φ (Units.mk0 _ h) rfl]
#align mv_power_series.mul_inv_cancel MvPowerSeries.mul_inv_cancel

@[simp]
protected theorem inv_mul_cancel (φ : MvPowerSeries σ k) (h : constantCoeff σ k φ ≠ 0) :
    φ⁻¹ * φ = 1 := by rw [mul_comm, φ.mul_inv_cancel h]
#align mv_power_series.inv_mul_cancel MvPowerSeries.inv_mul_cancel

protected theorem eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : MvPowerSeries σ k}
    (h : constantCoeff σ k φ₃ ≠ 0) : φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂ :=
  ⟨fun k => by simp [k, mul_assoc, MvPowerSeries.inv_mul_cancel _ h], fun k => by
    simp [← k, mul_assoc, MvPowerSeries.mul_inv_cancel _ h]⟩
#align mv_power_series.eq_mul_inv_iff_mul_eq MvPowerSeries.eq_mul_inv_iff_mul_eq

protected theorem eq_inv_iff_mul_eq_one {φ ψ : MvPowerSeries σ k} (h : constantCoeff σ k ψ ≠ 0) :
    φ = ψ⁻¹ ↔ φ * ψ = 1 := by rw [← MvPowerSeries.eq_mul_inv_iff_mul_eq h, one_mul]
#align mv_power_series.eq_inv_iff_mul_eq_one MvPowerSeries.eq_inv_iff_mul_eq_one

protected theorem inv_eq_iff_mul_eq_one {φ ψ : MvPowerSeries σ k} (h : constantCoeff σ k ψ ≠ 0) :
    ψ⁻¹ = φ ↔ φ * ψ = 1 := by rw [eq_comm, MvPowerSeries.eq_inv_iff_mul_eq_one h]
#align mv_power_series.inv_eq_iff_mul_eq_one MvPowerSeries.inv_eq_iff_mul_eq_one

@[simp]
protected theorem mul_inv_rev (φ ψ : MvPowerSeries σ k) :
    (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹ := by
  by_cases h : constantCoeff σ k (φ * ψ) = 0
  · rw [inv_eq_zero.mpr h]
    simp only [map_mul, mul_eq_zero] at h
    -- we don't have `NoZeroDivisors (MvPowerSeries σ k)` yet,
    cases' h with h h <;> simp [inv_eq_zero.mpr h]
  · rw [MvPowerSeries.inv_eq_iff_mul_eq_one h]
    simp only [not_or, map_mul, mul_eq_zero] at h
    rw [← mul_assoc, mul_assoc _⁻¹, MvPowerSeries.inv_mul_cancel _ h.left, mul_one,
      MvPowerSeries.inv_mul_cancel _ h.right]
#align mv_power_series.mul_inv_rev MvPowerSeries.mul_inv_rev

instance : InvOneClass (MvPowerSeries σ k) :=
  { inferInstanceAs (One (MvPowerSeries σ k)),
    inferInstanceAs (Inv (MvPowerSeries σ k)) with
    inv_one := by
      rw [MvPowerSeries.inv_eq_iff_mul_eq_one, mul_one]
      simp }

@[simp]
theorem C_inv (r : k) : (C σ k r)⁻¹ = C σ k r⁻¹ := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one, ← map_mul, inv_mul_cancel hr, map_one]
  simpa using hr
set_option linter.uppercaseLean3 false in
#align mv_power_series.C_inv MvPowerSeries.C_inv

@[simp]
theorem X_inv (s : σ) : (X s : MvPowerSeries σ k)⁻¹ = 0 := by
  rw [inv_eq_zero, constantCoeff_X]
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_inv MvPowerSeries.X_inv

@[simp]
theorem smul_inv (r : k) (φ : MvPowerSeries σ k) : (r • φ)⁻¹ = r⁻¹ • φ⁻¹ := by
  simp [smul_eq_C_mul, mul_comm]
#align mv_power_series.smul_inv MvPowerSeries.smul_inv

end Field

end MvPowerSeries

end
