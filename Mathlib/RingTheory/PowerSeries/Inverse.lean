/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse

#align_import ring_theory.power_series.basic from "leanprover-community/mathlib"@"2d5739b61641ee4e7e53eca5688a08f66f2e6a60"

/-! # Formal power series - Inverses

If the constant coefficient of a formal (univariate) power series is invertible,
then this formal power series is invertible.
(See the discussion in `Mathlib.RingTheory.MvPowerSeries.Inverse` for
the construction.)

Formal (univariate) power series over a local ring form a local ring.


-/


noncomputable section

open BigOperators Polynomial

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}


section Ring

variable [Ring R]

/-- Auxiliary function used for computing inverse of a power series -/
protected def inv.aux : R → R⟦X⟧ → R⟦X⟧ :=
  MvPowerSeries.inv.aux
#align power_series.inv.aux PowerSeries.inv.aux

theorem coeff_inv_aux (n : ℕ) (a : R) (φ : R⟦X⟧) :
    coeff R n (inv.aux a φ) =
      if n = 0 then a
      else
        -a *
          ∑ x in antidiagonal n,
            if x.2 < n then coeff R x.1 φ * coeff R x.2 (inv.aux a φ) else 0 := by
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [coeff, inv.aux, MvPowerSeries.coeff_inv_aux]
  simp only [Finsupp.single_eq_zero]
  split_ifs; · rfl
  congr 1
  symm
  apply Finset.sum_nbij' (fun (a, b) ↦ (single () a, single () b))
    fun (f, g) ↦ (f (), g ())
  · aesop
  · aesop
  · aesop
  · aesop
  · rintro ⟨i, j⟩ _hij
    obtain H | H := le_or_lt n j
    · aesop
    rw [if_pos H, if_pos]
    · rfl
    refine ⟨?_, fun hh ↦ H.not_le ?_⟩
    · rintro ⟨⟩
      simpa [Finsupp.single_eq_same] using le_of_lt H
    · simpa [Finsupp.single_eq_same] using hh ()
#align power_series.coeff_inv_aux PowerSeries.coeff_inv_aux

/-- A formal power series is invertible if the constant coefficient is invertible.-/
def invOfUnit (φ : R⟦X⟧) (u : Rˣ) : R⟦X⟧ :=
  MvPowerSeries.invOfUnit φ u
#align power_series.inv_of_unit PowerSeries.invOfUnit

theorem coeff_invOfUnit (n : ℕ) (φ : R⟦X⟧) (u : Rˣ) :
    coeff R n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ *
          ∑ x in antidiagonal n,
            if x.2 < n then coeff R x.1 φ * coeff R x.2 (invOfUnit φ u) else 0 :=
  coeff_inv_aux n (↑u⁻¹ : R) φ
#align power_series.coeff_inv_of_unit PowerSeries.coeff_invOfUnit

@[simp]
theorem constantCoeff_invOfUnit (φ : R⟦X⟧) (u : Rˣ) :
    constantCoeff R (invOfUnit φ u) = ↑u⁻¹ := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invOfUnit, if_pos rfl]
#align power_series.constant_coeff_inv_of_unit PowerSeries.constantCoeff_invOfUnit

theorem mul_invOfUnit (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff R φ = u) :
    φ * invOfUnit φ u = 1 :=
  MvPowerSeries.mul_invOfUnit φ u <| h
#align power_series.mul_inv_of_unit PowerSeries.mul_invOfUnit

/-- Two ways of removing the constant coefficient of a power series are the same. -/
theorem sub_const_eq_shift_mul_X (φ : R⟦X⟧) :
    φ - C R (constantCoeff R φ) = (PowerSeries.mk fun p => coeff R (p + 1) φ) * X :=
  sub_eq_iff_eq_add.mpr (eq_shift_mul_X_add_const φ)
set_option linter.uppercaseLean3 false in
#align power_series.sub_const_eq_shift_mul_X PowerSeries.sub_const_eq_shift_mul_X

theorem sub_const_eq_X_mul_shift (φ : R⟦X⟧) :
    φ - C R (constantCoeff R φ) = X * PowerSeries.mk fun p => coeff R (p + 1) φ :=
  sub_eq_iff_eq_add.mpr (eq_X_mul_shift_add_const φ)
set_option linter.uppercaseLean3 false in
#align power_series.sub_const_eq_X_mul_shift PowerSeries.sub_const_eq_X_mul_shift

end Ring

section Field

variable {k : Type*} [Field k]

/-- The inverse 1/f of a power series f defined over a field -/
protected def inv : PowerSeries k → PowerSeries k :=
  MvPowerSeries.inv
#align power_series.inv PowerSeries.inv

instance : Inv (PowerSeries k) :=
  ⟨PowerSeries.inv⟩

theorem inv_eq_inv_aux (φ : PowerSeries k) : φ⁻¹ = inv.aux (constantCoeff k φ)⁻¹ φ :=
  rfl
#align power_series.inv_eq_inv_aux PowerSeries.inv_eq_inv_aux

theorem coeff_inv (n) (φ : PowerSeries k) :
    coeff k n φ⁻¹ =
      if n = 0 then (constantCoeff k φ)⁻¹
      else
        -(constantCoeff k φ)⁻¹ *
          ∑ x in antidiagonal n,
            if x.2 < n then coeff k x.1 φ * coeff k x.2 φ⁻¹ else 0 :=
  by rw [inv_eq_inv_aux, coeff_inv_aux n (constantCoeff k φ)⁻¹ φ]
#align power_series.coeff_inv PowerSeries.coeff_inv

@[simp]
theorem constantCoeff_inv (φ : PowerSeries k) : constantCoeff k φ⁻¹ = (constantCoeff k φ)⁻¹ :=
  MvPowerSeries.constantCoeff_inv φ
#align power_series.constant_coeff_inv PowerSeries.constantCoeff_inv

theorem inv_eq_zero {φ : PowerSeries k} : φ⁻¹ = 0 ↔ constantCoeff k φ = 0 :=
  MvPowerSeries.inv_eq_zero
#align power_series.inv_eq_zero PowerSeries.inv_eq_zero

@[simp]
theorem zero_inv : (0 : PowerSeries k)⁻¹ = 0 :=
  MvPowerSeries.zero_inv
#align power_series.zero_inv PowerSeries.zero_inv

-- Porting note (#10618): simp can prove this.
-- @[simp]
theorem invOfUnit_eq (φ : PowerSeries k) (h : constantCoeff k φ ≠ 0) :
    invOfUnit φ (Units.mk0 _ h) = φ⁻¹ :=
  MvPowerSeries.invOfUnit_eq _ _
#align power_series.inv_of_unit_eq PowerSeries.invOfUnit_eq

@[simp]
theorem invOfUnit_eq' (φ : PowerSeries k) (u : Units k) (h : constantCoeff k φ = u) :
    invOfUnit φ u = φ⁻¹ :=
  MvPowerSeries.invOfUnit_eq' φ _ h
#align power_series.inv_of_unit_eq' PowerSeries.invOfUnit_eq'

@[simp]
protected theorem mul_inv_cancel (φ : PowerSeries k) (h : constantCoeff k φ ≠ 0) : φ * φ⁻¹ = 1 :=
  MvPowerSeries.mul_inv_cancel φ h
#align power_series.mul_inv_cancel PowerSeries.mul_inv_cancel

@[simp]
protected theorem inv_mul_cancel (φ : PowerSeries k) (h : constantCoeff k φ ≠ 0) : φ⁻¹ * φ = 1 :=
  MvPowerSeries.inv_mul_cancel φ h
#align power_series.inv_mul_cancel PowerSeries.inv_mul_cancel

theorem eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : PowerSeries k} (h : constantCoeff k φ₃ ≠ 0) :
    φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂ :=
  MvPowerSeries.eq_mul_inv_iff_mul_eq h
#align power_series.eq_mul_inv_iff_mul_eq PowerSeries.eq_mul_inv_iff_mul_eq

theorem eq_inv_iff_mul_eq_one {φ ψ : PowerSeries k} (h : constantCoeff k ψ ≠ 0) :
    φ = ψ⁻¹ ↔ φ * ψ = 1 :=
  MvPowerSeries.eq_inv_iff_mul_eq_one h
#align power_series.eq_inv_iff_mul_eq_one PowerSeries.eq_inv_iff_mul_eq_one

theorem inv_eq_iff_mul_eq_one {φ ψ : PowerSeries k} (h : constantCoeff k ψ ≠ 0) :
    ψ⁻¹ = φ ↔ φ * ψ = 1 :=
  MvPowerSeries.inv_eq_iff_mul_eq_one h
#align power_series.inv_eq_iff_mul_eq_one PowerSeries.inv_eq_iff_mul_eq_one

@[simp]
protected theorem mul_inv_rev (φ ψ : PowerSeries k) : (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹ :=
  MvPowerSeries.mul_inv_rev _ _
#align power_series.mul_inv_rev PowerSeries.mul_inv_rev

instance : InvOneClass (PowerSeries k) :=
  { inferInstanceAs <| InvOneClass <| MvPowerSeries Unit k with }

@[simp]
theorem C_inv (r : k) : (C k r)⁻¹ = C k r⁻¹ :=
  MvPowerSeries.C_inv _
set_option linter.uppercaseLean3 false in
#align power_series.C_inv PowerSeries.C_inv

@[simp]
theorem X_inv : (X : PowerSeries k)⁻¹ = 0 :=
  MvPowerSeries.X_inv _
set_option linter.uppercaseLean3 false in
#align power_series.X_inv PowerSeries.X_inv

@[simp]
theorem smul_inv (r : k) (φ : PowerSeries k) : (r • φ)⁻¹ = r⁻¹ • φ⁻¹ :=
  MvPowerSeries.smul_inv _ _
#align power_series.smul_inv PowerSeries.smul_inv

end Field

section LocalRing

variable {S : Type*} [CommRing R] [CommRing S] (f : R →+* S) [IsLocalRingHom f]

instance map.isLocalRingHom : IsLocalRingHom (map f) :=
  MvPowerSeries.map.isLocalRingHom f
#align power_series.map.is_local_ring_hom PowerSeries.map.isLocalRingHom

variable [LocalRing R] [LocalRing S]

instance : LocalRing R⟦X⟧ :=
  { inferInstanceAs <| LocalRing <| MvPowerSeries Unit R with }


end LocalRing


end PowerSeries

end
