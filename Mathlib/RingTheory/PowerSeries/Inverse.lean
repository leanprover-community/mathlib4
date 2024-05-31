/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Order



#align_import ring_theory.power_series.basic from "leanprover-community/mathlib"@"2d5739b61641ee4e7e53eca5688a08f66f2e6a60"

/-! # Formal power series - Inverses

If the constant coefficient of a formal (univariate) power series is invertible,
then this formal power series is invertible.
(See the discussion in `Mathlib.RingTheory.MvPowerSeries.Inverse` for
the construction.)

Formal (univariate) power series over a local ring form a local ring.

Formal (univariate) power series over a field form a discrete valuation ring, and a normalization
monoid. The definition `residueFieldOfPowerSeries` provides the isomorphism between the residue
field of `k⟦X⟧` and `k`, when `k` is a field.

-/


noncomputable section

open Polynomial

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
          ∑ x ∈ antidiagonal n,
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

/-- A formal power series is invertible if the constant coefficient is invertible. -/
def invOfUnit (φ : R⟦X⟧) (u : Rˣ) : R⟦X⟧ :=
  MvPowerSeries.invOfUnit φ u
#align power_series.inv_of_unit PowerSeries.invOfUnit

theorem coeff_invOfUnit (n : ℕ) (φ : R⟦X⟧) (u : Rˣ) :
    coeff R n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ *
          ∑ x ∈ antidiagonal n,
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
protected def inv : k⟦X⟧ → k⟦X⟧ :=
  MvPowerSeries.inv
#align power_series.inv PowerSeries.inv

instance : Inv k⟦X⟧ := ⟨PowerSeries.inv⟩

theorem inv_eq_inv_aux (φ : k⟦X⟧) : φ⁻¹ = inv.aux (constantCoeff k φ)⁻¹ φ :=
  rfl
#align power_series.inv_eq_inv_aux PowerSeries.inv_eq_inv_aux

theorem coeff_inv (n) (φ : k⟦X⟧) :
    coeff k n φ⁻¹ =
      if n = 0 then (constantCoeff k φ)⁻¹
      else
        -(constantCoeff k φ)⁻¹ *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff k x.1 φ * coeff k x.2 φ⁻¹ else 0 := by
  rw [inv_eq_inv_aux, coeff_inv_aux n (constantCoeff k φ)⁻¹ φ]
#align power_series.coeff_inv PowerSeries.coeff_inv

@[simp]
theorem constantCoeff_inv (φ : k⟦X⟧) : constantCoeff k φ⁻¹ = (constantCoeff k φ)⁻¹ :=
  MvPowerSeries.constantCoeff_inv φ
#align power_series.constant_coeff_inv PowerSeries.constantCoeff_inv

theorem inv_eq_zero {φ : k⟦X⟧} : φ⁻¹ = 0 ↔ constantCoeff k φ = 0 :=
  MvPowerSeries.inv_eq_zero
#align power_series.inv_eq_zero PowerSeries.inv_eq_zero

@[simp]
theorem zero_inv : (0 : k⟦X⟧)⁻¹ = 0 :=
  MvPowerSeries.zero_inv
#align power_series.zero_inv PowerSeries.zero_inv

-- Porting note (#10618): simp can prove this.
-- @[simp]
theorem invOfUnit_eq (φ : k⟦X⟧) (h : constantCoeff k φ ≠ 0) :
    invOfUnit φ (Units.mk0 _ h) = φ⁻¹ :=
  MvPowerSeries.invOfUnit_eq _ _
#align power_series.inv_of_unit_eq PowerSeries.invOfUnit_eq

@[simp]
theorem invOfUnit_eq' (φ : k⟦X⟧) (u : Units k) (h : constantCoeff k φ = u) :
    invOfUnit φ u = φ⁻¹ :=
  MvPowerSeries.invOfUnit_eq' φ _ h
#align power_series.inv_of_unit_eq' PowerSeries.invOfUnit_eq'

@[simp]
protected theorem mul_inv_cancel (φ : k⟦X⟧) (h : constantCoeff k φ ≠ 0) : φ * φ⁻¹ = 1 :=
  MvPowerSeries.mul_inv_cancel φ h
#align power_series.mul_inv_cancel PowerSeries.mul_inv_cancel

@[simp]
protected theorem inv_mul_cancel (φ : k⟦X⟧) (h : constantCoeff k φ ≠ 0) : φ⁻¹ * φ = 1 :=
  MvPowerSeries.inv_mul_cancel φ h
#align power_series.inv_mul_cancel PowerSeries.inv_mul_cancel

theorem eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : k⟦X⟧} (h : constantCoeff k φ₃ ≠ 0) :
    φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂ :=
  MvPowerSeries.eq_mul_inv_iff_mul_eq h
#align power_series.eq_mul_inv_iff_mul_eq PowerSeries.eq_mul_inv_iff_mul_eq

theorem eq_inv_iff_mul_eq_one {φ ψ : k⟦X⟧} (h : constantCoeff k ψ ≠ 0) :
    φ = ψ⁻¹ ↔ φ * ψ = 1 :=
  MvPowerSeries.eq_inv_iff_mul_eq_one h
#align power_series.eq_inv_iff_mul_eq_one PowerSeries.eq_inv_iff_mul_eq_one

theorem inv_eq_iff_mul_eq_one {φ ψ : k⟦X⟧} (h : constantCoeff k ψ ≠ 0) :
    ψ⁻¹ = φ ↔ φ * ψ = 1 :=
  MvPowerSeries.inv_eq_iff_mul_eq_one h
#align power_series.inv_eq_iff_mul_eq_one PowerSeries.inv_eq_iff_mul_eq_one

@[simp]
protected theorem mul_inv_rev (φ ψ : k⟦X⟧) : (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹ :=
  MvPowerSeries.mul_inv_rev _ _
#align power_series.mul_inv_rev PowerSeries.mul_inv_rev

instance : InvOneClass k⟦X⟧ :=
  { inferInstanceAs <| InvOneClass <| MvPowerSeries Unit k with }

@[simp]
theorem C_inv (r : k) : (C k r)⁻¹ = C k r⁻¹ :=
  MvPowerSeries.C_inv _
set_option linter.uppercaseLean3 false in
#align power_series.C_inv PowerSeries.C_inv

@[simp]
theorem X_inv : (X : k⟦X⟧)⁻¹ = 0 :=
  MvPowerSeries.X_inv _
set_option linter.uppercaseLean3 false in
#align power_series.X_inv PowerSeries.X_inv

@[simp]
theorem smul_inv (r : k) (φ : k⟦X⟧) : (r • φ)⁻¹ = r⁻¹ • φ⁻¹ :=
  MvPowerSeries.smul_inv _ _
#align power_series.smul_inv PowerSeries.smul_inv

/-- `firstUnitCoeff` is the non-zero coefficient whose index is `f.order`, seen as a unit of the
  field. It is obtained using `divided_by_X_pow_order`, defined in `PowerSeries.Order`-/
def firstUnitCoeff {f : k⟦X⟧} (hf : f ≠ 0) : kˣ :=
  let d := f.order.get (order_finite_iff_ne_zero.mpr hf)
  have f_const : coeff k d f ≠ 0 := by apply coeff_order
  have : Invertible (constantCoeff k (divided_by_X_pow_order hf)) := by
    apply invertibleOfNonzero
    convert f_const using 1
    rw [← coeff_zero_eq_constantCoeff, ← zero_add d]
    convert (coeff_X_pow_mul (exists_eq_mul_right_of_dvd (X_pow_order_dvd
      (order_finite_iff_ne_zero.mpr hf))).choose d 0).symm
    exact (self_eq_X_pow_order_mul_divided_by_X_pow_order hf).symm
  unitOfInvertible (constantCoeff k (divided_by_X_pow_order hf))

/-- `Inv_divided_by_X_pow_order` is the inverse of the element obtained by diving a non-zero power
series by the largest power of `X` dividing it. Useful to create a term of type `Units`, done in
`Unit_divided_by_X_pow_order` -/
def Inv_divided_by_X_pow_order {f : k⟦X⟧} (hf : f ≠ 0) : k⟦X⟧ :=
  invOfUnit (divided_by_X_pow_order hf) (firstUnitCoeff hf)

@[simp]
theorem Inv_divided_by_X_pow_order_rightInv {f : k⟦X⟧} (hf : f ≠ 0) :
    divided_by_X_pow_order hf * Inv_divided_by_X_pow_order hf = 1 :=
  mul_invOfUnit (divided_by_X_pow_order hf) (firstUnitCoeff hf) rfl

@[simp]
theorem Inv_divided_by_X_pow_order_leftInv {f : k⟦X⟧} (hf : f ≠ 0) :
    (Inv_divided_by_X_pow_order hf) * (divided_by_X_pow_order hf) = 1 := by
  rw [mul_comm]
  exact mul_invOfUnit (divided_by_X_pow_order hf) (firstUnitCoeff hf) rfl

open scoped Classical

/-- `Unit_of_divided_by_X_pow_order` is the unit power series obtained by dividing a non-zero
power series by the largest power of `X` that divides it. -/
def Unit_of_divided_by_X_pow_order (f : k⟦X⟧) : k⟦X⟧ˣ :=
  if hf : f = 0 then 1
  else
    { val := divided_by_X_pow_order hf
      inv := Inv_divided_by_X_pow_order hf
      val_inv := Inv_divided_by_X_pow_order_rightInv hf
      inv_val := Inv_divided_by_X_pow_order_leftInv hf }

theorem isUnit_divided_by_X_pow_order {f : k⟦X⟧} (hf : f ≠ 0) :
    IsUnit (divided_by_X_pow_order hf) :=
  ⟨Unit_of_divided_by_X_pow_order f,
    by simp only [Unit_of_divided_by_X_pow_order, dif_neg hf, Units.val_mk]⟩

theorem Unit_of_divided_by_X_pow_order_nonzero {f : k⟦X⟧} (hf : f ≠ 0) :
    ↑(Unit_of_divided_by_X_pow_order f) = divided_by_X_pow_order hf := by
  simp only [Unit_of_divided_by_X_pow_order, dif_neg hf, Units.val_mk]

@[simp]
theorem Unit_of_divided_by_X_pow_order_zero : Unit_of_divided_by_X_pow_order (0 : k⟦X⟧) = 1 := by
  simp only [Unit_of_divided_by_X_pow_order, dif_pos]

theorem eq_divided_by_X_pow_order_Iff_Unit {f : k⟦X⟧} (hf : f ≠ 0) :
    f = divided_by_X_pow_order hf ↔ IsUnit f :=
  ⟨fun h => by rw [h]; exact isUnit_divided_by_X_pow_order hf, fun h => by
    have : f.order.get (order_finite_iff_ne_zero.mpr hf) = 0 := by
      simp only [order_zero_of_unit h, PartENat.get_zero]
    convert (self_eq_X_pow_order_mul_divided_by_X_pow_order hf).symm
    simp only [this, pow_zero, one_mul]⟩

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

section DiscreteValuationRing

variable {k : Type*} [Field k]

open DiscreteValuationRing

theorem hasUnitMulPowIrreducibleFactorization :
    HasUnitMulPowIrreducibleFactorization k⟦X⟧ :=
  ⟨X, And.intro X_irreducible
      (by
        intro f hf
        use f.order.get (order_finite_iff_ne_zero.mpr hf)
        use Unit_of_divided_by_X_pow_order f
        simp only [Unit_of_divided_by_X_pow_order_nonzero hf]
        exact self_eq_X_pow_order_mul_divided_by_X_pow_order hf)⟩

instance : UniqueFactorizationMonoid k⟦X⟧ :=
  hasUnitMulPowIrreducibleFactorization.toUniqueFactorizationMonoid

instance : DiscreteValuationRing k⟦X⟧ :=
  ofHasUnitMulPowIrreducibleFactorization hasUnitMulPowIrreducibleFactorization

instance isNoetherianRing : IsNoetherianRing k⟦X⟧ :=
  PrincipalIdealRing.isNoetherianRing

/-- The maximal ideal of `k⟦X⟧` is generated by `X`. -/
theorem maximalIdeal_eq_span_X : LocalRing.maximalIdeal (k⟦X⟧) = Ideal.span {X} := by
  have hX : (Ideal.span {(X : k⟦X⟧)}).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    constructor
    · rw [Ideal.mem_span_singleton]
      exact Prime.not_dvd_one X_prime
    · intro I f hI hfX hfI
      rw [Ideal.mem_span_singleton, X_dvd_iff] at hfX
      have hfI0 : C k (f 0) ∈ I := by
        have : C k (f 0) = f - (f - C k (f 0)) := by rw [sub_sub_cancel]
        rw [this]
        apply Ideal.sub_mem I hfI
        apply hI
        rw [Ideal.mem_span_singleton, X_dvd_iff, map_sub, constantCoeff_C, ←
          coeff_zero_eq_constantCoeff_apply, sub_eq_zero, coeff_zero_eq_constantCoeff]
        rfl
      rw [← Ideal.eq_top_iff_one]
      apply Ideal.eq_top_of_isUnit_mem I hfI0 (IsUnit.map (C k) (Ne.isUnit hfX))
  rw [LocalRing.eq_maximalIdeal hX]

instance : NormalizationMonoid k⟦X⟧ where
  normUnit f := (Unit_of_divided_by_X_pow_order f)⁻¹
  normUnit_zero := by simp only [Unit_of_divided_by_X_pow_order_zero, inv_one]
  normUnit_mul  := fun hf hg => by
    simp only [← mul_inv, inv_inj]
    simp only [Unit_of_divided_by_X_pow_order_nonzero (mul_ne_zero hf hg),
      Unit_of_divided_by_X_pow_order_nonzero hf, Unit_of_divided_by_X_pow_order_nonzero hg,
      Units.ext_iff, val_unitOfInvertible, Units.val_mul, divided_by_X_pow_orderMul]
  normUnit_coe_units := by
    intro u
    set u₀ := u.1 with hu
    have h₀ : IsUnit u₀ := ⟨u, hu.symm⟩
    rw [inv_inj, Units.ext_iff, ← hu, Unit_of_divided_by_X_pow_order_nonzero h₀.ne_zero]
    exact ((eq_divided_by_X_pow_order_Iff_Unit h₀.ne_zero).mpr h₀).symm

theorem normUnit_X : normUnit (X : PowerSeries k) = 1 := by
  simp [normUnit, ← Units.val_eq_one, Unit_of_divided_by_X_pow_order_nonzero]

theorem X_eq_normalizeX : (X : PowerSeries k) = normalize X := by
  simp only [normalize_apply, normUnit_X, Units.val_one, mul_one]

open LocalRing

theorem ker_coeff_eq_max_ideal : RingHom.ker (constantCoeff k) = maximalIdeal _ :=
  Ideal.ext fun _ => by
    rw [RingHom.mem_ker, maximalIdeal_eq_span_X, Ideal.mem_span_singleton, X_dvd_iff]

/-- The ring isomorphism between the residue field of the ring of power series valued in a field `K`
and `K` itself. -/
def residueFieldOfPowerSeries : ResidueField k⟦X⟧ ≃+* k :=
  (Ideal.quotEquivOfEq (ker_coeff_eq_max_ideal).symm).trans
    (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj)

end DiscreteValuationRing


end PowerSeries

end
