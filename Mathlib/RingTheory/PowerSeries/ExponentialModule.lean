/-
Copyright (c) 2026 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Ring.Ext
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution

/-! # Exponential module of a commutative ring

Let `R` be a commutative ring. The exponential module of `R` is the set of all power series
`f : R⟦X⟧` that are of exponential type : `f (X + Y) = f X * f Y` where `X` and `Y` are two
indeterminates. It is an abelian group under multiplication, and an `R`-module under rescaling.

## Main Definitions

* `PowerSeries.IsExponential` : for `f : R⟦X⟧`, `IsExponential f` says that `f` is of
  exponential type.

* `PowerSeries.ExponentialModule R` : the exponential module of the commutative ring `R`.

* `PowerSeries.ExponentialModule.linearMap`: for an `A`-algebra map `f : R →ₐ[A] S`, we define
  the induced `linearMap f : ExponentialModule R →ₗ[A] ExponentialModule S`.

## Main Results

* `PowerSeries.IsExponential.neg` : if `f : R⟦X⟧` is an exponential power series, then the power
  series `f(-X)` is exponential.

* `PowerSeries.IsExponential.invOfUnit_eq_rescale_neg_one` : if `f : R⟦X⟧`, then the inverse of `f`
  is equal to the power series `f(-X)`.

## TODO

Once substitution of power series is available for `CommSemiring` (work in progress),
`PowerSeries.IsExponential` and `PowerSeries.ExponentialModule R` could automatically be generalized
to that setting.

-/

@[expose] public section

open Finset Finsupp MvPowerSeries Nat

namespace PowerSeries

variable {A R S : Type*}

name_power_vars X₀, X₁ over R

section CommSemiring

-- TODO: generalize to `CommSemiring R`.
variable [CommSemiring A] [CommRing R] [Algebra A R] [CommSemiring S] [Algebra A S]

/-- A power series `f : R⟦X⟧` is exponential if `f(X + Y) = f(X)*f(Y)` and `f(0) = 1`. -/
structure IsExponential (f : R⟦X⟧) : Prop where
  add_mul : subst (S := R) (X₀ + X₁) f = subst X₀ f * subst X₁ f
  constantCoeff : constantCoeff f = 1

/-- A power series `f` satisfies `f(X + Y) = f(X)*f(Y)` iff its coefficients `f n` satisfy
  the relations `(p + q).choose p * f (p + q)= f p * f q`. -/
theorem subst_add_eq_mul_iff (f : R⟦X⟧) :
    (subst (S := R) (X₀ + X₁) f) = (subst X₀ f) * (subst X₁ f) ↔
      ∀ (p q : ℕ), (p + q).choose p * (coeff (p + q) f) = coeff p f * coeff q f := by
  rw [MvPowerSeries.ext_iff]
  exact forall_congr_curry₀
    (fun e ↦ by rw [coeff_subst_X_zero_add_X_one , coeff_subst_X_zero_subst_mul_X_one])

/-- A power series `f` is exponential iff its coefficients `f n` satisfy the relations
  `(p + q).choose p * f (p + q)= f p * f q` and its constant coefficient is `1`. -/
theorem isExponential_iff {f : R⟦X⟧} :
    IsExponential f ↔ (∀ p q, (p + q).choose p * coeff (p + q) f = coeff p f * coeff q f) ∧
      (constantCoeff f = 1) := by
  rw [← subst_add_eq_mul_iff]
  exact ⟨fun hf ↦ ⟨hf.add_mul, hf.constantCoeff⟩, fun hf ↦ ⟨hf.1, hf.2⟩⟩

namespace IsExponential

/-- The unit power series is exponential. -/
protected theorem one : IsExponential (1 : R⟦X⟧) where
  add_mul := by
    rw [← Polynomial.coe_one, subst_coe (HasSubst.X 1), subst_coe (HasSubst.X 0),
      subst_coe ((HasSubst.X 0).add (HasSubst.X 1))]
    simp
  constantCoeff := by simp only [map_one]

/-- If `f` and `g` are exponential, then so is `f * g`. -/
protected theorem mul {f g : PowerSeries R} (hf : IsExponential f) (hg : IsExponential g) :
    IsExponential (f * g) where
  add_mul := by
    repeat rw [← coe_substAlgHom (HasSubst.of_constantCoeff_zero (by simp))]
    simp only [map_mul, coe_substAlgHom, hf.add_mul, hg.add_mul]
    ring
  constantCoeff := by simp only [map_mul, hf.constantCoeff, hg.constantCoeff, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- If `f` is exponential and  `n : ℕ`, then `f ^ n` is exponential. -/
protected theorem npow {f : R⟦X⟧} (hf : IsExponential f) (n : ℕ) :
    IsExponential (f ^ n) := by
  induction n with
  | zero => simp [pow_zero, IsExponential.one]
  | succ n hn => simp [pow_succ, hn.mul hf]

/-- If `f` is exponential, then `f(r • T)` is exponential, for any `r : R`. -/
protected theorem rescale (a : A) {f : PowerSeries R} (hf : IsExponential f) :
    IsExponential (rescale (algebraMap A R a) f) := by
  rw [isExponential_iff] at hf ⊢
  refine ⟨fun p q ↦ ?_, ?_⟩
  · simp only [coeff_rescale, mul_mul_mul_comm, ← hf.1 p q]
    ring
  · rw [← coeff_zero_eq_constantCoeff, coeff_rescale]
    simp [hf.2]

protected theorem rescale_add (r s : A) {f : R⟦X⟧} (hf : IsExponential f) :
    rescale (algebraMap A R r + algebraMap A R s) f =
      rescale (algebraMap A R r) f * rescale (algebraMap A R s) f := by
  rw [isExponential_iff] at hf
  ext d
  simp only [coeff_rescale, coeff_mul, add_pow', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mem_antidiagonal.mp hk, nsmul_eq_mul, mul_assoc, mul_comm _ ((coeff (k.1 + k.2)) f),
    ← mul_assoc, hf.1 k.1 k.2]
  ring

end IsExponential

open Additive

section Instances

noncomputable instance : SMul A (Additive R⟦X⟧) where
  smul r f := ofMul.toFun (rescale (algebraMap A R r) (toMul f))

lemma toAdditive_smul_coe (r : A) (f : R⟦X⟧) :
  r • (ofMul f) = ofMul (rescale (algebraMap A R r) f) := rfl

lemma toAdditive_smul_coe' (r : A) (f : Additive R⟦X⟧) :
  toMul (r • f) = rescale (algebraMap A R r) (toMul f) := rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : DistribMulAction A (Additive R⟦X⟧) where
  one_smul := by simp [toAdditive_smul_coe]
  mul_smul := by
    suffices  ∀ (x y : A) (b : Additive R⟦X⟧), (y * x) • b = x • y • b by
      intro x y b
      rw [← this, mul_comm]
    simp [toAdditive_smul_coe, rescale_mul]
  smul_zero a := by
    rw [← ofMul_one, toAdditive_smul_coe, map_one]
  smul_add := by simp [toAdditive_smul_coe, ← ofMul_mul]

end Instances

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- The `R`-module of exponential power series `f : R⟦X⟧` satisfying `f(X+Y) = f(X) f(Y)` and
  `f(0) = 1`. The addition law is the multiplication of power series.
  The scalar multiplication law is given by `PowerSeries.rescale`.
  This is implemented as an `AddSubmonoid (Additive R⟦X⟧) `. -/
def ExponentialModule : AddSubmonoid (Additive R⟦X⟧) where
  carrier := { f : Additive R⟦X⟧ | IsExponential (toMul f) }
  add_mem' {f g} hf hg := by simp [hf.mul hg]
  zero_mem' := by simp [IsExponential.one]

lemma mem_exponentialModule_iff (f : R⟦X⟧) :
    ofMul f ∈ ExponentialModule R ↔ IsExponential f := by
  simp [ExponentialModule]

lemma mem_exponentialModule_iff' (f : Additive R⟦X⟧) :
    f ∈ ExponentialModule R ↔ IsExponential (toMul f) := by
  simp [ExponentialModule]

namespace ExponentialModule

open PowerSeries Additive

/-- The coercion map from `ExponentialModule R` to `R⟦X⟧`. -/
@[coe] def toPowerSeries (f : ExponentialModule R) : R⟦X⟧ := toMul (f : Additive R⟦X⟧)

variable (R) in
instance instCoe : Coe (ExponentialModule R) R⟦X⟧ := ⟨toPowerSeries⟩

lemma coe_injective : Function.Injective ((↑) : ExponentialModule R → R⟦X⟧) :=
  fun f g ↦ by simp [toPowerSeries]

@[simp, norm_cast]
lemma coe_inj {f g : ExponentialModule R} : (f : R⟦X⟧) = ↑g ↔ f = g := coe_injective.eq_iff

@[ext]
lemma coe_ext {f g : ExponentialModule R} (h : (f : R⟦X⟧) = ↑g) : f = g := coe_injective h

@[simp]
theorem toMul_val_eq_coe {f : ExponentialModule R} : toMul (↑f : Additive R⟦X⟧) = ↑f := rfl

@[simp]
theorem coe_mk {f : R⟦X⟧} (hf : IsExponential f) : ↑(⟨ofMul f, hf⟩ : ExponentialModule R) = f := rfl

noncomputable instance instSMul : SMul A (ExponentialModule R) where
  smul r f := ⟨r • (f : Additive R⟦X⟧), by
    simp only [mem_exponentialModule_iff', toAdditive_smul_coe']
    exact f.prop.rescale (algebraMap A R r)⟩

theorem smul_def (r : A) (f : ExponentialModule R) :
  (r • f : ExponentialModule R) = r • (f : Additive R⟦X⟧) := rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable instance instModule : Module A (ExponentialModule R) where
  one_smul f := by rw [← Subtype.coe_inj, smul_def, one_smul]
  mul_smul r s f := by simp [← Subtype.coe_inj, smul_def, mul_smul]
  smul_zero r := by rw [← Subtype.coe_inj, smul_def, ZeroMemClass.coe_zero, smul_zero]
  smul_add r f g := by simp [← Subtype.coe_inj, smul_def]
  add_smul r s f := by
    simp only [← Subtype.coe_inj, smul_def, AddSubmonoid.coe_add]
    apply Additive.toMul.injective
    simp [toAdditive_smul_coe', -toMul_val_eq_coe, f.prop.rescale_add r s]
  zero_smul f := by
    simp only [← Subtype.coe_inj, smul_def, ZeroMemClass.coe_zero]
    apply Additive.toMul.injective
    have hf : constantCoeff f = (1 : R) := f.prop.constantCoeff
    simp [toAdditive_smul_coe', toMul_val_eq_coe, hf]

set_option backward.isDefEq.respectTransparency false in
lemma coe_add (f g : ExponentialModule R) : (↑(f + g) : R⟦X⟧) = ↑f * ↑g := by
  simp only [toPowerSeries, AddSubmonoid.coe_add, toMul_add]

lemma coe_smul (r : A) (f : ExponentialModule R) :
    ((r • f) : ExponentialModule R) = rescale (algebraMap A R r) (f : R⟦X⟧) := rfl

end ExponentialModule

end CommSemiring

section CommRing

namespace IsExponential

variable [CommRing R] [CommSemiring S]

protected theorem neg {f : R⟦X⟧} (hf : IsExponential f) :
    IsExponential (rescale  (-1 : R) f) := hf.rescale (-1 : R)

protected theorem self_mul_neg_eq_one {f : R⟦X⟧} (hf : IsExponential f) :
    f * (rescale (-1 : R) f) = 1 := by
  have hadd := hf.rescale_add (1 : R) (-1 : R)
  simp only [Algebra.algebraMap_self, RingHom.id_apply, add_neg_cancel, rescale_zero,
    RingHom.coe_comp, Function.comp_apply, rescale_one] at hadd
  rw [← hadd, hf.constantCoeff, map_one]

set_option backward.isDefEq.respectTransparency false in
protected theorem neg_mul_self_eq_one {f : R⟦X⟧} (hf : IsExponential f) :
    (rescale (-1) f) * f = 1 := by rw [mul_comm, hf.self_mul_neg_eq_one]

set_option backward.isDefEq.respectTransparency false in
protected theorem isUnit {f : R⟦X⟧} (hf : IsExponential f) : IsUnit f :=
  isUnit_iff_exists_inv'.mpr ⟨(rescale (-1) f),  hf.neg_mul_self_eq_one⟩

protected theorem inverse_eq_neg_mul_self {f : R⟦X⟧} (hf : IsExponential f) :
    Ring.inverse f = (rescale (-1) f) := by
  rw [Ring.inverse, dif_pos hf.isUnit]
  exact hf.isUnit.unit.inv_eq_of_mul_eq_one_left hf.neg_mul_self_eq_one

set_option backward.isDefEq.respectTransparency false in
protected theorem invOfUnit_eq_rescale_neg_one {f : R⟦X⟧} (hf : IsExponential f) :
    (f.invOfUnit 1) = rescale (-1) f := by
  rw [← IsUnit.mul_right_inj hf.isUnit, f.mul_invOfUnit, hf.self_mul_neg_eq_one]
  simp [Units.val_one, hf.constantCoeff]

protected theorem inv {f : R⟦X⟧} (hf : IsExponential f) : IsExponential (f.invOfUnit 1) := by
  simp [hf.invOfUnit_eq_rescale_neg_one, hf.neg]

protected theorem map (φ : R →+* S) {f : R⟦X⟧} (hf : IsExponential f) :
    let _ : CommRing S := RingHom.commSemiringToCommRing φ
    IsExponential (PowerSeries.map φ f) := by
  let _ : CommRing S := RingHom.commSemiringToCommRing φ
  rw [isExponential_iff] at hf ⊢
  refine ⟨fun p q ↦ ?_, ?_⟩
  · simp only [coeff_map, ← map_mul, ← hf.1 p q]
    simp
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff, hf.2, map_one]

end IsExponential

namespace ExponentialModule

open PowerSeries Additive

variable [CommRing R]

set_option backward.isDefEq.respectTransparency false in
noncomputable instance instAddCommGroup : AddCommGroup (ExponentialModule R) where
  neg f := (-1 : ℤ) • f
  zsmul n f := n • f
  zsmul_zero' f := by simp
  zsmul_succ' n f := by simp [add_smul]
  zsmul_neg' n f := by simp [Int.negSucc_eq, ← smul_assoc]
  neg_add_cancel f := by
    rw [← Subtype.coe_inj]
    apply Additive.toMul.injective
    simp only [AddSubmonoid.coe_add, toMul_add]
    rw [ZeroMemClass.coe_zero, toMul_zero, ← f.2.neg_mul_self_eq_one]
    simp [coe_smul]
  add_comm f g := add_comm f g

instance instIsScalarTower (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (A : Type*) [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] :
    IsScalarTower R S (ExponentialModule A) where
  smul_assoc r s f := by
    apply coe_injective
    simp only [coe_smul]
    rw [← algebraMap_smul S, smul_eq_mul, map_mul, mul_comm, rescale_mul]
    simp only [RingHom.coe_comp, Function.comp_apply]
    apply congr_fun
    ext f n
    simp [IsScalarTower.algebraMap_eq R S A, RingHom.coe_comp, Function.comp_apply]

lemma coe_ofMul (f : R⟦X⟧) (hf : IsExponential f) :
    ↑(⟨ofMul f, hf⟩ : ExponentialModule R) = f := rfl

lemma isExponential_coe (f : ExponentialModule R) : IsExponential (f : R⟦X⟧) := f.prop

lemma constantCoeff_coe (f : ExponentialModule R) : constantCoeff (f : R⟦X⟧) = 1 :=
  f.prop.constantCoeff

lemma subst_add_coe_eq_mul (f : ExponentialModule R) :
    subst (S := R) (X₀ + X₁) (f : R⟦X⟧) = (subst X₀ (f : R⟦X⟧)) * (subst X₁ (f : R⟦X⟧)) := by
  have hf := f.prop
  rw [mem_exponentialModule_iff'] at hf
  exact hf.add_mul

lemma choose_mul_coeff_add_eq (f : ExponentialModule R) (p q : ℕ) :
    (p + q).choose p * (coeff (p + q) (f : R⟦X⟧)) = coeff p f * coeff q f :=
  (subst_add_eq_mul_iff (R := R) f).mp (subst_add_coe_eq_mul f) p q

variable [CommRing A] [Algebra A R] {S : Type*} [CommRing S] [Algebra A S] (φ : R →ₐ[A] S)

set_option backward.isDefEq.respectTransparency false in
/-- Given `A`-algebras `R` and `S`, this is the linear map between their respective exponential
modules induced by an `A`-algebra map on the coefficients. -/
noncomputable def linearMap :
    ExponentialModule R →ₗ[A] ExponentialModule S where
  toFun := fun f ↦
    ⟨ofMul (PowerSeries.map φ (f : R⟦X⟧)), by
      simp only [mem_exponentialModule_iff]
      convert f.prop.map (φ  : R →+* S)
      ext <;> rfl⟩
  map_add' := fun f g ↦ coe_injective (by simp [coe_add])
  map_smul' := fun a f ↦
    coe_injective (by simp [-coe_mk, coe_smul, coe_ofMul, rescale_algebraMap_map])

theorem coeff_linearMap (n : ℕ) (f : ExponentialModule R) :
    coeff n (linearMap φ f) = φ (coeff n f) := rfl

@[simp]
lemma coe_zero_eq_one (A : Type*) [CommRing A] :
    ((0 : ExponentialModule A) : A⟦X⟧) = 1 := by rfl

end ExponentialModule

end CommRing

end PowerSeries
