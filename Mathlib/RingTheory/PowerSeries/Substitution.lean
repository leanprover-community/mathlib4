/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/

import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Basic

/-! # Substitutions in power series

A (possibly multivariate) power series can be substituted into
a (univariate) power series if and only if its constant coefficient is nilpotent.

This is a particularization of the substitution of multivariate power series
to the case of univariate power series.

## QUESTIONS :

Should `rescale` be redefined using `subst` or with the elementary explicit formula?

It is more convenient to have `PowerSeries.HasSusbt`, for for evaluation,
we just say `IsTopologicallyNilpotent`. Maybe it would be more consistent
to define `PowerSeries.HasEval` as an abbrev for `IsTopologicallyNilpotent`.
-/

namespace PowerSeries

variable
  {A : Type*} [CommRing A]
  {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*}
  {S : Type*} [CommRing S]

open MvPowerSeries.WithPiTopology

/-- Families of power series which can be substituted in other power series -/
abbrev HasSubst (a : MvPowerSeries τ S) : Prop :=
  IsNilpotent (MvPowerSeries.constantCoeff τ S a)

theorem hasSubst_iff (a : MvPowerSeries τ S) :
  HasSubst a ↔ MvPowerSeries.HasSubst (Function.const Unit a) :=
  ⟨fun ha ↦ MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (Function.const Unit ha),
   fun ha  ↦ (ha.const_coeff ())⟩

theorem HasSubst.of_constantCoeff_zero
    {a : MvPowerSeries τ S}
    (ha : MvPowerSeries.constantCoeff τ S a = 0) :
    HasSubst a := by
  simp [HasSubst, ha]

@[simp]
protected theorem HasSubst.X {t : τ} : HasSubst (MvPowerSeries.X t : MvPowerSeries τ S) := by
  simp [HasSubst]

/-- The univariate `X : R⟦X⟧` can be substituted in power series

This lemma is added because `simp` doesn't find it from `HasSubst.X` -/
@[simp]
theorem HasSubst.X' : HasSubst (X : R⟦X⟧) :=
  HasSubst.X

theorem HasSubst.smul (a : A) {f : MvPowerSeries τ R} (hf : HasSubst f) :
    HasSubst (a • f) := by
  simp only [HasSubst, MvPowerSeries.constantCoeff_smul]
  exact IsNilpotent.smul hf _

@[simp]
theorem HasSubst.smul_X (a : A) : HasSubst (a • X : R⟦X⟧) :=
  HasSubst.X.smul _

theorem HasSubst.add {f g : MvPowerSeries τ R} (hf : HasSubst f) (hg : HasSubst g) :
    HasSubst (f + g) := by
  simp only [HasSubst, map_add]
  exact Commute.isNilpotent_add (Commute.all _ _) hf hg

theorem HasSubst.mul_left {f g : MvPowerSeries τ R} (hf : HasSubst f) :
    HasSubst (f * g) := by
  simp only [HasSubst, map_mul]
  apply Commute.isNilpotent_mul_left (Commute.all _ _) hf

theorem HasSubst.mul_right {f g : MvPowerSeries τ R} (hf : HasSubst f) :
    HasSubst (g * f) := by
  simp only [HasSubst, map_mul]
  apply Commute.isNilpotent_mul_right (Commute.all _ _) hf

variable {υ : Type*} {T : Type*} [CommRing T] [Algebra R T] [Algebra S T]

/-- Substitution of power series into a power series -/
noncomputable def subst [Algebra R S] (a : MvPowerSeries τ S) (f : PowerSeries R) :
    MvPowerSeries τ S :=
  MvPowerSeries.subst (fun _ ↦ a) f

variable {a : MvPowerSeries τ S}

theorem HasSubst.const (ha : HasSubst a) :
    MvPowerSeries.HasSubst (fun () ↦ a) :=
  MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun _ ↦ ha

/-- Substitution of power series into a power series -/
noncomputable def substAlgHom [Algebra R S] (ha : HasSubst a) :
    PowerSeries R →ₐ[R] MvPowerSeries τ S :=
  MvPowerSeries.substAlgHom ha.const

theorem coe_substAlgHom [Algebra R S] (ha : HasSubst a) :
    ⇑(substAlgHom ha) = subst (R := R) a :=
  MvPowerSeries.coe_substAlgHom ha.const

theorem subst_add [Algebra R S] (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f + g) = subst a f + subst a g := by
  rw [← coe_substAlgHom ha, map_add]

theorem subst_pow [Algebra R S] (ha : HasSubst a) (f : PowerSeries R) (n : ℕ) :
    subst a (f ^ n) = (subst a f ) ^ n := by
  rw [← coe_substAlgHom ha, map_pow]

theorem subst_mul [Algebra R S] (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f * g) = subst a f * subst a g := by
  rw [← coe_substAlgHom ha, map_mul]

theorem subst_smul [Algebra A S] [Algebra R S] [IsScalarTower A R S]
    (ha : HasSubst a) (r : A) (f : PowerSeries R) :
    subst a (r • f) = r • (subst a f) := by
  rw [← coe_substAlgHom ha, AlgHom.map_smul_of_tower]

theorem coeff_subst_finite [Algebra R S] (ha : HasSubst a) (f : PowerSeries R) (e : τ →₀ ℕ) :
    Set.Finite (fun (d : ℕ) ↦ (coeff R d f) • (MvPowerSeries.coeff S e (a ^ d))).support := by
  convert (MvPowerSeries.coeff_subst_finite ha.const f e).image
    ⇑(Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv
  rw [← Equiv.preimage_eq_iff_eq_image, ← Function.support_comp_eq_preimage]
  apply congr_arg
  rw [← Equiv.eq_comp_symm]
  ext d
  simp only [Finsupp.prod_pow, Finset.univ_unique, PUnit.default_eq_unit, Finset.prod_singleton,
    LinearEquiv.coe_toEquiv_symm, EquivLike.coe_coe, Function.comp_apply,
    Finsupp.LinearEquiv.finsuppUnique_symm_apply, Finsupp.single_eq_same]
  congr

theorem coeff_subst [Algebra R S] (ha : HasSubst a) (f : PowerSeries R) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff S e (subst a f) =
      finsum (fun (d : ℕ) ↦
        (coeff R d f) • (MvPowerSeries.coeff S e (a ^ d))) := by
  erw [MvPowerSeries.coeff_subst ha.const f e]
  rw [← finsum_comp_equiv (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv.symm]
  apply finsum_congr
  intro d
  congr
  · ext; simp
  · simp

theorem constantCoeff_subst [Algebra R S] (ha : HasSubst a) (f : PowerSeries R) :
    MvPowerSeries.constantCoeff τ S (subst a f) =
      finsum (fun d ↦ (coeff R d f) • (MvPowerSeries.constantCoeff τ S (a ^ d))) := by
  simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

theorem map_algebraMap_eq_subst_X [Algebra R S] (f : R⟦X⟧) :
    map (algebraMap R S) f = subst X f :=
  MvPowerSeries.map_algebraMap_eq_subst_X f

theorem _root_.Polynomial.toPowerSeries_toMvPowerSeries (p : Polynomial R) :
    (p : PowerSeries R) =
      ((Polynomial.aeval (MvPolynomial.X ()) p : MvPolynomial Unit R) : MvPowerSeries Unit R) := by
  change (Polynomial.coeToPowerSeries.algHom R) p =
    (MvPolynomial.coeToMvPowerSeries.algHom R)
      (Polynomial.aeval (MvPolynomial.X () : MvPolynomial Unit R) p)
  rw [← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  apply Polynomial.algHom_ext
  simp only [Polynomial.coeToPowerSeries.algHom_apply, Algebra.id.map_eq_id, Polynomial.coe_X,
    map_X]
  erw [AlgHom.comp_apply]
  simp only [Polynomial.aeval_X, MvPolynomial.coeToMvPowerSeries.algHom_apply,
    Algebra.id.map_eq_id, MvPowerSeries.map_id, MvPolynomial.coe_X, RingHom.id_apply]
  rfl

/- example :(substAlgHom ha).comp
    ((MvPolynomial.coeToMvPowerSeries.algHom R).comp
      (Polynomial.aeval (MvPolynomial.X () : MvPolynomial Unit R)))
    = (Polynomial.aeval a) := by
  apply Polynomial.algHom_ext
  simp only [AlgHom.coe_comp, Function.comp_apply, Polynomial.aeval_X]
  erw [AlgHom.comp_apply]
  simp only [Polynomial.aeval_X, MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.id.map_eq_id,
    MvPowerSeries.map_id, MvPolynomial.coe_X, RingHom.id_apply]
  -- we need substAlgHom_coe
  rw [← MvPolynomial.coe_X, substAlgHom]
  erw [MvPowerSeries.substAlgHom_apply]
  rw [MvPowerSeries.subst_coe, MvPolynomial.aeval_X] -/

theorem substAlgHom_coe [Algebra R S] (ha : HasSubst a) (p : Polynomial R) :
    substAlgHom ha (p : PowerSeries R) = ↑(Polynomial.aeval a p) := by
  rw [p.toPowerSeries_toMvPowerSeries, substAlgHom]
  erw [MvPowerSeries.coe_substAlgHom]
  rw [MvPowerSeries.subst_coe ha.const, ← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  apply Polynomial.algHom_ext
  simp only [AlgHom.coe_comp, Function.comp_apply, Polynomial.aeval_X, MvPolynomial.aeval_X]

theorem substAlgHom_X [Algebra R S] (ha : HasSubst a) :
    substAlgHom ha (X : R⟦X⟧) = a := by
  rw [← Polynomial.coe_X, substAlgHom_coe, Polynomial.aeval_X]

theorem subst_coe [Algebra R S] (ha : HasSubst a) (p : Polynomial R) :
    subst (R := R) a (p : PowerSeries R) = ↑(Polynomial.aeval a p) := by
  rw [← coe_substAlgHom ha, substAlgHom_coe]

theorem subst_X [Algebra R S] (ha : HasSubst a) :
    subst a (X : R⟦X⟧) = a := by
  rw [← coe_substAlgHom ha, substAlgHom_X]

-- TODO: remove
/-
theorem comp_substAlgHom
    {T : Type*} [CommRing T] [Algebra R T] {ε : S →ₐ[R] T} :
    (MvPowerSeries.mapAlgHom τ ε).comp (substAlgHom ha) = substAlgHom (ha.map ε)  :=
  MvPowerSeries.comp_subst ha.const ε

theorem comp_substAlgHom
    {T : Type*} [CommRing T] [Algebra R T] (ε : S →ₐ[R] T) :
    (MvPowerSeries.mapAlgHom τ ε).comp (substAlgHom ha) = substAlgHom (ha.map ε)  :=
  MvPowerSeries.comp_substAlgHom ha.const ε
-/

theorem HasSubst.comp {a : PowerSeries S} (ha : HasSubst a)
    {b : MvPowerSeries υ T} (hb : HasSubst b):
    HasSubst (substAlgHom hb a) :=
  MvPowerSeries.IsNilpotent_subst hb.const ha

variable
    {υ : Type*} -- [DecidableEq υ]
    {T : Type*} [CommRing T] [Algebra R T] -- [Algebra S T] [Algebra R S] [IsScalarTower R S T]
    {a : PowerSeries S} -- (ha : HasSubst a)
    {b : MvPowerSeries υ T}  -- (hb : HasSubst b)
    {a' : MvPowerSeries τ S} -- (ha' : HasSubst a')
    {b' : τ → MvPowerSeries υ T} -- (hb' : MvPowerSeries.HasSubst b')

theorem substAlgHom_comp_substAlgHom [Algebra R S] [Algebra S T] [IsScalarTower R S T]
    (ha : HasSubst a) (hb : HasSubst b) :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha)
      = substAlgHom (ha.comp hb) :=
  MvPowerSeries.substAlgHom_comp_substAlgHom _ _

theorem substAlgHom_comp_substAlgHom_apply [Algebra R S] [Algebra S T] [IsScalarTower R S T]
    (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R) :
    (substAlgHom hb) (substAlgHom  ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

theorem subst_comp_subst [Algebra R S] [Algebra S T] [IsScalarTower R S T]
    (ha : HasSubst a) (hb : HasSubst b) :
    (subst b) ∘ (subst a) = subst (R := R) (subst b a) := by
  simpa only [funext_iff, DFunLike.ext_iff, AlgHom.coe_comp, AlgHom.coe_restrictScalars',
    Function.comp_apply, coe_substAlgHom]
    using substAlgHom_comp_substAlgHom (R := R) ha hb

theorem subst_comp_subst_apply [Algebra R S] [Algebra S T] [IsScalarTower R S T]
    (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R) :
    subst b (subst a f) = subst (subst b a) f :=
  congr_fun (subst_comp_subst (R := R) ha hb) f

theorem _root_.MvPowerSeries.rescaleUnit (a : R) (f : R⟦X⟧) :
    MvPowerSeries.rescale (Function.const _ a) f = rescale a f := by
  ext d
  rw [coeff_rescale, coeff, MvPowerSeries.coeff_rescale]
  simp [smul_eq_mul, Finsupp.prod_single_index]

/- -- Duplicates PowerSeries.rescale, the additional generality is probably useless
section scale

/-- Scale power series` -/
noncomputable def scale (a : A) (f : R⟦X⟧) : R⟦X⟧ :=
    MvPowerSeries.scale (Function.const Unit a) f

theorem scale_eq_subst (a : A) (f : R⟦X⟧) :
    scale a f = subst (a • X) f := rfl

variable (R) in
theorem hasSubst_scale (a : A) : HasSubst (a • (X : R⟦X⟧)) :=
  (hasSubst_iff _).mpr (MvPowerSeries.hasSubst_scale R _)

variable (R) in
/-- Scale power series, as an `AlgHom` -/
noncomputable def scale_algHom (a : A) :
    R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  MvPowerSeries.scale_algHom R (Function.const Unit a)

theorem coe_scale_algHom (a : A) :
    ⇑(scale_algHom R a) = scale a :=
  MvPowerSeries.coe_scale_algHom (Function.const Unit a)

theorem scale_algHom_comp (a b : A) :
    (scale_algHom R a).comp (scale_algHom R b) = scale_algHom R (a * b) := by
  simp only [scale_algHom, MvPowerSeries.scale_algHom_comp, Function.const_mul]

theorem scale_scale_apply (a b : A) (f : R⟦X⟧) :
    (f.scale b).scale a = f.scale (a * b) :=
  MvPowerSeries.scale_scale_apply _ _ f

theorem coeff_scale (a : A) (f : R⟦X⟧) (d : ℕ) :
    coeff R d (scale a f) = a ^ d • coeff R d f := by
  convert MvPowerSeries.coeff_scale (Function.const Unit a) f (Finsupp.single default d)
  simp only [PUnit.default_eq_unit, Function.const_apply, pow_zero, Finsupp.prod_single_index]

theorem scale_algebraMap (a : A) :
    scale (algebraMap A R a) = scale (R := R) a := by
  ext f n
  simp only [coeff_scale]
  rw [← algebraMap_smul (R := A) R, map_pow]

theorem scale_one : scale (1 : A) = @id (R⟦X⟧) :=
  MvPowerSeries.scale_one

theorem scale_algHom_one :
    scale_algHom R (1 : A) = AlgHom.id R R⟦X⟧ :=
  MvPowerSeries.scale_algHom_one

/-- Scale power series, as a `MonoidHom` in the scaling variable -/
noncomputable def scale_MonoidHom : A →* R⟦X⟧ →ₐ[R] R⟦X⟧ where
  toFun := scale_algHom R
  map_one' := scale_algHom_one
  map_mul' a b := by
    dsimp only
    rw [← scale_algHom_comp, AlgHom.End_toSemigroup_toMul_mul]

theorem scale_zero_apply (f : R⟦X⟧) :
    scale (0 : A) f = PowerSeries.C R (constantCoeff R f) :=
  MvPowerSeries.scale_zero_apply f

/-- When p is linear, substitution of p and then a scalar homothety
  is substitution of the homothety then p -/
lemma subst_linear_subst_scalar_comm (a : A)
    {σ : Type*} (p : MvPowerSeries σ R)
    (hp_lin : ∀ (d : σ →₀ ℕ), (d.sum (fun _ n ↦ n) ≠ 1) → MvPowerSeries.coeff R d p = 0)
    (f : PowerSeries R) :
    subst p (scale a f)
      = MvPowerSeries.scale (Function.const σ a) (subst p f) := by
  have hp : PowerSeries.HasSubst p := by
    apply hasSubst_of_constantCoeff_zero
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply hp_lin
    simp only [Finsupp.sum_zero_index, ne_eq, zero_ne_one, not_false_eq_true]
  rw [scale_eq_subst, MvPowerSeries.scale_eq_subst]
  rw [subst_comp_subst_apply (hasSubst_scale R _) hp]
  nth_rewrite 3 [subst]
  rw [MvPowerSeries.subst_comp_subst_apply hp.const (MvPowerSeries.hasSubst_scale R _)]
  rw [Function.funext_iff]
  intro _
  rw [subst_smul hp, ← Polynomial.coe_X, subst_coe hp, Polynomial.aeval_X]
  rw [← MvPowerSeries.scale_eq_subst]
  rw [MvPowerSeries.scale_linear_eq_smul _ _ hp_lin]
  rfl

theorem scale_map_eq_map_scale' (φ : R →+* S) (a : A) (f : R⟦X⟧) :
    scale (φ (algebraMap A R a)) (PowerSeries.map φ f) =
      PowerSeries.map (φ : R →+* S) (scale a f) := by
  ext n
  simp only [coeff_scale, coeff_map]
 --   algebra_compatible_smul S (a ^ n), algebra_compatible_smul R (a ^ n),
  rw [smul_eq_mul, smul_eq_mul, map_mul, map_pow]

theorem scale_map_eq_map_scale [Algebra A S] (φ : R →ₐ[A] S) (a : A) (f : R⟦X⟧) :
    scale a (PowerSeries.map φ f)
    = PowerSeries.map (φ : R →+* S) (scale a f) := by
  rw [← scale_map_eq_map_scale', ← scale_algebraMap, RingHom.coe_coe, AlgHom.commutes]

end scale
-/

end PowerSeries
