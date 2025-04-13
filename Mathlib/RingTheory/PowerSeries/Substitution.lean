/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/

import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Basic

import Mathlib.RingTheory.PowerSeries.Order

/-! # Substitutions in power series

A (possibly multivariate) power series can be substituted into
a (univariate) power series if and only if its constant coefficient is nilpotent.

This is a particularization of the substitution of multivariate power series
to the case of univariate power series.

-/

namespace PowerSeries

variable
  {A : Type*} [CommRing A]
  {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*}
  {S : Type*} [CommRing S]

open MvPowerSeries.WithPiTopology

attribute [local instance] DiscreteTopology.instContinuousSMul

/-- Families of power series which can be substituted in other power series -/
abbrev HasSubst (a : MvPowerSeries τ S) : Prop :=
  IsNilpotent (MvPowerSeries.constantCoeff τ S a)

theorem hasSubst_iff {a : MvPowerSeries τ S} :
  HasSubst a ↔ MvPowerSeries.HasSubst (Function.const Unit a) :=
  ⟨fun ha ↦ MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (Function.const Unit ha),
   fun ha  ↦ (ha.const_coeff ())⟩

theorem HasSubst.const {a : MvPowerSeries τ S} (ha : HasSubst a) :
    MvPowerSeries.HasSubst (fun () ↦ a) :=
  hasSubst_iff.mp ha

theorem hasSubst_iff_hasEval_of_discreteTopology
    [TopologicalSpace S] [DiscreteTopology S] {a : MvPowerSeries τ S} :
    HasSubst a ↔ PowerSeries.HasEval a := by
  rw [hasSubst_iff, MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology, hasEval_iff]
  rfl

theorem HasSubst.hasEval [TopologicalSpace S] {a : MvPowerSeries τ S} (ha : HasSubst a) :
    HasEval a := by
  rw [hasEval_iff]
  apply MvPowerSeries.HasSubst.hasEval
  simpa [hasSubst_iff] using ha

theorem HasSubst.of_constantCoeff_zero {a : MvPowerSeries τ S}
    (ha : MvPowerSeries.constantCoeff τ S a = 0) : HasSubst a := by
  simp [HasSubst, ha]

/-- A variant of `HasSubst.of_constantCoeff_zero` for `PowerSeries`
to avoid the expansion of `Unit` -/
theorem HasSubst.of_constantCoeff_zero' {a : PowerSeries S}
    (ha : PowerSeries.constantCoeff S a = 0) : HasSubst a :=
  HasSubst.of_constantCoeff_zero ha

protected theorem HasSubst.X {t : τ} :
    HasSubst (MvPowerSeries.X t : MvPowerSeries τ S) := by
  simp [HasSubst]

/-- The univariate `X : R⟦X⟧` can be substituted in power series

This lemma is added because `simp` doesn't find it from `HasSubst.X` -/
protected theorem HasSubst.X' : HasSubst (X : R⟦X⟧) :=
  HasSubst.X

protected theorem HasSubst.X_pow {n : ℕ} (hn : n ≠ 0) : HasSubst (X ^ n : R⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' (by simp only [map_pow, constantCoeff_X, zero_pow hn])

protected theorem HasSubst.monomial {n : τ →₀ ℕ} (hn : n ≠ 0) (s : S) :
    HasSubst (MvPowerSeries.monomial S n s) := by
  classical
  apply HasSubst.of_constantCoeff_zero
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.coeff_monomial,
    if_neg (Ne.symm hn)]

/-- A variant of `HasSubst.monomial` to avoid the expansion of `Unit` -/
protected theorem HasSubst.monomial' {n : ℕ} (hn : n ≠ 0) (s : S) :
    HasSubst (monomial S n s) :=
  HasSubst.monomial (Finsupp.single_ne_zero.mpr hn) s

theorem HasSubst.zero : HasSubst (0 : MvPowerSeries τ R) := by
  rw [hasSubst_iff]
  exact MvPowerSeries.HasSubst.zero

/-- A variant of `HasSubst.zero` to avoid the expansion of `Unit` -/
theorem HasSubst.zero' : HasSubst (0 : PowerSeries R) :=
  PowerSeries.HasSubst.zero

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

theorem HasSubst.smul (r : MvPowerSeries τ S) {a : MvPowerSeries τ S}
    (ha : HasSubst a) :
    HasSubst (r • a) := ha.mul_right

/-- Families of `PowerSeries` that can be substituted, as an `Ideal` -/
noncomputable def HasSubst.ideal : Ideal (MvPowerSeries τ S) :=
  { carrier := setOf HasSubst
    add_mem' := HasSubst.add
    zero_mem' := HasSubst.zero
    smul_mem' := HasSubst.smul }

/-- A more general version of `HasSubst.smul` -/
theorem HasSubst.smul' (a : A) {f : MvPowerSeries τ R} (hf : HasSubst f) :
    HasSubst (a • f) := by
  simp only [HasSubst, MvPowerSeries.constantCoeff_smul]
  exact IsNilpotent.smul hf _

theorem HasSubst.smul_X (a : A) : HasSubst (a • X : R⟦X⟧) :=
  HasSubst.X.smul' _

variable {υ : Type*} {T : Type*} [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]

/-- Substitution of power series into a power series -/
noncomputable def subst (a : MvPowerSeries τ S) (f : PowerSeries R) :
    MvPowerSeries τ S :=
  MvPowerSeries.subst (fun _ ↦ a) f

variable {a : MvPowerSeries τ S} {b : S⟦X⟧}

/-- Substitution of power series into a power series -/
noncomputable def substAlgHom (ha : HasSubst a) :
    PowerSeries R →ₐ[R] MvPowerSeries τ S :=
  MvPowerSeries.substAlgHom ha.const

theorem coe_substAlgHom (ha : HasSubst a) :
    ⇑(substAlgHom ha) = subst (R := R) a :=
  MvPowerSeries.coe_substAlgHom ha.const

/-- Rewrite `PowerSeries.substAlgHom` as `PowerSeries.aeval`.

Its use is discouraged because it introduces a topology and might lead
into awkward comparisons. -/
theorem substAlgHom_eq_aeval
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) :
    (substAlgHom ha : R⟦X⟧ →ₐ[R] MvPowerSeries τ S) = PowerSeries.aeval ha.hasEval := by
  ext1 f
  simpa only [substAlgHom, aeval, MvPowerSeries.coe_substAlgHom]
    using congr_fun (MvPowerSeries.substAlgHom_eq_aeval (R := R) ha.const) f

theorem subst_add (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f + g) = subst a f + subst a g := by
  rw [← coe_substAlgHom ha, map_add]

theorem subst_pow (ha : HasSubst a) (f : PowerSeries R) (n : ℕ) :
    subst a (f ^ n) = (subst a f ) ^ n := by
  rw [← coe_substAlgHom ha, map_pow]

theorem subst_mul (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f * g) = subst a f * subst a g := by
  rw [← coe_substAlgHom ha, map_mul]

theorem subst_smul [Algebra A S] [IsScalarTower A R S]
    (ha : HasSubst a) (r : A) (f : PowerSeries R) :
    subst a (r • f) = r • (subst a f) := by
  rw [← coe_substAlgHom ha, AlgHom.map_smul_of_tower]

theorem coeff_subst_finite (ha : HasSubst a) (f : PowerSeries R) (e : τ →₀ ℕ) :
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

theorem coeff_subst_finite' (hb : HasSubst b) (f : PowerSeries R) (e : ℕ) :
    Set.Finite (fun (d : ℕ) ↦ (coeff R d f) • (PowerSeries.coeff S e (b ^ d))).support :=
  coeff_subst_finite hb f  _

theorem coeff_subst (ha : HasSubst a) (f : PowerSeries R) (e : τ →₀ ℕ) :
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

theorem coeff_subst' {b : S⟦X⟧} (hb : HasSubst b) (f : R⟦X⟧) (e : ℕ) :
    coeff S e (f.subst b) =
      finsum (fun (d : ℕ) ↦
        (coeff R d f) • (PowerSeries.coeff S e (b ^ d))) := by
  simp only [PowerSeries.coeff, coeff_subst hb]

theorem constantCoeff_subst (ha : HasSubst a) (f : PowerSeries R) :
    MvPowerSeries.constantCoeff τ S (subst a f) =
      finsum (fun d ↦ (coeff R d f) • (MvPowerSeries.constantCoeff τ S (a ^ d))) := by
  simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

theorem map_algebraMap_eq_subst_X (f : R⟦X⟧) :
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

theorem substAlgHom_coe (ha : HasSubst a) (p : Polynomial R) :
    substAlgHom ha (p : PowerSeries R) = ↑(Polynomial.aeval a p) := by
  rw [p.toPowerSeries_toMvPowerSeries, substAlgHom]
  erw [MvPowerSeries.coe_substAlgHom]
  rw [MvPowerSeries.subst_coe, ← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  apply Polynomial.algHom_ext
  simp only [AlgHom.coe_comp, Function.comp_apply, Polynomial.aeval_X, MvPolynomial.aeval_X]

theorem substAlgHom_X (ha : HasSubst a) :
    substAlgHom ha (X : R⟦X⟧) = a := by
  rw [← Polynomial.coe_X, substAlgHom_coe, Polynomial.aeval_X]

theorem subst_coe (ha : HasSubst a) (p : Polynomial R) :
    subst (R := R) a (p : PowerSeries R) = ↑(Polynomial.aeval a p) := by
  rw [← coe_substAlgHom ha, substAlgHom_coe]

theorem subst_X (ha : HasSubst a) :
    subst a (X : R⟦X⟧) = a := by
  rw [← coe_substAlgHom ha, substAlgHom_X]

theorem HasSubst.comp {a : PowerSeries S} (ha : HasSubst a)
    {b : MvPowerSeries υ T} (hb : HasSubst b):
    HasSubst (substAlgHom hb a) :=
  MvPowerSeries.IsNilpotent_subst hb.const ha

variable
    {υ : Type*} -- [DecidableEq υ]
    {T : Type*} [CommRing T] [Algebra R T]
    {a : PowerSeries S}
    {b : MvPowerSeries υ T}
    {a' : MvPowerSeries τ S}
    {b' : τ → MvPowerSeries υ T}

theorem substAlgHom_comp_substAlgHom [Algebra S T] [IsScalarTower R S T]
    (ha : HasSubst a) (hb : HasSubst b) :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha)
      = substAlgHom (ha.comp hb) :=
  MvPowerSeries.substAlgHom_comp_substAlgHom _ _

theorem substAlgHom_comp_substAlgHom_apply [Algebra S T] [IsScalarTower R S T]
    (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R) :
    (substAlgHom hb) (substAlgHom  ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

theorem subst_comp_subst [Algebra S T] [IsScalarTower R S T]
    (ha : HasSubst a) (hb : HasSubst b) :
    (subst b) ∘ (subst a) = subst (R := R) (subst b a) := by
  simpa only [funext_iff, DFunLike.ext_iff, AlgHom.coe_comp, AlgHom.coe_restrictScalars',
    Function.comp_apply, coe_substAlgHom]
    using substAlgHom_comp_substAlgHom (R := R) ha hb

theorem subst_comp_subst_apply [Algebra S T] [IsScalarTower R S T]
    (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R) :
    subst b (subst a f) = subst (subst b a) f :=
  congr_fun (subst_comp_subst (R := R) ha hb) f

theorem _root_.MvPowerSeries.rescaleUnit (a : R) (f : R⟦X⟧) :
    MvPowerSeries.rescale (Function.const _ a) f = rescale a f := by
  ext d
  rw [coeff_rescale, coeff, MvPowerSeries.coeff_rescale]
  simp [smul_eq_mul, Finsupp.prod_single_index]

namespace Example

open Nat

/-- the exponential power series -/
def exp : ℚ⟦X⟧ := mk (fun n ↦ 1/(n !))

theorem exp_def : exp = mk (fun n ↦ 1/(n ! : ℚ)) := rfl

example : exp.coeff ℚ 3 = 1/6 := by
  simp [exp_def]; rfl

def coeff_zero_exp_sub_one : constantCoeff ℚ (exp - 1) = 0 := by
  simp [map_sub, constantCoeff_one, ← coeff_zero_eq_constantCoeff, exp]

theorem hasSubst_exp_sub_one : HasSubst (exp - 1) := by
  apply HasSubst.of_constantCoeff_zero'
  exact coeff_zero_exp_sub_one

/-- The power series exp (exp X - 1) -/
noncomputable def e₂ : ℚ⟦X⟧ := exp.subst (exp - 1)

theorem e₂_def : e₂ = exp.subst (exp - 1) := rfl

theorem _root_.PowerSeries.order_pow
    {R : Type*} [CommRing R] [IsDomain R] (φ : PowerSeries R) (n : ℕ) :
    (φ ^ n).order = n • φ.order := by
  induction n with
  | zero => simp [order_one]
  | succ n hn => simp [pow_succ, order_mul, add_smul, hn]

theorem coeff_pow_eq_zero {b : S⟦X⟧} [IsDomain S]
    (hf : constantCoeff S b = 0) {d n : ℕ} (hd : d < n) :
    coeff S d (b ^ n) = 0 := by
  suffices 1 ≤ b.order  by
    apply PowerSeries.coeff_of_lt_order
    rw [order_pow]
    apply lt_of_lt_of_le  (b := (n : ℕ∞))
    exact ENat.coe_lt_coe.mpr hd
    simp
    exact le_mul_of_one_le_right' this
  apply le_order
  intro i hi
  simp only [cast_lt_one] at hi
  simp [hi, hf]

example : e₂.coeff ℚ 2 = 1 := by
  simp [e₂]
  rw [coeff_subst' hasSubst_exp_sub_one exp 2]
  set c := fun d ↦ (coeff ℚ 2) ((exp - 1) ^ d)
  set c' := fun d ↦ (coeff ℚ d) exp • (coeff ℚ 2) ((exp - 1) ^ d) with c'_eq
  have hc' : Function.support c' ⊆ Finset.range 3 := by
    intro d
    simp only [Function.mem_support, ne_eq, not_imp_comm, Finset.coe_range, Set.mem_Iio, not_lt]
    intro hd
    simp only [c']
    rw [coeff_pow_eq_zero coeff_zero_exp_sub_one hd, smul_zero]
  have hc'' : (Function.support c').Finite :=
    coeff_subst_finite' hasSubst_exp_sub_one exp _
  rw [finsum_eq_sum_of_support_subset _ hc']
  simp [Finset.sum_range_succ]
  have H0 : c' 0 = 0 := by simp [c', exp]
  have H1 : c' 1 = 1/(2 : ℚ) := by simp [c'_eq, exp]
  have H2 : c' 2 = 1/2 := by
    simp [c'_eq, exp, pow_two, coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_range_succ]
  rw [H0, H1, H2]
  norm_num

end Example

end PowerSeries
