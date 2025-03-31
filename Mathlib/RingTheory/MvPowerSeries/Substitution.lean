/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.UniformSpace.DiscreteUniformity

/-! # Substitutions in power series

Here we define the substitution of power series into other power series.
We follow Bourbaki, Algèbre, chap. 4, §4, n° 3.

Evaluation of a power series at adequate elements has been defined
in `DividedPowers.ForMathlib.MvPowerSeries.Evaluation.lean`.
The goal here is to check the relevant hypotheses:
* The ring of coefficients is endowed the discrete topology.
* The main condition rewrites as having vanishing constant coefficient
* Power series have a linear topology
-/

/-- Change of coefficients in mv power series, as an `AlgHom` -/
def MvPowerSeries.mapAlgHom {σ : Type*} {R : Type*} [CommSemiring R] {S : Type*}
    [Semiring S] [Algebra R S] {T : Type*} [Semiring T] [Algebra R T]
    (φ : S →ₐ[R] T) :
    MvPowerSeries σ S →ₐ[R] MvPowerSeries σ T where
  toRingHom   := MvPowerSeries.map σ φ
  commutes' r := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, MvPowerSeries.algebraMap_apply, map_C, RingHom.coe_coe, AlgHom.commutes]

/-- Change of coefficients in power series, as an `AlgHom` -/
def PowerSeries.mapAlgHom {R : Type*} [CommSemiring R]
    {S : Type*} [Semiring S] [Algebra R S] {T : Type*} [Semiring T] [Algebra R T]
    (φ : S →ₐ[R] T) :
    PowerSeries S →ₐ[R] PowerSeries T :=
  MvPowerSeries.mapAlgHom φ

theorem MvPowerSeries.monomial_one_eq {σ : Type*} {R : Type*} [CommSemiring R] (e : σ →₀ ℕ) :
    MvPowerSeries.monomial R e 1 = e.prod fun s n ↦ (X s : MvPowerSeries σ R) ^ n := by
  simp only [← MvPolynomial.coe_X, ← MvPolynomial.coe_pow, ← MvPolynomial.coe_monomial,
    MvPolynomial.monomial_eq, map_one, one_mul]
  simp only [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, ← map_finsupp_prod]

theorem MvPowerSeries.prod_smul_X_eq_smul_monomial_one {σ : Type*}
    {A : Type*} [CommSemiring A] (R : Type*) [CommSemiring R] [Algebra A R]
    (e : σ →₀ ℕ) (a : σ → A)  :
    e.prod (fun s n ↦ ((a s • X s : MvPowerSeries σ R) ^ n))
      = (e.prod fun s n ↦ (a s) ^ n) • monomial R e 1 := by
  rw [Finsupp.prod_congr
    (g2 := fun s n ↦ ((C σ R (algebraMap A R (a s)) * (X s : MvPowerSeries σ R)) ^ n))]
  · have (a : A) (f : MvPowerSeries σ R) : a • f = (C σ R) ((algebraMap A R) a) * f := by
      rw [← smul_eq_C_mul, IsScalarTower.algebraMap_smul]
    simp only [mul_pow, Finsupp.prod_mul, ← map_pow , ← monomial_one_eq, this]
    simp only [map_finsupp_prod, map_pow]
  · intro x _
    rw [algebra_compatible_smul R, smul_eq_C_mul]

theorem MvPowerSeries.monomial_eq
    {σ : Type*} {R : Type*} [CommSemiring R]
    (e : σ →₀ ℕ) (r : σ → R) :
    MvPowerSeries.monomial R e (e.prod (fun s n => r s ^  n))
      = (Finsupp.prod e fun s e => (r s • MvPowerSeries.X s) ^ e) := by
  rw [prod_smul_X_eq_smul_monomial_one, ← map_smul, smul_eq_mul, mul_one]

theorem MvPowerSeries.monomial_smul_const
    {σ : Type*} {R : Type*} [CommSemiring R]
    (e : σ →₀ ℕ) (r : R) :
    MvPowerSeries.monomial R e (r ^ (Finsupp.sum e fun _ n => n))
      = (Finsupp.prod e fun s e => (r • MvPowerSeries.X s) ^ e) := by
  rw [prod_smul_X_eq_smul_monomial_one, ← map_smul, smul_eq_mul, mul_one]
  simp only [Finsupp.sum, Finsupp.prod, Finset.prod_pow_eq_pow_sum]

namespace MvPowerSeries

variable {σ : Type*}
  {A : Type*} [CommSemiring A]
  {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*}
  {S : Type*} [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower A R S]

open WithPiTopology

/-- Families of power series which can be substituted -/
structure HasSubst (a : σ → MvPowerSeries τ S) : Prop where
  const_coeff : ∀ s, IsNilpotent (constantCoeff τ S (a s))
  tendsto_zero : Filter.Tendsto a Filter.cofinite (@nhds _ (@instTopologicalSpace τ S ⊥) 0)

theorem hasSubst_X :
    HasSubst (fun (s : σ) ↦ (X s : MvPowerSeries σ S)) :=
  letI : UniformSpace S := ⊥
  { const_coeff := fun s ↦ by
     simp only [constantCoeff_X, IsNilpotent.zero]
    tendsto_zero := variables_tendsto_zero }

theorem hasSubst_zero :
    HasSubst (fun (_ : σ) ↦ (0 : MvPowerSeries τ S)) :=
  letI : UniformSpace S := ⊥
  { const_coeff := fun _ ↦ by simp only [Pi.zero_apply, map_zero, IsNilpotent.zero]
    tendsto_zero := tendsto_const_nhds }

theorem hasSubst_add {a b : σ → MvPowerSeries τ S}
    (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (a + b) where
  const_coeff := fun s ↦ by
    simp only [Pi.add_apply, map_add]
    exact (Commute.all _ _).isNilpotent_add (ha.const_coeff s) (hb.const_coeff s)
  tendsto_zero := by
    letI : UniformSpace S := ⊥
    convert Filter.Tendsto.add (ha.tendsto_zero) (hb.tendsto_zero)
    rw [add_zero]

@[simp]
theorem constantCoeff_smul {R : Type*} [Semiring R] {S : Type*} [Semiring S] [Module R S]
    (φ : MvPowerSeries σ S) (a : R) :
    constantCoeff σ S (a • φ) = a • constantCoeff σ S φ :=
  rfl

theorem hasSubst_mul (b : σ → MvPowerSeries τ S)
    {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (b * a) :=
  letI : UniformSpace S := ⊥
  { const_coeff := fun s ↦ by
      simp only [Pi.mul_apply, map_mul]
      exact Commute.isNilpotent_mul_right (Commute.all _ _) (ha.const_coeff _)
    tendsto_zero := IsLinearTopology.tendsto_mul_zero_of_right b a ha.tendsto_zero }

theorem hasSubst_smul (r : MvPowerSeries τ S) {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (r • a) := by convert hasSubst_mul _ ha

/-- Families of mv power series that can be substituted, as an `Ideal` -/
noncomputable def hasSubst.ideal : Ideal (σ → MvPowerSeries τ S) :=
  letI : UniformSpace S := ⊥
  { carrier := setOf HasSubst
    add_mem' := hasSubst_add
    zero_mem' := hasSubst_zero
    smul_mem' := hasSubst_mul }

/-- If σ is finite, then the nilpotent condition is enough for HasSubst -/
theorem hasSubst_of_constantCoeff_nilpotent [Finite σ]
    {a : σ → MvPowerSeries τ S} (ha : ∀ s, IsNilpotent (constantCoeff τ S (a s))) :
    HasSubst a where
  const_coeff := ha
  tendsto_zero := by simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]

/-- If σ is finite, then having zero constant coefficient is enough for HasSubst -/
theorem hasSubst_of_constantCoeff_zero [Finite σ]
    {a : σ → MvPowerSeries τ S} (ha : ∀ s, constantCoeff τ S (a s) = 0) :
    HasSubst a :=
  hasSubst_of_constantCoeff_nilpotent (fun s ↦ by simp only [ha s, IsNilpotent.zero])

/-- Substitution of power series into a power series -/
noncomputable def subst (a : σ → MvPowerSeries τ S) (f : MvPowerSeries σ R) :
    MvPowerSeries τ S :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  MvPowerSeries.eval₂ (algebraMap _ _) a f

variable {a : σ → MvPowerSeries τ S}

theorem HasSubst.evalDomain (ha : HasSubst a) :
    @HasEval σ (MvPowerSeries τ S) _ (@instTopologicalSpace τ S ⊥) a :=
  letI : UniformSpace S := ⊥
  { hpow := fun s ↦ (tendsto_pow_of_constantCoeff_nilpotent_iff (a s)).mpr (ha.const_coeff s)
    tendsto_zero := ha.tendsto_zero }

/-- Substitution of power series into a power series -/
noncomputable def substAlgHom (ha : HasSubst a) :
    MvPowerSeries σ R →ₐ[R] MvPowerSeries τ S := by
-- NOTE : Could there be a tactic that introduces these local instances?
  classical
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) := IsScalarTower.continuousSMul S
  exact MvPowerSeries.aeval ha.evalDomain

@[simp]
theorem coe_substAlgHom (ha : HasSubst a) :
    ⇑(substAlgHom ha) = subst (R := R) a :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) := IsScalarTower.continuousSMul S
  coe_aeval (HasSubst.evalDomain ha)

theorem subst_add (ha : HasSubst a) (f g : MvPowerSeries σ R) :
    subst a (f + g) = subst a f + subst a g := by
  rw [← coe_substAlgHom ha, map_add]

theorem subst_mul (ha : HasSubst a) (f g : MvPowerSeries σ R) :
    subst a (f * g) = subst a f * subst a g := by
  rw [← coe_substAlgHom ha, map_mul]

theorem subst_pow (ha : HasSubst a) (f : MvPowerSeries σ R) (n : ℕ) :
    subst a (f ^ n) = (subst a f ) ^ n := by
  rw [← coe_substAlgHom ha, map_pow]

theorem subst_smul (ha : HasSubst a) (r : A) (f : MvPowerSeries σ R) :
    subst a (r • f) = r • (subst a f) := by
  rw [← coe_substAlgHom ha, AlgHom.map_smul_of_tower]

theorem substAlgHom_coe (ha : HasSubst a) (p : MvPolynomial σ R) :
    substAlgHom (R := R) ha p = MvPolynomial.aeval a p :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) := IsScalarTower.continuousSMul S
  aeval_coe ha.evalDomain p

theorem substAlgHom_X (ha : HasSubst a) (s : σ) :
    substAlgHom (R := R) ha (X s) = a s := by
  rw [← MvPolynomial.coe_X, substAlgHom_coe, MvPolynomial.aeval_X]

theorem substAlgHom_monomial (ha : HasSubst a) (e : σ →₀ ℕ) (r : R) :
    substAlgHom ha (monomial R e r) =
      (algebraMap R (MvPowerSeries τ S) r) * (e.prod (fun s n ↦ (a s) ^ n)) := by
  rw [← MvPolynomial.coe_monomial, substAlgHom_coe, MvPolynomial.aeval_monomial]

theorem subst_coe (ha : HasSubst a) (p : MvPolynomial σ R) :
    subst (R := R) a p = MvPolynomial.aeval a p := by
  rw [← coe_substAlgHom ha, substAlgHom_coe]

theorem subst_X (ha : HasSubst a) (s : σ) :
    subst (R := R) a (X s) = a s := by
  rw [← coe_substAlgHom ha, substAlgHom_X]

theorem subst_monomial (ha : HasSubst a) (e : σ →₀ ℕ) (r : R) :
    subst a (monomial R e r) =
      (algebraMap R (MvPowerSeries τ S) r) * (e.prod (fun s n ↦ (a s) ^ n)) := by
  rw [← coe_substAlgHom ha, substAlgHom_monomial]

theorem continuous_subst (ha : HasSubst a) :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    Continuous (subst a : MvPowerSeries σ R → MvPowerSeries τ S) :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) := IsScalarTower.continuousSMul S
  continuous_eval₂ (continuous_algebraMap _ _) ha.evalDomain

theorem coeff_subst_finite (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    Set.Finite (fun d ↦ (coeff R d f) • (coeff S e (d.prod fun s e => (a s) ^ e))).support :=
  letI : UniformSpace S := ⊥
  letI : UniformSpace R := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) := IsScalarTower.continuousSMul S
  Summable.finite_support _
    ((hasSum_aeval ha.evalDomain f).map (coeff S e) (continuous_coeff S e)).summable

theorem coeff_subst (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    coeff S e (subst a f) =
      finsum (fun d ↦ (coeff R d f) • (coeff S e (d.prod fun s e => (a s) ^ e))) := by
  letI : UniformSpace S := ⊥
  letI : UniformSpace R := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) := IsScalarTower.continuousSMul S
  have := ((hasSum_aeval ha.evalDomain f).map (coeff S e) (continuous_coeff S e))
  erw [← coe_substAlgHom ha, ← this.tsum_eq, tsum_def]
  erw [dif_pos this.summable, if_pos (coeff_subst_finite ha f e)]
  rfl

theorem constantCoeff_subst (ha : HasSubst a) (f : MvPowerSeries σ R) :
    constantCoeff τ S (subst a f) =
      finsum (fun d ↦ (coeff R d f) • (constantCoeff τ S (d.prod fun s e => (a s) ^ e))) := by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

theorem map_algebraMap_eq_subst_X (f : MvPowerSeries σ R) :
    map σ (algebraMap R S) f = subst X f := by
  ext e
  rw [coeff_map, coeff_subst hasSubst_X f e, finsum_eq_single _ e]
  · rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_same,
      algebra_compatible_smul S, smul_eq_mul, mul_one]
  · intro d hd
    rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_ne hd.symm, smul_zero]

variable
    {T : Type*} [CommRing T]
    [UniformSpace T] [T2Space T] [CompleteSpace T]
    [IsUniformAddGroup T] [IsTopologicalRing T] [IsLinearTopology T T]
    [Algebra R T] -- [Algebra S T] [IsScalarTower R S T]
    {ε : MvPowerSeries τ S →ₐ[R] T}

theorem comp_substAlgHom (ha : HasSubst a) :
    letI : UniformSpace S := ⊥
    letI : UniformSpace R := ⊥
    haveI : ContinuousSMul R T := DiscreteTopology.instContinuousSMul R T
    (hε : Continuous ε) →
      ε.comp (substAlgHom ha) = aeval (HasEval.map hε ha.evalDomain) :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  haveI : ContinuousSMul R T := DiscreteTopology.instContinuousSMul R T
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) := IsScalarTower.continuousSMul S
  fun hε ↦ comp_aeval ha.evalDomain hε

theorem comp_subst (ha : HasSubst a) :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    haveI : ContinuousSMul R T := DiscreteTopology.instContinuousSMul R T
    (hε : Continuous ε) →
      ⇑ε ∘ (subst a) = ⇑(aeval (R := R) (HasEval.map hε ha.evalDomain)) :=
  fun hε ↦ by rw [← comp_substAlgHom ha hε, AlgHom.coe_comp, coe_substAlgHom]

theorem comp_subst_apply (ha : HasSubst a) :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    haveI : ContinuousSMul R T := DiscreteTopology.instContinuousSMul R T
    (hε : Continuous ε) → (f : MvPowerSeries σ R) →
      ε (subst a f) = aeval (R := R) (HasEval.map hε ha.evalDomain) f :=
  fun hε ↦ congr_fun (comp_subst ha hε)

variable [Algebra S T] [IsScalarTower R S T]

theorem eval₂_subst (ha : HasSubst a) {b : τ → T} (hb : HasEval b) (f : MvPowerSeries σ R) :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    eval₂ (algebraMap S T) b (subst a f) =
      eval₂ (algebraMap R T) (fun s ↦ eval₂ (algebraMap S T) b (a s)) f := by
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  haveI : ContinuousSMul S T := DiscreteTopology.instContinuousSMul S T
  let ε : MvPowerSeries τ S →ₐ[R] T := (aeval hb).restrictScalars R
  have hε : Continuous ε := continuous_aeval hb
  simpa only [AlgHom.coe_restrictScalars', AlgHom.toRingHom_eq_coe,
    AlgHom.coe_restrictScalars, RingHom.coe_coe, ε, coe_aeval]
    using comp_subst_apply ha hε f

/- a : σ → MvPowerSeries τ S
   b : τ → MvPowerSeries υ T
   f ∈ R⟦σ⟧, f(a) = substAlgHom ha f ∈ S⟦τ⟧
   f(a) (b) = substAlgHom hb (substAlgHom ha f)
   f = X s, f (a) = a s
   f(a) (b) = substAlgHom hb (a s)
   -/

variable {υ : Type*}
  {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {b : τ → MvPowerSeries υ T}

-- TODO? : the converse holds when the kernel of `algebraMap R S` is a nilideal
theorem IsNilpotent_subst (ha : HasSubst a)
    {f : MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff σ R f)) :
    IsNilpotent (constantCoeff τ S ((substAlgHom ha) f)) := by
  classical
  rw [coe_substAlgHom, constantCoeff_subst ha]
  apply isNilpotent_finsum
  intro d
  by_cases hd : d = 0
  · rw [← algebraMap_smul S, smul_eq_mul, mul_comm, ← smul_eq_mul, hd]
    apply IsNilpotent.smul
    simp only [Finsupp.prod_zero_index, map_one, coeff_zero_eq_constantCoeff, smul_eq_mul, one_mul]
    exact IsNilpotent.map hf (algebraMap R S)
  · apply IsNilpotent.smul
    rw [← ne_eq, Finsupp.ne_iff] at hd
    obtain ⟨t, hs⟩ := hd
    rw [← Finsupp.prod_filter_mul_prod_filter_not (fun i ↦ i = t), map_mul,
      mul_comm, ← smul_eq_mul]
    apply IsNilpotent.smul
    rw [Finsupp.prod_eq_single t]
    · simp only [Finsupp.filter_apply_pos, map_pow]
      exact IsNilpotent.pow_of_pos (ha.const_coeff t) hs
    · intro t' htt' ht'
      simp only [Finsupp.filter_apply, if_neg ht', ne_eq, not_true_eq_false] at htt'
    · exact fun _ ↦ by rw [pow_zero]

theorem HasSubst.comp (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (fun s ↦ substAlgHom hb (a s)) where
  const_coeff s := IsNilpotent_subst hb (ha.const_coeff s)
  tendsto_zero := by
    letI : TopologicalSpace S := ⊥
    letI : TopologicalSpace T := ⊥
    apply Filter.Tendsto.comp _ (ha.tendsto_zero)
    simp only [← map_zero (substAlgHom (R := S) hb), coe_substAlgHom]
    exact (continuous_subst hb).continuousAt

theorem substAlgHom_comp_substAlgHom (ha : HasSubst a) (hb : HasSubst b) :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha) = substAlgHom (ha.comp hb) := by
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  letI : UniformSpace T := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) := IsScalarTower.continuousSMul S
  haveI : ContinuousSMul R T := DiscreteTopology.instContinuousSMul R T
  haveI : ContinuousSMul R (MvPowerSeries υ T) := IsScalarTower.continuousSMul T
  apply comp_aeval (R := R) (ε := (substAlgHom hb).restrictScalars R)
    ha.evalDomain
  simp only [AlgHom.coe_restrictScalars', coe_substAlgHom]
  exact (continuous_subst (R := S) hb)

theorem substAlgHom_comp_substAlgHom_apply (ha : HasSubst a) (hb : HasSubst b)
    (f : MvPowerSeries σ R) :
    (substAlgHom hb) (substAlgHom ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

theorem subst_comp_subst (ha : HasSubst a) (hb : HasSubst b) :
    (subst b) ∘ (subst a) = subst (R := R) (fun s ↦ subst b (a s)) := by
  simpa only [funext_iff, coe_substAlgHom, DFunLike.ext_iff,
    AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply]
    using substAlgHom_comp_substAlgHom (R := R) ha hb

theorem subst_comp_subst_apply (ha : HasSubst a) (hb : HasSubst b) (f : MvPowerSeries σ R) :
    subst b (subst a f) = subst (fun s ↦ subst b (a s)) f :=
  congr_fun (subst_comp_subst (R := R) ha hb) f

section rescale

/-- Scale multivariate power series -/
noncomputable def rescale (a : σ → R) (f : MvPowerSeries σ R) :
    MvPowerSeries σ R :=
  subst (a • X) f

theorem rescale_eq_subst (a : σ → R) (f : MvPowerSeries σ R) :
    rescale a f = subst (a • X) f := rfl

variable (R) in
theorem hasSubst_rescale (a : σ → R) :
    HasSubst ((a • X) : σ → MvPowerSeries σ R) := by
  convert hasSubst_mul (fun s ↦ algebraMap R (MvPowerSeries σ R) (a s))
    hasSubst_X using 1
  rw [funext_iff]
  intro s
  simp only [Pi.smul_apply', Pi.mul_apply]
  rw [algebra_compatible_smul (MvPowerSeries σ R), smul_eq_mul]

variable (R) in
/-- Scale multivariate power series, as an `AlgHom` -/
noncomputable def rescale_algHom (a : σ → R) :
    MvPowerSeries σ R →ₐ[R] MvPowerSeries σ  R :=
  substAlgHom (hasSubst_rescale R a)

theorem coe_rescale_algHom (a : σ → R) :
    ⇑(rescale_algHom R a) = rescale a :=
  coe_substAlgHom (hasSubst_rescale R a)

theorem rescale_algHom_comp (a b : σ → R) :
    (rescale_algHom R a).comp (rescale_algHom R b) = rescale_algHom R (a * b) := by
  rw [AlgHom.ext_iff]
  intro f
  simp only [AlgHom.coe_comp, Function.comp_apply, rescale_algHom]
  rw [substAlgHom_comp_substAlgHom_apply]
  congr
  rw [funext_iff]
  intro s
  simp only [Pi.smul_apply', Pi.mul_apply]
  rw [AlgHom.map_smul_of_tower]
  rw [← MvPolynomial.coe_X, substAlgHom_coe, MvPolynomial.aeval_X, MvPolynomial.coe_X]
  simp only [Pi.smul_apply', algebraMap_smul]
  rw [← mul_smul, mul_comm]

theorem rescale_rescale_apply (a b : σ → R) (f : MvPowerSeries σ R) :
    (f.rescale b).rescale a = f.rescale (a * b) := by
  simp only [← coe_rescale_algHom, ← AlgHom.comp_apply, rescale_algHom_comp]

theorem coeff_rescale (r : σ → R) (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff R d (rescale r f) = (d.prod fun s n ↦ r s ^ n) • coeff R d f := by
  unfold rescale
  rw [coeff_subst (hasSubst_rescale R _)]
  simp only [Pi.smul_apply', smul_eq_mul, prod_smul_X_eq_smul_monomial_one]
  simp only [LinearMap.map_smul_of_tower, Algebra.mul_smul_comm]
  rw [finsum_eq_single _ d]
  · simp only [coeff_monomial_same, mul_one, smul_eq_mul]
  · intro e he
    simp only [coeff_monomial_ne he.symm, mul_zero, smul_zero]

theorem rescale_one :
    rescale 1 = @id (MvPowerSeries σ R) := by
  ext f d
  simp only [coeff_rescale, Finsupp.prod, Pi.one_apply, one_pow, Finset.prod_const_one, smul_eq_mul,
    one_mul, id_eq]

theorem rescale_algHom_one :
    rescale_algHom R 1 = AlgHom.id R (MvPowerSeries σ R):= by
  rw [DFunLike.ext_iff]
  intro f
  simp only [Function.const_one, coe_rescale_algHom, AlgHom.coe_id, id_eq, rescale_one]

/-- Scale mv power series, as a `MonoidHom` in the scaling parameters -/
noncomputable def rescale_MonoidHom : (σ → R) →* MvPowerSeries σ R →ₐ[R] MvPowerSeries σ R where
  toFun := rescale_algHom R
  map_one' := rescale_algHom_one
  map_mul' a b := by
    dsimp only
    rw [← rescale_algHom_comp, AlgHom.End_toSemigroup_toMul_mul]

theorem rescale_zero_apply (f : MvPowerSeries σ R) :
    rescale 0 f = MvPowerSeries.C σ R (constantCoeff σ R f) := by
  classical
  ext d
  simp only [coeff_rescale, coeff_C]
  by_cases hd : d = 0
  · simp only [hd, Pi.zero_apply, Finsupp.prod_zero_index, coeff_zero_eq_constantCoeff,
      smul_eq_mul, one_mul, ↓reduceIte]
  · simp only [Pi.zero_apply, smul_eq_mul, if_neg hd]
    convert zero_smul R _
    simp only [DFunLike.ext_iff, Finsupp.coe_zero, Pi.zero_apply, not_forall] at hd
    obtain ⟨s, hs⟩ := hd
    apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
    simp only [Function.const_apply, zero_pow hs]

/-- Scaling a linear power series is smul -/
lemma rescale_linear_eq_smul (r : R) (f : MvPowerSeries σ R)
    (hf : ∀ (d : σ →₀ ℕ), (d.sum (fun _ n ↦ n) ≠ 1) → MvPowerSeries.coeff R d f = 0) :
    MvPowerSeries.rescale (Function.const σ r) f = r • f := by
  ext e
  simp only [MvPowerSeries.coeff_rescale, map_smul]
  simp only [Finsupp.prod, Function.const_apply, Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  by_cases he : Finsupp.sum e (fun _ n ↦ n) = 1
  · simp only [Finsupp.sum] at he
    simp only [he, pow_one]
  · simp only [hf e he, mul_zero]

open PowerSeries

theorem rescaleUnit (a : R) (f : R⟦X⟧) :
    MvPowerSeries.rescale (Function.const _ a) f = PowerSeries.rescale a f := by
  ext d
  change MvPowerSeries.coeff R _ _ = _
  rw [PowerSeries.coeff_rescale, coeff_rescale, smul_eq_mul]
  simp only [Function.const_apply, pow_zero, Finsupp.prod_single_index, PowerSeries.coeff]

end rescale

/- section scale

-- More general version, deleted for the moment, because it often needs more explicit [Algebra...]

/-- Scale multivariate power series -/
noncomputable def scale (a : σ → A) (f : MvPowerSeries σ R) :
    MvPowerSeries σ R :=
  subst (a • X) f

theorem scale_eq_subst (a : σ → A) (f : MvPowerSeries σ R) :
    scale a f = subst (a • X) f := rfl

variable (R) in
theorem hasSubst_scale (a : σ → A) :
    HasSubst ((a • X) : σ → MvPowerSeries σ R) := by
  convert hasSubst_mul (fun s ↦ algebraMap A (MvPowerSeries σ R) (a s))
    hasSubst_X using 1
  rw [Function.funext_iff]
  intro s
  simp only [Pi.smul_apply', Pi.mul_apply]
  rw [algebra_compatible_smul (MvPowerSeries σ R), smul_eq_mul]

variable (R) in
/-- Scale multivariate power series, as an `AlgHom` -/
noncomputable def scale_algHom (a : σ → A) :
    MvPowerSeries σ R →ₐ[R] MvPowerSeries σ  R :=
  substAlgHom (hasSubst_scale R a)

theorem coe_scale_algHom (a : σ → A) :
    ⇑(scale_algHom R a) = scale a :=
  coe_substAlgHom (hasSubst_scale R a)

theorem scale_algHom_comp (a b : σ → A) :
    (scale_algHom R a).comp (scale_algHom R b) = scale_algHom R (a * b) := by
  rw [AlgHom.ext_iff]
  intro f
  simp only [AlgHom.coe_comp, Function.comp_apply, scale_algHom]
  rw [substAlgHom_comp_substAlgHom_apply]
  congr
  rw [Function.funext_iff]
  intro s
  simp only [Pi.smul_apply', Pi.mul_apply]
  rw [AlgHom.map_smul_of_tower]
  rw [← MvPolynomial.coe_X, substAlgHom_coe, MvPolynomial.aeval_X, MvPolynomial.coe_X]
  simp only [Pi.smul_apply', algebraMap_smul]
  rw [← mul_smul, mul_comm]

theorem scale_scale_apply (a b : σ → A) (f : MvPowerSeries σ R) :
    (f.scale b).scale a = f.scale (a * b) := by
  simp only [← coe_scale_algHom, ← AlgHom.comp_apply, scale_algHom_comp]

theorem coeff_scale (r : σ → A) (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff R d (scale r f) = (d.prod fun s n ↦ r s ^ n) • coeff R d f := by
  unfold scale
  rw [coeff_subst (hasSubst_scale R _)]
  simp only [Pi.smul_apply', smul_eq_mul, prod_smul_X_eq_smul_monomial_one]
  simp only [LinearMap.map_smul_of_tower, Algebra.mul_smul_comm]
  rw [finsum_eq_single _ d]
  · simp only [coeff_monomial_same, mul_one]
  · intro e he
    simp only [coeff_monomial_ne he.symm, mul_zero, smul_zero]

theorem scale_one :
    scale (1 : σ → A) = @id (MvPowerSeries σ R) := by
  ext f d
  simp only [coeff_scale, Pi.one_apply, one_pow, Finsupp.prod, id_eq,
    Finset.prod_const_one, one_smul]

theorem scale_algHom_one :
    scale_algHom R (Function.const σ (1 : A)) = AlgHom.id R (MvPowerSeries σ R):= by
  rw [DFunLike.ext_iff]
  intro f
  simp only [Function.const_one, coe_scale_algHom, AlgHom.coe_id, id_eq, scale_one]

/-- Scale mv power series, as a `MonoidHom` in the scaling parameters -/
noncomputable def scale_MonoidHom : (σ → A) →* MvPowerSeries σ R →ₐ[R] MvPowerSeries σ R where
  toFun := scale_algHom R
  map_one' := scale_algHom_one
  map_mul' a b := by
    dsimp only
    rw [← scale_algHom_comp, AlgHom.End_toSemigroup_toMul_mul]

theorem scale_zero_apply (f : MvPowerSeries σ R) :
    (scale (Function.const σ (0 : A))) f = MvPowerSeries.C σ R (constantCoeff σ R f) := by
  classical
  ext d
  simp only [coeff_scale, coeff_C]
  by_cases hd : d = 0
  · simp only [hd, Function.const_apply, Finsupp.prod_zero_index, coeff_zero_eq_constantCoeff,
    one_smul, ↓reduceIte]
  · simp only [if_neg hd]
    convert zero_smul A _
    simp only [DFunLike.ext_iff, Finsupp.coe_zero, Pi.zero_apply, not_forall] at hd
    obtain ⟨s, hs⟩ := hd
    simp only [Finsupp.prod]
    apply Finset.prod_eq_zero (i := s)
    rw [Finsupp.mem_support_iff]
    exact hs
    simp only [Function.const_apply, zero_pow hs]

/-- Scaling a linear power series is smul -/
lemma scale_linear_eq_smul (r : A) (f : MvPowerSeries σ R)
    (hf : ∀ (d : σ →₀ ℕ), (d.sum (fun _ n ↦ n) ≠ 1) → MvPowerSeries.coeff R d f = 0) :
    MvPowerSeries.scale (Function.const σ r) f = r • f := by
  ext e
  simp only [MvPowerSeries.coeff_scale, map_smul]
  simp only [Finsupp.prod, Function.const_apply, Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  by_cases he : Finsupp.sum e (fun _ n ↦ n) = 1
  · simp only [Finsupp.sum] at he
    simp only [he, pow_one, LinearMap.map_smul_of_tower]
  · simp only [hf e he, smul_zero, LinearMap.map_smul_of_tower]


end scale
-/
end MvPowerSeries

namespace PowerSeries

variable
  {A : Type*} [CommRing A]
  {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*}
  {S : Type*} [CommRing S]

open MvPowerSeries.WithPiTopology

/-- Families of power series which can be substituted in other power series -/
structure HasSubst (a : MvPowerSeries τ S) : Prop where
  const_coeff : IsNilpotent (MvPowerSeries.constantCoeff τ S a)

theorem hasSubst_of_constantCoeff_nilpotent
    {a : MvPowerSeries τ S}
    (ha : IsNilpotent (MvPowerSeries.constantCoeff τ S a)) :
    HasSubst a where
  const_coeff := ha

theorem hasSubst_iff (a : MvPowerSeries τ S) :
    HasSubst a ↔ MvPowerSeries.HasSubst (Function.const Unit a) :=
  ⟨fun ha ↦ MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
    (Function.const Unit ha.const_coeff),
   fun ha  ↦ hasSubst_of_constantCoeff_nilpotent (ha.const_coeff ())⟩

theorem hasSubst_of_constantCoeff_zero
    {a : MvPowerSeries τ S}
    (ha : MvPowerSeries.constantCoeff τ S a = 0) :
    HasSubst a where
  const_coeff := by simp only [ha, IsNilpotent.zero]

theorem hasSubst_X : HasSubst (X : R⟦X⟧) :=
  hasSubst_of_constantCoeff_zero (by
    change constantCoeff R X = 0
    rw [constantCoeff_X])

theorem hasSubst_smul_X (a : A) : HasSubst (a • X : R⟦X⟧) :=
  hasSubst_of_constantCoeff_zero (by
    change constantCoeff R (a • X) = 0
    rw [← coeff_zero_eq_constantCoeff]
    simp only [LinearMap.map_smul_of_tower, coeff_zero_X, smul_zero])

variable {υ : Type*} -- [DecidableEq υ]
  {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] -- [IsScalarTower R S T]

/-- Substitution of power series into a power series -/
noncomputable def subst [Algebra R S] (a : MvPowerSeries τ S) (f : PowerSeries R) :
    MvPowerSeries τ S :=
  MvPowerSeries.subst (fun _ ↦ a) f

variable {a : MvPowerSeries τ S}

theorem HasSubst.const (ha : HasSubst a) :
    MvPowerSeries.HasSubst (fun (_ : Unit) ↦ a) where
  const_coeff  := fun _ ↦ ha.const_coeff
  tendsto_zero := by simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]

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

/-
-- TODO LIST:
- Add PowerSeries.toMvPowerSeries_Unit
- Show it is a topological equivalence.
- The support under finsuppUnitEquiv should be the image of the support.
-/

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
    HasSubst (substAlgHom hb a) where
  const_coeff := MvPowerSeries.IsNilpotent_subst hb.const (ha.const_coeff)

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
