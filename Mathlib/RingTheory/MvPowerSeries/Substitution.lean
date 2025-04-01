/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/

import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Topology.UniformSpace.DiscreteUniformity

/-! # Substitutions in multivariate power series

Here we define the substitution of power series into other power series.
We follow Bourbaki, Algèbre, chap. 4, §4, n° 3.

Evaluation of a power series at adequate elements has been defined
in `Mathlib.RingTheory.MvPowerSeries.Evaluation`.
The goal here is to check the relevant hypotheses:
* The ring of coefficients is endowed the discrete topology.
* The main condition rewrites as having vanishing constant coefficient
* Multivariate power series have a linear topology

-/

namespace MvPowerSeries

variable {σ : Type*}
  {A : Type*} [CommSemiring A]
  {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*}
  {S : Type*} [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower A R S]

open WithPiTopology

/-- Families of power series which can be substituted -/
structure HasSubst (a : σ → MvPowerSeries τ S) : Prop where
  const_coeff s : IsNilpotent (constantCoeff τ S (a s))
  coeff_zero d : {s | (a s).coeff S d ≠ 0}.Finite

variable {a : σ → MvPowerSeries τ S}

lemma coeff_zero_iff :
    Filter.Tendsto a Filter.cofinite (@nhds _ (@instTopologicalSpace τ S ⊥) 0) ↔
      ∀ d : τ →₀ ℕ, {s | (a s).coeff S d ≠ 0}.Finite := by
  letI : UniformSpace S := ⊥
  simp_rw [tendsto_iff_coeff_tendsto, coeff_zero]
  apply forall_congr'
  intro d
  simp [nhds_discrete]

lemma hasSubst_iff_hasEval_of_discreteTopology :
    HasSubst a ↔ @HasEval σ (MvPowerSeries τ S) _ (@instTopologicalSpace τ S ⊥) a := by
  letI : UniformSpace S := ⊥
  constructor
  · intro ha
    exact {
      hpow s := (tendsto_pow_of_constantCoeff_nilpotent_iff (a s)).mpr (ha.const_coeff s)
      tendsto_zero := coeff_zero_iff.mpr ha.coeff_zero }
  · intro ha
    exact {
      const_coeff s := (tendsto_pow_of_constantCoeff_nilpotent_iff (a s)).mp (ha.hpow s)
      coeff_zero d := (coeff_zero_iff.mp ha.tendsto_zero) d }

theorem HasSubst.hasEval (ha : HasSubst a) :
    @HasEval σ (MvPowerSeries τ S) _ (@instTopologicalSpace τ S ⊥) a :=
  hasSubst_iff_hasEval_of_discreteTopology.mp ha

theorem hasSubst_X :
    HasSubst (fun (s : σ) ↦ (X s : MvPowerSeries σ S)) := by
  letI : UniformSpace S := ⊥
  rw [hasSubst_iff_hasEval_of_discreteTopology]
  exact HasEval.X

/-   { const_coeff s := by simp only [constantCoeff_X, IsNilpotent.zero]
    coeff_zero d := by
      suffices { s | (X s).coeff S d ≠ 0 } ⊆ d.support by
        apply Set.Finite.subset _ this
        exact Finset.finite_toSet d.support
      intro s
      classical
      simp [coeff_X, not_iff_not]
      rintro ⟨rfl⟩ _
      simp only [Finsupp.single_eq_same, one_ne_zero, not_false_eq_true] } -/

theorem hasSubst_zero :
    HasSubst (fun (_ : σ) ↦ (0 : MvPowerSeries τ S)) := by
  letI : UniformSpace S := ⊥
  rw [hasSubst_iff_hasEval_of_discreteTopology]
  exact HasEval.zero
/-   letI : UniformSpace S := ⊥
  { const_coeff := fun _ ↦ by simp only [Pi.zero_apply, map_zero, IsNilpotent.zero]
    coeff_zero d := by simp } -/

theorem hasSubst_add {a b : σ → MvPowerSeries τ S}
    (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (a + b) := by
  letI : UniformSpace S := ⊥
  rw [hasSubst_iff_hasEval_of_discreteTopology] at ha hb ⊢
  exact HasEval.add ha hb

/-
  const_coeff s := by
    simp only [Pi.add_apply, map_add]
    exact (Commute.all _ _).isNilpotent_add (ha.const_coeff s) (hb.const_coeff s)
  coeff_zero d := by
    simp only [Pi.add_apply, map_add]
    apply Set.Finite.subset ((ha.coeff_zero d).union (hb.coeff_zero d))
    intro s
    simp only [ne_eq, Set.mem_setOf_eq, not_imp_not, Set.mem_union, ← not_and_or]
    rintro ⟨ha, hb⟩
    rw [ha, hb, add_zero]
-/

@[simp]
theorem constantCoeff_smul {R : Type*} [Semiring R] {S : Type*} [Semiring S] [Module R S]
    (φ : MvPowerSeries σ S) (a : R) :
    constantCoeff σ S (a • φ) = a • constantCoeff σ S φ :=
  rfl

theorem hasSubst_mul (b : σ → MvPowerSeries τ S)
    {a : σ → MvPowerSeries τ S} (ha : HasSubst a) : HasSubst (b * a) := by
  letI : UniformSpace S := ⊥
  rw [hasSubst_iff_hasEval_of_discreteTopology] at ha ⊢
  exact HasEval.mul_left b ha
 /-  { const_coeff s := by
      simp only [Pi.mul_apply, map_mul]
      exact Commute.isNilpotent_mul_right (Commute.all _ _) (ha.const_coeff _)
    coeff_zero d := by

      -- }IsLinearTopology.tendsto_mul_zero_of_right b a ha.tendsto_zero
      sorry }
-/
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
  coeff_zero _ := Set.toFinite _

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

/-- Substitution of power series into a power series -/
noncomputable def substAlgHom (ha : HasSubst a) :
    MvPowerSeries σ R →ₐ[R] MvPowerSeries τ S :=
-- NOTE : Could there be a tactic that introduces these local instances?
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) := IsScalarTower.continuousSMul S
  MvPowerSeries.aeval ha.hasEval

@[simp]
theorem coe_substAlgHom (ha : HasSubst a) :
    ⇑(substAlgHom ha) = subst (R := R) a :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) := IsScalarTower.continuousSMul S
  coe_aeval ha.hasEval

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
  aeval_coe ha.hasEval p

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
  continuous_eval₂ (continuous_algebraMap _ _) ha.hasEval

theorem coeff_subst_finite (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    Set.Finite (fun d ↦ (coeff R d f) • (coeff S e (d.prod fun s e => (a s) ^ e))).support :=
  letI : UniformSpace S := ⊥
  letI : UniformSpace R := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) := IsScalarTower.continuousSMul S
  Summable.finite_support_of_discreteTopology _
    ((hasSum_aeval ha.hasEval f).map (coeff S e) (continuous_coeff S e)).summable

theorem coeff_subst (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    coeff S e (subst a f) =
      finsum (fun d ↦ (coeff R d f) • (coeff S e (d.prod fun s e => (a s) ^ e))) := by
  letI : UniformSpace S := ⊥
  letI : UniformSpace R := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) := IsScalarTower.continuousSMul S
  have := ((hasSum_aeval ha.hasEval f).map (coeff S e) (continuous_coeff S e))
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
      ε.comp (substAlgHom ha) = aeval (HasEval.map hε ha.hasEval) :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  haveI : ContinuousSMul R T := DiscreteTopology.instContinuousSMul R T
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) := IsScalarTower.continuousSMul S
  fun hε ↦ comp_aeval ha.hasEval hε

theorem comp_subst (ha : HasSubst a) :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    haveI : ContinuousSMul R T := DiscreteTopology.instContinuousSMul R T
    (hε : Continuous ε) →
      ⇑ε ∘ (subst a) = ⇑(aeval (R := R) (HasEval.map hε ha.hasEval)) :=
  fun hε ↦ by rw [← comp_substAlgHom ha hε, AlgHom.coe_comp, coe_substAlgHom]

theorem comp_subst_apply (ha : HasSubst a) :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    haveI : ContinuousSMul R T := DiscreteTopology.instContinuousSMul R T
    (hε : Continuous ε) → (f : MvPowerSeries σ R) →
      ε (subst a f) = aeval (R := R) (HasEval.map hε ha.hasEval) f :=
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
  coeff_zero := by
    letI : TopologicalSpace S := ⊥
    letI : TopologicalSpace T := ⊥
    rw [← coeff_zero_iff]
    apply Filter.Tendsto.comp _ (ha.hasEval.tendsto_zero)
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
    ha.hasEval
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
