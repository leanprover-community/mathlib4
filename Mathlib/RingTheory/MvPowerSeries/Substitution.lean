/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/

import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
<<<<<<< HEAD
import Mathlib.RingTheory.PowerSeries.Basic
=======
>>>>>>> master
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Topology.UniformSpace.DiscreteUniformity

/-! # Substitutions in multivariate power series

Here we define the substitution of power series into other power series.
We follow [Bourbaki, Algebra II, chap. 4, §4, n° 3][bourbaki1981]
who present substitution of power series as an application of evaluation.

<<<<<<< HEAD
=======
For an `R`-algebra `S`, `f : MvPowerSeries σ R` and `a : σ → MvPowerSeries τ S`,
`MvPowerSeries.subst a f` is the substitution of `X s` by `a s` in `f`.
It is only well defined under one of the two following conditions:
  * `f` is a polynomial, in which case it is the classical evaluation;
  * or the condition `MvPowerSeries.HasSubst a` holds, which means:
    - For every `s`, the constant coefficient of `a s` is nilpotent;
    - For every `d : σ →₀ ℕ`, all but finitely many of the coefficients
      `(a s).coeff d` vanish.
In the other cases, it is defined as 0 (dummy value).

When `HasSubst a`, `MvPowerSeries.subst a` gives rise to an algebra homomorphism
`MvPowerSeries.substAlgHom ha : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ S`.

>>>>>>> master
As an application, we define `MvPowerSeries.rescale` which rescales a multivariate
power series `f : MvPowerSeries σ R` by a map `a : σ → R`.

## Implementation note

Evaluation of a power series at adequate elements has been defined
in `Mathlib.RingTheory.MvPowerSeries.Evaluation`.
The goal here is to check the relevant hypotheses:
* The ring of coefficients is endowed the discrete topology.
<<<<<<< HEAD
* The main condition rewrites as having vanishing constant coefficient
* Multivariate power series have a linear topology

To this aim, we add a local instance
  `localinstanceUniformSpace_bot : UniformSpace S = ⊥`
and two associated `ContinuousSMul` local instances.
=======
* The main condition rewrites as having nilpotent constant coefficient
* Multivariate power series have a linear topology

The function `MvPowerSeries.subst` is defined using an explicit
invocation of the discrete uniformity (`⊥`).
If users need to enter the API, they can use `MvPowerSeries.subst_eq_eval₂`
and similar lemmas that hold for whatever uniformity on the space as soon
as it is discrete.
>>>>>>> master

## TODO

* Refactor `PowerSeries.rescale` using this API.

<<<<<<< HEAD
=======
* `MvPowerSeries.IsNilpotent_subst` asserts that the constant coefficient
of a legit substitution is nilpotent; prove that the converse holds when
the kernel of `algebraMap R S` is a nilideal.
>>>>>>> master
-/

namespace MvPowerSeries

variable {σ : Type*}
  {A : Type*} [CommSemiring A]
  {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*}
  {S : Type*} [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower A R S]

open WithPiTopology

<<<<<<< HEAD
/-- In this file, rings are given the discrete uniformity -/
local instance localInstanceUniformSpace_bot : UniformSpace S := ⊥

local instance : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S

local instance : ContinuousSMul R (MvPowerSeries τ S) := IsScalarTower.continuousSMul S
=======
attribute [local instance] DiscreteTopology.instContinuousSMul
>>>>>>> master

/-- Families of power series which can be substituted -/
structure HasSubst (a : σ → MvPowerSeries τ S) : Prop where
  const_coeff s : IsNilpotent (constantCoeff τ S (a s))
  coeff_zero d : {s | (a s).coeff S d ≠ 0}.Finite

variable {a : σ → MvPowerSeries τ S}

<<<<<<< HEAD
lemma coeff_zero_iff :
    Filter.Tendsto a Filter.cofinite (@nhds _ (@instTopologicalSpace τ S ⊥) 0) ↔
      ∀ d : τ →₀ ℕ, {s | (a s).coeff S d ≠ 0}.Finite := by
  simp_rw [tendsto_iff_coeff_tendsto, coeff_zero]
  apply forall_congr'
  intro d
  simp [nhds_discrete]

/-- A multivariate power series can be substituted if and only if
it can be evaluated when the topology on the coefficients of its coefficients
is the discrete topology. -/
/- We make the arguments of `HasEval` explicit to be sure that Lean infers the correct topology. -/
lemma hasSubst_iff_hasEval_of_discreteTopology :
    HasSubst a ↔ @HasEval σ _ _ (@instTopologicalSpace τ S ⊥) a :=
  ⟨fun ha ↦
    {
      hpow s := (tendsto_pow_of_constantCoeff_nilpotent_iff (a s)).mpr (ha.const_coeff s)
      tendsto_zero := coeff_zero_iff.mpr ha.coeff_zero },
    fun ha ↦
    {
      const_coeff s := (tendsto_pow_of_constantCoeff_nilpotent_iff (a s)).mp (ha.hpow s)
      coeff_zero d := (coeff_zero_iff.mp ha.tendsto_zero) d }⟩

theorem HasSubst.hasEval (ha : HasSubst a) :
    @HasEval σ (MvPowerSeries τ S) _ (@instTopologicalSpace τ S ⊥) a :=
  hasSubst_iff_hasEval_of_discreteTopology.mp ha

theorem hasSubst_X :
    HasSubst (fun (s : σ) ↦ (X s : MvPowerSeries σ S)) := by
  rw [hasSubst_iff_hasEval_of_discreteTopology]
  exact HasEval.X

theorem hasSubst_zero :
    HasSubst (fun (_ : σ) ↦ (0 : MvPowerSeries τ S)) := by
  rw [hasSubst_iff_hasEval_of_discreteTopology]
  exact HasEval.zero

theorem hasSubst_add {a b : σ → MvPowerSeries τ S}
    (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (a + b) := by
  rw [hasSubst_iff_hasEval_of_discreteTopology] at ha hb ⊢
  exact HasEval.add ha hb

@[simp]
theorem constantCoeff_smul {R : Type*} [Semiring R] {S : Type*} [Semiring S] [Module R S]
    (φ : MvPowerSeries σ S) (a : R) :
    constantCoeff σ S (a • φ) = a • constantCoeff σ S φ :=
  rfl

theorem hasSubst_mul (b : σ → MvPowerSeries τ S)
    {a : σ → MvPowerSeries τ S} (ha : HasSubst a) : HasSubst (b * a) := by
  rw [hasSubst_iff_hasEval_of_discreteTopology] at ha ⊢
  exact HasEval.mul_left b ha

theorem hasSubst_smul (r : MvPowerSeries τ S) {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (r • a) := by convert hasSubst_mul _ ha

/-- Families of mv power series that can be substituted, as an `Ideal` -/
=======
lemma coeff_zero_iff [TopologicalSpace S] [DiscreteTopology S] :
    Filter.Tendsto a Filter.cofinite (nhds 0) ↔
      ∀ d : τ →₀ ℕ, {s | (a s).coeff S d ≠ 0}.Finite := by
  simp_rw [tendsto_iff_coeff_tendsto, coeff_zero]
  apply forall_congr'
  simp [nhds_discrete]

/-- A multivariate power series can be substituted if and only if
it can be evaluated when the topology on the coefficients ring is the discrete topology. -/
lemma hasSubst_iff_hasEval_of_discreteTopology [TopologicalSpace S] [DiscreteTopology S] :
    HasSubst a ↔ HasEval a :=
  ⟨fun ha ↦ ⟨fun s ↦ (tendsto_pow_of_constantCoeff_nilpotent_iff (a s)).mpr (ha.const_coeff s),
      coeff_zero_iff.mpr ha.coeff_zero⟩,
    fun ha ↦ ⟨fun s ↦ (tendsto_pow_of_constantCoeff_nilpotent_iff (a s)).mp (ha.hpow s),
      fun d ↦ (coeff_zero_iff.mp ha.tendsto_zero) d⟩⟩

theorem HasSubst.hasEval [TopologicalSpace S] (ha : HasSubst a) :
    HasEval a := HasEval.mono (instTopologicalSpace_mono τ bot_le) <|
  (@hasSubst_iff_hasEval_of_discreteTopology σ τ _ _ a ⊥ (@DiscreteTopology.mk S ⊥ rfl)).mp ha

theorem hasSubst_X : HasSubst (fun (s : σ) ↦ (X s : MvPowerSeries σ S)) := by
  letI : UniformSpace S := ⊥
  simpa [hasSubst_iff_hasEval_of_discreteTopology] using HasEval.X

theorem hasSubst_zero : HasSubst (fun (_ : σ) ↦ (0 : MvPowerSeries τ S)) := by
  letI : UniformSpace S := ⊥
  simpa [hasSubst_iff_hasEval_of_discreteTopology] using HasEval.zero

theorem hasSubst_add {a b : σ → MvPowerSeries τ S} (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (a + b) := by
  letI : UniformSpace S := ⊥
  rw [hasSubst_iff_hasEval_of_discreteTopology] at ha hb ⊢
  exact ha.add hb

theorem hasSubst_mul (b : σ → MvPowerSeries τ S) {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (b * a) := by
  letI : UniformSpace S := ⊥
  rw [hasSubst_iff_hasEval_of_discreteTopology] at ha ⊢
  exact ha.mul_left b

theorem hasSubst_smul (r : MvPowerSeries τ S) {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (r • a) := hasSubst_mul _ ha

/-- Families of `MvPowerSeries` that can be substituted, as an `Ideal` -/
>>>>>>> master
noncomputable def hasSubst.ideal : Ideal (σ → MvPowerSeries τ S) :=
  { carrier := setOf HasSubst
    add_mem' := hasSubst_add
    zero_mem' := hasSubst_zero
    smul_mem' := hasSubst_mul }

<<<<<<< HEAD
/-- If σ is finite, then the nilpotent condition is enough for HasSubst -/
=======
/-- If `σ` is finite, then the nilpotent condition is enough for `HasSubst` -/
>>>>>>> master
theorem hasSubst_of_constantCoeff_nilpotent [Finite σ]
    {a : σ → MvPowerSeries τ S} (ha : ∀ s, IsNilpotent (constantCoeff τ S (a s))) :
    HasSubst a where
  const_coeff := ha
  coeff_zero _ := Set.toFinite _

<<<<<<< HEAD
/-- If σ is finite, then having zero constant coefficient is enough for HasSubst -/
=======
/-- If `σ` is finite, then having zero constant coefficient is enough for `HasSubst` -/
>>>>>>> master
theorem hasSubst_of_constantCoeff_zero [Finite σ]
    {a : σ → MvPowerSeries τ S} (ha : ∀ s, constantCoeff τ S (a s) = 0) :
    HasSubst a :=
  hasSubst_of_constantCoeff_nilpotent (fun s ↦ by simp only [ha s, IsNilpotent.zero])

<<<<<<< HEAD
/-- Substitution of power series into a power series -/
noncomputable def subst (a : σ → MvPowerSeries τ S) (f : MvPowerSeries σ R) :
    MvPowerSeries τ S :=
  MvPowerSeries.eval₂ (algebraMap _ _) a f

variable {a : σ → MvPowerSeries τ S}

/-- Substitution of power series into a power series -/
noncomputable def substAlgHom (ha : HasSubst a) :
    MvPowerSeries σ R →ₐ[R] MvPowerSeries τ S :=
  MvPowerSeries.aeval ha.hasEval

@[simp]
theorem coe_substAlgHom (ha : HasSubst a) :
    ⇑(substAlgHom ha) = subst (R := R) a :=
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
  aeval_coe ha.hasEval p

theorem substAlgHom_X (ha : HasSubst a) (s : σ) :
    substAlgHom (R := R) ha (X s) = a s := by
  rw [← MvPolynomial.coe_X, substAlgHom_coe, MvPolynomial.aeval_X]
=======
/-- Substitution of power series into a power series

It coincides with evaluation when `f` is a polynomial, or under `HasSubst a`.
Otherwise, it is given the dummy value `0`. -/
noncomputable def subst (a : σ → MvPowerSeries τ S) (f : MvPowerSeries σ R) :
    MvPowerSeries τ S :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  eval₂ (algebraMap _ _) a f

theorem subst_eq_eval₂
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] :
    (subst : (σ → MvPowerSeries τ S) → (MvPowerSeries σ R) → _) = eval₂ (algebraMap _ _) := by
  ext; simp [subst, DiscreteUniformity.eq_bot]

theorem subst_coe (p : MvPolynomial σ R) :
    subst (R := R) a p = MvPolynomial.aeval a p := by
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  rw [subst_eq_eval₂, eval₂_coe, MvPolynomial.aeval_def]

variable {a : σ → MvPowerSeries τ S}

/-- For `HasSubst a`, `MvPowerSeries.subst` is an algebra morphism. -/
noncomputable def substAlgHom (ha : HasSubst a) :
    MvPowerSeries σ R →ₐ[R] MvPowerSeries τ S :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  MvPowerSeries.aeval ha.hasEval

/-- Rewrite `MvPowerSeries.substAlgHom` as `MvPowerSeries.aeval`.

Its use is discouraged because it introduces a topology and might lead
into awkward comparisons. -/
theorem substAlgHom_eq_aeval
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) :
    (substAlgHom ha : MvPowerSeries σ R → MvPowerSeries τ S) = MvPowerSeries.aeval ha.hasEval := by
  simp only [substAlgHom, coe_aeval ha.hasEval]
  convert coe_aeval (R := R) (hasSubst_iff_hasEval_of_discreteTopology.mp ha) <;>
  exact DiscreteUniformity.eq_bot.symm

@[simp]
theorem coe_substAlgHom (ha : HasSubst a) : ⇑(substAlgHom ha) = subst (R := R) a := by
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  rw [substAlgHom_eq_aeval, coe_aeval ha.hasEval, subst_eq_eval₂]

@[simp]
theorem substAlgHom_apply (ha : HasSubst a) (f : MvPowerSeries σ R) :
    substAlgHom ha f = subst a f := by
  rw [coe_substAlgHom]

theorem subst_add (ha : HasSubst a) (f g : MvPowerSeries σ R) :
    subst a (f + g) = subst a f + subst a g := by
  simp only [← substAlgHom_apply ha, map_add]

theorem subst_mul (ha : HasSubst a) (f g : MvPowerSeries σ R) :
    subst a (f * g) = subst a f * subst a g := by
  simp only [← substAlgHom_apply ha, map_mul]

theorem subst_pow (ha : HasSubst a) (f : MvPowerSeries σ R) (n : ℕ) :
    subst a (f ^ n) = (subst a f ) ^ n := by
  simp only [← substAlgHom_apply ha, map_pow]

theorem subst_smul (ha : HasSubst a) (r : A) (f : MvPowerSeries σ R) :
    subst a (r • f) = r • (subst a f) := by
  simp only [← substAlgHom_apply ha, AlgHom.map_smul_of_tower]

theorem substAlgHom_coe (ha : HasSubst a) (p : MvPolynomial σ R) :
    substAlgHom (R := R) ha p = MvPolynomial.aeval a p := by
  simp [substAlgHom]

theorem substAlgHom_X (ha : HasSubst a) (s : σ) :
    substAlgHom (R := R) ha (X s) = a s := by
  rw [← MvPolynomial.coe_X, substAlgHom_coe ha, MvPolynomial.aeval_X]
>>>>>>> master

theorem substAlgHom_monomial (ha : HasSubst a) (e : σ →₀ ℕ) (r : R) :
    substAlgHom ha (monomial R e r) =
      (algebraMap R (MvPowerSeries τ S) r) * (e.prod (fun s n ↦ (a s) ^ n)) := by
  rw [← MvPolynomial.coe_monomial, substAlgHom_coe, MvPolynomial.aeval_monomial]

<<<<<<< HEAD
theorem subst_coe (ha : HasSubst a) (p : MvPolynomial σ R) :
    subst (R := R) a p = MvPolynomial.aeval a p := by
  rw [← coe_substAlgHom ha, substAlgHom_coe]

=======
@[simp]
>>>>>>> master
theorem subst_X (ha : HasSubst a) (s : σ) :
    subst (R := R) a (X s) = a s := by
  rw [← coe_substAlgHom ha, substAlgHom_X]

theorem subst_monomial (ha : HasSubst a) (e : σ →₀ ℕ) (r : R) :
    subst a (monomial R e r) =
      (algebraMap R (MvPowerSeries τ S) r) * (e.prod (fun s n ↦ (a s) ^ n)) := by
  rw [← coe_substAlgHom ha, substAlgHom_monomial]

<<<<<<< HEAD
theorem continuous_subst (ha : HasSubst a) :
    Continuous (subst a : MvPowerSeries σ R → MvPowerSeries τ S) :=
  continuous_eval₂ (continuous_algebraMap _ _) ha.hasEval

theorem coeff_subst_finite (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    Set.Finite (fun d ↦ (coeff R d f) • (coeff S e (d.prod fun s e => (a s) ^ e))).support :=
=======
theorem continuous_subst (ha : HasSubst a)
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] :
    Continuous (subst a : MvPowerSeries σ R → MvPowerSeries τ S) := by
  rw [subst_eq_eval₂]
  exact continuous_eval₂ (continuous_algebraMap _ _) ha.hasEval

theorem coeff_subst_finite (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    Set.Finite (fun d ↦ (coeff R d f) • (coeff S e (d.prod fun s e => (a s) ^ e))).support :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
>>>>>>> master
  Summable.finite_support_of_discreteTopology _
    ((hasSum_aeval ha.hasEval f).map (coeff S e) (continuous_coeff S e)).summable

theorem coeff_subst (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    coeff S e (subst a f) =
      finsum (fun d ↦ (coeff R d f) • (coeff S e (d.prod fun s e => (a s) ^ e))) := by
<<<<<<< HEAD
  have := ((hasSum_aeval ha.hasEval f).map (coeff S e) (continuous_coeff S e))
  erw [← coe_substAlgHom ha, ← this.tsum_eq, tsum_def]
  erw [dif_pos this.summable, if_pos (coeff_subst_finite ha f e)]
  rfl
=======
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  have := ((hasSum_aeval ha.hasEval f).map (coeff S e) (continuous_coeff S e))
  rw [← coe_substAlgHom ha, substAlgHom,  ← this.tsum_eq, tsum_def, dif_pos this.summable]
  exact if_pos (coeff_subst_finite ha f e)
>>>>>>> master

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
    [IsUniformAddGroup T] [IsTopologicalRing T] [IsLinearTopology T T] [Algebra R T]
    {ε : MvPowerSeries τ S →ₐ[R] T}

<<<<<<< HEAD
local instance : ContinuousSMul R T := DiscreteTopology.instContinuousSMul R T

theorem comp_substAlgHom (ha : HasSubst a) (hε : Continuous ε) :
      ε.comp (substAlgHom ha) = aeval (HasEval.map hε ha.hasEval) :=
  comp_aeval ha.hasEval hε

theorem comp_subst (ha : HasSubst a) (hε : Continuous ε) :
    ⇑ε ∘ (subst a) = ⇑(aeval (R := R) (HasEval.map hε ha.hasEval)) := by
  rw [← comp_substAlgHom ha hε, AlgHom.coe_comp, coe_substAlgHom]

theorem comp_subst_apply (ha : HasSubst a) (hε : Continuous ε) (f : MvPowerSeries σ R) :
    ε (subst a f) = aeval (R := R) (HasEval.map hε ha.hasEval) f :=
=======
theorem comp_substAlgHom
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) (hε : Continuous ε) :
    ε.comp (substAlgHom ha) = aeval (ha.hasEval.map hε) := by
  ext f
  simp only [AlgHom.coe_comp, substAlgHom_eq_aeval ha]
  exact DFunLike.congr_fun (comp_aeval ha.hasEval hε) f

theorem comp_subst [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) (hε : Continuous ε) :
    ε ∘ (subst a) = aeval (R := R) (ha.hasEval.map hε) := by
  rw [← comp_substAlgHom ha hε, AlgHom.coe_comp, coe_substAlgHom]

theorem comp_subst_apply
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) (hε : Continuous ε) (f : MvPowerSeries σ R) :
    ε (subst a f) = aeval (R := R) (ha.hasEval.map hε) f :=
>>>>>>> master
  congr_fun (comp_subst ha hε) f

variable [Algebra S T] [IsScalarTower R S T]

<<<<<<< HEAD
theorem eval₂_subst (ha : HasSubst a) {b : τ → T} (hb : HasEval b) (f : MvPowerSeries σ R) :
=======
theorem eval₂_subst
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) {b : τ → T} (hb : HasEval b) (f : MvPowerSeries σ R) :
>>>>>>> master
    eval₂ (algebraMap S T) b (subst a f) =
      eval₂ (algebraMap R T) (fun s ↦ eval₂ (algebraMap S T) b (a s)) f := by
  let ε : MvPowerSeries τ S →ₐ[R] T := (aeval hb).restrictScalars R
  have hε : Continuous ε := continuous_aeval hb
  simpa only [AlgHom.coe_restrictScalars', AlgHom.toRingHom_eq_coe,
    AlgHom.coe_restrictScalars, RingHom.coe_coe, ε, coe_aeval]
    using comp_subst_apply ha hε f

variable {υ : Type*}
  {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {b : τ → MvPowerSeries υ T}

<<<<<<< HEAD
-- TODO? : the converse holds when the kernel of `algebraMap R S` is a nilideal
=======
>>>>>>> master
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
<<<<<<< HEAD
    simp only [Finsupp.prod_zero_index, map_one, coeff_zero_eq_constantCoeff, smul_eq_mul, one_mul]
    exact IsNilpotent.map hf (algebraMap R S)
=======
    simpa using IsNilpotent.map hf (algebraMap R S)
>>>>>>> master
  · apply IsNilpotent.smul
    rw [← ne_eq, Finsupp.ne_iff] at hd
    obtain ⟨t, hs⟩ := hd
    rw [← Finsupp.prod_filter_mul_prod_filter_not (fun i ↦ i = t), map_mul,
      mul_comm, ← smul_eq_mul]
    apply IsNilpotent.smul
    rw [Finsupp.prod_eq_single t]
<<<<<<< HEAD
    · simp only [Finsupp.filter_apply_pos, map_pow]
      exact IsNilpotent.pow_of_pos (ha.const_coeff t) hs
    · intro t' htt' ht'
      simp only [Finsupp.filter_apply, if_neg ht', ne_eq, not_true_eq_false] at htt'
=======
    · simpa using IsNilpotent.pow_of_pos (ha.const_coeff t) hs
    · intro t' htt' ht'
      simp [ht'] at htt'
>>>>>>> master
    · exact fun _ ↦ by rw [pow_zero]

theorem HasSubst.comp (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (fun s ↦ substAlgHom hb (a s)) where
  const_coeff s := IsNilpotent_subst hb (ha.const_coeff s)
  coeff_zero := by
<<<<<<< HEAD
    rw [← coeff_zero_iff]
    apply Filter.Tendsto.comp _ (ha.hasEval.tendsto_zero)
    simp only [← map_zero (substAlgHom (R := S) hb), coe_substAlgHom]
    exact (continuous_subst hb).continuousAt

theorem substAlgHom_comp_substAlgHom (ha : HasSubst a) (hb : HasSubst b) :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha) = substAlgHom (ha.comp hb) := by
  apply comp_aeval (R := R) (ε := (substAlgHom hb).restrictScalars R)
    ha.hasEval
  simp only [AlgHom.coe_restrictScalars', coe_substAlgHom]
  exact (continuous_subst (R := S) hb)
=======
    letI : UniformSpace S := ⊥
    letI : UniformSpace T := ⊥
    rw [← coeff_zero_iff]
    apply Filter.Tendsto.comp _ (ha.hasEval.tendsto_zero)
    simpa [← map_zero (substAlgHom (R := S) hb)] using (continuous_subst hb).continuousAt

theorem substAlgHom_comp_substAlgHom (ha : HasSubst a) (hb : HasSubst b) :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha) = substAlgHom (ha.comp hb) := by
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  letI : UniformSpace T := ⊥
  apply comp_aeval (R := R) (ε := (substAlgHom hb).restrictScalars R) ha.hasEval
  simpa [AlgHom.coe_restrictScalars'] using continuous_subst (R := S) hb
>>>>>>> master

theorem substAlgHom_comp_substAlgHom_apply (ha : HasSubst a) (hb : HasSubst b)
    (f : MvPowerSeries σ R) :
    (substAlgHom hb) (substAlgHom ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

theorem subst_comp_subst (ha : HasSubst a) (hb : HasSubst b) :
    (subst b) ∘ (subst a) = subst (R := R) (fun s ↦ subst b (a s)) := by
<<<<<<< HEAD
  simpa only [funext_iff, coe_substAlgHom, DFunLike.ext_iff,
    AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply]
    using substAlgHom_comp_substAlgHom (R := R) ha hb
=======
  simpa [funext_iff, DFunLike.ext_iff] using substAlgHom_comp_substAlgHom (R := R) ha hb
>>>>>>> master

theorem subst_comp_subst_apply (ha : HasSubst a) (hb : HasSubst b) (f : MvPowerSeries σ R) :
    subst b (subst a f) = subst (fun s ↦ subst b (a s)) f :=
  congr_fun (subst_comp_subst (R := R) ha hb) f

section rescale

/-- Rescale multivariate power series -/
noncomputable def rescale (a : σ → R) (f : MvPowerSeries σ R) :
    MvPowerSeries σ R :=
  subst (a • X) f

theorem rescale_eq_subst (a : σ → R) (f : MvPowerSeries σ R) :
    rescale a f = subst (a • X) f := rfl

<<<<<<< HEAD
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
/-- Rescale multivariate power series, as an `AlgHom` -/
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
=======
theorem hasSubst_rescale (a : σ → R) :
    HasSubst ((a • X) : σ → MvPowerSeries σ R) := by
  convert hasSubst_mul (fun s ↦ algebraMap R (MvPowerSeries σ R) (a s)) hasSubst_X
  simp [funext_iff, algebra_compatible_smul (MvPowerSeries σ R)]

/-- Rescale multivariate power series, as an `AlgHom` -/
noncomputable def rescale_algHom (a : σ → R) :
    MvPowerSeries σ R →ₐ[R] MvPowerSeries σ  R :=
  substAlgHom (hasSubst_rescale a)

theorem coe_rescale_algHom (a : σ → R) :
    rescale_algHom a = rescale a :=
  coe_substAlgHom (hasSubst_rescale a)

theorem rescale_algHom_comp (a b : σ → R) :
    (rescale_algHom a).comp (rescale_algHom b) = rescale_algHom (a * b) := by
  ext f
>>>>>>> master
  simp only [AlgHom.coe_comp, Function.comp_apply, rescale_algHom]
  rw [substAlgHom_comp_substAlgHom_apply]
  congr
  rw [funext_iff]
  intro s
  simp only [Pi.smul_apply', Pi.mul_apply]
<<<<<<< HEAD
  rw [AlgHom.map_smul_of_tower]
  rw [← MvPolynomial.coe_X, substAlgHom_coe, MvPolynomial.aeval_X, MvPolynomial.coe_X]
  simp only [Pi.smul_apply', algebraMap_smul]
  rw [← mul_smul, mul_comm]
=======
  rw [AlgHom.map_smul_of_tower, ← MvPolynomial.coe_X, substAlgHom_coe]
  simp [algebraMap_smul, ← mul_smul, mul_comm]
>>>>>>> master

theorem rescale_rescale_apply (a b : σ → R) (f : MvPowerSeries σ R) :
    (f.rescale b).rescale a = f.rescale (a * b) := by
  simp only [← coe_rescale_algHom, ← AlgHom.comp_apply, rescale_algHom_comp]

theorem coeff_rescale (r : σ → R) (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff R d (rescale r f) = (d.prod fun s n ↦ r s ^ n) • coeff R d f := by
<<<<<<< HEAD
  unfold rescale
  rw [coeff_subst (hasSubst_rescale R _)]
  simp only [Pi.smul_apply', smul_eq_mul, prod_smul_X_eq_smul_monomial_one]
  simp only [LinearMap.map_smul_of_tower, Algebra.mul_smul_comm]
  rw [finsum_eq_single _ d]
  · simp only [coeff_monomial_same, mul_one, smul_eq_mul]
  · intro e he
    simp only [coeff_monomial_ne he.symm, mul_zero, smul_zero]
=======
  rw [rescale_eq_subst, coeff_subst (hasSubst_rescale _)]
  simp only [Pi.smul_apply', smul_eq_mul, prod_smul_X_eq_smul_monomial_one]
  simp only [LinearMap.map_smul_of_tower, Algebra.mul_smul_comm]
  rw [finsum_eq_single _ d]
  · simp
  · intro e he
    simp [coeff_monomial_ne he.symm]
>>>>>>> master

theorem rescale_one :
    rescale 1 = @id (MvPowerSeries σ R) := by
  ext f d
<<<<<<< HEAD
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
=======
  simp [coeff_rescale, Finsupp.prod]

theorem rescale_algHom_one :
    rescale_algHom 1 = AlgHom.id R (MvPowerSeries σ R):= by
  rw [DFunLike.ext_iff]
  intro f
  simp [coe_rescale_algHom, rescale_one]

/-- Rescale a multivariate power series, as a `MonoidHom` in the scaling parameters -/
noncomputable def rescale_MonoidHom : (σ → R) →* MvPowerSeries σ R →ₐ[R] MvPowerSeries σ R where
  toFun := rescale_algHom
>>>>>>> master
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
<<<<<<< HEAD
  · simp only [hd, Pi.zero_apply, Finsupp.prod_zero_index, coeff_zero_eq_constantCoeff,
      smul_eq_mul, one_mul, ↓reduceIte]
=======
  · simp [hd]
>>>>>>> master
  · simp only [Pi.zero_apply, smul_eq_mul, if_neg hd]
    convert zero_smul R _
    simp only [DFunLike.ext_iff, Finsupp.coe_zero, Pi.zero_apply, not_forall] at hd
    obtain ⟨s, hs⟩ := hd
    apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
<<<<<<< HEAD
    simp only [Function.const_apply, zero_pow hs]

/-- Scaling a linear power series is smul -/
=======
    simp [hs]

/-- Rescaling a linear power series is `smul` -/
>>>>>>> master
lemma rescale_linear_eq_smul (r : R) (f : MvPowerSeries σ R)
    (hf : ∀ (d : σ →₀ ℕ), (d.sum (fun _ n ↦ n) ≠ 1) → MvPowerSeries.coeff R d f = 0) :
    MvPowerSeries.rescale (Function.const σ r) f = r • f := by
  ext e
<<<<<<< HEAD
  simp only [MvPowerSeries.coeff_rescale, map_smul]
  simp only [Finsupp.prod, Function.const_apply, Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  by_cases he : Finsupp.sum e (fun _ n ↦ n) = 1
  · simp only [Finsupp.sum] at he
    simp only [he, pow_one]
  · simp only [hf e he, mul_zero]
=======
  simp only [MvPowerSeries.coeff_rescale, map_smul, Finsupp.prod, Function.const_apply,
    Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  by_cases he : Finsupp.sum e (fun _ n ↦ n) = 1
  · simp only [Finsupp.sum] at he
    simp [he]
  · simp [hf e he]
>>>>>>> master

end rescale

end MvPowerSeries
