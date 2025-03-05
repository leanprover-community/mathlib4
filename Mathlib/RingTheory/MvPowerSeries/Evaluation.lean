/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.TopologicallyNilpotent
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.UniformRing

/-! # Evaluation of multivariate power series

Let `σ`, `R` `S` be types, with `CommRing R`, `CommRing S`.
One assumes that `TopologicalRing R` and `UniformAddGroup R`,
and that `S` is a complete and separated topological `R`-algebra,
with `LinearTopology R`, which means there is a basis of neighborhoods of 0
consisting of ideals.

* `MvPowerSeries.eval₂` : Given `φ : R →+* S` and `a : σ → S`,
this file defines an evaluation of `f : MvPowerSeries σ R`,
that extends the evaluation of polynomials at `a`, by density,
provided `φ` and `a` satisfy certain conditions of which
the following lemmas assert the necessity

* `Continuous.on_scalars` : The map `φ` is continuous
* `Continuous.tendsto_apply_pow_zero_of_constantCoeff_zero` :
  for all `s : σ`, `(a s) ^ n` tends to 0 when `n` tends to infinity
* `Continuous.tendsto_apply_variables_zero_of_cofinite`:
  when `a s` tends to  zero for the filter of cofinite subsets of `σ`.

* `MvPowerSeries.eval₂_domain` : the `Prop`-valued structure
that is required to evaluate power series

* `MvPowerSeries.uniformContinuous_eval₂` : uniform continuity of the evaluation

* `MvPowerSeries.continuous_eval₂` : continuity of the evaluation

* `MvPowerSeries.aeval` : the evaluation map as an algebra map

-/

namespace MvPowerSeries

open Topology

open Filter MvPolynomial RingHom Set TopologicalSpace UniformSpace

/- ## Necessary conditions -/

section

variable {σ : Type*}
variable {R : Type*} [CommRing R] [TopologicalSpace R]
variable {S : Type*} [CommRing S] [TopologicalSpace S]
variable {φ : R →+* S}

-- We endow MvPowerSeries σ R with the Pi topology
open WithPiTopology

/-- Families at which power series can be evaluated -/
structure EvalDomain (a : σ → S) : Prop where
  hpow : ∀ s, IsTopologicallyNilpotent (a s)
  tendsto_zero : Tendsto a cofinite (𝓝 0)

/-- The domain of evaluation of `MvPowerSeries`, as an ideal -/
def EvalDomain_ideal [IsTopologicalRing S] [IsLinearTopology S S] :
    Ideal (σ → S) where
  carrier := setOf EvalDomain
  add_mem' {a} {b} ha hb := {
    hpow := fun s ↦ IsTopologicallyNilpotent.add (ha.hpow s) (hb.hpow s)
    tendsto_zero := by
      rw [← add_zero 0]
      exact ha.tendsto_zero.add hb.tendsto_zero }
  zero_mem' := {
    hpow := fun s ↦ by
      simp only [Pi.zero_apply]
      apply tendsto_atTop_of_eventually_const (i₀ := 1)
      intro i hi
      rw [zero_pow (Nat.ne_zero_iff_zero_lt.mpr hi)]
    tendsto_zero := tendsto_const_nhds }
  smul_mem' c {x} hx := {
    hpow := fun s ↦ by
      simp only [IsTopologicallyNilpotent, Pi.smul_apply', smul_eq_mul, mul_pow]
      exact IsLinearTopology.tendsto_mul_zero_of_right _ _ (hx.hpow s)
    tendsto_zero := IsLinearTopology.tendsto_mul_zero_of_right _ _ hx.tendsto_zero }

theorem EvalDomain.comp {a : σ → R} (ha : EvalDomain a) {ε : R →+* S} (hε : Continuous ε) :
    EvalDomain (ε ∘ a) := by
  apply EvalDomain.mk _ ((map_zero ε ▸ Continuous.tendsto' hε 0 (ε 0) rfl).comp ha.tendsto_zero)
  · intro s
    unfold IsTopologicallyNilpotent
    convert (Continuous.tendsto' hε 0 (ε 0) rfl).comp (ha.hpow s)
    · ext n; simp only [Function.comp_apply, map_pow]
    · rw [map_zero]

/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (i) (a & b) -/
theorem EvalDomain.map (hφ : Continuous φ) {a : σ → R} (ha : EvalDomain a) :
    EvalDomain (fun s ↦ φ (a s)) where
  hpow := fun s ↦ IsTopologicallyNilpotent.map hφ (ha.hpow s)
  tendsto_zero := (map_zero φ ▸ hφ.tendsto 0).comp ha.tendsto_zero

theorem EvalDomain.evalDomain_X :
    EvalDomain (fun s ↦ (MvPowerSeries.X s : MvPowerSeries σ R)) where
  hpow := fun s ↦ tendsto_pow_zero_of_constantCoeff_zero (constantCoeff_X s)
  tendsto_zero := by
    classical
    exact variables_tendsto_zero

theorem Continuous.on_scalars {ε : MvPowerSeries σ R →+* S} (hε : Continuous ε) :
    Continuous (ε.comp (C σ R)) := by
  rw [coe_comp]
  exact Continuous.comp hε MvPowerSeries.WithPiTopology.continuous_C

/-- The inclusion of polynomials into power series has dense image -/
theorem _root_.MvPolynomial.coeToMvPowerSeries_denseRange :
    DenseRange (coeToMvPowerSeries.ringHom (R := R) (σ := σ)) := fun f => by
  have : Tendsto (fun d ↦ (trunc' R d f : MvPowerSeries σ R)) atTop (𝓝 f) := by
    rw [tendsto_iff_coeff_tendsto]
    refine fun d ↦ tendsto_atTop_of_eventually_const fun n (hdn : d ≤ n) ↦ ?_
    simp [coeff_trunc', hdn]
  exact mem_closure_of_tendsto this <| .of_forall fun _ ↦ mem_range_self _

end

/- ## Construction of an evaluation morphism for power series -/

section Evaluation

open WithPiTopology

variable {σ : Type*} -- [DecidableEq σ]
variable {R : Type*} [CommRing R] [UniformSpace R]
variable {S : Type*} [CommRing S] [UniformSpace S]
variable {φ : R →+* S} -- (hφ : Continuous φ)

-- We endow MvPowerSeries σ R with the product uniform structure
private instance : UniformSpace (MvPolynomial σ R) :=
  comap toMvPowerSeries (Pi.uniformSpace _)

/-- The induced uniform structure of MvPolynomial σ R is an add group uniform structure -/
private instance [UniformAddGroup R] : UniformAddGroup (MvPolynomial σ R) :=
  UniformAddGroup.comap coeToMvPowerSeries.ringHom

theorem _root_.MvPolynomial.coeToMvPowerSeries_uniformInducing :
    IsUniformInducing (coeToMvPowerSeries.ringHom (σ := σ) (R := R)) :=
  (isUniformInducing_iff ⇑coeToMvPowerSeries.ringHom).mpr rfl

theorem _root_.MvPolynomial.coeToMvPowerSeries_denseInducing :
    IsDenseInducing (coeToMvPowerSeries.ringHom (σ := σ) (R := R)) :=
  coeToMvPowerSeries_uniformInducing.isDenseInducing coeToMvPowerSeries_denseRange

variable {a : σ → S}

/- The evaluation map on multivariate polynomials is uniformly continuous
for the uniform structure induced by that on multivariate power series. -/
theorem _root_.MvPolynomial.coeToMvPowerSeries_uniformContinuous
    [UniformAddGroup R] [UniformAddGroup S] [IsLinearTopology S S]
    (hφ : Continuous φ) (ha : EvalDomain a) :
    UniformContinuous (MvPolynomial.eval₂Hom φ a) := by
  classical
  apply uniformContinuous_of_continuousAt_zero
  intro u hu
  simp only [coe_eval₂Hom, (induced_iff_nhds_eq _).mp rfl, coe_zero, mem_map, mem_comap]
  rw [map_zero, IsLinearTopology.hasBasis_ideal.mem_iff] at hu
  rcases hu with ⟨I, hI, hI'⟩
  let tendsto_zero := ha.tendsto_zero
  let hpow := ha.hpow
  simp only [tendsto_def] at tendsto_zero hpow
  specialize tendsto_zero I hI
  simp only [mem_cofinite] at tendsto_zero
  let hpow' := fun s ↦ hpow s hI
  simp only [mem_map, mem_atTop_sets, ge_iff_le, mem_preimage, SetLike.mem_coe] at hpow'
  let n : σ → ℕ := fun s ↦ sInf {n : ℕ | (a s) ^ n.succ ∈ I}
  have hn_ne : ∀ s, Set.Nonempty {n : ℕ | (a s) ^ n.succ ∈ I} := fun s ↦ by
    rcases hpow' s with ⟨n, hn⟩
    use n
    simp only [mem_setOf_eq, hn n.succ (Nat.le_succ n)]
  have hn : Set.Finite (n.support) := by
    apply @Finite.Set.subset  _ _ _ tendsto_zero
    intro s
    simp only [Function.mem_support, ne_eq, mem_compl_iff, mem_preimage, SetLike.mem_coe, not_not,
      not_imp_comm, imp_or, n, Nat.sInf_eq_zero, mem_setOf_eq, zero_add, pow_one, imp_self, true_or]
  let n₀ : σ →₀ ℕ := {
    toFun := n
    support := hn.toFinset
    mem_support_toFun := fun (s : σ) ↦ by simp }
  let D := Iic n₀
  have hD : Set.Finite D := finite_Iic _
  use iInter (fun (d : D) ↦ { p | φ (p d.val) ∈ I})
  rw [nhds_pi, Filter.mem_pi]
  constructor
  · use D, hD
    use fun d ↦ if d ∈ D then φ ⁻¹' I else univ
    constructor
    · intro d
      split_ifs with hd
      · exact hφ.continuousAt.preimage_mem_nhds (map_zero φ ▸ hI)
      · exact univ_mem
    · intro p
      simp only [Set.mem_pi, mem_ite_univ_right, mem_preimage, SetLike.mem_coe,
        iInter_coe_set, mem_iInter]
      exact fun hp i hi ↦ hp i hi hi
  · intro p hp
    simp only [iInter_coe_set, mem_preimage, coeToMvPowerSeries.ringHom_apply,
      mem_iInter, mem_setOf_eq] at hp
    simp only [mem_preimage]
    apply hI'
    simp only [coe_eval₂Hom, SetLike.mem_coe]
    rw [eval₂_eq]
    apply Ideal.sum_mem
    intro d _
    by_cases hd : d ∈ D
    · exact Ideal.mul_mem_right _ _ (hp d hd)
    · apply Ideal.mul_mem_left
      simp only [mem_Iic, D, Finsupp.le_iff] at hd
      push_neg at hd
      rcases hd with ⟨s, hs', hs⟩
      exact I.mem_prod_of_mem hs' (I.pow_mem_of_pow_mem (Nat.sInf_mem (hn_ne s)) hs)

variable (φ a)
/-- Evaluation of power series. Meaningful on adequate elements or on `MvPolynomial`)  -/
noncomputable def eval₂ (f : MvPowerSeries σ R) : S := by
  let hp := fun (p : MvPolynomial σ R) ↦ p = f
  classical
  exact if (Classical.epsilon hp = f) then (MvPolynomial.eval₂ φ a (Classical.epsilon hp))
    else IsDenseInducing.extend coeToMvPowerSeries_denseInducing (MvPolynomial.eval₂ φ a) f

theorem eval₂_coe (f : MvPolynomial σ R) :
    MvPowerSeries.eval₂ φ a f = MvPolynomial.eval₂ φ a f := by
  have hf := Classical.epsilon_spec
    (p := fun (p : MvPolynomial σ R) ↦ p = (f : MvPowerSeries σ R)) ⟨f, rfl⟩
  rw [eval₂, if_pos hf]
  apply _root_.congr_arg
  rw [← MvPolynomial.coe_inj, hf]

theorem eval₂_C (r : R) :
    eval₂ φ a (C σ R r) = φ r := by
  rw [← coe_C, eval₂_coe, MvPolynomial.eval₂_C]

theorem eval₂_X (s : σ) :
    eval₂ φ a (X s) = a s := by
  rw [← coe_X, eval₂_coe, MvPolynomial.eval₂_X]

variable [IsTopologicalSemiring R] [UniformAddGroup R]
    [UniformAddGroup S] [CompleteSpace S] [T2Space S]
    [IsTopologicalRing S] [IsLinearTopology S S]

variable {φ a}

/-- Evaluation of power series at adequate elements, as a `RingHom` -/
noncomputable def eval₂Hom (hφ : Continuous φ) (ha : EvalDomain a) :
    MvPowerSeries σ R →+* S :=
  IsDenseInducing.extendRingHom
    coeToMvPowerSeries_uniformInducing
    coeToMvPowerSeries_denseRange
    (coeToMvPowerSeries_uniformContinuous hφ ha)

theorem eval₂Hom_apply (hφ : Continuous φ) (ha : EvalDomain a) (f : MvPowerSeries σ R) :
    eval₂Hom hφ ha f =
      coeToMvPowerSeries_denseInducing.extend (MvPolynomial.eval₂ φ a) f :=
  rfl

theorem coe_eval₂Hom (hφ : Continuous φ) (ha : EvalDomain a) :
    ⇑(eval₂Hom hφ ha) = eval₂ φ a := by
  ext f
  let hf := fun (p : MvPolynomial σ R) ↦ p = f
  simp only [eval₂Hom_apply, eval₂]
  split_ifs with h
  · conv_lhs => rw [← h]
    simpa only [MvPolynomial.coe_eval₂Hom, coeToMvPowerSeries.ringHom_apply]
      using IsDenseInducing.extend_eq coeToMvPowerSeries_denseInducing
        (coeToMvPowerSeries_uniformContinuous hφ ha).continuous (Classical.epsilon hf)
  · rfl

theorem uniformContinuous_eval₂ (hφ : Continuous φ) (ha : EvalDomain a) :
    UniformContinuous (eval₂ φ a) := by
  rw [← coe_eval₂Hom hφ ha]
  exact uniformContinuous_uniformly_extend
    coeToMvPowerSeries_uniformInducing
    coeToMvPowerSeries_denseRange
    (coeToMvPowerSeries_uniformContinuous hφ ha)

theorem continuous_eval₂ (hφ : Continuous φ) (ha : EvalDomain a) :
    Continuous (eval₂ φ a : MvPowerSeries σ R → S) :=
  (uniformContinuous_eval₂ hφ ha).continuous

theorem hasSum_eval₂ (hφ : Continuous φ) (ha : EvalDomain a)(f : MvPowerSeries σ R) :
    HasSum
    (fun (d : σ →₀ ℕ) ↦ φ (coeff R d f) * (d.prod fun s e => (a s) ^ e))
    (MvPowerSeries.eval₂ φ a f) := by
  rw [← coe_eval₂Hom hφ ha, eval₂Hom_apply hφ ha]
  convert (hasSum_of_monomials_self f).map (eval₂Hom hφ ha) (?_) with d
  · simp only [Function.comp_apply, coe_eval₂Hom, ← MvPolynomial.coe_monomial,
    eval₂_coe, eval₂_monomial]
  · rw [coe_eval₂Hom]; exact continuous_eval₂ hφ ha

theorem eval₂_eq_sum (hφ : Continuous φ) (ha : EvalDomain a)(f : MvPowerSeries σ R) :
    MvPowerSeries.eval₂ φ a f =
      tsum (fun (d : σ →₀ ℕ) ↦ φ (coeff R d f) * (d.prod fun s e => (a s) ^ e)) :=
  (hasSum_eval₂ hφ ha f).tsum_eq.symm

theorem eval₂_unique (hφ : Continuous φ) (ha : EvalDomain a)
    {ε : MvPowerSeries σ R →+* S} (hε : Continuous ε)
    (h : ∀ p : MvPolynomial σ R, ε p = MvPolynomial.eval₂ φ a p) :
    ε = eval₂ φ a := by
  rw [← coe_eval₂Hom hφ ha]
  exact (MvPolynomial.coeToMvPowerSeries_denseInducing.extend_unique h hε).symm

theorem comp_eval₂ (hφ : Continuous φ) (ha : EvalDomain a)
    {T : Type*} [UniformSpace T] [CompleteSpace T] [T2Space T]
    [CommRing T] [IsTopologicalRing T] [IsLinearTopology T T] [UniformAddGroup T]
    {ε : S →+* T} (hε : Continuous ε) :
    ε ∘ eval₂ φ a = eval₂ (ε.comp φ) (ε ∘ a) := by
  rw [← coe_eval₂Hom hφ ha, ← coe_comp]
  apply eval₂_unique _ (ha.comp hε)
  · simp only [coe_comp, coe_eval₂Hom hφ ha]
    exact Continuous.comp hε (continuous_eval₂ hφ ha)
  · intro p
    simp only [coe_comp, Function.comp_apply, eval₂_coe]
    rw [coe_eval₂Hom hφ ha, eval₂_coe φ a, ← MvPolynomial.coe_eval₂Hom, ← comp_apply,
    MvPolynomial.comp_eval₂Hom]
    rfl
  · simp only [coe_comp, Continuous.comp hε hφ]

variable [Algebra R S] [ContinuousSMul R S]

/-- Evaluation of power series at adequate elements, as an `AlgHom` -/
noncomputable def aeval (ha : EvalDomain a) : MvPowerSeries σ R →ₐ[R] S where
  toRingHom := MvPowerSeries.eval₂Hom (continuous_algebraMap R S) ha
  commutes' := fun r ↦ by
    simp only [toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
    rw [← c_eq_algebraMap, coe_eval₂Hom, eval₂_C]

theorem coe_aeval (ha : EvalDomain a) :
    ⇑(MvPowerSeries.aeval ha) = MvPowerSeries.eval₂ (algebraMap R S) a := by
  simp only [aeval, AlgHom.coe_mk, coe_eval₂Hom]

theorem continuous_aeval (ha : EvalDomain a) : Continuous (aeval ha : MvPowerSeries σ R → S) := by
  rw [coe_aeval]
  exact continuous_eval₂ (continuous_algebraMap R S) ha

theorem aeval_coe (ha : EvalDomain a) (p : MvPolynomial σ R) :
    MvPowerSeries.aeval ha (p : MvPowerSeries σ R) = MvPolynomial.aeval a p := by
  rw [coe_aeval, aeval_def, eval₂_coe]

theorem aeval_unique {ε : MvPowerSeries σ R →ₐ[R] S} (hε : Continuous ε) :
    ε = aeval (EvalDomain.evalDomain_X.map hε) := by
  apply DFunLike.ext'
  rw [coe_aeval]
  apply eval₂_unique (continuous_algebraMap R S) _ hε
  · intro p
    induction p using MvPolynomial.induction_on with
    | h_C r =>
      simp only [AlgHom.toRingHom_eq_coe, coe_C, coe_coe, MvPolynomial.eval₂_C]
      rw [c_eq_algebraMap, AlgHom.commutes]
    | h_add p q hp hq =>
      simp only [AlgHom.toRingHom_eq_coe, coe_coe] at hp hq
      simp only [AlgHom.toRingHom_eq_coe, coe_add, map_add, coe_coe, eval₂_add, hp, hq]
    | h_X p s h =>
      simp only [AlgHom.toRingHom_eq_coe, coe_coe] at h
      simp only [AlgHom.toRingHom_eq_coe, MvPolynomial.coe_mul, coe_X, map_mul, coe_coe, eval₂_mul,
        MvPolynomial.eval₂_X, h]
  · exact EvalDomain.evalDomain_X.comp hε

theorem hasSum_aeval (ha : EvalDomain a) (f : MvPowerSeries σ R) :
    HasSum (fun (d : σ →₀ ℕ) ↦ (coeff R d f) • (d.prod fun s e => (a s) ^ e))
      (MvPowerSeries.aeval ha f) := by
  simp_rw [coe_aeval, ← algebraMap_smul (R := R) S, smul_eq_mul]
  exact hasSum_eval₂ (continuous_algebraMap R S) ha f

theorem aeval_eq_sum (ha : EvalDomain a) (f : MvPowerSeries σ R) :
    MvPowerSeries.aeval ha f =
      tsum (fun (d : σ →₀ ℕ) ↦ (coeff R d f) • (d.prod fun s e => (a s) ^ e)) :=
  (hasSum_aeval ha f).tsum_eq.symm

theorem comp_aeval (ha : EvalDomain a)
    {T : Type*} [CommRing T] [UniformSpace T] [UniformAddGroup T]
    [IsTopologicalRing T] [IsLinearTopology T T]
    [T2Space T] [Algebra R T] [ContinuousSMul R T] [CompleteSpace T]
    {ε : S →ₐ[R] T} (hε : Continuous ε) :
    ε.comp (aeval ha) = aeval (ha.map hε)  := by
  apply DFunLike.coe_injective
  simp only [AlgHom.coe_comp, coe_aeval ha]
  erw [comp_eval₂ (continuous_algebraMap R S) ha hε, coe_aeval]
  apply congr_arg₂
  · simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower, RingHom.coe_coe]
  · rfl

end Evaluation

end MvPowerSeries
