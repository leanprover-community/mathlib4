/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/

import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.UniformGroup
import Mathlib.Topology.UniformSpace.Pi

/-! # Topology on power series

Let `R` be with Semiring R` and `TopologicalSpace R`
In this file we the topology on `MvPowerSeries σ R`
that corresponds to the simple convergence on its coefficients.
It is the coarsest topology for which all coefficients maps are continuous.

When `R` has `UniformSpace R`, we define the corresponding uniform structure.

When the type of coefficients has the discrete topology,
it corresponds to the topology defined by [bourbaki1981], chapter 4, §4, n°2

It is *not* the adic topology in general.

- `tendsto_pow_zero_of_constantCoeff_nilpotent`, `tendsto_pow_zero_of_constantCoeff_zero`:
if the constant coefficient of `f` is nilpotent, or vanishes,
then the powers of `f` converge to zero.

- `tendsto_pow_of_constantCoeff_nilpotent_iff` : the powers of `f` converge to zero iff
the constant coefficient of `f` is nilpotent

- `hasSum_of_monomials_self` : viewed as an infinite sum, a power series coverges to itself

TODO: add the similar result for the series of homogeneous components

## Instances

- If `R` is a topological (semi)ring, then so is `MvPowerSeries σ R`

- If the topology of `R` is T2, then so is that of `MvPowerSeries σ R``

- If `R` is a `uniformAddGroup`, then so is `MvPowerSeries σ R``

- If `R` is complete, then so is `MvPowerSeries σ R`

-/


theorem Finset.prod_one_add {ι R : Type _} [DecidableEq ι] [CommRing R] {f : ι → R} (s : Finset ι) :
    (s.prod fun i => 1 + f i) = s.powerset.sum fun t => t.prod f := by
  simp_rw [add_comm, Finset.prod_add]
  congr
  ext t
  convert mul_one (Finset.prod t fun a => f a)
  exact Finset.prod_eq_one (fun i _ => rfl)

theorem MvPowerSeries.coeff_eq_apply {σ R : Type _} [Semiring R] (f : MvPowerSeries σ R)
    (d : σ →₀ ℕ) : MvPowerSeries.coeff R d f = f d :=
  rfl

namespace MvPowerSeries

open Function

variable (σ : Type _) (R : Type _)

namespace WithPiTopology

variable [TopologicalSpace R]

/-- The pointwise topology on MvPowerSeries -/
scoped instance topologicalSpace : TopologicalSpace (MvPowerSeries σ R) :=
  Pi.topologicalSpace

/-- Components are continuous -/
theorem continuous_component :
    ∀ d : σ →₀ ℕ, Continuous fun a : MvPowerSeries σ R => a d :=
  continuous_pi_iff.mp continuous_id

variable {σ R}

/-- coeff are continuous -/
theorem continuous_coeff [Semiring R] (d : σ →₀ ℕ) :
    Continuous (MvPowerSeries.coeff R d) :=
  continuous_component σ R d

/-- constant_coeff is continuous -/
theorem continuous_constantCoeff [Semiring R] :
    Continuous (constantCoeff σ R) :=
  continuous_component σ R 0

/-- A family of power series converges iff it converges coefficientwise -/
theorem tendsto_iff_coeff_tendsto [Semiring R] {ι : Type _}
    (f : ι → MvPowerSeries σ R) (u : Filter ι) (g : MvPowerSeries σ R) :
    Filter.Tendsto f u (nhds g) ↔
    ∀ d : σ →₀ ℕ, Filter.Tendsto (fun i => coeff R d (f i)) u (nhds (coeff R d g)) := by
  rw [nhds_pi, Filter.tendsto_pi]
  exact forall_congr' (fun d => Iff.rfl)

variable (σ R)

/-- The semiring topology on MvPowerSeries of a topological semiring -/
@[scoped instance] theorem topologicalSemiring [Semiring R] [TopologicalSemiring R] :
    TopologicalSemiring (MvPowerSeries σ R) where
    continuous_add := continuous_pi fun d => Continuous.comp continuous_add
      (Continuous.prod_mk (Continuous.fst' (continuous_component σ R d))
        (Continuous.snd' (continuous_component σ R d)))
    continuous_mul := continuous_pi fun _ => continuous_finset_sum _ (fun i _ => Continuous.comp
      continuous_mul (Continuous.prod_mk (Continuous.fst' (continuous_component σ R i.fst))
        (Continuous.snd' (continuous_component σ R i.snd))))

/-- The ring topology on MvPowerSeries of a topological ring -/
@[scoped instance] theorem topologicalRing [Ring R] [TopologicalRing R] :
    TopologicalRing (MvPowerSeries σ R) :=
  { topologicalSemiring σ R with
    continuous_neg := continuous_pi fun d ↦ Continuous.comp continuous_neg
      (continuous_component σ R d) }

/-- MvPowerSeries on a T2Space form a T2Space -/
@[scoped instance] theorem t2Space [T2Space R] : T2Space (MvPowerSeries σ R) where
  t2 x y h := by
    obtain ⟨d, h⟩ := Function.ne_iff.mp h
    obtain ⟨u, v, ⟨hu, hv, hx, hy, huv⟩⟩ := t2_separation h
    exact ⟨(fun x => x d) ⁻¹' u, (fun x => x d) ⁻¹' v,
      IsOpen.preimage (continuous_component σ R d) hu,
      IsOpen.preimage (continuous_component σ R d) hv, hx, hy,
      Disjoint.preimage _ huv⟩

end WithPiTopology

namespace WithPiUniformity

open WithPiTopology

variable [UniformSpace R]

/-- The componentwise uniformity on MvPowerSeries -/
scoped instance uniformSpace : UniformSpace (MvPowerSeries σ R) :=
  Pi.uniformSpace fun _ : σ →₀ ℕ => R

/-- Components are uniformly continuous -/
theorem uniformContinuous_component :
    ∀ d : σ →₀ ℕ, UniformContinuous fun a : MvPowerSeries σ R => a d :=
  uniformContinuous_pi.mp uniformContinuous_id

/-- The uniform_add_group structure on MvPowerSeries of a uniform_add_group -/
@[scoped instance] theorem uniformAddGroup [AddGroup R] [UniformAddGroup R] :
    UniformAddGroup (MvPowerSeries σ R) where
  uniformContinuous_sub := uniformContinuous_pi.mpr fun _ => UniformContinuous.comp
    uniformContinuous_sub
    (UniformContinuous.prod_mk
      (UniformContinuous.comp (uniformContinuous_component _ _ _) uniformContinuous_fst)
      (UniformContinuous.comp (uniformContinuous_component _ _ _) uniformContinuous_snd))

/-- Completeness of the uniform structure on MvPowerSeries -/
@[scoped instance] theorem completeSpace [AddGroup R] [CompleteSpace R] :
    CompleteSpace (MvPowerSeries σ R) where
  complete := by
    intro f hf
    suffices ∀ d, ∃ x, (f.map fun a => a d) ≤ nhds x by
      use fun d => (this d).choose
      rw [nhds_pi, Filter.le_pi]
      exact fun d => (this d).choose_spec
    intro d
    use lim (f.map fun a => a d)
    exact (Cauchy.map hf (uniformContinuous_component σ R d)).le_nhds_lim

/-- Separation of the uniform structure on MvPowerSeries -/
@[scoped instance] theorem t0Space [T0Space R] : T0Space (MvPowerSeries σ R) := by
  suffices T2Space (MvPowerSeries σ R) by infer_instance
  exact WithPiTopology.t2Space σ R

/-- The ring of multivariate power series is a uniform topological ring -/
@[scoped instance] theorem uniform_topologicalRing [Ring R] [UniformAddGroup R] [TopologicalRing R] :
    TopologicalRing (MvPowerSeries σ R) :=
  { uniformAddGroup σ R with
    continuous_add :=  (@uniformContinuous_add _ _ _ (uniformAddGroup σ R)).continuous
    continuous_mul := continuous_pi fun _ => continuous_finset_sum _ fun i _ => Continuous.comp
      continuous_mul (Continuous.prod_mk (Continuous.fst' (continuous_component σ R i.fst))
        (Continuous.snd' (continuous_component σ R i.snd)))
    continuous_neg := (@uniformContinuous_neg _ _ _ (uniformAddGroup σ R)).continuous
    }

end WithPiUniformity

variable {σ R} [DecidableEq σ]
variable [TopologicalSpace R]

open WithPiTopology

theorem continuous_C [Ring R] [TopologicalRing R] :
    Continuous (C σ R) := by
  apply continuous_of_continuousAt_zero
  rw [continuousAt_pi]
  intro d
  change ContinuousAt (fun y => coeff R d ((C σ R) y)) 0
  by_cases hd : d = 0
  · convert continuousAt_id
    rw [hd, coeff_zero_C, id_eq]
  · convert continuousAt_const
    rw [coeff_C, if_neg hd]

theorem variables_tendsto_zero [Ring R] [TopologicalRing R] :
    Filter.Tendsto (fun s : σ => (X s : MvPowerSeries σ R)) Filter.cofinite (nhds 0) := by
  classical
  rw [tendsto_pi_nhds]
  intro d s hs
  rw [Filter.mem_map, Filter.mem_cofinite, ← Set.preimage_compl]
  by_cases h : ∃ i, d = Finsupp.single i 1
  · obtain ⟨i, rfl⟩ := h
    apply Set.Finite.subset (Set.finite_singleton i)
    intro x
    simp only [OfNat.ofNat, Zero.zero] at hs
    rw [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, not_imp_comm]
    intro hx
    convert mem_of_mem_nhds hs
    rw [← coeff_eq_apply (X x) (Finsupp.single i 1), coeff_X, if_neg]
    rfl
    · simp only [Finsupp.single_eq_single_iff, Ne.symm hx, and_true, one_ne_zero, and_self,
      or_self, not_false_eq_true]
  · convert Set.finite_empty
    rw [Set.eq_empty_iff_forall_not_mem]
    intro x
    rw [Set.mem_preimage, Set.not_mem_compl_iff]
    convert mem_of_mem_nhds hs using 1
    rw [← coeff_eq_apply (X x) d, coeff_X, if_neg]
    rfl
    · intro h'
      apply h
      exact ⟨x, h'⟩

theorem tendsto_pow_zero_of_constantCoeff_nilpotent [CommRing R]
    {f} (hf : IsNilpotent (constantCoeff σ R f)) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) := by
  classical
  obtain ⟨m, hm⟩ := hf
  simp_rw [tendsto_iff_coeff_tendsto, coeff_zero]
  exact fun d =>  tendsto_atTop_of_eventually_const fun n hn =>
    coeff_eq_zero_of_constantCoeff_nilpotent hm hn

theorem tendsto_pow_zero_of_constantCoeff_zero [CommRing R]
    {f} (hf : constantCoeff σ R f = 0) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) := by
  apply tendsto_pow_zero_of_constantCoeff_nilpotent
  rw [hf]
  exact IsNilpotent.zero

/-- The powers of a `MvPowerSeries` converge to 0 iff its constant coefficient is nilpotent.
N. Bourbaki, *Algebra II*, [bourbaki1981] (chap. 4, §4, n°2, corollaire de la prop. 3) -/
theorem tendsto_pow_of_constantCoeff_nilpotent_iff [CommRing R] [DiscreteTopology R] (f) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) ↔
      IsNilpotent (constantCoeff σ R f) := by
  refine ⟨?_, tendsto_pow_zero_of_constantCoeff_nilpotent ⟩
  intro h
  suffices Filter.Tendsto (fun n : ℕ => constantCoeff σ R (f ^ n)) Filter.atTop (nhds 0) by
    simp only [Filter.tendsto_def] at this
    specialize this {0} _
    suffices  ∀ x : R, {x} ∈ nhds x by exact this 0
    rw [← discreteTopology_iff_singleton_mem_nhds]; infer_instance
    simp only [map_pow, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage,
      Set.mem_singleton_iff] at this
    obtain ⟨m, hm⟩ := this
    use m
    apply hm m (le_refl m)
  simp only [← @comp_apply _ R ℕ]
  rw [← Filter.tendsto_map'_iff]
  simp only [Filter.Tendsto, Filter.map_le_iff_le_comap] at h ⊢
  apply le_trans h
  apply Filter.comap_mono
  rw [← Filter.map_le_iff_le_comap]
  apply continuous_constantCoeff.continuousAt


variable [Semiring R]

/-- A power series is the sum (in the sense of summable families) of its monomials -/
theorem hasSum_of_monomials_self (f : MvPowerSeries σ R) :
    HasSum (fun d : σ →₀ ℕ => monomial R d (coeff R d f)) f := by
  rw [Pi.hasSum]
  intro d
  convert hasSum_single d ?_ using 1
  exact (coeff_monomial_same d _).symm
  exact fun d' h ↦ coeff_monomial_ne (Ne.symm h) _

/-- If the coefficient space is T2, then the power series is `tsum` of its monomials -/
theorem as_tsum [T2Space R] (f : MvPowerSeries σ R) :
    f = tsum fun d : σ →₀ ℕ => monomial R d (coeff R d f) :=
  (HasSum.tsum_eq (hasSum_of_monomials_self _)).symm

end MvPowerSeries
