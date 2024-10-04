/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.Ring.Basic

/-! # Product topology on MvPowerSeries

Let `R` be with `Semiring R` and `TopologicalSpace R`. In this file we define the topology on
`MvPowerSeries σ R` that corresponds to the simple convergence on its coefficients.
It is the coarsest topology for which all coefficients maps are continuous.

When `R` has `UniformSpace R`, we define the corresponding uniform structure.

This topology can be included by writing `open scoped MvPowerSeries.WithPiTopology`.

When the type of coefficients has the discrete topology,
it corresponds to the topology defined by [bourbaki1981], chapter 4, §4, n°2.

It is *not* the adic topology in general.

- `MvPowerSeries.WithPiTopology.tendsto_pow_zero_of_constantCoeff_nilpotent`,
`MvPowerSeries.WithPiTopology.tendsto_pow_zero_of_constantCoeff_zero`: if the constant coefficient
of `f` is nilpotent, or vanishes, then the powers of `f` converge to zero.

- `MvPowerSeries.WithPiTopology.tendsto_pow_of_constantCoeff_nilpotent_iff` : the powers of `f`
converge to zero iff the constant coefficient of `f` is nilpotent.

- `MvPowerSeries.WithPiTopology.hasSum_of_monomials_self` : viewed as an infinite sum, a power
series coverges to itself.

TODO: add the similar result for the series of homogeneous components.

## Instances

- If `R` is a topological (semi)ring, then so is `MvPowerSeries σ R`.

- If the topology of `R` is T0 or T2, then so is that of `MvPowerSeries σ R`.

- If `R` is a `UniformAddGroup`, then so is `MvPowerSeries σ R`.

- If `R` is complete, then so is `MvPowerSeries σ R`.

-/

theorem MvPowerSeries.apply_eq_coeff {σ R : Type _} [Semiring R] (f : MvPowerSeries σ R)
    (d : σ →₀ ℕ) : f d = MvPowerSeries.coeff R d f := rfl

namespace MvPowerSeries

open Filter Function Set

variable {σ R : Type*}

namespace WithPiTopology

section Topology

variable [TopologicalSpace R]

variable (R) in
/-- The pointwise topology on MvPowerSeries -/
scoped instance : TopologicalSpace (MvPowerSeries σ R) := Pi.topologicalSpace

/-- MvPowerSeries on a T0Space form a T0Space -/
@[scoped instance]
theorem instT0Space [T0Space R] : T0Space (MvPowerSeries σ R) := Pi.instT0Space

/-- MvPowerSeries on a T2Space form a T2Space -/
@[scoped instance]
theorem instT2Space [T2Space R] : T2Space (MvPowerSeries σ R) := Pi.t2Space

variable (R) in
/-- coeff are continuous -/
theorem continuous_coeff [Semiring R] (d : σ →₀ ℕ) : Continuous (MvPowerSeries.coeff R d) :=
  continuous_pi_iff.mp continuous_id d

variable (R) in
/-- constant_coeff is continuous -/
theorem continuous_constantCoeff [Semiring R] : Continuous (constantCoeff σ R) :=
  continuous_coeff R 0

/-- A family of power series converges iff it converges coefficientwise -/
theorem tendsto_iff_coeff_tendsto [Semiring R] {ι : Type*}
    (f : ι → MvPowerSeries σ R) (u : Filter ι) (g : MvPowerSeries σ R) :
    Filter.Tendsto f u (nhds g) ↔
    ∀ d : σ →₀ ℕ, Filter.Tendsto (fun i => coeff R d (f i)) u (nhds (coeff R d g)) := by
  rw [nhds_pi, Filter.tendsto_pi]
  exact forall_congr' (fun d => Iff.rfl)

variable (σ R)

/-- The semiring topology on MvPowerSeries of a topological semiring -/
@[scoped instance]
theorem instTopologicalSemiring [Semiring R] [TopologicalSemiring R] :
    TopologicalSemiring (MvPowerSeries σ R) where
    continuous_add := continuous_pi fun d => continuous_add.comp
      ((continuous_coeff R d).fst'.prod_mk (continuous_coeff R d).snd')
    continuous_mul := continuous_pi fun _ => continuous_finset_sum _ (fun i _ => continuous_mul.comp
       ((continuous_coeff R i.fst).fst'.prod_mk (continuous_coeff R i.snd).snd'))

/-- The ring topology on MvPowerSeries of a topological ring -/
@[scoped instance]
theorem instTopologicalRing (R : Type*) [TopologicalSpace R] [Ring R] [TopologicalRing R] :
    TopologicalRing (MvPowerSeries σ R) :=
  { instTopologicalSemiring σ R with
    continuous_neg := continuous_pi fun d ↦ Continuous.comp continuous_neg
      (continuous_coeff R d) }

variable {σ R}

open WithPiTopology

theorem continuous_C [Ring R] [TopologicalRing R] : Continuous (C σ R) := by
  classical
  apply continuous_of_continuousAt_zero
  rw [continuousAt_pi]
  intro d
  change ContinuousAt (fun y => coeff R d ((C σ R) y)) 0
  by_cases hd : d = 0
  · simp only [hd, coeff_zero_C]
    exact continuousAt_id
  · simp only [coeff_C, if_neg hd]
    exact continuousAt_const

theorem variables_tendsto_zero [Semiring R] :
    Tendsto (fun s : σ => (X s : MvPowerSeries σ R)) cofinite (nhds 0) := by
  classical
  rw [tendsto_pi_nhds]
  intro d s hs
  rw [mem_map, mem_cofinite, ← preimage_compl]
  by_cases h : ∃ i, d = Finsupp.single i 1
  · obtain ⟨i, rfl⟩ := h
    apply Finite.subset (finite_singleton i)
    intro x
    simp only [OfNat.ofNat, Zero.zero] at hs
    rw [mem_preimage, mem_compl_iff, mem_singleton_iff, not_imp_comm]
    intro hx
    convert mem_of_mem_nhds hs
    rw [apply_eq_coeff (X x) (Finsupp.single i 1), coeff_X, if_neg]
    rfl
    · simp only [Finsupp.single_eq_single_iff, Ne.symm hx, and_true, one_ne_zero, and_self,
      or_self, not_false_eq_true]
  · convert finite_empty
    rw [eq_empty_iff_forall_not_mem]
    intro x
    rw [mem_preimage, not_mem_compl_iff]
    convert mem_of_mem_nhds hs using 1
    rw [apply_eq_coeff (X x) d, coeff_X, if_neg (fun h' ↦ h ⟨x, h'⟩)]
    rfl

theorem tendsto_pow_zero_of_constantCoeff_nilpotent [CommSemiring R]
    {f} (hf : IsNilpotent (constantCoeff σ R f)) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) := by
  classical
  obtain ⟨m, hm⟩ := hf
  simp_rw [tendsto_iff_coeff_tendsto, coeff_zero]
  exact fun d =>  tendsto_atTop_of_eventually_const fun n hn =>
    coeff_eq_zero_of_constantCoeff_nilpotent hm hn

theorem tendsto_pow_zero_of_constantCoeff_zero [CommSemiring R] {f} (hf : constantCoeff σ R f = 0) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) :=
  tendsto_pow_zero_of_constantCoeff_nilpotent (hf ▸ IsNilpotent.zero)

/-- The powers of a `MvPowerSeries` converge to 0 iff its constant coefficient is nilpotent.
N. Bourbaki, *Algebra II*, [bourbaki1981] (chap. 4, §4, n°2, corollaire de la prop. 3) -/
theorem tendsto_pow_of_constantCoeff_nilpotent_iff [CommSemiring R] [DiscreteTopology R] (f) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) ↔
      IsNilpotent (constantCoeff σ R f) := by
  refine ⟨?_, tendsto_pow_zero_of_constantCoeff_nilpotent⟩
  intro h
  suffices Tendsto (fun n : ℕ => constantCoeff σ R (f ^ n)) Filter.atTop (nhds 0) by
    simp only [tendsto_def] at this
    specialize this {0} _
    suffices  ∀ x : R, {x} ∈ nhds x by exact this 0
    rw [← discreteTopology_iff_singleton_mem_nhds]; infer_instance
    simp only [map_pow, mem_atTop_sets, ge_iff_le, mem_preimage,
      mem_singleton_iff] at this
    obtain ⟨m, hm⟩ := this
    use m, hm m (le_refl m)
  simp only [← @comp_apply _ R ℕ, ← tendsto_map'_iff]
  simp only [Tendsto, map_le_iff_le_comap] at h ⊢
  refine le_trans h (comap_mono ?_)
  rw [← map_le_iff_le_comap]
  exact (continuous_constantCoeff R).continuousAt

variable [Semiring R]

/-- A power series is the sum (in the sense of summable families) of its monomials -/
theorem hasSum_of_monomials_self (f : MvPowerSeries σ R) :
    HasSum (fun d ↦ monomial R d (coeff R d f)) f := by
  rw [Pi.hasSum]
  intro d
  convert hasSum_single d ?_ using 1
  · exact (coeff_monomial_same d _).symm
  · exact fun d' h ↦ coeff_monomial_ne (Ne.symm h) _

/-- If the coefficient space is T2, then the power series is `tsum` of its monomials -/
theorem as_tsum [T2Space R] (f : MvPowerSeries σ R) :
    f = tsum fun d ↦ monomial R d (coeff R d f) :=
  (HasSum.tsum_eq (hasSum_of_monomials_self _)).symm

end Topology

section Uniformity

variable [UniformSpace R]

variable (σ R) in
/-- The componentwise uniformity on MvPowerSeries -/
scoped instance : UniformSpace (MvPowerSeries σ R) :=
  Pi.uniformSpace fun _ : σ →₀ ℕ => R

/-- Completeness of the uniform structure on MvPowerSeries -/
@[scoped instance]
theorem instCompleteSpace [CompleteSpace R] :
    CompleteSpace (MvPowerSeries σ R) := Pi.complete _

variable (R)

/-- Coefficients are uniformly continuous -/
theorem uniformContinuous_coeff [Semiring R] (d : σ →₀ ℕ) :
    UniformContinuous fun f : MvPowerSeries σ R => coeff R d f :=
  uniformContinuous_pi.mp uniformContinuous_id d

variable [Ring R]

variable (σ)

/-- The `UniformAddGroup` structure on `MvPowerSeries` of a `UniformAddGroup` -/
@[scoped instance]
theorem instUniformAddGroup [UniformAddGroup R] :
    UniformAddGroup (MvPowerSeries σ R) := Pi.instUniformAddGroup

end Uniformity

end WithPiTopology

end MvPowerSeries
