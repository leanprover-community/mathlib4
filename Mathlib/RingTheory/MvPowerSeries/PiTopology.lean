/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-! # Product topology on multivariate power series

Let `R` be with `Semiring R` and `TopologicalSpace R`
In this file we define the topology on `MvPowerSeries σ R`
that corresponds to the simple convergence on its coefficients.
It is the coarsest topology for which all coefficient maps are continuous.

When `R` has `UniformSpace R`, we define the corresponding uniform structure.

This topology can be included by writing `open scoped MvPowerSeries.WithPiTopology`.

When the type of coefficients has the discrete topology, it corresponds to the topology defined by
[N. Bourbaki, *Algebra {II}*, Chapter 4, §4, n°2][bourbaki1981].

It is *not* the adic topology in general.

## Main results

- `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_isNilpotent`,
  `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero`: if the constant
  coefficient of `f` is nilpotent, or vanishes, then `f` is topologically nilpotent.

- `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent` :
  assuming the base ring has the discrete topology, `f` is topologically nilpotent iff the constant
  coefficient of `f` is nilpotent.

- `MvPowerSeries.WithPiTopology.hasSum_of_monomials_self` : viewed as an infinite sum, a power
  series converges to itself.

TODO: add the similar result for the series of homogeneous components.

## Instances

- If `R` is a topological (semi)ring, then so is `MvPowerSeries σ R`.
- If the topology of `R` is T0 or T2, then so is that of `MvPowerSeries σ R`.
- If `R` is a `IsUniformAddGroup`, then so is `MvPowerSeries σ R`.
- If `R` is complete, then so is `MvPowerSeries σ R`.

## Implementation Notes

In `Mathlib/RingTheory/MvPowerSeries/LinearTopology.lean`, we generalize the criterion for
topological nilpotency by proving that, if the base ring is equipped with a *linear* topology, then
a power series is topologically nilpotent if and only if its constant coefficient is.
This is lemma `MvPowerSeries.LinearTopology.isTopologicallyNilpotent_iff_constantCoeff`.

Mathematically, everything proven in this files follows from that general statement. However,
formalizing this yields a few (minor) annoyances:

- we would need to push the results in this file slightly lower in the import tree
  (likely, in a new dedicated file);
- we would have to work in `CommRing`s rather than `CommSemiring`s (this probably does not
  matter in any way though);
- because `isTopologicallyNilpotent_of_constantCoeff_isNilpotent` holds for *any* topology,
  not necessarily discrete nor linear, the proof going through the general case involves
  juggling a bit with the topologies.

Since the code duplication is rather minor (the interesting part of the proof is already extracted
as `MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent`), we just leave this as is for now.
But future contributors wishing to clean this up should feel free to give it a try !

-/

namespace MvPowerSeries

open Function Filter

open scoped Topology

variable {σ R : Type*}

namespace WithPiTopology

section Topology

variable [TopologicalSpace R]

variable (R) in
/-- The pointwise topology on `MvPowerSeries` -/
scoped instance : TopologicalSpace (MvPowerSeries σ R) :=
  Pi.topologicalSpace

theorem instTopologicalSpace_mono (σ : Type*) {R : Type*} {t u : TopologicalSpace R} (htu : t ≤ u) :
    @instTopologicalSpace σ R t ≤ @instTopologicalSpace σ R u := by
  simp only [instTopologicalSpace, Pi.topologicalSpace, le_iInf_iff]
  exact fun i ↦ le_trans (iInf_le _ i) (induced_mono htu)

/-- `MvPowerSeries` on a `T0Space` form a `T0Space` -/
@[scoped instance]
theorem instT0Space [T0Space R] : T0Space (MvPowerSeries σ R) := Pi.instT0Space

/-- `MvPowerSeries` on a `T2Space` form a `T2Space` -/
@[scoped instance]
theorem instT2Space [T2Space R] : T2Space (MvPowerSeries σ R) := Pi.t2Space

variable (R) in
/-- `MvPowerSeries.coeff` is continuous. -/
@[fun_prop]
theorem continuous_coeff [Semiring R] (d : σ →₀ ℕ) :
    Continuous (MvPowerSeries.coeff R d) :=
  continuous_pi_iff.mp continuous_id d

variable (R) in
/-- `MvPowerSeries.constantCoeff` is continuous -/
theorem continuous_constantCoeff [Semiring R] : Continuous (constantCoeff σ R) :=
  continuous_coeff R 0

/-- A family of power series converges iff it converges coefficientwise -/
theorem tendsto_iff_coeff_tendsto [Semiring R] {ι : Type*}
    (f : ι → MvPowerSeries σ R) (u : Filter ι) (g : MvPowerSeries σ R) :
    Tendsto f u (nhds g) ↔
    ∀ d : σ →₀ ℕ, Tendsto (fun i => coeff R d (f i)) u (nhds (coeff R d g)) := by
  rw [nhds_pi, tendsto_pi]
  exact forall_congr' (fun d => Iff.rfl)

theorem tendsto_trunc'_atTop [DecidableEq σ] [CommSemiring R] (f : MvPowerSeries σ R) :
    Tendsto (fun d ↦ (trunc' R d f : MvPowerSeries σ R)) atTop (𝓝 f) := by
  rw [tendsto_iff_coeff_tendsto]
  intro d
  exact tendsto_atTop_of_eventually_const fun n (hdn : d ≤ n) ↦ (by simp [coeff_trunc', hdn])

theorem tendsto_trunc_atTop [DecidableEq σ] [CommSemiring R] [Nonempty σ] (f : MvPowerSeries σ R) :
    Tendsto (fun d ↦ (trunc R d f : MvPowerSeries σ R)) atTop (𝓝 f) := by
  rw [tendsto_iff_coeff_tendsto]
  intro d
  obtain ⟨s, _⟩ := (exists_const σ).mpr trivial
  apply tendsto_atTop_of_eventually_const (i₀ := d + Finsupp.single s 1)
  intro n hn
  rw [MvPolynomial.coeff_coe, coeff_trunc, if_pos]
  apply lt_of_lt_of_le _ hn
  simp only [lt_add_iff_pos_right, Finsupp.lt_def]
  refine ⟨zero_le _, ⟨s, by simp⟩⟩

/-- The inclusion of polynomials into power series has dense image -/
theorem denseRange_toMvPowerSeries [CommSemiring R] :
    DenseRange (MvPolynomial.toMvPowerSeries (R := R) (σ := σ)) := fun f ↦ by
  classical
  exact mem_closure_of_tendsto (tendsto_trunc'_atTop f) <| .of_forall fun _ ↦ Set.mem_range_self _

@[deprecated (since := "2025-05-21")] alias toMvPowerSeries_denseRange := denseRange_toMvPowerSeries

variable (σ R)

/-- The semiring topology on `MvPowerSeries` of a topological semiring -/
@[scoped instance]
theorem instIsTopologicalSemiring [Semiring R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring (MvPowerSeries σ R) where
  continuous_add := continuous_pi fun d => continuous_add.comp
    (((continuous_coeff R d).fst').prodMk (continuous_coeff R d).snd')
  continuous_mul := continuous_pi fun _ =>
    continuous_finset_sum _ fun i _ => continuous_mul.comp
      ((continuous_coeff R i.fst).fst'.prodMk (continuous_coeff R i.snd).snd')

/-- The ring topology on `MvPowerSeries` of a topological ring -/
@[scoped instance]
theorem instIsTopologicalRing [Ring R] [IsTopologicalRing R] :
    IsTopologicalRing (MvPowerSeries σ R) :=
  { instIsTopologicalSemiring σ R with
    continuous_neg := continuous_pi fun d ↦ Continuous.comp continuous_neg
      (continuous_coeff R d) }

variable {σ R}

@[fun_prop]
theorem continuous_C [Semiring R] :
    Continuous (C σ R) := by
  classical
  simp only [continuous_iff_continuousAt]
  refine fun r ↦ (tendsto_iff_coeff_tendsto _ _ _).mpr fun d ↦ ?_
  simp only [coeff_C]
  split_ifs
  · exact tendsto_id
  · exact tendsto_const_nhds

/-- Scalar multiplication on `MvPowerSeries` is continuous. -/
instance {S : Type*} [Semiring S] [TopologicalSpace S]
    [CommSemiring R] [Algebra R S] [ContinuousSMul R S] :
    ContinuousSMul R (MvPowerSeries σ S) :=
  instContinuousSMulForall

theorem variables_tendsto_zero [Semiring R] :
    Tendsto (X · : σ → MvPowerSeries σ R) cofinite (nhds 0) := by
  classical
  simp only [tendsto_iff_coeff_tendsto, ← coeff_apply, coeff_X, coeff_zero]
  refine fun d ↦ tendsto_nhds_of_eventually_eq ?_
  by_cases h : ∃ i, d = Finsupp.single i 1
  · obtain ⟨i, hi⟩ := h
    filter_upwards [eventually_cofinite_ne i] with j hj
    simp [hi, Finsupp.single_eq_single_iff, hj.symm]
  · simpa only [ite_eq_right_iff] using
      Eventually.of_forall fun x h' ↦ (not_exists.mp h x h').elim

theorem isTopologicallyNilpotent_of_constantCoeff_isNilpotent [CommSemiring R]
    {f} (hf : IsNilpotent (constantCoeff σ R f)) :
    IsTopologicallyNilpotent f := by
  classical
  obtain ⟨m, hm⟩ := hf
  simp_rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto, coeff_zero]
  exact fun d ↦ tendsto_atTop_of_eventually_const fun n hn ↦
    coeff_eq_zero_of_constantCoeff_nilpotent hm hn

theorem isTopologicallyNilpotent_of_constantCoeff_zero [CommSemiring R]
    {f} (hf : constantCoeff σ R f = 0) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) := by
  apply isTopologicallyNilpotent_of_constantCoeff_isNilpotent
  rw [hf]
  exact IsNilpotent.zero

/-- Assuming the base ring has a discrete topology, the powers of a `MvPowerSeries` converge to 0
iff its constant coefficient is nilpotent.
[N. Bourbaki, *Algebra {II}*, Chapter 4, §4, n°2, corollary of prop. 3][bourbaki1981]

See also `MvPowerSeries.LinearTopology.isTopologicallyNilpotent_iff_constantCoeff`. -/
theorem isTopologicallyNilpotent_iff_constantCoeff_isNilpotent
    [CommRing R] [DiscreteTopology R] (f) :
    IsTopologicallyNilpotent f ↔ IsNilpotent (constantCoeff σ R f) := by
  refine ⟨fun H ↦ ?_, isTopologicallyNilpotent_of_constantCoeff_isNilpotent⟩
  replace H := H.map (continuous_constantCoeff R)
  simp_rw [IsTopologicallyNilpotent, nhds_discrete, tendsto_pure] at H
  exact H.exists

variable [Semiring R]

/-- A multivariate power series is the sum (in the sense of summable families) of its monomials -/
theorem hasSum_of_monomials_self (f : MvPowerSeries σ R) :
    HasSum (fun d : σ →₀ ℕ => monomial R d (coeff R d f)) f := by
  rw [Pi.hasSum]
  intro d
  convert hasSum_single d ?_ using 1
  · exact (coeff_monomial_same d _).symm
  · exact fun d' h ↦ coeff_monomial_ne (Ne.symm h) _

/-- If the coefficient space is T2, then the multivariate power series is `tsum` of its monomials -/
theorem as_tsum [T2Space R] (f : MvPowerSeries σ R) :
    f = tsum fun d : σ →₀ ℕ => monomial R d (coeff R d f) :=
  (HasSum.tsum_eq (hasSum_of_monomials_self _)).symm

end Topology

section Uniformity

variable [UniformSpace R]

/-- The componentwise uniformity on `MvPowerSeries` -/
scoped instance : UniformSpace (MvPowerSeries σ R) :=
  Pi.uniformSpace fun _ : σ →₀ ℕ => R

variable (R) in
/-- Coefficients of a multivariate power series are uniformly continuous -/
theorem uniformContinuous_coeff [Semiring R] (d : σ →₀ ℕ) :
    UniformContinuous fun f : MvPowerSeries σ R => coeff R d f :=
  uniformContinuous_pi.mp uniformContinuous_id d

/-- Completeness of the uniform structure on `MvPowerSeries` -/
@[scoped instance]
theorem instCompleteSpace [CompleteSpace R] :
    CompleteSpace (MvPowerSeries σ R) := Pi.complete _

/-- The `IsUniformAddGroup` structure on `MvPowerSeries` of a `IsUniformAddGroup` -/
@[scoped instance]
theorem instIsUniformAddGroup [AddGroup R] [IsUniformAddGroup R] :
    IsUniformAddGroup (MvPowerSeries σ R) := Pi.instIsUniformAddGroup

@[deprecated (since := "2025-03-27")] alias instUniformAddGroup := instIsUniformAddGroup

end Uniformity

end WithPiTopology

end MvPowerSeries
