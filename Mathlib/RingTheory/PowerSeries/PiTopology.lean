/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! # Product topology on power series

Let `R` be with `Semiring R` and `TopologicalSpace R`
In this file we define the topology on `PowerSeries σ R`
that corresponds to the simple convergence on its coefficients.
It is the coarsest topology for which all coefficients maps are continuous.

When `R` has `UniformSpace R`, we define the corresponding uniform structure.

This topology can be included by writing `open scoped PowerSeries.WithPiTopology`.

When the type of coefficients has the discrete topology, it corresponds to the topology defined by
[N. Bourbaki, *Algebra {II}*, Chapter 4, §4, n°2][bourbaki1981].

It corresponds with the adic topology but this is not proved here.

- `PowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_isNilpotent`,
  `PowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero`: if the constant
  coefficient of `f` is nilpotent, or vanishes, then `f` is topologically nilpotent.

- `PowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent` :
  assuming the base ring has the discrete topology, `f` is topologically nilpotent iff the constant
  coefficient of `f` is nilpotent.

- `PowerSeries.WithPiTopology.hasSum_of_monomials_self` : viewed as an infinite sum, a power
  series converges to itself.

TODO: add the similar result for the series of homogeneous components.

## Instances

- If `R` is a topological (semi)ring, then so is `PowerSeries σ R`.
- If the topology of `R` is T0 or T2, then so is that of `PowerSeries σ R`.
- If `R` is a `IsUniformAddGroup`, then so is `PowerSeries σ R`.
- If `R` is complete, then so is `PowerSeries σ R`.

-/

public section


namespace PowerSeries

open Filter Function

variable (R : Type*)

section Topological

variable [TopologicalSpace R]

namespace WithPiTopology

open scoped Topology

/-- The pointwise topology on `PowerSeries` -/
scoped instance : TopologicalSpace (PowerSeries R) :=
  Pi.topologicalSpace

/-- Separation of the topology on `PowerSeries` -/
@[scoped instance]
theorem instT0Space [T0Space R] : T0Space (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instT0Space

/-- `PowerSeries` on a `T2Space` form a `T2Space` -/
@[scoped instance]
theorem instT2Space [T2Space R] : T2Space (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instT2Space

/-- Coefficients are continuous -/
theorem continuous_coeff [Semiring R] (d : ℕ) : Continuous (PowerSeries.coeff (R := R) d) :=
  continuous_pi_iff.mp continuous_id (Finsupp.single () d)

/-- The constant coefficient is continuous -/
theorem continuous_constantCoeff [Semiring R] : Continuous (constantCoeff (R := R)) :=
  coeff_zero_eq_constantCoeff (R := R) ▸ continuous_coeff R 0

/-- A family of power series converges iff it converges coefficientwise -/
theorem tendsto_iff_coeff_tendsto [Semiring R] {ι : Type*}
    (f : ι → PowerSeries R) (u : Filter ι) (g : PowerSeries R) :
    Tendsto f u (nhds g) ↔
    ∀ d : ℕ, Tendsto (fun i => coeff d (f i)) u (nhds (coeff d g)) := by
  rw [MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  apply (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv.forall_congr
  intro d
  simp only [LinearEquiv.coe_toEquiv, Finsupp.LinearEquiv.finsuppUnique_apply,
    PUnit.default_eq_unit, coeff]
  apply iff_of_eq
  congr
  · ext _; congr; ext; simp
  · ext; simp

theorem tendsto_trunc_atTop [CommSemiring R] (f : R⟦X⟧) :
    Tendsto (fun d ↦ (trunc d f : R⟦X⟧)) atTop (𝓝 f) := by
  rw [tendsto_iff_coeff_tendsto]
  intro d
  exact tendsto_atTop_of_eventually_const fun n (hdn : d < n) ↦ (by simp [coeff_trunc, hdn])

/-- The inclusion of polynomials into power series has dense image -/
theorem denseRange_toPowerSeries [CommSemiring R] :
    DenseRange (Polynomial.toPowerSeries (R := R)) := fun f =>
  mem_closure_of_tendsto (tendsto_trunc_atTop R f) <| .of_forall fun _ ↦ Set.mem_range_self _

/-- The semiring topology on `PowerSeries` of a topological semiring -/
@[scoped instance]
theorem instIsTopologicalSemiring [Semiring R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instIsTopologicalSemiring Unit R

/-- The ring topology on `PowerSeries` of a topological ring -/
@[scoped instance]
theorem instIsTopologicalRing [Ring R] [IsTopologicalRing R] :
    IsTopologicalRing (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instIsTopologicalRing Unit R

section Sum
variable [Semiring R] {ι : Type*} {f : ι → R⟦X⟧}

theorem hasSum_iff_hasSum_coeff {g : R⟦X⟧} :
    HasSum f g ↔ ∀ d, HasSum (fun i ↦ coeff d (f i)) (coeff d g) := by
  simp_rw [HasSum, ← map_sum]
  apply tendsto_iff_coeff_tendsto

theorem summable_iff_summable_coeff :
    Summable f ↔ ∀ d : ℕ, Summable (fun i ↦ coeff d (f i)) := by
  simp_rw [Summable, hasSum_iff_hasSum_coeff]
  constructor
  · rintro ⟨a, h⟩ n
    exact ⟨coeff n a, h n⟩
  · intro h
    choose a h using h
    exact ⟨mk a, by simpa using h⟩

/-- A family of `PowerSeries` is summable if their order tends to infinity. -/
theorem summable_of_tendsto_order_atTop_nhds_top [LinearOrder ι] [LocallyFiniteOrderBot ι]
    (h : Tendsto (fun i ↦ (f i).order) atTop (𝓝 ⊤)) : Summable f := by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply summable_empty
  rw [summable_iff_summable_coeff]
  intro n
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop] at h
  obtain ⟨i, hi⟩ := h n
  refine summable_of_hasFiniteSupport <| (Set.finite_Iic i).subset ?_
  simp_rw [Function.support_subset_iff, Set.mem_Iic]
  intro k hk
  contrapose! hk
  exact coeff_of_lt_order _ <| by simpa using (hi k hk.le)

variable {R} in
/-- The geometric series converges if the constant term is zero. -/
theorem summable_pow_of_constantCoeff_eq_zero {f : PowerSeries R} (h : f.constantCoeff = 0) :
    Summable (f ^ ·) :=
  MvPowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero h

section GeomSeries
variable {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R] [T2Space R]
variable {f : PowerSeries R}

/-- Formula for geometric series. -/
theorem tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (h : f.constantCoeff = 0) :
    (∑' (i : ℕ), f ^ i) * (1 - f) = 1 :=
  (summable_pow_of_constantCoeff_eq_zero h).tsum_pow_mul_one_sub

/-- Formula for geometric series. -/
theorem one_sub_mul_tsum_pow_of_constantCoeff_eq_zero (h : f.constantCoeff = 0) :
    (1 - f) * ∑' (i : ℕ), f ^ i = 1 :=
  (summable_pow_of_constantCoeff_eq_zero h).one_sub_mul_tsum_pow

end GeomSeries

end Sum

section Prod
variable [CommSemiring R] {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] {f : ι → R⟦X⟧}

/-- If the order of a family of `PowerSeries` tends to infinity, the collection of all
possible products over `Finset` is summable. -/
theorem summable_prod_of_tendsto_order_atTop_nhds_top
    (h : Tendsto (fun i ↦ (f i).order) atTop (𝓝 ⊤)) : Summable (∏ i ∈ ·, f i) := by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply Summable.of_finite
  refine (summable_iff_summable_coeff _).mpr fun n ↦ summable_of_hasFiniteSupport ?_
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, eventually_atTop] at h
  obtain ⟨i, hi⟩ := h n
  apply (Finset.Iio i).powerset.finite_toSet.subset
  suffices ∀ s : Finset ι, coeff n (∏ i ∈ s, f i) ≠ 0 → ↑s ⊆ Set.Iio i by simpa
  intro s hs
  contrapose! hs
  obtain ⟨x, hxs, hxi⟩ := Set.not_subset.mp hs
  rw [Set.mem_Iio, not_lt] at hxi
  refine coeff_of_lt_order _ <| (hi x hxi).trans_le <| le_trans ?_ (le_order_prod _ _)
  apply Finset.single_le_sum (by simp) hxs

/-- A family of `PowerSeries` in the form `1 + f i` is multipliable if the order of `f i` tends to
infinity. -/
theorem multipliable_one_add_of_tendsto_order_atTop_nhds_top
    (h : Tendsto (fun i ↦ (f i).order) atTop (nhds ⊤)) : Multipliable (1 + f ·) :=
  multipliable_one_add_of_summable_prod <| summable_prod_of_tendsto_order_atTop_nhds_top _ h

end Prod

section ProdOneSubPow
variable (R : Type*) [CommRing R] [TopologicalSpace R]

set_option backward.isDefEq.respectTransparency false in
theorem multipliable_one_sub_X_pow : Multipliable fun n ↦ (1 : R⟦X⟧) - X ^ (n + 1) := by
  nontriviality R
  simp_rw [sub_eq_add_neg]
  apply multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n ↦ Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  rw [order_neg, order_X_pow]
  norm_cast
  exact Nat.lt_add_one_iff.mpr hm

theorem tprod_one_sub_X_pow_ne_zero [T2Space R] [Nontrivial R] :
    ∏' i, (1 - X ^ (i + 1)) ≠ (0 : R⟦X⟧) := by
  by_contra! h
  obtain h := PowerSeries.ext_iff.mp h 0
  simp [coeff_zero_eq_constantCoeff, (multipliable_one_sub_X_pow R).map_tprod _
    (continuous_constantCoeff R)] at h

end ProdOneSubPow

end WithPiTopology

end Topological

section Uniform

namespace WithPiTopology

variable [UniformSpace R]

/-- The product uniformity on `PowerSeries` -/
scoped instance : UniformSpace (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instUniformSpace

/-- Coefficients are uniformly continuous -/
theorem uniformContinuous_coeff [Semiring R] (d : ℕ) :
    UniformContinuous fun f : PowerSeries R ↦ coeff d f :=
  uniformContinuous_pi.mp uniformContinuous_id (Finsupp.single () d)

/-- Completeness of the uniform structure on `PowerSeries` -/
@[scoped instance]
theorem instCompleteSpace [CompleteSpace R] :
    CompleteSpace (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instCompleteSpace

/-- The `IsUniformAddGroup` structure on `PowerSeries` of a `IsUniformAddGroup` -/
@[scoped instance]
theorem instIsUniformAddGroup [AddGroup R] [IsUniformAddGroup R] :
    IsUniformAddGroup (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instIsUniformAddGroup

end WithPiTopology

end Uniform

section

variable {R}

variable [TopologicalSpace R]

namespace WithPiTopology

open MvPowerSeries.WithPiTopology

theorem continuous_C [Semiring R] : Continuous (C (R := R)) :=
  MvPowerSeries.WithPiTopology.continuous_C

theorem isTopologicallyNilpotent_of_constantCoeff_isNilpotent [CommSemiring R]
    {f : PowerSeries R} (hf : IsNilpotent (constantCoeff (R := R) f)) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) :=
  MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_isNilpotent hf

theorem isTopologicallyNilpotent_of_constantCoeff_zero [CommSemiring R]
    {f : PowerSeries R} (hf : constantCoeff (R := R) f = 0) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) :=
  MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero hf

/-- Assuming the base ring has a discrete topology, the powers of a `PowerSeries` converge to 0
iff its constant coefficient is nilpotent.
[N. Bourbaki, *Algebra {II}*, Chapter 4, §4, n°2, corollary of prop. 3][bourbaki1981] -/
theorem isTopologicallyNilpotent_iff_constantCoeff_isNilpotent
    [CommRing R] [DiscreteTopology R] (f : PowerSeries R) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) ↔
      IsNilpotent (constantCoeff f) :=
  MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent f

end WithPiTopology

end

section Summable

variable [Semiring R] [TopologicalSpace R]

open WithPiTopology MvPowerSeries.WithPiTopology

variable {R}

-- NOTE : one needs an API to apply `Finsupp.LinearEquiv.finsuppUnique`
/-- A power series is the sum (in the sense of summable families) of its monomials -/
theorem hasSum_of_monomials_self (f : PowerSeries R) :
    HasSum (fun d : ℕ => monomial d (coeff d f)) f := by
  rw [← (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv.hasSum_iff]
  convert MvPowerSeries.WithPiTopology.hasSum_of_monomials_self f
  simp only [LinearEquiv.coe_toEquiv, comp_apply, monomial, coeff,
    Finsupp.LinearEquiv.finsuppUnique_apply, PUnit.default_eq_unit]
  congr
  all_goals { ext; simp }

/-- If the coefficient space is T2, then the power series is `tsum` of its monomials -/
theorem as_tsum [T2Space R] (f : PowerSeries R) :
    f = tsum fun d : ℕ => monomial d (coeff d f) :=
  (HasSum.tsum_eq (hasSum_of_monomials_self f)).symm

end Summable

end PowerSeries
