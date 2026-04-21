/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions

/-! # Product topology on multivariate power series

Let `R` be with `Semiring R` and `TopologicalSpace R`
In this file we define the topology on `MvPowerSeries σ R`
that corresponds to the simple convergence on its coefficients.
It is the coarsest topology for which all coefficient maps are continuous.

When `R` has `UniformSpace R`, we define the corresponding uniform structure.

This topology can be included by writing `open scoped MvPowerSeries.WithPiTopology`.

When the type of coefficients has the discrete topology, it corresponds to the topology defined by
[N. Bourbaki, *Algebra II*, Chapter 4, §4, n°2][bourbaki1981].

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

Mathematically, everything proven in this file follows from that general statement. However,
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
But future contributors wishing to clean this up should feel free to give it a try!

-/

@[expose] public section

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
  inferInstanceAs <| TopologicalSpace ((σ →₀ ℕ) → R)

set_option backward.isDefEq.respectTransparency false in
theorem instTopologicalSpace_mono (σ : Type*) {R : Type*} {t u : TopologicalSpace R} (htu : t ≤ u) :
    @instTopologicalSpace σ R t ≤ @instTopologicalSpace σ R u := by
  change ⨅ i, _ ≤ ⨅ i, _
  gcongr

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
    Continuous (MvPowerSeries.coeff (R := R) d) :=
  continuous_pi_iff.mp continuous_id d

variable (R) in
/-- `MvPowerSeries.constantCoeff` is continuous -/
theorem continuous_constantCoeff [Semiring R] : Continuous (constantCoeff (σ := σ) (R := R)) :=
  continuous_coeff (R := R) 0

set_option backward.isDefEq.respectTransparency false in
/-- A family of power series converges iff it converges coefficientwise -/
theorem tendsto_iff_coeff_tendsto [Semiring R] {ι : Type*}
    (f : ι → MvPowerSeries σ R) (u : Filter ι) (g : MvPowerSeries σ R) :
    Tendsto f u (nhds g) ↔
    ∀ d : σ →₀ ℕ, Tendsto (fun i => coeff d (f i)) u (nhds (coeff d g)) := by
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
    Continuous (C (σ := σ) (R := R)) := by
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
  by_cases! h : ∃ i, d = Finsupp.single i 1
  · obtain ⟨i, hi⟩ := h
    filter_upwards [eventually_cofinite_ne i] with j hj
    simp [hi, Finsupp.single_eq_single_iff, hj.symm]
  · simpa only [ite_eq_right_iff] using
      Eventually.of_forall fun x h' ↦ (h x h').elim

theorem isTopologicallyNilpotent_of_constantCoeff_isNilpotent [CommSemiring R]
    {f : MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff f)) :
    IsTopologicallyNilpotent f := by
  classical
  obtain ⟨m, hm⟩ := hf
  simp_rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto, coeff_zero]
  exact fun d ↦ tendsto_atTop_of_eventually_const fun n hn ↦
    coeff_eq_zero_of_constantCoeff_nilpotent hm hn

theorem isTopologicallyNilpotent_of_constantCoeff_zero [CommSemiring R]
    {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) := by
  apply isTopologicallyNilpotent_of_constantCoeff_isNilpotent
  rw [hf]
  exact IsNilpotent.zero

/-- Assuming the base ring has a discrete topology, the powers of a `MvPowerSeries` converge to 0
iff its constant coefficient is nilpotent.
[N. Bourbaki, *Algebra II*, Chapter 4, §4, n°2, corollary of prop. 3][bourbaki1981]

See also `MvPowerSeries.LinearTopology.isTopologicallyNilpotent_iff_constantCoeff`. -/
theorem isTopologicallyNilpotent_iff_constantCoeff_isNilpotent
    [CommRing R] [DiscreteTopology R] (f : MvPowerSeries σ R) :
    IsTopologicallyNilpotent f ↔ IsNilpotent (constantCoeff f) := by
  refine ⟨fun H ↦ ?_, isTopologicallyNilpotent_of_constantCoeff_isNilpotent⟩
  replace H := H.map (continuous_constantCoeff R)
  simp_rw [IsTopologicallyNilpotent, nhds_discrete, tendsto_pure] at H
  exact H.exists

variable [Semiring R]

set_option backward.isDefEq.respectTransparency false in
/-- A multivariate power series is the sum (in the sense of summable families) of its monomials -/
theorem hasSum_of_monomials_self (f : MvPowerSeries σ R) :
    HasSum (fun d : σ →₀ ℕ => monomial d (coeff d f)) f := by
  rw [Pi.hasSum]
  intro d
  simpa using hasSum_single d (fun d' h ↦ coeff_monomial_ne h.symm _)

/-- If the coefficient space is T2, then the multivariate power series is `tsum` of its monomials -/
theorem as_tsum [T2Space R] (f : MvPowerSeries σ R) :
    f = tsum fun d : σ →₀ ℕ => monomial d (coeff d f) :=
  (HasSum.tsum_eq (hasSum_of_monomials_self _)).symm

section Sum
variable {ι : Type*} {f : ι → MvPowerSeries σ R}

theorem hasSum_iff_hasSum_coeff {g : MvPowerSeries σ R} :
    HasSum f g ↔ ∀ d : σ →₀ ℕ, HasSum (fun i ↦ coeff d (f i)) (coeff d g) := by
  simp_rw [HasSum, ← map_sum]
  apply tendsto_iff_coeff_tendsto

theorem summable_iff_summable_coeff :
    Summable f ↔ ∀ d : σ →₀ ℕ, Summable (fun i ↦ coeff d (f i)) := by
  simp_rw [Summable, hasSum_iff_hasSum_coeff]
  constructor
  · rintro ⟨a, h⟩ n
    exact ⟨coeff n a, h n⟩
  · intro h
    choose a h using h
    exact ⟨a, by simpa using h⟩

variable [LinearOrder ι] [LocallyFiniteOrderBot ι]

/-- A family of `MvPowerSeries` is summable if their weighted order tends to infinity. -/
theorem summable_of_tendsto_weightedOrder_atTop_nhds_top {w : σ → ℕ}
    (h : Tendsto (fun i ↦ weightedOrder w (f i)) atTop (𝓝 ⊤)) : Summable f := by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply summable_empty
  rw [summable_iff_summable_coeff]
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop] at h
  intro d
  obtain ⟨i, hi⟩ := h (Finsupp.weight w d)
  refine summable_of_hasFiniteSupport <| (Set.finite_Iic i).subset ?_
  simp_rw [Function.support_subset_iff, Set.mem_Iic]
  intro k hk
  contrapose! hk
  exact coeff_eq_zero_of_lt_weightedOrder w <| hi k hk.le

/-- A family of `MvPowerSeries` is summable if their order tends to infinity. -/
theorem summable_of_tendsto_order_atTop_nhds_top
    (h : Tendsto (fun i ↦ (f i).order) atTop (𝓝 ⊤)) : Summable f :=
  summable_of_tendsto_weightedOrder_atTop_nhds_top h

/-- The geometric series converges if the constant term is zero. -/
theorem summable_pow_of_constantCoeff_eq_zero {f : MvPowerSeries σ R}
    (h : f.constantCoeff = 0) : Summable (f ^ ·) := by
  apply summable_of_tendsto_order_atTop_nhds_top
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop]
  refine fun n ↦ ⟨n + 1, fun m hm ↦ lt_of_lt_of_le ?_ (le_order_pow _)⟩
  refine (ENat.coe_lt_coe.mpr (Nat.add_one_le_iff.mp hm.le)).trans_le ?_
  simpa [nsmul_eq_mul] using ENat.self_le_mul_right m (order_ne_zero_iff_constCoeff_eq_zero.mpr h)

section GeomSeries
variable {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R] [T2Space R]
variable {f : MvPowerSeries σ R}

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
variable {σ R : Type*} [TopologicalSpace R] [CommSemiring R]
variable {ι : Type*} {f : ι → MvPowerSeries σ R} [LinearOrder ι] [LocallyFiniteOrderBot ι]

/-- If the weighted order of a family of `MvPowerSeries` tends to infinity, the collection of all
possible products over `Finset` is summable. -/
theorem summable_prod_of_tendsto_weightedOrder_atTop_nhds_top {w : σ → ℕ}
    (h : Tendsto (fun i ↦ weightedOrder w (f i)) atTop (𝓝 ⊤)) : Summable (∏ i ∈ ·, f i) := by
  rcases isEmpty_or_nonempty ι with hempty | hempty
  · apply Summable.of_finite
  refine summable_iff_summable_coeff.mpr fun d ↦ summable_of_hasFiniteSupport ?_
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, eventually_atTop] at h
  obtain ⟨i, hi⟩ := h (Finsupp.weight w d)
  apply (Finset.Iio i).powerset.finite_toSet.subset
  suffices ∀ s : Finset ι, coeff d (∏ i ∈ s, f i) ≠ 0 → ↑s ⊆ Set.Iio i by simpa
  intro s hs
  contrapose hs
  obtain ⟨x, hxs, hxi⟩ := Set.not_subset.mp hs
  rw [Set.mem_Iio, not_lt] at hxi
  refine coeff_eq_zero_of_lt_weightedOrder w <| (hi x hxi).trans_le <| ?_
  apply le_trans (Finset.single_le_sum (by simp) hxs) (le_weightedOrder_prod w _ _)

/-- If the order of a family of `MvPowerSeries` tends to infinity, the collection of all
possible products over `Finset` is summable. -/
theorem summable_prod_of_tendsto_order_atTop_nhds_top
    (h : Tendsto (fun i ↦ (f i).order) atTop (𝓝 ⊤)) : Summable (∏ i ∈ ·, f i) :=
  summable_prod_of_tendsto_weightedOrder_atTop_nhds_top h

/-- A family of `MvPowerSeries` in the form `1 + f i` is multipliable if the weighted order of `f i`
tends to infinity. -/
theorem multipliable_one_add_of_tendsto_weightedOrder_atTop_nhds_top {w : σ → ℕ}
    (h : Tendsto (fun i ↦ weightedOrder w (f i)) atTop (nhds ⊤)) : Multipliable (1 + f ·) :=
  multipliable_one_add_of_summable_prod <| summable_prod_of_tendsto_weightedOrder_atTop_nhds_top h

/-- A family of `MvPowerSeries` in the form `1 + f i` is multipliable if the order of `f i`
tends to infinity. -/
theorem multipliable_one_add_of_tendsto_order_atTop_nhds_top
    (h : Tendsto (fun i ↦ (f i).order) atTop (nhds ⊤)) : Multipliable (1 + f ·) :=
  multipliable_one_add_of_summable_prod <| summable_prod_of_tendsto_order_atTop_nhds_top h

end Prod

end Topology

section Uniformity

variable [UniformSpace R]

/-- The componentwise uniformity on `MvPowerSeries` -/
scoped instance : UniformSpace (MvPowerSeries σ R) :=
  inferInstanceAs <| UniformSpace ((σ →₀ ℕ) → R)

variable (R) in
/-- Coefficients of a multivariate power series are uniformly continuous -/
theorem uniformContinuous_coeff [Semiring R] (d : σ →₀ ℕ) :
    UniformContinuous fun f : MvPowerSeries σ R => coeff d f :=
  uniformContinuous_pi.mp uniformContinuous_id d

/-- Completeness of the uniform structure on `MvPowerSeries` -/
@[scoped instance]
theorem instCompleteSpace [CompleteSpace R] :
    CompleteSpace (MvPowerSeries σ R) := Pi.complete _

/-- The `IsUniformAddGroup` structure on `MvPowerSeries` of a `IsUniformAddGroup` -/
@[scoped instance]
theorem instIsUniformAddGroup [AddGroup R] [IsUniformAddGroup R] :
    IsUniformAddGroup (MvPowerSeries σ R) := Pi.instIsUniformAddGroup

end Uniformity

end WithPiTopology

end MvPowerSeries
