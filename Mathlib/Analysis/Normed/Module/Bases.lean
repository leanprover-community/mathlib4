/-
Copyright (c) 2025 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Schauder Bases and Generalized Bases

This file defines the theory of bases in Banach spaces, unifying the classical
sequential notion with modern generalized bases.

## Overview

A **basis** in a normed space allows every vector to be expanded as a (potentially infinite) linear
combination of basis vectors. Historically, this was defined strictly for sequences with convergence
of partial sums (the "classical Schauder basis").

However, modern functional analysis requires bases indexed by arbitrary sets
`β` (e.g., for non-separable spaces or Hilbert spaces), where convergence
is defined via nets over finite subsets (unconditional convergence).

This file provides a unified structure `GeneralSchauderBasis` that captures both:
* **Classical Schauder Bases:** Indexed by `ℕ`, using `SummationFilter.conditional`
  to enforce sequential convergence of partial sums.
* **Unconditional/Extended Bases:** Indexed by an arbitrary type `β`, using
  `SummationFilter.unconditional` to enforce convergence of the net of all finite subsets.

## Main Definitions

* `GeneralSchauderBasis β 𝕜 X L`: A structure representing a generalized Schauder basis for a
  normed space `X` over a field `𝕜`, indexed by a type `β` with a `SummationFilter L`.
* `SchauderBasis 𝕜 X`: The classical Schauder basis, an abbreviation for
  `GeneralSchauderBasis ℕ 𝕜 X (SummationFilter.conditional ℕ)`.
* `UnconditionalSchauderBasis β 𝕜 X`: An unconditional Schauder basis, an abbreviation for
  `GeneralSchauderBasis β 𝕜 X (SummationFilter.unconditional β)`.
* `GeneralSchauderBasis.proj b A`: The projection onto a finite set `A` of basis vectors,
  mapping `x ↦ ∑ i ∈ A, b.coord i x • b i`.
* `SchauderBasis.proj b n`: The `n`-th projection `X → X`,
  mapping `x ↦ ∑ i ∈ Finset.range n, b.coord i x • b i`.
* `UnconditionalSchauderBasis.enormProjBound`: The supremum of projection norms (`ℝ≥0∞`).
* `UnconditionalSchauderBasis.nnnormProjBound`: The supremum of projection norms (`ℝ≥0`),
  requires `[CompleteSpace X]`.
* `RankOneDecomposition 𝕜 X`: Data for constructing a Schauder basis from
  a sequence of finite-rank projections whose differences are rank one.
* `RankOneDecomposition.basis`: Constructs a `SchauderBasis` from a `RankOneDecomposition`.

## Main Results

* `GeneralSchauderBasis.linearIndependent`: A Schauder basis is linearly independent.
* `GeneralSchauderBasis.tendsto_proj`: The projections `proj A` converge to identity
  along the summation filter.
* `GeneralSchauderBasis.range_proj_eq_span`: The range of `proj A` is the span of the basis
  elements in `A`.
* `GeneralSchauderBasis.proj_comp`: Composition of projections satisfies
  `proj A (proj B x) = proj (A ∩ B) x`.
* `SchauderBasis.exists_norm_proj_le`: In a Banach space, the projections are uniformly bounded.
* `UnconditionalSchauderBasis.exists_norm_proj_le`: For unconditional bases, projections
  onto all finite sets are uniformly bounded.
## References

* [Albiac, Fernando. and Kalton, Nigel J., Topics in Banach Space Theory][Albiac_Kalton_2016].
* [Singer, Ivan, Bases in Banach spaces][Singer_1970].
* [Marti, Jürg T., Introduction to the theory of bases][MartiJurg1969].

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

noncomputable section

open Filter Topology LinearMap Set ENNReal NNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

open scoped Classical in
/--
A generalized Schauder basis indexed by `β` with summation along filter `L`.

The key fields are:
* `basis`: The basis vectors `e i` for `i : β`
* `coord`: The coordinate functionals `f i` for `i : β` in the dual space
* `ortho`: Biorthogonality condition `f i (e j) = if i = j then 1 else 0`
* `expansion`: Every `x` equals `∑ i, f i x • e i`, converging along `L`

See `SchauderBasis` for the classical `ℕ`-indexed case with conditional convergence,
and `UnconditionalSchauderBasis` for the unconditional case.
-/
@[ext]
structure GeneralSchauderBasis (β : Type*) (𝕜 : Type*)
    (X : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (L : SummationFilter β) where
  /-- The basis vectors. -/
  basis : β → X
  /-- Coordinate functionals. -/
  coord : β → StrongDual 𝕜 X
  /-- Biorthogonality. -/
  ortho (i j : β) : coord i (basis j) = (Pi.single j (1 : 𝕜) : β → 𝕜) i
  /-- The sum converges to `x` along the provided `SummationFilter L`. -/
  expansion (x : X) : HasSum (fun i ↦ (coord i) x • basis i) x L

variable {β : Type*}
variable {L : SummationFilter β}

/-- A classical Schauder basis indexed by `ℕ` with conditional convergence. -/
abbrev SchauderBasis (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] :=
  GeneralSchauderBasis ℕ 𝕜 X (SummationFilter.conditional ℕ)

/--
An unconditional Schauder basis indexed by `β`.

In the literature, this is known as:
* An **Extended Basis** [Marti, Jürg T., Introduction to the theory of bases][MartiJurg1969]:
Defined via convergence of the net of finite partial sums.
* An **Unconditional Basis** [Singer, Ivan., Bases in Banach spaces][Singer_1970]: On an arbitrary
set, convergence is necessarily unconditional.

This structure generalizes the classical Schauder basis by replacing sequential
convergence with summability over the directed set of finite subsets.
-/
abbrev UnconditionalSchauderBasis (β : Type*)
    (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] :=
  GeneralSchauderBasis β 𝕜 X (SummationFilter.unconditional β)

/-- Coercion from a `GeneralSchauderBasis` to the underlying basis function. -/
instance : CoeFun (GeneralSchauderBasis β 𝕜 X L) (fun _ ↦ β → X) where
  coe b := b.basis
attribute [coe] GeneralSchauderBasis.basis
namespace GeneralSchauderBasis

variable (b : GeneralSchauderBasis β 𝕜 X L)

/-- The basis vectors are linearly independent. -/
theorem linearIndependent : LinearIndependent 𝕜 b := by
  classical
  refine linearIndependent_iff.mpr (fun l hl ↦ l.ext ?_)
  simpa [l.linearCombination_apply, Finsupp.sum, b.ortho, Pi.single_apply] using
    fun i ↦ congr_arg (b.coord i) hl

/-- Projection onto a finite set of basis vectors. -/
def proj (A : Finset β) : X →L[𝕜] X := ∑ i ∈ A, (b.coord i).smulRight (b i)

/-- The projection on the empty set is the zero map. -/
@[simp]
theorem proj_empty : b.proj ∅ = 0 := by simp [proj]

/-- The action of the projection on a vector `x`. -/
@[simp]
theorem proj_apply (A : Finset β) (x : X) : b.proj A x = ∑ i ∈ A, b.coord i x • b i := by
  simp [proj, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]

open scoped Classical in
/-- The action of the projection on a basis element `e i`. -/
theorem proj_apply_basis_mem (A : Finset β) (i : β) :
    b.proj A (b i) = if i ∈ A then b i else 0 := by
  simp [b.ortho, Pi.single_apply]

/-- The projections `b.proj A x` converge to `x` along the summation filter. -/
theorem tendsto_proj (x : X) : Tendsto (fun A ↦ b.proj A x) L.filter (𝓝 x) := by
  simpa using b.expansion x

/-- The range of the projection is the span of the basis elements in `A`. -/
theorem range_proj_eq_span (A : Finset β) :
    (b.proj A).toLinearMap.range = Submodule.span 𝕜 (b '' A) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.coe_coe, proj_apply]
    exact Submodule.sum_mem _ fun i hi ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    use b i
    rw [ContinuousLinearMap.coe_coe, proj_apply_basis_mem, if_pos (Finset.mem_coe.mp hi)]

open Classical in
/-- Composition of projections: `proj A (proj B x) = proj (A ∩ B) x`. -/
theorem proj_comp (A B : Finset β) (x : X) : b.proj A (b.proj B x) = b.proj (A ∩ B) x := by
  simp only [proj_apply, map_sum, map_smul, b.ortho, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', smul_ite, smul_zero, Finset.sum_ite_mem]
  congr 1
  ext _
  simp [and_comm]

/-- The dimension of the range of the projection `proj A` equals the cardinality of `A`. -/
theorem finrank_range_proj (A : Finset β) :
    Module.finrank 𝕜 (b.proj A).toLinearMap.range = A.card := by
  rw [range_proj_eq_span, Set.image_eq_range, finrank_span_eq_card]
  · exact Fintype.card_coe A
  · exact b.linearIndependent.comp (fun i : A ↦ i.val) Subtype.val_injective

end GeneralSchauderBasis

/-! ### Unconditional Schauder bases -/

namespace UnconditionalSchauderBasis

variable (b : UnconditionalSchauderBasis β 𝕜 X)

/-- The basis constant for unconditional bases (supremum over all finite sets) as `enorm`. -/
noncomputable def enormProjBound : ℝ≥0∞ := ⨆ A : Finset β, ‖b.proj A‖ₑ

/-- The `enorm` of any projection is bounded by the basis constant. -/
theorem enorm_proj_le_enormProjBound (A : Finset β) : ‖b.proj A‖ₑ ≤ b.enormProjBound :=
  le_iSup (fun A ↦ ‖b.proj A‖ₑ) A

/-- Projections are uniformly bounded for unconditional bases. -/
theorem exists_norm_proj_le [CompleteSpace X] : ∃ C : ℝ, ∀ A : Finset β, ‖b.proj A‖ ≤ C := by
  classical
  apply banach_steinhaus
  intro x
  obtain ⟨A₀, hA₀⟩ := summable_iff_vanishing_norm.mp (b.expansion x).summable 1 zero_lt_one
  use (A₀.powerset.image fun B ↦ ‖b.proj B x‖).sup' ((Finset.powerset_nonempty A₀).image _) id + 1
  intro A
  have hdecomp : b.proj A x = b.proj (A ∩ A₀) x + b.proj (A \ A₀) x := by
    simp only [GeneralSchauderBasis.proj_apply]
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter A A₀).symm,
      Finset.union_comm, Finset.sdiff_union_inter]
  rw [hdecomp]
  -- -- The projection on the tail (A \ A₀) at `x` is bounded by 1
  have htail : ‖b.proj (A \ A₀) x‖ < 1 := by
    rw [GeneralSchauderBasis.proj_apply]
    exact hA₀ (A \ A₀) Finset.sdiff_disjoint
  apply (norm_add_le _ _).trans (add_le_add _ htail.le)
  -- The projection on (A ∩ A₀) at `x` is bounded by the `sup'`.
  exact Finset.le_sup' id <| Finset.mem_image_of_mem (fun B ↦ ‖b.proj B x‖)
      (Finset.mem_powerset.2 Finset.inter_subset_right)

/-- The basis constant for unconditional bases (supremum over all finite sets) as `nnnorm`.
    It requires completeness to guarantee that the supremum is finite,
    see lemma `bddAbove_range_nnnorm_proj` below. -/
noncomputable def nnnormProjBound : ℝ≥0 := ⨆ A : Finset β, ‖b.proj A‖₊

/-- The projection norms are bounded above in a complete space. -/
theorem bddAbove_range_nnnorm_proj [CompleteSpace X] :
    BddAbove (Set.range (fun A : Finset β ↦ ‖b.proj A‖₊)) := by
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hCpos : 0 ≤ C := by simpa [GeneralSchauderBasis.proj_empty] using hC ∅
  refine ⟨C.toNNReal, ?_⟩
  rintro _ ⟨A, rfl⟩
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hCpos, coe_nnnorm]
  exact hC A

/-- The `nnnorm` of any projection is bounded by the basis constant. -/
theorem nnnorm_proj_le_nnnormProjBound [CompleteSpace X] (A : Finset β) :
    ‖b.proj A‖₊ ≤ b.nnnormProjBound :=
  le_ciSup (bddAbove_range_nnnorm_proj b) A

/-- The norm of any projection is bounded by the basis constant. -/
theorem norm_proj_le_nnnormProjBound [CompleteSpace X] (A : Finset β) :
    ‖b.proj A‖ ≤ b.nnnormProjBound :=
  mod_cast b.nnnorm_proj_le_nnnormProjBound A

end UnconditionalSchauderBasis

/-! ### ℕ-indexed Schauder bases with conditional convergence -/

namespace SchauderBasis

variable (b : SchauderBasis 𝕜 X)

/-- The `n`-th projection `P_n = b.proj (Finset.range n)`, given by:
    `P_n x = ∑ i ∈ Finset.range n, b.coord i x • b i` -/
def proj (n : ℕ) : X →L[𝕜] X := GeneralSchauderBasis.proj b (Finset.range n)

/-- The projection at `0` is the zero map. -/
@[simp]
theorem proj_zero : b.proj 0 = 0 := by rw [proj, Finset.range_zero, GeneralSchauderBasis.proj_empty]

/-- The action of the projection on a vector. -/
@[simp]
theorem proj_apply (n : ℕ) (x : X) : b.proj n x = ∑ i ∈ Finset.range n, b.coord i x • b i := by
  rw [proj, GeneralSchauderBasis.proj_apply]

/-- The action of the projection on a basis element `e i`. -/
theorem proj_apply_basis_mem (n i : ℕ) : b.proj n (b i) = if i < n then b i else 0 := by
  rw [proj, GeneralSchauderBasis.proj_apply_basis_mem]
  simp

/-- The range of the projection is the span of the first `n` basis elements. -/
theorem range_proj_eq_span (n : ℕ) :
    (b.proj n).toLinearMap.range = Submodule.span 𝕜 (b '' ↑(Finset.range n)) := by
  rw [proj, GeneralSchauderBasis.range_proj_eq_span]

/-- The dimension of the range of the projection `P n` is `n`. -/
theorem finrank_range_proj (n : ℕ) :
    Module.finrank 𝕜 (b.proj n).toLinearMap.range = n := by
  rw [proj, GeneralSchauderBasis.finrank_range_proj, Finset.card_range]

/-- The projections converge pointwise to the identity map. -/
theorem tendsto_proj (x : X) : Tendsto (fun n ↦ b.proj n x) atTop (𝓝 x) := by
  have := GeneralSchauderBasis.tendsto_proj b x
  rwa [SummationFilter.conditional_filter_eq_map_range] at this

/-- Composition of projections: `proj n (proj m x) = proj (min n m) x`. -/
theorem proj_comp (n m : ℕ) (x : X) : b.proj n (b.proj m x) = b.proj (min n m) x := by
  simp only [proj, GeneralSchauderBasis.proj_comp]
  congr 2
  ext _
  simp only [Finset.mem_inter, Finset.mem_range]
  omega

/-- The projections are uniformly bounded. -/
theorem exists_norm_proj_le [CompleteSpace X] : ∃ C : ℝ, ∀ n : ℕ, ‖b.proj n‖ ≤ C := by
  apply banach_steinhaus
  intro x
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto (fun n ↦ b.proj n x) (tendsto_proj b x))
  exact ⟨M, Set.forall_mem_range.mp hM⟩

/-- The basis constant for Schauder bases (supremum over projections) as `enorm`. -/
noncomputable def enormProjBound : ℝ≥0∞ := ⨆ n, ‖b.proj n‖ₑ

/-- The enorm of any projection is bounded by the basis constant. -/
theorem enorm_proj_le_enormProjBound (n : ℕ) : ‖b.proj n‖ₑ ≤ b.enormProjBound :=
  le_iSup (fun i ↦ ‖b.proj i‖ₑ) n

/-- The basis constant for Schauder bases (supremum over projections) as `nnnorm`.
    Requires completeness to guarantee the supremum is finite,
    see lemma `bddAbove_range_nnnorm_proj` below. -/
noncomputable def nnnormProjBound : ℝ≥0 := ⨆ n, ‖b.proj n‖₊

/-- The projection norms are bounded above in a complete space. -/
theorem bddAbove_range_nnnorm_proj [CompleteSpace X] :
    BddAbove (Set.range (fun n : ℕ ↦ ‖b.proj n‖₊)) := by
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hCpos : 0 ≤ C := by simpa [proj_zero] using hC 0
  refine ⟨C.toNNReal, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hCpos, coe_nnnorm]
  exact hC n

/-- The `nnnorm` of any projection is bounded by the basis constant. -/
theorem nnnorm_proj_le_nnnormProjBound [CompleteSpace X] (n : ℕ) :
    ‖b.proj n‖₊ ≤ b.nnnormProjBound :=
  le_ciSup (bddAbove_range_nnnorm_proj b) n

/-- The norm of any projection is bounded by the basis constant. -/
theorem norm_proj_le_nnnormProjBound [CompleteSpace X] (n : ℕ) :
    ‖b.proj n‖ ≤ b.nnnormProjBound :=
  mod_cast b.nnnorm_proj_le_nnnormProjBound n

/-!
### Construction of Schauder basis

We explain how to construct a Schauder basis from a sequence `P n` of projections
satisfying `P n ∘ P m = P (min n m)`, converging to the identity pointwise, and such that each
`P (n+1) - P n` has rank one. The idea is to define the basis vectors as
`e n = (P (n+1) - P n) x` for some `x` such that this is non-zero, and then
show that these vectors form a Schauder basis. -/

/-- The difference operator `P (n + 1) - P n`. -/
def succSub (P : ℕ → X →L[𝕜] X) (n : ℕ) : X →L[𝕜] X := P (n + 1) - P n

/-- The sum of `succSub` operators up to `n` equals `P n`. -/
@[simp]
lemma sum_succSub (P : ℕ → X →L[𝕜] X) (h0 : P 0 = 0) (n : ℕ) :
    ∑ i ∈ Finset.range n, succSub P i = P n := by
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Finset.sum_range_succ, ih, succSub]; abel

/-- The operators `succSub P i` satisfy a biorthogonality relation. -/
lemma succSub_ortho {P : ℕ → X →L[𝕜] X} (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x)
    (i j : ℕ) (x : X) : succSub P i (succSub P j x) = if i = j then succSub P j x else 0 := by
  simp only [succSub, ContinuousLinearMap.sub_apply, map_sub, hcomp,
    Nat.add_min_add_right]
  split_ifs with h
  · rw [h, min_self, min_eq_right (Nat.le_succ j), Nat.min_eq_left (Nat.le_succ j)]
    abel
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · rw [min_eq_left_of_lt h', min_eq_left (Nat.succ_le_of_lt h'),
        min_eq_left_of_lt (Nat.lt_succ_of_lt h')]
      abel
    · rw [min_eq_right_of_lt h', min_eq_right (Nat.succ_le_of_lt h'),
        min_eq_right_of_lt (Nat.lt_succ_of_lt h')]
      abel

/-- Assuming that the `finrank` of the range of `P n` is `n` then the `finrank` of the range of
    `succSub P n` is `1`. -/
lemma finrank_range_succSub_eq_one {P : ℕ → X →L[𝕜] X}
    (hrank : ∀ n, Module.finrank 𝕜 (P n).toLinearMap.range = n)
    (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x) (n : ℕ) :
    Module.finrank 𝕜 (succSub P n).toLinearMap.range = 1 := by
  let U := (succSub P n).toLinearMap.range
  let V := (P n).toLinearMap.range
  let W := (P (n + 1)).toLinearMap.range
  have hV : V ≤ W := by
    rintro _ ⟨y, rfl⟩
    exact ⟨P n y, by simp [ContinuousLinearMap.coe_coe, hcomp]⟩
  have hUW : U ≤ W := by
    rintro _ ⟨y, rfl⟩
    exact Submodule.sub_mem W ⟨y, rfl⟩ (hV ⟨y, rfl⟩)
  have hW : W = U ⊔ V := by
    apply le_antisymm
    · rintro x ⟨y, hy⟩
      rw [← hy, ContinuousLinearMap.coe_coe, ← sub_add_cancel ((P (n + 1)) y) ((P n) y)]
      exact Submodule.add_mem_sup ⟨y, rfl⟩ ⟨y, rfl⟩
    · exact sup_le hUW hV
  have hdisj : U ⊓ V = ⊥ := eq_bot_iff.mpr fun x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ ↦ by
    simp only [Submodule.mem_bot]
    calc x = (P n) x := by rw [← hz, ContinuousLinearMap.coe_coe, hcomp, min_self]
         _ = 0       := by rw [← hy, ContinuousLinearMap.coe_coe]; simp [succSub, map_sub, hcomp]
  have : FiniteDimensional 𝕜 W := .of_finrank_pos (by rw [hrank]; exact Nat.succ_pos n)
  have : FiniteDimensional 𝕜 U := Submodule.finiteDimensional_of_le hUW
  have : FiniteDimensional 𝕜 V := Submodule.finiteDimensional_of_le hV
  have h_dim := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [hdisj, finrank_bot, add_zero, ← hW, hrank, hrank, Nat.add_comm] at h_dim
  exact Nat.add_right_cancel h_dim.symm

variable (𝕜 X) in
/-- Data for constructing a Schauder basis from a sequence of finite-rank projections.

Given a sequence of continuous linear maps `P n : X →L[𝕜] X` satisfying:
* `P 0 = 0` and `finrank(range(P n)) = n`,
* `P n ∘ P m = P (min n m)` (the projections are nested and commute),
* `P n x → x` for every `x` (pointwise convergence to the identity),

the differences `succSub P n = P (n+1) - P n` are rank-one operators
(see `finrank_range_succSub_eq_one`). Choosing a nonzero vector `e n` in the range of each
`succSub P n` yields a Schauder basis for `X`.

Use `RankOneDecomposition.basis` to construct the `SchauderBasis` from this data. -/
structure RankOneDecomposition where
  /-- The sequence of finite-rank projections. -/
  P : ℕ → X →L[𝕜] X
  /-- The sequence of candidate basis vectors. -/
  e : ℕ → X
  /-- The projections start at `0`. -/
  proj_zero : P 0 = 0
  /-- The `n`-th projection has rank `n`. -/
  finrank_range (n : ℕ) : Module.finrank 𝕜 (P n).toLinearMap.range = n
  /-- The projections commute and are nested `P n (P m) = P (min n m)`. -/
  proj_comp (n m : ℕ) (x : X) : P n (P m x) = P (min n m) x
  /-- The projections converge pointwise to the identity. -/
  proj_tendsto (x : X) : Tendsto (fun n ↦ P n x) atTop (𝓝 x)
  /-- The vector `e_n` lies in the range of the operator `succSub P n = P (n+1) - P n`. -/
  e_mem_range (n : ℕ) : e n ∈ (succSub P n).toLinearMap.range
  /-- The vector `e_n` is non-zero. -/
  e_ne_zero (n : ℕ) : e n ≠ 0

namespace RankOneDecomposition

variable (D : RankOneDecomposition 𝕜 X)

/-- There exists a coefficient scaling `e n` to match `(succSub D.P n) x`. -/
lemma exists_coeff (n : ℕ) (x : X) :
    ∃ c : 𝕜, c • D.e n = (succSub D.P n) x := by
  let S := (succSub D.P n).toLinearMap
  have hrank : Module.finrank 𝕜 S.range = 1 :=
    finrank_range_succSub_eq_one D.finrank_range D.proj_comp n
  have : FiniteDimensional 𝕜 S.range := .of_finrank_pos (hrank.symm ▸ zero_lt_one)
  have hspan : Submodule.span 𝕜 {D.e n} = S.range := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (D.e_mem_range n)
    · simp [hrank, finrank_span_singleton (D.e_ne_zero n)]
  exact Submodule.mem_span_singleton.mp (hspan.symm ▸ LinearMap.mem_range_self S x)

/-- The coefficient functional value for the basis construction. -/
def basisCoeff (n : ℕ) (x : X) : 𝕜 :=
  Classical.choose (exists_coeff D n x)

/-- The coefficient satisfies `basisCoeff D n x • D.e n = (succSub D.P n) x`. -/
@[simp]
lemma basisCoeff_spec (n : ℕ) (x : X) :
    basisCoeff D n x • D.e n = (succSub D.P n) x :=
  Classical.choose_spec (exists_coeff D n x)

/-- Constructs a Schauder basis from rank one decomposition. -/
def basis : SchauderBasis 𝕜 X :=
  let coeff := basisCoeff D
  have hcoeff : ∀ n x, (succSub D.P n) x = coeff n x • D.e n := fun n x ↦
    (basisCoeff_spec D n x).symm
  { basis := D.e
    coord := fun n ↦ LinearMap.mkContinuous
      { toFun := coeff n
        map_add' := fun x y ↦ smul_left_injective 𝕜 (D.e_ne_zero n) <| by
          simp only [add_smul, ← hcoeff, map_add]
        map_smul' := fun c x ↦ smul_left_injective 𝕜 (D.e_ne_zero n) <| by
          dsimp only [RingHom.id_apply]
          rw [smul_eq_mul, ← smul_smul, ← hcoeff, ← hcoeff, map_smul] }
      (‖succSub D.P n‖ / ‖D.e n‖)
      (fun x ↦ by
        rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr (D.e_ne_zero n))]
        calc ‖coeff n x‖ * ‖D.e n‖ = ‖coeff n x • D.e n‖ := (norm_smul _ _).symm
          _ = ‖(succSub D.P n) x‖ := by rw [hcoeff]
          _ ≤ ‖succSub D.P n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _)
    ortho := fun i j ↦ smul_left_injective 𝕜 (D.e_ne_zero i) <| by
      obtain ⟨x, hx⟩ : ∃ x, (succSub D.P j) x = D.e j := D.e_mem_range j
      simp only [mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← hcoeff, ← hx, succSub_ortho D.proj_comp, hx]
      simp only [Pi.single_apply]
      split_ifs with h <;> simp [h]
    expansion := fun x ↦ by
      rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
      exact (D.proj_tendsto x).congr fun n ↦ by
        simp only [Function.comp, LinearMap.coe_mk, AddHom.coe_mk,
                   LinearMap.mkContinuous_apply, ← hcoeff]
        rw [← ContinuousLinearMap.sum_apply, sum_succSub D.P D.proj_zero] }

/-- The projections of the constructed basis correspond to the input data `D.P`. -/
@[simp]
theorem basis_proj : (basis D).proj = D.P := by
  ext n _
  rw [SchauderBasis.proj_apply, ← sum_succSub D.P D.proj_zero n]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  dsimp [basis, mkContinuous_apply, IsLinearMap.mk'_apply]
  rw [basisCoeff_spec]

/-- The sequence of the constructed basis corresponds to the input data `D.e`. -/
@[simp]
theorem basis_coe : ⇑(basis D) = D.e :=
  rfl

end RankOneDecomposition

end SchauderBasis
