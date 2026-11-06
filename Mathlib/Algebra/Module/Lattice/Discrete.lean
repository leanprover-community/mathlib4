/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.LinearAlgebra.Countable
public import Mathlib.Topology.Algebra.Group.Cocompact
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Lattices and discrete subgroups

If `R` embeds as a discrete subring of a topological field `K`, then any lattice
`M : Submodule R V` (in the sense of `Submodule.IsLattice K M`) whose `K`-span carries the module
topology is a discrete subgroup of `V`. This holds automatically if `K` is a complete normed field
and `V` is Hausdorff, see `isModuleTopologyOfFiniteDimensional`.
Conversely, if `R` is infinite and cocompact in a topological field `K`, any `M` with
finite-dimensional `K`-span that meets every compact set in a finite set is a lattice, see
`Submodule.IsLattice.of_tendsto_cofinite_cocompact`. In particular, this applies to discrete `M`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, Proposition 4.2

-/

@[expose] public section

open Topology Module

variable {R : Type*} [CommRing R]

namespace Submodule

section DiscreteTopology

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [Algebra R K]
  [FaithfulSMul R K] [DiscreteTopology (algebraMap R K).range]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [TopologicalSpace V]

/-- If `R` is a discrete subring of `K`, the `R`-span of a finite `K`-linearly independent family
is discrete, provided its `K`-span carries the module topology. -/
theorem discreteTopology_span {ι : Type*} [Finite ι] {v : ι → V} (hv : LinearIndependent K v)
    [IsModuleTopology K (span K (Set.range v))] : DiscreteTopology (span R (Set.range v)) := by
  classical
  have := Fintype.ofFinite ι
  let b := Basis.span (hv.restrict_scalars' R)
  -- Consider `f : span R v → (ι → R)` sending `m` to its coefficient vector w.r.t. `b`, viewed
  -- in the discrete image of `R` in `K`. `f` is clearly injective. What's left is continuity.
  refine .of_continuous_injective (f := fun m i ↦ (algebraMap R K).rangeRestrict (b.repr m i))
    (continuous_pi fun i ↦ .subtype_mk ?_ _) fun m m' h ↦ b.repr.injective <| Finsupp.ext
      fun i ↦ FaithfulSMul.algebraMap_injective R K (congrArg Subtype.val (congrFun h i))
  -- We show that the coordinate functions `span R v → K` are continuous.
  -- Let `c` be a basis of `W := span K v`.
  let c := Basis.span hv
  -- `e : span R v → W` sends `m` to its representation in terms of the basis,
  let e (m : span R (Set.range v)) := ∑ j, algebraMap R K (b.repr m j) • c j
  -- hence `e` is just the inclusion.
  have he (m : span R (Set.range v)) : (e m).1 = m := by
    conv_rhs => rw [← b.sum_repr m]
    simp [e, b, c, algebraMap_smul, -Basis.sum_repr]
  have : Continuous e := continuous_induced_rng.mpr
    (by simpa only [Function.comp_def, he] using continuous_subtype_val)
  -- The coordinate function `span R v → K` equals the composition of `e` with the coordinate
  -- function `W → K`. The latter is continuous since `W` carries the module topology.
  convert (IsModuleTopology.continuous_of_linearMap (c.coord i)).comp this using 1
  ext m
  simp [e, Finsupp.single_apply, Algebra.smul_def]

/-- If `R` is a discrete subring of `K`, any lattice whose `K`-span carries the module topology is
a discrete subgroup. -/
theorem IsLattice.discreteTopology (M : Submodule R V) [IsLattice K M]
    [IsModuleTopology K (span K (M : Set V))] : DiscreteTopology M := by
  obtain ⟨s, hs, hli, hM, hsM⟩ := exists_finite_linearIndepOn_le_span K M
  have := hs.to_subtype
  have : IsModuleTopology K (span K (Set.range ((↑) : s → V))) := by
    rwa [Subtype.range_coe, hsM]
  have := discreteTopology_span (R := R) (v := ((↑) : s → V)) hli
  rw [Subtype.range_coe] at this
  exact .of_subset this hM

end DiscreteTopology

/-- If `K` is not compact, any cocompact `R`-submodule of `V` spans `V` over `K`, provided `V`
carries the module topology. -/
theorem span_eq_top_of_isCocompact {K V : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] [NoncompactSpace K] [AddCommGroup V] [Module R V] [Module K V]
    [TopologicalSpace V] [IsModuleTopology K V] (M : Submodule R V)
    [M.toAddSubgroup.IsCocompact] : span K (M : Set V) = ⊤ := by
  by_contra h
  obtain ⟨f, hf₁, hf₂⟩ := (span K (M : Set V)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr h)
  apply noncompact_univ K
  rw [← (LinearMap.surjective hf₁).range_eq]
  apply AddSubgroup.IsCocompact.isCompact_range_of_periodic (H := M.toAddSubgroup)
  · exact IsModuleTopology.continuous_of_linearMap f
  · intro m hm x
    simp [LinearMap.mem_ker.mp (hf₂ (subset_span hm))]

section Cocompact

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [WeaklyLocallyCompactSpace K] [Algebra R K] [(algebraMap R K).range.toAddSubgroup.IsCocompact]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]

/-- If `R` is cocompact in `K`, any `R`-submodule spanning a finite-dimensional `V` over `K` is
cocompact. -/
theorem isCocompact_of_span_eq_top [FiniteDimensional K V] (M : Submodule R V)
    (hM : span K (M : Set V) = ⊤) : M.toAddSubgroup.IsCocompact := by
  obtain ⟨C, hC, hRC⟩ :=
    (algebraMap R K).range.toAddSubgroup.exists_isCompact_add_eq_univ_of_isCocompact
  obtain ⟨s, hsM, hs, hli⟩ := exists_linearIndependent K (M : Set V)
  let b := Basis.mk hli (by rw [Subtype.range_coe, hs, hM])
  have := @Fintype.ofFinite s <| Module.Finite.finite_basis b
  refine .of_isCompact_add_eq_univ _
    ((isCompact_univ_pi fun _ ↦ hC).image (f := fun c : s → K ↦ ∑ i, c i • i.1) (by fun_prop))
    (Set.eq_univ_of_forall fun x ↦ ?_)
  choose c hc _ hh hck using fun i ↦ hRC ▸ Set.mem_univ (b.repr x i)
  choose r hrh using hh
  refine ⟨_, ⟨c, fun i _ ↦ hc i, rfl⟩, ∑ i, r i • i.1, sum_mem fun i _ ↦ M.smul_mem _ (hsM i.2), ?_⟩
  rw [← b.sum_repr x]
  simp_rw [← hck, ← hrh, b, add_smul, Basis.coe_mk, algebraMap_smul, Finset.sum_add_distrib]

/-- If `R` is cocompact in the non-compact field `K`, an `R`-submodule of a finite-dimensional `V`
with the module topology is cocompact if and only if it spans `V` over `K`. -/
theorem isCocompact_iff_span_eq_top [NoncompactSpace K] [FiniteDimensional K V]
    [IsModuleTopology K V] (M : Submodule R V) :
    M.toAddSubgroup.IsCocompact ↔ span K (M : Set V) = ⊤ :=
  ⟨fun _ ↦ span_eq_top_of_isCocompact M, isCocompact_of_span_eq_top M⟩

variable [Infinite R] [FaithfulSMul R K]
variable (M : Submodule R V) [FiniteDimensional K (span K (M : Set V))]

/-- If `R` is infinite and cocompact in `K`, any subgroup with finite-dimensional `K`-span that
meets every compact set in a finite set is a lattice. -/
theorem IsLattice.of_tendsto_cofinite_cocompact
    (hM : Filter.Tendsto ((↑) : M → V) Filter.cofinite (Filter.cocompact V)) :
    IsLattice K M := by
  have := IsDomain.of_faithfulSMul R K
  obtain ⟨C, hC, hRC⟩ :=
    (algebraMap R K).range.toAddSubgroup.exists_isCompact_add_eq_univ_of_isCocompact
  obtain ⟨s, hsM, hs, hli⟩ := exists_linearIndependent K (M : Set V)
  have : FiniteDimensional K (span K (Set.range ((↑) : s → V))) := by
    rw [Subtype.range_coe, hs]; infer_instance
  have := @Fintype.ofFinite s <| Module.Finite.finite_basis (Basis.span hli)
  have hsR : span R s ≤ M := span_le.mpr hsM
  let P := (fun (c : s → K) ↦ ∑ i, c i • i.1) '' Set.univ.pi fun _ ↦ C
  have hP : IsCompact P := (isCompact_univ_pi fun _ ↦ hC).image (by fun_prop)
  have hPM : {m : M | m.1 ∈ P}.Finite := tendsto_cofinite_cocompact_iff.mp hM P hP
  let N := (span R s).comap M.subtype
  have : Finite (M ⧸ N) := by
    refine Set.finite_univ_iff.mp <| (hPM.image N.mkQ).subset fun x _ ↦ ?_
    obtain ⟨m, rfl⟩ := N.mkQ_surjective x
    obtain ⟨k, hk⟩ := (mem_span_range_iff_exists_fun K).mp <| by
      rw [Subtype.range_coe, hs]; exact subset_span m.2
    choose c hc _ hh hck using fun i ↦ hRC ▸ Set.mem_univ (k i)
    choose r hrh using hh
    have hr : ∑ i, r i • i.1 ∈ span R s := sum_mem fun i _ ↦ smul_mem _ _ (subset_span i.2)
    refine ⟨⟨m - ∑ i, r i • i.1, sub_mem m.2 (hsR hr)⟩, ⟨c, fun i _ ↦ hc i, ?_⟩,
      (Submodule.Quotient.eq N).mpr (by simpa [N] using neg_mem hr)⟩
    simp [← hk, ← hck, ← hrh, add_smul, algebraMap_smul, Finset.sum_add_distrib]
  have := Module.Finite.span_of_finite R s.toFinite
  have : Module.Finite R N := .equiv (comapSubtypeEquivOfLe hsR).symm
  rw [iff_fg_and_finrank_span_eq_finrank]
  refine ⟨Module.Finite.iff_fg.mp (.of_submodule_quotient N), congrArg Cardinal.toNat ?_⟩
  rw [← rank_quotient_add_rank_of_isDomain N, (comapSubtypeEquivOfLe hsR).rank_eq, ← hs,
    rank_span_set (hli.restrict_scalars' R), rank_span_set hli, rank_eq_zero_iff.mpr ?_, zero_add]
  intro x
  obtain ⟨a, b, hab, h⟩ := Finite.exists_ne_map_eq_of_infinite (· • x : R → M ⧸ N)
  exact ⟨a - b, sub_ne_zero.mpr hab, by rwa [sub_smul, sub_eq_zero]⟩

/-- If `R` is infinite and cocompact in `K`, any discrete subgroup with finite-dimensional `K`-span
is a lattice. -/
theorem IsLattice.of_discreteTopology [DiscreteTopology M] : IsLattice K M :=
  of_tendsto_cofinite_cocompact M <|
    M.toAddSubgroup.tendsto_coe_cofinite_of_isDiscrete (isDiscrete_iff_discreteTopology.mpr ‹_›)

end Cocompact

section Int

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V]
variable (M : Submodule ℤ V)

attribute [local instance] isModuleTopologyOfFiniteDimensional

instance discreteTopology_range_algebraMap_int : DiscreteTopology (algebraMap ℤ ℝ).range :=
  Int.isClosedEmbedding_coe_real.1.toHomeomorph.discreteTopology

instance isCocompact_range_algebraMap_int :
    (algebraMap ℤ ℝ).range.toAddSubgroup.IsCocompact :=
  .of_isCompact_add_eq_univ _ isCompact_Icc <| Set.eq_univ_of_forall fun x ↦
    ⟨Int.fract x, ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩, ⌊x⌋, ⟨⌊x⌋, rfl⟩, by simp⟩

/-- Any lattice in a real vector space is a discrete subgroup. -/
instance IsLattice.discreteTopology_int [T2Space V] [IsLattice ℝ M] : DiscreteTopology M :=
  discreteTopology (K := ℝ) M

/-- Any discrete subgroup of a real vector space with finite-dimensional span is a finitely
generated `ℤ`-module. -/
instance finite_of_discreteTopology_int [FiniteDimensional ℝ (span ℝ (M : Set V))]
    [DiscreteTopology M] : Module.Finite ℤ M :=
  have := IsLattice.of_discreteTopology (K := ℝ) M
  IsLattice.finite ℝ M

/-- Any discrete subgroup of a real vector space with finite-dimensional span is countable. -/
instance countable_of_discreteTopology_int (M : Submodule ℤ V)
    [FiniteDimensional ℝ (span ℝ (M : Set V))] [DiscreteTopology M] : Countable M :=
  Countable.of_moduleFinite (R := ℤ)

/-- Any discrete subgroup of a real vector space with finite-dimensional span is a free
`ℤ`-module. -/
instance free_of_discreteTopology_int [FiniteDimensional ℝ (span ℝ (M : Set V))]
    [DiscreteTopology M] : Module.Free ℤ M :=
  have := IsLattice.of_discreteTopology (K := ℝ) M
  IsLattice.free ℝ M

/-- A subgroup of a real vector space with finite-dimensional span is a lattice if and only if it
is discrete. -/
theorem IsLattice.iff_discreteTopology_int [T2Space V] [FiniteDimensional ℝ (span ℝ (M : Set V))] :
    IsLattice ℝ M ↔ DiscreteTopology M :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ of_discreteTopology M⟩

/-- A subgroup of a finite-dimensional real vector space is a full lattice if and only if it is
discrete and spans. -/
theorem IsFullLattice.iff_discreteTopology_int [T2Space V] [FiniteDimensional ℝ V] :
    IsFullLattice ℝ M ↔ DiscreteTopology M ∧ span ℝ (M : Set V) = ⊤ :=
  ⟨fun _ ↦ ⟨inferInstance, IsFullLattice.span_eq_top⟩,
    fun ⟨_, h⟩ ↦ { toIsLattice := IsLattice.of_discreteTopology M, span_eq_top := h }⟩

/-- Any full lattice in a real vector space is cocompact. -/
instance IsFullLattice.isCocompact_int [IsFullLattice ℝ M] : M.toAddSubgroup.IsCocompact :=
  have := IsFullLattice.finiteDimensional ℝ M
  isCocompact_of_span_eq_top M ‹IsFullLattice ℝ M›.span_eq_top

/-- A subgroup of a finite-dimensional real vector space is cocompact if and only if it spans. -/
theorem isCocompact_iff_span_eq_top_int [T2Space V] [FiniteDimensional ℝ V] :
    M.toAddSubgroup.IsCocompact ↔ span ℝ (M : Set V) = ⊤ :=
  have := isModuleTopologyOfFiniteDimensional (𝕜 := ℝ) (E := V)
  isCocompact_iff_span_eq_top M

end Int

section Normed

variable {V : Type*} [NormedAddCommGroup V]

/-- A discrete submodule of a proper normed group meets every bounded set in a finite set. -/
theorem finite_inter_of_isBounded [ProperSpace V] [Module R V] (M : Submodule R V)
    [DiscreteTopology M] {s : Set V} (hs : Bornology.IsBounded s) : (s ∩ M).Finite := by
  have h := SetLike.isDiscrete_iff_discreteTopology.mpr ‹DiscreteTopology M›
  exact Metric.finite_isBounded_inter_isClosed h hs (M.toAddSubgroup.isClosed_of_isDiscrete h)

variable [NormedSpace ℝ V] (M : Submodule ℤ V)

/-- Any subgroup of a real normed space with finite-dimensional span that meets every closed ball
in a finite set is a lattice. -/
theorem IsLattice.of_finite_inter_closedBall [FiniteDimensional ℝ (span ℝ (M : Set V))]
    (hM : ∀ r, ((M : Set V) ∩ Metric.closedBall 0 r).Finite) : IsLattice ℝ M := by
  refine of_tendsto_cofinite_cocompact M (tendsto_cofinite_cocompact_iff.mpr fun C hC ↦ ?_)
  obtain ⟨r, hr⟩ := hC.isBounded.subset_closedBall 0
  exact ((hM r).preimage Subtype.val_injective.injOn).subset fun x hx ↦ ⟨x.2, hr hx⟩

end Normed

end Submodule
