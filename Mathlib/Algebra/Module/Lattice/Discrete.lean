/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.LinearAlgebra.Countable
public import Mathlib.Topology.Algebra.Module.Cocompact
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Lattices and discrete subgroups

If `R` embeds as a discrete subring of a topological field `K`, then any
lattice `M : Submodule R V` whose `K`-span carries the module topology is a
discrete subgroup of `V`, see `IsLattice.discreteTopology`. This holds
automatically if `K` is a complete normed field and `V` is Hausdorff, see
`isModuleTopologyOfFiniteDimensional`.

Conversely, if `R` is infinite and cocompact in a topological field `K`, any
`M` with finite-dimensional `K`-span that meets every compact set in a finite
set is a lattice, see `Submodule.IsLattice.of_tendsto_cofinite_cocompact`. In
particular, this applies to discrete `M`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, Proposition 4.2

-/

@[expose] public section

open Topology Module

section Metric

variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G] [ProperSpace G]

/-- A discrete subgroup of a proper metric group meets every bounded set in a finite set. -/
@[to_additive /-- A discrete additive subgroup of a proper metric group meets every bounded set
in a finite set. -/]
theorem SubgroupClass.finite_inter_of_isBounded {S : Type*} [SetLike S G] [SubgroupClass S G]
    (H : S) [DiscreteTopology H] {s : Set G} (hs : Bornology.IsBounded s) : (s ∩ H).Finite :=
  have h := SetLike.isDiscrete_iff_discreteTopology.mpr ‹DiscreteTopology H›
  Metric.finite_isBounded_inter_isClosed h hs ((Subgroup.ofClass H).isClosed_of_isDiscrete h)

end Metric

variable {R : Type*} [CommRing R]

namespace Submodule

section DiscreteTopology

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [Algebra R K]
  [FaithfulSMul R K] [DiscreteTopology (algebraMap R K).range]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [TopologicalSpace V]

variable (R) in
/-- If `R` is a discrete subring of `K`, the `R`-span of a finite `K`-linearly independent family
is discrete, provided its `K`-span carries the module topology. -/
theorem discreteTopology_span {ι : Type*} [Finite ι] {v : ι → V} (hv : LinearIndependent K v)
    [IsModuleTopology K (span K (Set.range v))] : DiscreteTopology (span R (Set.range v)) := by
  classical
  have := Fintype.ofFinite ι
  let b := Basis.span (hv.restrict_scalars' R)
  refine .of_continuous_injective (f := fun m i ↦ (algebraMap R K).rangeRestrict (b.repr m i))
    (continuous_pi fun i ↦ .subtype_mk ?_ _) fun m m' h ↦ b.repr.injective <| Finsupp.ext
      fun i ↦ FaithfulSMul.algebraMap_injective R K (congrArg Subtype.val (congrFun h i))
  let c := Basis.span hv
  let e (m : span R (Set.range v)) := ∑ j, algebraMap R K (b.repr m j) • c j
  have he (m : span R (Set.range v)) : (e m).val = m := by
    conv_rhs => rw [← b.sum_repr m]
    simp [e, b, c, algebraMap_smul, -Basis.sum_repr]
  have : Continuous e := continuous_induced_rng.mpr
    (by simpa only [Function.comp_def, he] using continuous_subtypeVal)
  convert (IsModuleTopology.continuous_of_linearMap (c.coord i)).comp this using 1
  ext m
  simp [e, Finsupp.single_apply, Algebra.smul_def]

/-- If `R` is a discrete subring of `K`, any lattice whose `K`-span carries the module topology is
a discrete subgroup. -/
theorem IsLattice.discreteTopology (M : Submodule R V) [IsLattice K M]
    [IsModuleTopology K (span K (M : Set V))] : DiscreteTopology M := by
  obtain ⟨s, hs, hli, hM, hsM⟩ := exists_finite_linearIndepOn_le_span K M
  refine .of_subset ?_ hM
  have : Finite s := hs.to_subtype
  have : IsModuleTopology K (span K (Set.range ((↑) : s → V))) := by
    rwa [Subtype.range_coe, hsM]
  have := discreteTopology_span R (v := ((↑) : s → V)) hli
  rwa [Subtype.range_coe] at this

end DiscreteTopology

section Cocompact

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [WeaklyLocallyCompactSpace K] [Algebra R K] [(algebraMap R K).range.toAddSubgroup.IsCocompact]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]

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
  let P := (fun (c : s → K) ↦ ∑ i, c i • i.val) '' Set.univ.pi fun _ ↦ C
  have hP : IsCompact P := (isCompact_univ_pi fun _ ↦ hC).image (by fun_prop)
  have hPM : {m : M | m.val ∈ P}.Finite := tendsto_cofinite_cocompact_iff.mp hM P hP
  let N := (span R s).comap M.subtype
  have : Finite (M ⧸ N) := by
    refine Set.finite_univ_iff.mp <| (hPM.image N.mkQ).subset fun x _ ↦ ?_
    obtain ⟨m, rfl⟩ := N.mkQ_surjective x
    obtain ⟨k, hk⟩ := (mem_span_range_iff_exists_fun K).mp <| by
      rw [Subtype.range_coe, hs]; exact subset_span m.property
    choose c hc _ hh hck using fun i ↦ hRC ▸ Set.mem_univ (k i)
    choose r hrh using hh
    have hr : ∑ i, r i • i.val ∈ span R s := sum_mem fun i _ ↦ smul_mem _ _ (subset_span i.property)
    refine ⟨⟨m - ∑ i, r i • i.val, sub_mem m.property (hsR hr)⟩, ⟨c, fun i _ ↦ hc i, ?_⟩,
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

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (M : Submodule ℤ V)

/-- Any lattice in a real vector space is a finitely generated `ℤ`-module. -/
instance IsLattice.finite_int [IsLattice ℝ M] : Module.Finite ℤ M :=
  IsLattice.finite ℝ M

/-- Any lattice in a real vector space is a free `ℤ`-module. -/
instance IsLattice.free_int [IsLattice ℝ M] : Module.Free ℤ M :=
  IsLattice.free ℝ M

/-- Any lattice in a real vector space is countable. -/
instance IsLattice.countable_int [IsLattice ℝ M] : Countable M :=
  .of_moduleFinite (R := ℤ)

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

attribute [local instance] isModuleTopologyOfFiniteDimensional

instance discreteTopology_range_algebraMap_int : DiscreteTopology (algebraMap ℤ ℝ).range :=
  Int.isClosedEmbedding_coe_real.toIsEmbedding.toHomeomorph.discreteTopology

/-- Any lattice in a real vector space is a discrete subgroup. -/
instance IsLattice.discreteTopology_int [T2Space V] [IsLattice ℝ M] : DiscreteTopology M :=
  discreteTopology (K := ℝ) M

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

end Int

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (M : Submodule ℤ V)

/-- Any subgroup of a real normed space with finite-dimensional span that meets every closed ball
in a finite set is a lattice. -/
theorem IsLattice.of_finite_inter_closedBall [FiniteDimensional ℝ (span ℝ (M : Set V))]
    (hM : ∀ r, ((M : Set V) ∩ Metric.closedBall 0 r).Finite) : IsLattice ℝ M := by
  refine of_tendsto_cofinite_cocompact M (tendsto_cofinite_cocompact_iff.mpr fun C hC ↦ ?_)
  obtain ⟨r, hr⟩ := hC.isBounded.subset_closedBall 0
  exact ((hM r).preimage Subtype.val_injective.injOn).subset fun x hx ↦ ⟨x.property, hr hx⟩

end Normed

end Submodule
