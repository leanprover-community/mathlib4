/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Topology.Algebra.Group.Cocompact
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Cocompact subgroups of topological vector spaces

Let `V` be a topological vector space over a topological field `K` carrying the module topology.

## Main statements

* `Submodule.isCocompact_iff_span_eq_top`: If `R` is cocompact in the
  non-compact field `K`, an `R`-submodule of a finite-dimensional `V` with the
  module topology is cocompact if and only if it spans `V` over `K`.
-/

@[expose] public section

open Module

/-- If `K` is not compact, any cocompact additive subgroup of `V` spans `V` over `K`, provided `V`
carries the module topology. -/
theorem AddSubgroup.span_eq_top_of_isCocompact {K V : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] [NoncompactSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
    [IsModuleTopology K V] (H : AddSubgroup V) [H.IsCocompact] :
    Submodule.span K (H : Set V) = ⊤ := by
  by_contra h
  apply noncompact_univ K
  obtain ⟨f, hf₁, hf₂⟩ :=
    (Submodule.span K (H : Set V)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr h)
  rw [← (LinearMap.surjective hf₁).range_eq]
  apply AddSubgroup.IsCocompact.isCompact_range_of_periodic (H := H)
    (IsModuleTopology.continuous_of_linearMap f)
  intro h hh x
  simp [LinearMap.mem_ker.mp (hf₂ (Submodule.subset_span hh))]

namespace Submodule

variable {R : Type*} [CommRing R]
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
    ((isCompact_univ_pi fun _ ↦ hC).image (f := fun c : s → K ↦ ∑ i, c i • i.val) (by fun_prop))
    (Set.eq_univ_of_forall fun x ↦ ?_)
  choose c hc _ hh hck using fun i ↦ hRC ▸ Set.mem_univ (b.repr x i)
  choose r hrh using hh
  refine ⟨_, ⟨c, fun i _ ↦ hc i, rfl⟩, ∑ i, r i • i.val,
    sum_mem fun i _ ↦ M.smul_mem _ (hsM i.prop), ?_⟩
  rw [← b.sum_repr x]
  simp_rw [← hck, ← hrh, b, add_smul, Basis.coe_mk, algebraMap_smul, Finset.sum_add_distrib]

/-- If `R` is cocompact in the non-compact field `K`, an `R`-submodule of a finite-dimensional `V`
with the module topology is cocompact if and only if it spans `V` over `K`. -/
theorem isCocompact_iff_span_eq_top [NoncompactSpace K] [FiniteDimensional K V]
    [IsModuleTopology K V] (M : Submodule R V) :
    M.toAddSubgroup.IsCocompact ↔ span K (M : Set V) = ⊤ :=
  ⟨fun _ ↦ M.toAddSubgroup.span_eq_top_of_isCocompact, isCocompact_of_span_eq_top M⟩

end Submodule

/-- `ℤ` is cocompact in `ℝ`. -/
instance isCocompact_range_algebraMap_int : (algebraMap ℤ ℝ).range.toAddSubgroup.IsCocompact :=
  .of_isCompact_add_eq_univ _ isCompact_Icc <| Set.eq_univ_of_forall fun x ↦
    ⟨Int.fract x, ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩, ⌊x⌋, ⟨⌊x⌋, rfl⟩, by simp⟩

/-- A subgroup of a finite-dimensional real vector space is cocompact if and only if it spans. -/
theorem Submodule.isCocompact_iff_span_eq_top_int {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [FiniteDimensional ℝ V] (M : Submodule ℤ V) :
    M.toAddSubgroup.IsCocompact ↔ span ℝ (M : Set V) = ⊤ :=
  have := isModuleTopologyOfFiniteDimensional (𝕜 := ℝ) (E := V)
  isCocompact_iff_span_eq_top M
