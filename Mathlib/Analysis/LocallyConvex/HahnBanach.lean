/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.RCLike.Extend
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Hahn-Banach for locally convex spaces

This file contains an outline of the locally convex analogue of the extension statements from
`Mathlib.Analysis.Normed.Module.HahnBanach`.

The key new ingredient is `Seminorm.bound_of_continuous`: in a locally convex space, a continuous
linear form on a subspace is bounded by the restriction of a continuous seminorm on the ambient
space. Once such a seminorm is available, the abstract extension theorem
`exists_extension_of_le_sublinear` applies exactly as in the normed proof.

We outline:

* `Real.exists_extension`: extension of continuous real linear forms;
* `exists_extension`: the `RCLike` version;
* `ContinuousLinearMap.exist_extension_of_finiteDimensional_range`: extension of maps with
  finite-dimensional range;
* `Submodule.ClosedComplemented.of_finiteDimensional`: finite-dimensional submodules are closed
  complemented.
-/

public section

open Module Topology

variable {𝕜 E F : Type*} [NormedField 𝕜] [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

/-- A seminorm defined by a continuous linear form `f : E →L[𝕜] 𝕜` over a normed field `𝕜` is
continuous. -/
theorem ContinuousLinearMap.continuous_seminorm (f : E →L[𝕜] 𝕜) :
    Continuous f.toSeminorm := by
  simp only [LinearMap.coe_toSeminorm]
  fun_prop

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- **Hahn-Banach theorem** for continuous linear functions on locally convex spaces over `ℝ`. -/
theorem Real.exists_extension (p : Subspace ℝ E) (f : StrongDual ℝ p) :
    ∃ g : StrongDual ℝ E, ∀ x : p, g x = f x := by
  -- Find a sublinear map defined on `E` that bounds `f` on `p`.
  obtain ⟨s, C, hc, hs⟩ :=
    f.toSeminorm.bound_of_continuous (IsInducing.subtypeVal.withSeminorms
      (f := p.subtype) (PolynormableSpace.withSeminorms ℝ E)) f.continuous_seminorm
  let h := C • s.sup (fun q : { q : Seminorm ℝ E // Continuous q } => q.1)
  obtain ⟨g, hg, hl⟩ := by
    refine exists_extension_of_le_sublinear ⟨p, f⟩ h ?_ ?_ ?_
    · intro c hc x
      simp [h]
      -- missing APIs
      sorry
    · intro x y
      simp [h]
      -- missing APIs
      sorry
    · intro x
      simp only [LinearPMap.mk_apply, ContinuousLinearMap.coe_coe, h]
      have := hs x
      calc
      _ ≤ f.toSeminorm x := by simp [le_abs_self]
      _ ≤ C • s.sup (SeminormFamily.comp (fun p ↦ ↑p) p.subtype) x := hs x
      _ = _ := by
        -- missing APIs for sup comm comp
        sorry
  refine ⟨⟨g, ?_⟩, hg⟩
  sorry

section RCLike

open RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E]

/-- **Hahn-Banach theorem** for continuous linear functions on locally convex spaces over an
`RCLike` field. -/
theorem exists_extension (p : Submodule 𝕜 E) (f : StrongDual 𝕜 p) :
    ∃ g : StrongDual 𝕜 E, ∀ x : p, g x = f x := by
  have := IsScalarTower.continuousSMul (M := ℝ) (α := E) 𝕜
  let fr := reCLM.comp (f.restrictScalars ℝ)
  obtain ⟨g, hg⟩ := Real.exists_extension (p.restrictScalars ℝ) fr
  /- Outline:
  1. Restrict scalars and apply the real theorem to the real part `fr`.
  2. Extend the resulting real functional to a `𝕜`-linear functional using
     `StrongDual.extendRCLike`.
  3. Check, exactly as in `Mathlib.Analysis.Normed.Module.HahnBanach`, that this extension agrees
     with `f` on `p`.
  -/
  sorry

variable [AddCommGroup F] [TopologicalSpace F] [T2Space F] [IsTopologicalAddGroup F]
  [Module 𝕜 F] [ContinuousSMul 𝕜 F]

/-- Corollary of the locally convex **Hahn-Banach theorem**: if `f : p → F` is a continuous linear
map with finite-dimensional range, then `f` extends to a continuous linear map on the whole space.

This is the same coordinatewise argument as
`ContinuousLinearMap.exist_extension_of_finiteDimensional_range` in the normed setting. -/
lemma ContinuousLinearMap.exist_extension_of_finiteDimensional_range {p : Submodule 𝕜 E}
    (f : p →L[𝕜] F) [FiniteDimensional 𝕜 f.range] :
    ∃ g : E →L[𝕜] F, f = g.comp p.subtypeL := by
  let b := Module.finBasis 𝕜 f.range
  let e := b.equivFunL
  let fi := fun i => (LinearMap.toContinuousLinearMap (b.coord i)).comp
    (f.codRestrict _ <| LinearMap.mem_range_self _)
  /- Outline:
  1. For each coordinate functional `fi i : p →L[𝕜] 𝕜`, apply `exists_extension`.
  2. Assemble the coordinate extensions into a map `E →L[𝕜] (ι → 𝕜)`.
  3. Compose with `e.symm` and then with `f.range.subtypeL` to recover an extension of `f`.
  4. The verification is word-for-word the same as in the normed file.
  -/
  sorry

/-- A finite-dimensional submodule of a locally convex real or complex topological vector space is
`Submodule.ClosedComplemented`. -/
lemma Submodule.ClosedComplemented.of_finiteDimensional (p : Submodule 𝕜 F)
    [FiniteDimensional 𝕜 p] [LocallyConvexSpace ℝ F] : p.ClosedComplemented := by
  let ⟨g, hg⟩ := (ContinuousLinearMap.id 𝕜 p).exist_extension_of_finiteDimensional_range
  exact ⟨g, DFunLike.congr_fun hg.symm⟩

end RCLike

#min_imports
