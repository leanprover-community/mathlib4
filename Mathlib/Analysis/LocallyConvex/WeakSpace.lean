/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-! # Closures of convex sets in locally convex spaces

This file contains the standard result that if `E` is a vector space with two locally convex
topologies, then the closure of a convex set is the same in either topology, provided they have the
same collection of continuous linear functionals. In particular, the weak closure of a convex set
in a locally convex space coincides with the closure in the original topology.
Of course, we phrase this in terms of linear maps between locally convex spaces, rather than
creating two separate topologies on the same space.
-/
set_option backward.defeqAttrib.useBackward true

public section

variable {𝕜 E F : Type*}
variable [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]
variable [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [LocallyConvexSpace ℝ F]

variable (𝕜) in
/-- If `E` is a locally convex space over `𝕜` (with `RCLike 𝕜`), and `s : Set E` is `ℝ`-convex, then
the closure of `s` and the weak closure of `s` coincide. More precisely, the topological closure
commutes with `toWeakSpace 𝕜 E`.

This holds more generally for any linear equivalence `e : E ≃ₗ[𝕜] F` between locally convex spaces
such that precomposition with `e` and `e.symm` preserves continuity of linear functionals. See
`LinearEquiv.image_closure_of_convex`. -/
theorem Convex.toWeakSpace_closure {s : Set E} (hs : Convex ℝ s) :
    (toWeakSpace 𝕜 E) '' (closure s) = closure (toWeakSpace 𝕜 E '' s) := by
  refine le_antisymm (map_continuous <| toWeakSpaceCLM 𝕜 E).continuousOn.image_closure
    (Set.compl_subset_compl.mp fun x hx ↦ ?_)
  obtain ⟨x, -, rfl⟩ := (toWeakSpace 𝕜 E).toEquiv.image_compl (closure s) |>.symm.subset hx
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  obtain ⟨f, u, hus, hux⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
    hs.closure isClosed_closure (by simpa using hx)
  let f' : StrongDual 𝕜 (WeakSpace 𝕜 E) :=
    { toLinearMap := (f : E →ₗ[𝕜] 𝕜).comp ((toWeakSpace 𝕜 E).symm : WeakSpace 𝕜 E →ₗ[𝕜] E)
      cont := WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip _ }
  have hux' : u < RCLike.reCLM.comp (f'.restrictScalars ℝ) (toWeakSpace 𝕜 E x) := by simpa [f']
  have hus' : closure (toWeakSpace 𝕜 E '' s) ⊆
      {y | RCLike.reCLM.comp (f'.restrictScalars ℝ) y ≤ u} := by
    refine closure_minimal ?_ <| isClosed_le (by fun_prop) (by fun_prop)
    rintro - ⟨y, hy, rfl⟩
    simpa [f'] using (hus y <| subset_closure hy).le
  exact (hux'.not_ge <| hus' ·)

set_option backward.isDefEq.respectTransparency false in
open ComplexOrder in
theorem toWeakSpace_closedConvexHull_eq {s : Set E} :
    (toWeakSpace 𝕜 E) '' (closedConvexHull 𝕜 s) = closedConvexHull 𝕜 (toWeakSpace 𝕜 E '' s) := by
  rw [closedConvexHull_eq_closure_convexHull (𝕜 := 𝕜),
    ((convex_convexHull 𝕜 s).lift ℝ).toWeakSpace_closure _, closedConvexHull_eq_closure_convexHull]
  congr
  refine LinearMap.image_convexHull (toWeakSpace 𝕜 E).toLinearMap s

/-- If `e : E →ₗ[𝕜] F` is a linear map between locally convex spaces, and `f ∘ e` is continuous
for every continuous linear functional `f : StrongDual 𝕜 F`, then `e` commutes with the closure on
convex sets. -/
theorem LinearMap.image_closure_of_convex {s : Set E} (hs : Convex ℝ s) (e : E →ₗ[𝕜] F)
    (he : ∀ f : StrongDual 𝕜 F, Continuous (e.dualMap f)) :
    e '' (closure s) ⊆ closure (e '' s) := by
  suffices he' : Continuous (toWeakSpace 𝕜 F <| e <| (toWeakSpace 𝕜 E).symm ·) by
    have h_convex : Convex ℝ (e '' s) := hs.linear_image (F := F) e
    rw [← Set.image_subset_image_iff (toWeakSpace 𝕜 F).injective, h_convex.toWeakSpace_closure 𝕜]
    simpa only [Set.image_image, ← hs.toWeakSpace_closure 𝕜, LinearEquiv.symm_apply_apply]
      using he'.continuousOn.image_closure (s := toWeakSpace 𝕜 E '' s)
  exact WeakBilin.continuous_of_continuous_eval _ fun f ↦ WeakBilin.eval_continuous _ ({
      toLinearMap := e.dualMap f
      cont := by dsimp; fun_prop } : StrongDual 𝕜 E)

/-- If `e` is a linear isomorphism between two locally convex spaces, and `e` induces (via
precomposition) an isomorphism between their continuous duals, then `e` commutes with the closure
on convex sets.

The hypotheses hold automatically for `e := toWeakSpace 𝕜 E`, see `Convex.toWeakSpace_closure`. -/
theorem LinearEquiv.image_closure_of_convex {s : Set E} (hs : Convex ℝ s) (e : E ≃ₗ[𝕜] F)
    (he₁ : ∀ f : StrongDual 𝕜 F, Continuous (e.dualMap f))
    (he₂ : ∀ f : StrongDual 𝕜 E, Continuous (e.symm.dualMap f)) :
    e '' (closure s) = closure (e '' s) := by
  refine le_antisymm ((e : E →ₗ[𝕜] F).image_closure_of_convex hs he₁) ?_
  simp only [Set.le_eq_subset, ← Set.image_subset_image_iff e.symm.injective]
  simpa [Set.image_image]
    using (e.symm : F →ₗ[𝕜] E).image_closure_of_convex (hs.linear_image (e : E →ₗ[𝕜] F)) he₂

/-- If `e` is a linear isomorphism between two locally convex spaces, and `e` induces (via
precomposition) an isomorphism between their continuous duals, then `e` commutes with the closure
on convex sets.

The hypotheses hold automatically for `e := toWeakSpace 𝕜 E`, see `Convex.toWeakSpace_closure`. -/
theorem LinearEquiv.image_closure_of_convex' {s : Set E} (hs : Convex ℝ s) (e : E ≃ₗ[𝕜] F)
    (e_dual : StrongDual 𝕜 F ≃ StrongDual 𝕜 E)
    (he : ∀ f : StrongDual 𝕜 F, (e_dual f : E →ₗ[𝕜] 𝕜) = e.dualMap f) :
    e '' (closure s) = closure (e '' s) := by
  have he' (f : StrongDual 𝕜 E) : (e_dual.symm f : F →ₗ[𝕜] 𝕜) = e.symm.dualMap f := by
    simp only [DFunLike.ext'_iff, ContinuousLinearMap.coe_coe] at he ⊢
    have (g : StrongDual 𝕜 E) : ⇑g = e_dual.symm g ∘ e := by
      have := he _ ▸ congr(⇑$(e_dual.apply_symm_apply g)).symm
      simpa
    ext x
    conv_rhs => rw [LinearEquiv.dualMap_apply, ContinuousLinearMap.coe_coe, this]
    simp
  refine e.image_closure_of_convex hs ?_ ?_
  · simpa [← he] using fun f ↦ map_continuous (e_dual f)
  · simpa [← he'] using fun f ↦ map_continuous (e_dual.symm f)

/-- The weak topology on a space with separating dual is T2 (Hausdorff). -/
instance {R V : Type*} [CommRing R] [TopologicalSpace R] [T2Space R]
    [ContinuousAdd R] [ContinuousConstSMul R R] [AddCommGroup V] [Module R V]
    [TopologicalSpace V] [SeparatingDual R V] : T2Space (WeakSpace R V) :=
  (WeakBilin.isEmbedding (B := (topDualPairing R V).flip) fun _ _ h => by
    by_contra hne
    obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := R) hne
    exact hf (DFunLike.congr_fun h f)).t2Space
