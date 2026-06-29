/-
Copyright (c) 2026 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill, Andrew Yang, Edison Xie
-/

module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology

/-!

# Continuous cohomology

We define continuous cohomology as the homology of homogeneous cochains.

## Implementation details

We define homogeneous cochains as `g`-invariant continuous function in `C(G, C(G,...,C(G, M)))`
instead of the usual `C(Gⁿ, M)` to allow more general topological groups other than locally compact
ones. For this to work, we also work in `Action (TopModuleCat R) G`, where the `G` action on `M`
is only continuous on `M`, and not necessarily continuous in both variables, because the `G` action
on `C(G, M)` might not be continuous on both variables even if it is on `M`.

For the differential map, instead of a finite sum we use the inductive definition
`d₋₁ : M → C(G, M) := const : m ↦ g ↦ m` and
`dₙ₊₁ : C(G, _) → C(G, C(G, _)) := const - C(G, dₙ) : f ↦ g ↦ f - dₙ (f (g))`
See `ContinuousCohomology.MultiInd.d`.

## Main definition
- `ContinuousCohomology.homogeneousCochains`:
  The functor taking an `R`-linear `G`-representation to the complex of homogeneous cochains.
- `continuousCohomology`:
  The functor taking an `R`-linear `G`-representation to its `n`-th continuous cohomology.

## TODO
- Show that it coincides with `groupCohomology` for discrete groups.
- Give the usual description of cochains in terms of `n`-ary functions for locally compact groups.
- Show that short exact sequences induce long exact sequences in certain scenarios.
-/

universe u₁ u₂ u₃

@[expose] public section

open CategoryTheory Functor ContinuousMap TopRep

variable (k : Type u₁) (G : Type u₂) [CommRing k] [Group G] [TopologicalSpace k]
  [IsTopologicalRing k]

namespace ContinuousCohomology
open TopRep.MultiInd ContRepresentation
variable [TopologicalSpace G] [IsTopologicalGroup G]

/--
The functor which removes the zeroth
term in a cochain complex and shufts the other terms down by one.
-/
abbrev crop (C : Type*) [Category C] [Limits.HasZeroMorphisms C]:=
  (ComplexShape.embeddingUp'Add 1 1).restrictionFunctor C

/-- `homogeneousCochains R G` is the functor taking
an `k`-linear `G`-representation to the complex of homogeneous cochains. -/
abbrev homogeneousCochains : TopRep k G ⥤ CochainComplex (TopModuleCat k) ℕ :=
  (MultiInd.complex k G).asFunctor ⋙ (invariants k G).mapHomologicalComplex _
  ⋙ crop (TopModuleCat k)

instance {n : ℕ} {rep : TopRep k G} : FunLike (((homogeneousCochains k G).obj rep).X n) G
    ((MultiInd.functor k G n).obj rep) where
  coe σ := σ.val.toFun
  coe_injective _ _ _ := by simp_all

lemma homogeneousCochains_coe_apply {n : ℕ} {rep : TopRep k G}
    (σ : ((homogeneousCochains k G).obj rep).X n) (g : G) :
    σ.val.toFun g = σ g := rfl

lemma homogeneousCochains.d_eq (n : ℕ) (rep : TopRep k G) :
    ((homogeneousCochains k G).obj rep).d n (n + 1)
    = (invariants k G).map (((MultiInd.complex k G).asFunctor.obj rep).d (n + 1) (n + 2)) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma homogeneousCochains.property {n : ℕ} {rep : TopRep k G}
    (σ : ((homogeneousCochains k G).obj rep).X n) (g₁ g₂ : G) :
    σ (g₁ * g₂) = ((MultiInd.functor k G n).obj rep).ρ g₁ (σ g₂) := by
  have := σ.2 g₁⁻¹
  simp only [ComplexShape.embeddingUp'Add_f, HomologicalComplex.asFunctor_obj_X] at this
  apply_fun DFunLike.coe (F := ((MultiInd.functor k G (n + 1)).obj rep)) at this
  have := congr_fun this g₂
  simp only [functor, comp_obj, coind₁_apply_apply, inv_inv, ContinuousMap.comp_apply, coe_mulLeft,
    coe_mk] at this
  have key := congrArg (((MultiInd.functor k G n).obj rep).ρ g₁) this
  rwa [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self] at key

/-- `continuousCohomologyFunctor k G n` is the functor taking
an `k`-linear `G`-representation to its `n`-th continuous cohomology. -/
noncomputable def _root_.continuousCohomologyFunctor (n : ℕ) : TopRep k G ⥤ TopModuleCat k :=
  homogeneousCochains k G ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- The continuous cohomology of a continuous representation defined
by `continuousCohomologyFunctor`. -/
noncomputable abbrev _root_.continuousCohomology (n : ℕ) (A : TopRep k G) :
    TopModuleCat k := (continuousCohomologyFunctor k G n).obj A

end ContinuousCohomology
