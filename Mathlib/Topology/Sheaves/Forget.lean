/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts

#align_import topology.sheaves.forget from "leanprover-community/mathlib"@"5dc6092d09e5e489106865241986f7f2ad28d4c8"

/-!
# Checking the sheaf condition on the underlying presheaf of types.

If `G : C ⥤ D` is a functor which reflects isomorphisms and preserves limits
(we assume all limits exist in both `C` and `D`),
then checking the sheaf condition for a presheaf `F : presheaf C X`
is equivalent to checking the sheaf condition for `F ⋙ G`.

The important special case is when
`C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphisms.
Then to check the sheaf condition it suffices
to check it on the underlying sheaf of types.

## References
* https://stacks.math.columbia.edu/tag/0073
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

open Opposite

namespace TopCat

namespace Presheaf

namespace SheafCondition

open SheafConditionEqualizerProducts

universe v u₁ u₂

variable {C : Type u₁} [Category.{v} C] [HasLimits C]

variable {D : Type u₂} [Category.{v} D] [HasLimits D]

variable (G : C ⥤ D) [PreservesLimits G]

variable {X : TopCat.{v}} (F : Presheaf C X)

variable {ι : Type v} (U : ι → Opens X)

-- Porting note : Lean4 does not support this
-- attribute [local reducible] diagram left_res right_res

/-- When `G` preserves limits, the sheaf condition diagram for `F` composed with `G` is
naturally isomorphic to the sheaf condition diagram for `F ⋙ G`.
-/
def diagramCompPreservesLimits : diagram F U ⋙ G ≅ diagram.{v} (F ⋙ G) U := by
  fapply NatIso.ofComponents
  rintro ⟨j⟩
  exact PreservesProduct.iso _ _
  exact PreservesProduct.iso _ _
  rintro ⟨⟩ ⟨⟩ ⟨⟩
  · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
    -- See https://github.com/leanprover-community/mathlib4/issues/5229
    refine limit.hom_ext (fun j => ?_)
    simp
  · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
    -- See https://github.com/leanprover-community/mathlib4/issues/5229
    refine limit.hom_ext (fun j => ?_)
    -- Porting note : `attribute [local reducible]` doesn't work, this is its replacement
    dsimp [diagram, leftRes, rightRes]
    simp [limit.lift_π, Functor.comp_map, map_lift_piComparison, Fan.mk_π_app,
      PreservesProduct.iso_hom, parallelPair_map_left, Functor.map_comp, Category.assoc]
  · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
    -- See https://github.com/leanprover-community/mathlib4/issues/5229
    refine limit.hom_ext (fun j => ?_)
    -- Porting note : `attribute [local reducible]` doesn't work, this is its replacement
    dsimp [diagram, leftRes, rightRes]
    simp [limit.lift_π, Functor.comp_map, map_lift_piComparison, Fan.mk_π_app,
      PreservesProduct.iso_hom, parallelPair_map_left, Functor.map_comp, Category.assoc]
  · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
    -- See https://github.com/leanprover-community/mathlib4/issues/5229
    refine limit.hom_ext (fun j => ?_)
    simp [diagram, leftRes, rightRes]
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition.diagram_comp_preserves_limits TopCat.Presheaf.SheafCondition.diagramCompPreservesLimits

-- attribute [local reducible] res

/-- When `G` preserves limits, the image under `G` of the sheaf condition fork for `F`
is the sheaf condition fork for `F ⋙ G`,
postcomposed with the inverse of the natural isomorphism `diagramCompPreservesLimits`.
-/
def mapConeFork :
    G.mapCone (fork.{v} F U) ≅
      (Cones.postcompose (diagramCompPreservesLimits G F U).inv).obj (fork (F ⋙ G) U) :=
  Cones.ext (Iso.refl _) fun j => by
    dsimp; simp [diagramCompPreservesLimits]; cases j <;> dsimp
    · rw [Iso.eq_comp_inv]
      -- Porting note : `ext` can't see `limit.hom_ext` applies here:
      -- See https://github.com/leanprover-community/mathlib4/issues/5229
      refine limit.hom_ext (fun j => ?_)
      -- Porting note : `attribute [local reducible]` doesn't work, this is its replacement
      simp [diagram, leftRes, rightRes, res]
    · rw [Iso.eq_comp_inv]
      -- Porting note : `ext` can't see `limit.hom_ext` applies here:
      -- See https://github.com/leanprover-community/mathlib4/issues/5229
      refine limit.hom_ext (fun j => ?_)
      -- Porting note : `attribute [local reducible]` doesn't work, this is its replacement
      dsimp [diagram, leftRes, rightRes, res]
      -- Porting note : there used to be a non-terminal `simp` for `squeeze_simp` did not work,
      -- however, `simp?` works fine now, but in both mathlib3 and mathlib4, two `simp`s are
      -- required to close goal
      simp only [Functor.map_comp, Category.assoc, map_lift_piComparison, limit.lift_π, Fan.mk_pt,
        Fan.mk_π_app, limit.lift_π_assoc, Discrete.functor_obj]
      simp only [limit.lift_π, Fan.mk_π_app, ← G.map_comp, limit.lift_π_assoc, Fan.mk_π_app]
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition.map_cone_fork TopCat.Presheaf.SheafCondition.mapConeFork

end SheafCondition

universe v u₁ u₂

open SheafCondition SheafConditionEqualizerProducts

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

variable (G : C ⥤ D)

variable [ReflectsIsomorphisms G]

variable [HasLimits C] [HasLimits D] [PreservesLimits G]

variable {X : TopCat.{v}} (F : Presheaf C X)

/-- If `G : C ⥤ D` is a functor which reflects isomorphisms and preserves limits
(we assume all limits exist in both `C` and `D`),
then checking the sheaf condition for a presheaf `F : presheaf C X`
is equivalent to checking the sheaf condition for `F ⋙ G`.

The important special case is when
`C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphisms.
Then to check the sheaf condition it suffices to check it on the underlying sheaf of types.

Another useful example is the forgetful functor `TopCommRing ⥤ Top`.

See <https://stacks.math.columbia.edu/tag/0073>.
In fact we prove a stronger version with arbitrary complete target category.
-/
theorem isSheaf_iff_isSheaf_comp : Presheaf.IsSheaf F ↔ Presheaf.IsSheaf (F ⋙ G) := by
  rw [Presheaf.isSheaf_iff_isSheafEqualizerProducts,
    Presheaf.isSheaf_iff_isSheafEqualizerProducts]
  constructor
  · intro S ι U
    -- We have that the sheaf condition fork for `F` is a limit fork,
    obtain ⟨t₁⟩ := S U
    -- and since `G` preserves limits, the image under `G` of this fork is a limit fork too.
    letI := preservesSmallestLimitsOfPreservesLimits G
    have t₂ := @PreservesLimit.preserves _ _ _ _ _ _ _ G _ _ t₁
    -- As we established above, that image is just the sheaf condition fork
    -- for `F ⋙ G` postcomposed with some natural isomorphism,
    have t₃ := IsLimit.ofIsoLimit t₂ (mapConeFork G F U)
    -- and as postcomposing by a natural isomorphism preserves limit cones,
    have t₄ := IsLimit.postcomposeInvEquiv _ _ t₃
    -- we have our desired conclusion.
    exact ⟨t₄⟩
  · intro S ι U
    refine' ⟨_⟩
    -- Let `f` be the universal morphism from `F.obj U` to the equalizer
    -- of the sheaf condition fork, whatever it is.
    -- Our goal is to show that this is an isomorphism.
    let f := equalizer.lift _ (w F U)
    -- If we can do that,
    suffices IsIso (G.map f) by
      skip
      -- we have that `f` itself is an isomorphism, since `G` reflects isomorphisms
      haveI : IsIso f := isIso_of_reflects_iso f G
      -- TODO package this up as a result elsewhere:
      apply IsLimit.ofIsoLimit (limit.isLimit _)
      apply Iso.symm
      fapply Cones.ext
      exact asIso f
      rintro ⟨_ | _⟩ <;>
        · simp
    · -- Returning to the task of showing that `G.map f` is an isomorphism,
      -- we note that `G.map f` is almost but not quite (see below) a morphism
      -- from the sheaf condition cone for `F ⋙ G` to the
      -- image under `G` of the equalizer cone for the sheaf condition diagram.
      let c := fork (F ⋙ G) U
      obtain ⟨hc⟩ := S U
      let d := G.mapCone (equalizer.fork (leftRes.{v} F U) (rightRes F U))
      letI := preservesSmallestLimitsOfPreservesLimits G
      have hd : IsLimit d := PreservesLimit.preserves (limit.isLimit _)
      -- Since both of these are limit cones
      -- (`c` by our hypothesis `S`, and `d` because `G` preserves limits),
      -- we hope to be able to conclude that `f` is an isomorphism.
      -- We say "not quite" above because `c` and `d` don't quite have the same shape:
      -- we need to postcompose by the natural isomorphism `diagramCompPreservesLimits`
      -- introduced above.
      let d' := (Cones.postcompose (diagramCompPreservesLimits G F U).hom).obj d
      have hd' : IsLimit d' :=
        (IsLimit.postcomposeHomEquiv (diagramCompPreservesLimits G F U : _) d).symm hd
      -- Now everything works: we verify that `f` really is a morphism between these cones:
      let f' : c ⟶ d' := Fork.mkHom (G.map f) (by
        dsimp only [diagramCompPreservesLimits, res]
        dsimp only [Fork.ι]
        -- Porting note : `ext` can't see `limit.hom_ext` applies here:
        -- See https://github.com/leanprover-community/mathlib4/issues/5229
        refine limit.hom_ext fun j => ?_
        dsimp
        simp only [Category.assoc, ← Functor.map_comp_assoc, equalizer.lift_ι,
          map_lift_piComparison_assoc]
        dsimp [res])
      -- conclude that it is an isomorphism,
      -- just because it's a morphism between two limit cones.
      haveI : IsIso f' := IsLimit.hom_isIso hc hd' f'
      -- A cone morphism is an isomorphism exactly if the morphism between the cone points is,
      -- so we're done!
      exact IsIso.of_iso ((Cones.forget _).mapIso (asIso f'))
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_sheaf_iff_is_sheaf_comp TopCat.Presheaf.isSheaf_iff_isSheaf_comp

/-!
As an example, we now have everything we need to check the sheaf condition
for a presheaf of commutative rings, merely by checking the sheaf condition
for the underlying sheaf of types.
```lean
example (X : TopCat) (F : Presheaf CommRingCat X)
    (h : Presheaf.IsSheaf (F ⋙ (forget CommRingCat))) :
    F.IsSheaf :=
(isSheaf_iff_isSheaf_comp (forget CommRingCat) F).mpr h
```
-/
example (X : TopCat) (F : Presheaf CommRingCat X)
    (h : Presheaf.IsSheaf (F ⋙ (forget CommRingCat))) :
    F.IsSheaf :=
(isSheaf_iff_isSheaf_comp (forget CommRingCat) F).mpr h

end Presheaf

end TopCat
