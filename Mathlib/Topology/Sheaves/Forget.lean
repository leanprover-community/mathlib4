/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module topology.sheaves.forget
! leanprover-community/mathlib commit 85d6221d32c37e68f05b2e42cde6cee658dae5e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathbin.Topology.Sheaves.SheafCondition.EqualizerProducts

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

attribute [local reducible] diagram left_res right_res

/-- When `G` preserves limits, the sheaf condition diagram for `F` composed with `G` is
naturally isomorphic to the sheaf condition diagram for `F ⋙ G`.
-/
def diagramCompPreservesLimits : diagram F U ⋙ G ≅ diagram.{v} (F ⋙ G) U :=
  by
  fapply nat_iso.of_components
  rintro ⟨j⟩
  exact preserves_product.iso _ _
  exact preserves_product.iso _ _
  rintro ⟨⟩ ⟨⟩ ⟨⟩
  · ext
    simp
    dsimp
    simp
  -- non-terminal `simp`, but `squeeze_simp` fails
  · ext
    simp only [limit.lift_π, functor.comp_map, map_lift_pi_comparison, fan.mk_π_app,
      preserves_product.iso_hom, parallel_pair_map_left, functor.map_comp, category.assoc]
    dsimp
    simp
  · ext
    simp only [limit.lift_π, functor.comp_map, parallel_pair_map_right, fan.mk_π_app,
      preserves_product.iso_hom, map_lift_pi_comparison, functor.map_comp, category.assoc]
    dsimp
    simp
  · ext
    simp
    dsimp
    simp
#align Top.presheaf.sheaf_condition.diagram_comp_preserves_limits TopCat.Presheaf.SheafCondition.diagramCompPreservesLimits

attribute [local reducible] res

/-- When `G` preserves limits, the image under `G` of the sheaf condition fork for `F`
is the sheaf condition fork for `F ⋙ G`,
postcomposed with the inverse of the natural isomorphism `diagram_comp_preserves_limits`.
-/
def mapConeFork :
    G.mapCone (fork.{v} F U) ≅
      (Cones.postcompose (diagramCompPreservesLimits G F U).inv).obj (fork (F ⋙ G) U) :=
  Cones.ext (Iso.refl _) fun j => by
    dsimp; simp [diagram_comp_preserves_limits]; cases j <;> dsimp
    · rw [iso.eq_comp_inv]
      ext
      simp
      dsimp
      simp
    · rw [iso.eq_comp_inv]
      ext
      simp
      -- non-terminal `simp`, but `squeeze_simp` fails
      dsimp
      simp only [limit.lift_π, fan.mk_π_app, ← G.map_comp, limit.lift_π_assoc, fan.mk_π_app]
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
theorem isSheaf_iff_isSheaf_comp : Presheaf.IsSheaf F ↔ Presheaf.IsSheaf (F ⋙ G) :=
  by
  rw [presheaf.is_sheaf_iff_is_sheaf_equalizer_products,
    presheaf.is_sheaf_iff_is_sheaf_equalizer_products]
  constructor
  · intro S ι U
    -- We have that the sheaf condition fork for `F` is a limit fork,
    obtain ⟨t₁⟩ := S U
    -- and since `G` preserves limits, the image under `G` of this fork is a limit fork too.
    letI := preserves_smallest_limits_of_preserves_limits G
    have t₂ := @preserves_limit.preserves _ _ _ _ _ _ _ G _ _ t₁
    -- As we established above, that image is just the sheaf condition fork
    -- for `F ⋙ G` postcomposed with some natural isomorphism,
    have t₃ := is_limit.of_iso_limit t₂ (map_cone_fork G F U)
    -- and as postcomposing by a natural isomorphism preserves limit cones,
    have t₄ := is_limit.postcompose_inv_equiv _ _ t₃
    -- we have our desired conclusion.
    exact ⟨t₄⟩
  · intro S ι U
    refine' ⟨_⟩
    -- Let `f` be the universal morphism from `F.obj U` to the equalizer
    -- of the sheaf condition fork, whatever it is.
    -- Our goal is to show that this is an isomorphism.
    let f := equalizer.lift _ (w F U)
    -- If we can do that,
    suffices is_iso (G.map f) by
      skip
      -- we have that `f` itself is an isomorphism, since `G` reflects isomorphisms
      haveI : is_iso f := is_iso_of_reflects_iso f G
      -- TODO package this up as a result elsewhere:
      apply is_limit.of_iso_limit (limit.is_limit _)
      apply iso.symm
      fapply cones.ext
      exact as_iso f
      rintro ⟨_ | _⟩ <;>
        · dsimp [f]
          simp
    · -- Returning to the task of shwoing that `G.map f` is an isomorphism,
      -- we note that `G.map f` is almost but not quite (see below) a morphism
      -- from the sheaf condition cone for `F ⋙ G` to the
      -- image under `G` of the equalizer cone for the sheaf condition diagram.
      let c := fork (F ⋙ G) U
      obtain ⟨hc⟩ := S U
      let d := G.map_cone (equalizer.fork (leftRes.{v} F U) (right_res F U))
      letI := preserves_smallest_limits_of_preserves_limits G
      have hd : is_limit d := preserves_limit.preserves (limit.is_limit _)
      -- Since both of these are limit cones
      -- (`c` by our hypothesis `S`, and `d` because `G` preserves limits),
      -- we hope to be able to conclude that `f` is an isomorphism.
      -- We say "not quite" above because `c` and `d` don't quite have the same shape:
      -- we need to postcompose by the natural isomorphism `diagram_comp_preserves_limits`
      -- introduced above.
      let d' := (cones.postcompose (diagram_comp_preserves_limits G F U).Hom).obj d
      have hd' : is_limit d' :=
        (is_limit.postcompose_hom_equiv (diagram_comp_preserves_limits G F U : _) d).symm hd
      -- Now everything works: we verify that `f` really is a morphism between these cones:
      let f' : c ⟶ d' :=
        fork.mk_hom (G.map f)
          (by
            dsimp only [c, d, d', f, diagram_comp_preserves_limits, res]
            dsimp only [fork.ι]
            ext1 j
            dsimp
            simp only [category.assoc, ← functor.map_comp_assoc, equalizer.lift_ι,
              map_lift_pi_comparison_assoc]
            dsimp [res]; simp)
      -- conclude that it is an isomorphism,
      -- just because it's a morphism between two limit cones.
      haveI : is_iso f' := is_limit.hom_is_iso hc hd' f'
      -- A cone morphism is an isomorphism exactly if the morphism between the cone points is,
      -- so we're done!
      exact is_iso.of_iso ((cones.forget _).mapIso (as_iso f'))
#align Top.presheaf.is_sheaf_iff_is_sheaf_comp TopCat.Presheaf.isSheaf_iff_isSheaf_comp

/-!
As an example, we now have everything we need to check the sheaf condition
for a presheaf of commutative rings, merely by checking the sheaf condition
for the underlying sheaf of types.
```
import algebra.category.Ring.limits
example (X : Top) (F : presheaf CommRing X) (h : presheaf.is_sheaf (F ⋙ (forget CommRing))) :
  F.is_sheaf :=
(is_sheaf_iff_is_sheaf_comp (forget CommRing) F).mpr h
```
-/


end Presheaf

end TopCat

