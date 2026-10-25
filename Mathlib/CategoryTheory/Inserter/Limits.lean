/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Inserter.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# (Co)limits of inserters

Let `F G : C ⥤ D` be a parallel pair of functors. In this file, we show that if `F` (resp. `G`)
preserves colimits (resp. limits) of shape `J` and if `C` has colimits (resp. limits) of shape `J`,
then `Inserter F G` has colimits (resp. limits) of shape `J` and the projection preserves them.

-/

@[expose] public section

namespace CategoryTheory.Inserter
open Limits

variable {C D J : Type*} [Category* C] [Category* D] [Category* J] {F G : C ⥤ D}

section Colimits

/-- Assuming `F` preserves the colimit of `K ⋙ proj F G` where `K` is a diagram valued in the
inserter category `Inserter F _`, a colimit cocone under `K ⋙ proj F _`
can be lifted to a cocone under `K`. -/
@[implicit_reducible, simps! pt_obj ι_app_hom]
noncomputable def coconeOfPreserves
    {K : J ⥤ Inserter F G} [Limits.PreservesColimit (K ⋙ proj F G) F]
    {c : Cocone (K ⋙ proj F G)} (hc : IsColimit c) :
    Cocone K where
  pt.obj := c.pt
  pt.hom :=
    letI p : Cocone ((K ⋙ proj F G) ⋙ F) := {
      pt := G.obj c.pt
      ι.app j := (K.obj j).hom ≫ G.map (c.ι.app j)
      ι.naturality {_ _} f := by grind [congr(G.map $(c.ι.naturality f)), Functor.const] }
    (isColimitOfPreserves F hc).desc p
  ι.app j := {
    hom := c.ι.app j
    comm := (isColimitOfPreserves F hc).fac .. }
  ι.naturality {_ _} f := by
    ext
    simpa using (c.ι.naturality f)

@[reassoc (attr := simp)]
lemma map_ι_coconeOfPreserves_pt_hom {K : J ⥤ Inserter F G} [Limits.PreservesColimit (K ⋙ proj F G) F]
    {c : Cocone (K ⋙ proj F G)} (hc : IsColimit c) (j : J) :
    F.map (c.ι.app j) ≫ (coconeOfPreserves hc).pt.hom = (K.obj j).hom ≫ G.map (c.ι.app j) :=
  ((coconeOfPreserves hc).ι.app j).comm

/-- Assuming `F` preserves the colimit of `K ⋙ proj F G` where `K` is a diagram valued in the
inserter category `Inserter F _`, `coconeOfPreserves` is a colimit cocone. -/
noncomputable def isColimitCoconeOfPreserves
    {K : J ⥤ Inserter F G} [Limits.PreservesColimit (K ⋙ proj F G) F]
    {c : Cocone (K ⋙ proj F G)} (hc : IsColimit c) :
    IsColimit (coconeOfPreserves hc) where
  desc s := {
    hom := hc.desc ((proj F G).mapCocone s)
    comm := by
      apply (isColimitOfPreserves F hc).hom_ext
      intro j
      simp [← Functor.map_comp_assoc, ← Functor.map_comp] }
  uniq s s' hj := by
    ext
    apply hc.hom_ext
    intro j
    simpa using congr($(hj j).hom)

instance hasColimit (K : J ⥤ Inserter F G) [HasColimit (K ⋙ proj F G)]
    [PreservesColimit (K ⋙ proj F G) F] : HasColimit K :=
  HasColimit.mk ⟨_, isColimitCoconeOfPreserves (colimit.isColimit _)⟩

instance hasColimitsOfShape [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [PreservesColimitsOfShape J F] : HasColimitsOfShape J (Inserter F G) where

instance preservesColimitsOfShape_proj [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [PreservesColimitsOfShape J F] : PreservesColimitsOfShape J (proj F G) where
  preservesColimit :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitCoconeOfPreserves (colimit.isColimit _))
      (colimit.isColimit _)

instance reflectsColimitsOfShape_proj [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [PreservesColimitsOfShape J F] : ReflectsColimitsOfShape J (proj F G) :=
  reflectsColimitsOfShape_of_reflectsIsomorphisms

end Colimits

section Limits

/-- Assuming `G` preserves the limit of `K ⋙ proj F G` where `K` is a diagram valued in the
inserter category `Inserter _ G`, a limit cone over `K ⋙ proj _ G`
can be lifted to a cone under `K`. -/
@[implicit_reducible, simps! pt_obj π_app_hom]
noncomputable def coneOfPreserves
    {K : J ⥤ Inserter F G} [Limits.PreservesLimit (K ⋙ proj F G) G]
    {c : Cone (K ⋙ proj F G)} (hc : IsLimit c) :
    Cone K where
  pt.obj := c.pt
  pt.hom :=
    letI p : Cone ((K ⋙ proj F G) ⋙ G) := {
      pt := F.obj c.pt
      π.app j := F.map (c.π.app j) ≫ (K.obj j).hom
      π.naturality {_ _} f := by grind [congr(F.map $(c.π.naturality f)), Functor.const] }
    (isLimitOfPreserves G hc).lift p
  π.app j := {
    hom := c.π.app j
    comm := by
      let p : Cone ((K ⋙ proj F G) ⋙ G) := {
        pt := F.obj c.pt
        π.app j := F.map (c.π.app j) ≫ (K.obj j).hom
        π.naturality {_ _} f := by grind [congr(F.map $(c.π.naturality f)), Functor.const] }
      exact ((isLimitOfPreserves G hc).fac p j).symm }
  π.naturality {_ _} f := by
    ext
    simpa using (c.π.naturality f)

@[reassoc (attr := simp)]
lemma coneOfPreserves_pt_hom_map_π_app {K : J ⥤ Inserter F G} [Limits.PreservesLimit (K ⋙ proj F G) G]
    {c : Cone (K ⋙ proj F G)} (hc : IsLimit c) (j : J) :
    (coneOfPreserves hc).pt.hom ≫ G.map (c.π.app j) = F.map (c.π.app j) ≫ (K.obj j).hom :=
  (coneOfPreserves hc).π.app j |>.comm.symm

/-- Assuming `G` preserves the limit of `K ⋙ proj F G` where `K` is a diagram valued in the
inserter category `Inserter _ G`, `coneOfPreserves` is a limit cone. -/
@[implicit_reducible]
noncomputable def isLimitConeOfPreserves
    {K : J ⥤ Inserter F G} [Limits.PreservesLimit (K ⋙ proj F G) G]
    {c : Cone (K ⋙ proj F G)} (hc : IsLimit c) :
    IsLimit (coneOfPreserves hc) where
  lift s := {
    hom := hc.lift ((proj F G).mapCone s)
    comm := by
      apply (isLimitOfPreserves G hc).hom_ext
      intro j
      simp [← Functor.map_comp_assoc, ← Functor.map_comp] }
  uniq s s' hj := by
    ext
    apply hc.hom_ext
    intro j
    simpa using congr($(hj j).hom)

instance hasLimit (K : J ⥤ Inserter F G) [HasLimit (K ⋙ proj F G)]
    [PreservesLimit (K ⋙ proj F G) G] : HasLimit K :=
  HasLimit.mk ⟨_, isLimitConeOfPreserves (limit.isLimit _)⟩

instance hasLimitsOfShape [HasLimitsOfShape J C] [HasLimitsOfShape J D]
    [PreservesLimitsOfShape J G] : HasLimitsOfShape J (Inserter F G) where

instance preservesLimitsOfShape_proj [HasLimitsOfShape J C] [HasLimitsOfShape J D]
    [PreservesLimitsOfShape J G] : PreservesLimitsOfShape J (proj F G) where
  preservesLimit :=
    preservesLimit_of_preserves_limit_cone
      (isLimitConeOfPreserves (limit.isLimit _)) (limit.isLimit _)

instance reflectsLimitsOfShape_proj [HasLimitsOfShape J C] [HasLimitsOfShape J D]
    [PreservesLimitsOfShape J G] : ReflectsLimitsOfShape J (proj F G) :=
  reflectsLimitsOfShape_of_reflectsIsomorphisms

end Limits

end Inserter

end CategoryTheory
