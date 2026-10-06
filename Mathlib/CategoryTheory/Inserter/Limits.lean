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
# Colimits in inserters

Let `F G : C ⥤ D` be a parallel pair of functors of categories. In this file,
we show that if `F` and `G` preserves colimits of shape `J` and if `C` has colimits of
shape `J`, then `Inserter F G` has colimits of shape `J` and the projection preserves them.

# TODO: dualise to limits
-/

@[expose] public section

namespace CategoryTheory.Inserter
open Limits

variable {C D J : Type*} [Category* C] [Category* D] [Category* J] {F G : C ⥤ D}

/-- Assuming `F` preserves the colimit of `K ⋙ proj F G` where `K` is a diagram valued in the
inserter category `Inserter F _`, a colimit cocone under `K ⋙ proj F _`
can be lifted to a cocone under `K`. -/
@[implicit_reducible, simps]
noncomputable def coconeOfPreserves
    {K : J ⥤ Inserter F G} [Limits.PreservesColimit (K ⋙ proj F G) F]
    (c : Cocone (K ⋙ proj F G)) (hc : IsColimit c) :
    Cocone K where
  pt.obj := c.pt
  pt.hom :=
    letI p : Cocone ((K ⋙ proj F G) ⋙ F) := {
      pt := G.obj c.pt
      ι.app j := (K.obj j).hom ≫ G.map (c.ι.app j)
      ι.naturality {_ _} f := by
        have := congr(G.map $(c.ι.naturality f))
        dsimp at this ⊢
        grind }
    (isColimitOfPreserves F hc).desc p
  ι.app j := {
    hom := c.ι.app j
    comm := by
      simp only [Functor.comp_obj, proj_obj, Functor.const_obj_obj]
      exact (isColimitOfPreserves F hc).fac .. }
  ι.naturality {_ _} f := by
    ext
    simpa using (c.ι.naturality f)

/-- Assuming `F` preserves the colimit of `K ⋙ proj F G` where `K` is a diagram valued in the
inserter category `Inserter F _`, `coconeOfPreserves` is a colimit cocone. -/
@[implicit_reducible]
noncomputable def isColimitCoconeOfPreserves
    {K : J ⥤ Inserter F G} [Limits.PreservesColimit (K ⋙ proj F G) F]
    (c : Cocone (K ⋙ proj F G)) (hc : IsColimit c) :
    IsColimit (coconeOfPreserves c hc) where
  desc s := {
    hom := hc.desc ((proj F G).mapCocone s)
    comm := by
      apply (isColimitOfPreserves F hc).hom_ext
      intro j
      dsimp
      simp only [← Functor.map_comp_assoc, IsColimit.fac, Functor.mapCocone_pt, proj_obj,
        Functor.mapCocone_ι_app, proj_map, comm]
      rw [← F.mapCocone_ι_app, (isColimitOfPreserves F hc).fac_assoc]
      simp [← Functor.map_comp] }
  fac s j := by cat_disch
  uniq s s' hj := by
    ext
    apply hc.hom_ext
    intro j
    have := congr($(hj j).hom)
    simpa [coconeOfPreserves]

instance hasColimit (K : J ⥤ Inserter F G) [HasColimit (K ⋙ proj F G)]
    [PreservesColimit (K ⋙ proj F G) F] : HasColimit K :=
  HasColimit.mk ⟨_, isColimitCoconeOfPreserves _ (colimit.isColimit _)⟩

instance hasColimitsOfShape [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [PreservesColimitsOfShape J F] : HasColimitsOfShape J (Inserter F G) where

instance preservesColimitsOfShape_proj [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [PreservesColimitsOfShape J F] : PreservesColimitsOfShape J (proj F G) where
  preservesColimit :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitCoconeOfPreserves _ (colimit.isColimit _))
      (colimit.isColimit _)

instance reflectsColimitsOfShape_proj [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [PreservesColimitsOfShape J F] : ReflectsColimitsOfShape J (proj F G) :=
  reflectsColimitsOfShape_of_reflectsIsomorphisms

end Inserter

end CategoryTheory

