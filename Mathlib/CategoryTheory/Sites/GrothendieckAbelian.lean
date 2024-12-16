/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Generator.Sheaf
import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Categories of sheaves are Grothendieck abelian

If `J` is a Grothendieck topology on a small category `C : Type v`,
and `A : Type u` (with `Category.{v} A`) is a Grothendieck abelian category,
then `Sheaf J A` is a Grothendieck abelian category.

-/

universe v'' v' v u'' u' u

namespace CategoryTheory

open Limits

-- this should be moved
namespace Adjunction

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  {K : Type u''} [Category.{v''} K]
  [G.Faithful] [G.Full]

namespace colimIso

variable {P : K ⥤ D} (c : Cocone (P ⋙ G)) (hc : IsColimit c)

/-- A cocone for `P : K ⥤ D` deduced from a cocone for `P ⋙ G` when `adj : F ⊣ G`
is an adjunction such that `G : D ⥤ C` is fully faithful. -/
@[simps pt]
noncomputable def cocone : Cocone P where
  pt := F.obj c.pt
  ι :=
    { app k := G.preimage (c.ι.app k ≫ adj.unit.app _)
      naturality k k' f := by
        apply G.map_injective
        have := c.w f
        dsimp at this
        simp [reassoc_of% this]}

@[simp]
lemma map_cocone_ι_app (k : K) :
    G.map ((cocone adj c).ι.app k) = c.ι.app k ≫ adj.unit.app _ := by
  simp [cocone]

namespace isColimitCocone

variable {c}

/-- Auxiliary definition for `Adjunction.isColimitCocone`. -/
noncomputable def desc (s : Cocone P) : F.obj c.pt ⟶ s.pt :=
  (adj.homEquiv _ _).symm (hc.desc (G.mapCocone s))

@[reassoc]
lemma fac (s : Cocone P) (k : K) :
    (cocone adj c).ι.app k ≫ isColimitCocone.desc adj hc s = s.ι.app k :=
  G.map_injective (by simp [desc, homEquiv_counit])

include hc in
lemma uniq {s : Cocone P} {f g : F.obj c.pt ⟶ s.pt}
    (h : ∀ (k : K), (cocone adj c).ι.app k ≫ f = (cocone adj c).ι.app k ≫ g) : f = g :=
  (adj.homEquiv _ _).injective
    (hc.hom_ext (fun k ↦ by simpa [homEquiv_unit] using G.congr_map (h k)))

end isColimitCocone

/-- Given an adjunction `adj : F ⊣ G` such that `G : D ⥤ C` is fully faithful,
this is a construction of a colimit cocone for `P : K ⥤ D` from a colimit
cocone for `P ⋙ G`. -/
noncomputable def isColimitCocone : IsColimit (cocone adj c) where
  desc s := isColimitCocone.desc adj hc s
  fac s k := isColimitCocone.fac adj hc s k
  uniq s m hm := isColimitCocone.uniq adj hc (fun _ ↦ by rw [isColimitCocone.fac, hm])

end colimIso

variable [HasColimitsOfShape K C] [HasColimitsOfShape K D]

/-- If `adj : F ⊣ G` is an adjuncton such that `G` is fully faithful, this is the
isomorphism between the colimit of `P : K ⥤ D` and the image by `F` of
the colimit of `P ⋙ G`. -/
noncomputable def colimIsoObj (P : K ⥤ D) : colimit P ≅ F.obj (colimit (P ⋙ G)) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit P)
      (colimIso.isColimitCocone adj _ (colimit.isColimit (P ⋙ G)))

@[reassoc]
lemma ι_colimIsoObj_hom (P : K ⥤ D) (k : K) :
    colimit.ι P k ≫ (colimIsoObj adj P).hom =
      (colimIso.cocone adj (colimit.cocone (P ⋙ G))).ι.app k :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _

variable (K)

/-- If `adj : F ⊣ G` is an adjuncton such that `G` is fully faithful, this is the
natural isomorphism between the colimit of `P : K ⥤ D` and the image by `F` of
the colimit of `P ⋙ G`. -/
noncomputable def colimIso : colim (J := K) (C := D) ≅
    (whiskeringRight _ _ _).obj G ⋙ colim (J := K) (C := C) ⋙ F :=
  NatIso.ofComponents adj.colimIsoObj (fun {P Q} f ↦ by
    dsimp
    ext k
    rw [ι_colimMap_assoc, ι_colimIsoObj_hom, ι_colimIsoObj_hom_assoc]
    apply G.map_injective
    simp)

include adj in
lemma hasExactColimitsOfShape [HasExactColimitsOfShape K C] [Abelian D]
    [F.PreservesMonomorphisms] :
    HasExactColimitsOfShape K D := by
  suffices (colim (J := K) (C := D)).PreservesMonomorphisms by
    apply hasExactColimitsOfShape_of_preservesMono
  have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
  apply Functor.preservesMonomorphisms.of_iso (adj.colimIso K).symm

end Adjunction

namespace Sheaf

-- this should be moved to Abelian.GrothendieckAxioms.Sheaf

instance hasExactColimitsOfShape
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Type u') [Category.{v'} A] [Abelian A]
    (K : Type u'') [Category.{v''} K] [HasSheafify J A] [HasColimitsOfShape K A]
    [HasExactColimitsOfShape K A] :
    HasExactColimitsOfShape K (Sheaf J A) :=
  (sheafificationAdjunction J A).hasExactColimitsOfShape K

instance hasFilteredColimitsOfSize {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Type u') [Category.{v'} A] [HasSheafify J A]
    [HasFilteredColimitsOfSize.{v'', u''} A] :
    HasFilteredColimitsOfSize.{v'', u''} (Sheaf J A) where
  HasColimitsOfShape K := by infer_instance

instance ab5ofSize {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Type u') [Category.{v'} A] [Abelian A] [HasSheafify J A]
    [HasFilteredColimitsOfSize.{v'', u''} A] [AB5OfSize.{v'', u''} A] :
    AB5OfSize.{v'', u''} (Sheaf J A) where
  ofShape K _ _ := by infer_instance

instance {C : Type v} [SmallCategory C] (J : GrothendieckTopology C) (A : Type u)
    [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasSheafify J A] : IsGrothendieckAbelian.{v} (Sheaf J A) where

end Sheaf

end CategoryTheory
