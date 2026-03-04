/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!

In this file, we show that an adjunction `G ⊣ F` induces an adjunction between
categories of sheaves. We also show that `G` preserves sheafification.

-/

@[expose] public section


namespace CategoryTheory

open GrothendieckTopology Limits Opposite Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type*} [Category* E]
variable {F : D ⥤ E} {G : E ⥤ D}

/-- The forgetful functor from `Sheaf J D` to sheaves of types, for a concrete category `D`
whose forgetful functor preserves the correct limits. -/
abbrev sheafForget {FD : D → D → Type*} {CD : D → Type*}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    [HasSheafCompose J (forget D)] : Sheaf J D ⥤ Sheaf J (Type _) :=
  sheafCompose J (forget D)

namespace Sheaf

noncomputable section

/-- An adjunction `adj : G ⊣ F` with `F : D ⥤ E` and `G : E ⥤ D` induces an adjunction
between `Sheaf J D` and `Sheaf J E`, in contexts where one can sheafify `D`-valued presheaves,
and postcomposing with `F` preserves the property of being a sheaf. -/
def adjunction [HasWeakSheafify J D] [HasSheafCompose J F] (adj : G ⊣ F) :
    composeAndSheafify J G ⊣ sheafCompose J F :=
  Adjunction.restrictFullyFaithful ((adj.whiskerRight Cᵒᵖ).comp (sheafificationAdjunction J D))
    (fullyFaithfulSheafToPresheaf J E) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma adjunction_unit_app_val [HasWeakSheafify J D] [HasSheafCompose J F] (adj : G ⊣ F)
    (X : Sheaf J E) : ((adjunction J adj).unit.app X).hom =
      (adj.whiskerRight Cᵒᵖ).unit.app _ ≫ whiskerRight (toSheafify J (X.obj ⋙ G)) F := by
  change (sheafToPresheaf _ _).map ((adjunction J adj).unit.app X) = _
  simp only [Functor.id_obj, Functor.comp_obj, whiskeringRight_obj_obj, adjunction,
    Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.comp_unit_app,
    sheafificationAdjunction_unit_app, whiskeringRight_obj_map, Iso.refl_hom, NatTrans.id_app,
    Functor.comp_map, Functor.map_id, whiskerRight_id', Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma adjunction_counit_app_val [HasWeakSheafify J D] [HasSheafCompose J F] (adj : G ⊣ F)
    (Y : Sheaf J D) : ((adjunction J adj).counit.app Y).hom =
      sheafifyLift J (((adj.whiskerRight Cᵒᵖ).counit.app Y.obj)) Y.property :=
  ((sheafToPresheaf _ _).congr_map
    (Adjunction.map_restrictFullyFaithful_counit_app _ _ (Functor.FullyFaithful.id _)
      (L := composeAndSheafify J G) (R := sheafCompose J F) _ _ Y)).trans (by
        dsimp
        simp only [Adjunction.comp_counit_app, ObjectProperty.ι_obj, comp_obj,
          whiskeringRight_obj_obj, id_obj, ObjectProperty.FullSubcategory.comp_hom,
          sheafificationAdjunction_counit_app_val, sheafifyMap_sheafifyLift, Category.comp_id,
          Category.id_comp]
        congr 1
        cat_disch)

instance [HasWeakSheafify J D] [F.IsRightAdjoint] : (sheafCompose J F).IsRightAdjoint :=
  (adjunction J (Adjunction.ofIsRightAdjoint F)).isRightAdjoint

instance [HasWeakSheafify J D] [G.IsLeftAdjoint] : (composeAndSheafify J G).IsLeftAdjoint :=
  (adjunction J (Adjunction.ofIsLeftAdjoint G)).isLeftAdjoint

set_option backward.isDefEq.respectTransparency false in
lemma preservesSheafification_of_adjunction (adj : G ⊣ F) :
    J.PreservesSheafification G where
  le P Q f hf := by
    have := adj.isRightAdjoint
    rw [MorphismProperty.inverseImage_iff]
    dsimp
    intro R hR
    rw [← ((adj.whiskerRight Cᵒᵖ).homEquiv P R).comp_bijective]
    convert (((adj.whiskerRight Cᵒᵖ).homEquiv Q R).trans
      (hf.homEquiv (R ⋙ F) ((sheafCompose J F).obj ⟨R, hR⟩).property)).bijective
    ext g X
    -- The rest of this proof was
    -- `dsimp [Adjunction.whiskerRight, Adjunction.mkOfUnitCounit]; simp` before https://github.com/leanprover-community/mathlib4/pull/16317.
    dsimp
    rw [← NatTrans.comp_app]
    congr
    exact Adjunction.homEquiv_naturality_left _ _ _

instance [G.IsLeftAdjoint] : J.PreservesSheafification G :=
  preservesSheafification_of_adjunction J (Adjunction.ofIsLeftAdjoint G)

section ForgetToType

variable [HasWeakSheafify J D] {FD : D → D → Type*} {CD : D → Type (max u₁ v₁)}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD] [HasSheafCompose J (forget D)]

example [(forget D).IsRightAdjoint] :
    (sheafForget.{_, _, _, _, _, max u₁ v₁} (D := D) J).IsRightAdjoint := by infer_instance

end ForgetToType

end

end Sheaf

end CategoryTheory
