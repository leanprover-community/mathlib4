/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Sites.Sheafification

#align_import category_theory.sites.limits from "leanprover-community/mathlib"@"95e83ced9542828815f53a1096a4d373c1b08a77"

/-!

# Limits and colimits of sheaves

## Limits

We prove that the forgetful functor from `Sheaf J D` to presheaves creates limits.
If the target category `D` has limits (of a certain shape),
this then implies that `Sheaf J D` has limits of the same shape and that the forgetful
functor preserves these limits.

## Colimits

Given a diagram `F : K ⥤ Sheaf J D` of sheaves, and a colimit cocone on the level of presheaves,
we show that the cocone obtained by sheafifying the cocone point is a colimit cocone of sheaves.

This allows us to show that `Sheaf J D` has colimits (of a certain shape) as soon as `D` does.

-/


namespace CategoryTheory

namespace Sheaf

open CategoryTheory.Limits

open Opposite

section Limits

universe w v u z

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable {D : Type w} [Category.{max v u} D]

variable {K : Type z} [SmallCategory K]

noncomputable section

section

/-- An auxiliary definition to be used below.

Whenever `E` is a cone of shape `K` of sheaves, and `S` is the multifork associated to a
covering `W` of an object `X`, with respect to the cone point `E.X`, this provides a cone of
shape `K` of objects in `D`, with cone point `S.X`.

See `isLimitMultiforkOfIsLimit` for more on how this definition is used.
-/
def multiforkEvaluationCone (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D)) (X : C)
    (W : J.Cover X) (S : Multifork (W.index E.pt)) :
    Cone (F ⋙ sheafToPresheaf J D ⋙ (evaluation Cᵒᵖ D).obj (op X)) where
  pt := S.pt
  π :=
    { app := fun k => (Presheaf.isLimitOfIsSheaf J (F.obj k).1 W (F.obj k).2).lift <|
        Multifork.ofι _ S.pt (fun i => S.ι i ≫ (E.π.app k).app (op i.Y))
          (by
            intro i
            -- ⊢ (fun i => Multifork.ι S i ≫ NatTrans.app (NatTrans.app E.π k) (op i.Y)) (Mul …
            simp only [Category.assoc]
            -- ⊢ Multifork.ι S (MulticospanIndex.fstTo (GrothendieckTopology.Cover.index W (F …
            erw [← (E.π.app k).naturality, ← (E.π.app k).naturality]
            -- ⊢ Multifork.ι S (MulticospanIndex.fstTo (GrothendieckTopology.Cover.index W (F …
            dsimp
            -- ⊢ Multifork.ι S (MulticospanIndex.fstTo (GrothendieckTopology.Cover.index W (F …
            simp only [← Category.assoc]
            -- ⊢ (Multifork.ι S (MulticospanIndex.fstTo (GrothendieckTopology.Cover.index W ( …
            congr 1
            -- ⊢ Multifork.ι S (MulticospanIndex.fstTo (GrothendieckTopology.Cover.index W (F …
            apply S.condition)
            -- 🎉 no goals
      naturality := by
        intro i j f
        -- ⊢ ((Functor.const K).obj S.pt).map f ≫ (fun k => IsLimit.lift (Presheaf.isLimi …
        dsimp [Presheaf.isLimitOfIsSheaf]
        -- ⊢ 𝟙 S.pt ≫ Presheaf.IsSheaf.amalgamate (_ : Presheaf.IsSheaf J (F.obj j).val)  …
        rw [Category.id_comp]
        -- ⊢ Presheaf.IsSheaf.amalgamate (_ : Presheaf.IsSheaf J (F.obj j).val) W (fun I  …
        apply Presheaf.IsSheaf.hom_ext (F.obj j).2 W
        -- ⊢ ∀ (I : GrothendieckTopology.Cover.Arrow W), Presheaf.IsSheaf.amalgamate (_ : …
        intro ii
        -- ⊢ Presheaf.IsSheaf.amalgamate (_ : Presheaf.IsSheaf J (F.obj j).val) W (fun I  …
        rw [Presheaf.IsSheaf.amalgamate_map, Category.assoc, ← (F.map f).val.naturality, ←
          Category.assoc, Presheaf.IsSheaf.amalgamate_map]
        dsimp [Multifork.ofι]
        -- ⊢ Multifork.ι
        erw [Category.assoc, ← E.w f]
        -- ⊢ Multifork.ι
        aesop_cat }
        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.multifork_evaluation_cone CategoryTheory.Sheaf.multiforkEvaluationCone

variable [HasLimitsOfShape K D]

/-- If `E` is a cone of shape `K` of sheaves, which is a limit on the level of presheaves,
this definition shows that the limit presheaf satisfies the multifork variant of the sheaf
condition, at a given covering `W`.

This is used below in `isSheaf_of_isLimit` to show that the limit presheaf is indeed a sheaf.
-/
def isLimitMultiforkOfIsLimit (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D))
    (hE : IsLimit E) (X : C) (W : J.Cover X) : IsLimit (W.multifork E.pt) :=
  Multifork.IsLimit.mk _
    (fun S => (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).lift <|
      multiforkEvaluationCone F E X W S)
    (by
      intro S i
      -- ⊢ (fun S => IsLimit.lift (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) h …
      apply (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op i.Y)) hE).hom_ext
      -- ⊢ ∀ (j : K), ((fun S => IsLimit.lift (isLimitOfPreserves ((evaluation Cᵒᵖ D).o …
      intro k
      -- ⊢ ((fun S => IsLimit.lift (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X))  …
      dsimp [Multifork.ofι]
      -- ⊢ (IsLimit.lift (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE) (multi …
      erw [Category.assoc, (E.π.app k).naturality]
      -- ⊢ IsLimit.lift (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE) (multif …
      dsimp
      -- ⊢ IsLimit.lift (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE) (multif …
      rw [← Category.assoc]
      -- ⊢ (IsLimit.lift (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE) (multi …
      erw [(isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac
        (multiforkEvaluationCone F E X W S)]
      dsimp [multiforkEvaluationCone, Presheaf.isLimitOfIsSheaf]
      -- ⊢ Presheaf.IsSheaf.amalgamate (_ : Presheaf.IsSheaf J (F.obj k).val) W (fun I  …
      erw [Presheaf.IsSheaf.amalgamate_map]
      -- ⊢ Multifork.ι (Multifork.ofι (GrothendieckTopology.Cover.index W (F.obj k).val …
      rfl)
      -- 🎉 no goals
    (by
      intro S m hm
      -- ⊢ m = (fun S => IsLimit.lift (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X …
      apply (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).hom_ext
      -- ⊢ ∀ (j : K), m ≫ NatTrans.app (((evaluation Cᵒᵖ D).obj (op X)).mapCone E).π j  …
      intro k
      -- ⊢ m ≫ NatTrans.app (((evaluation Cᵒᵖ D).obj (op X)).mapCone E).π k = (fun S => …
      dsimp
      -- ⊢ m ≫ NatTrans.app (NatTrans.app E.π k) (op X) = IsLimit.lift (isLimitOfPreser …
      erw [(isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac]
      -- ⊢ m ≫ NatTrans.app (NatTrans.app E.π k) (op X) = NatTrans.app (multiforkEvalua …
      apply Presheaf.IsSheaf.hom_ext (F.obj k).2 W
      -- ⊢ ∀ (I : GrothendieckTopology.Cover.Arrow W), (m ≫ NatTrans.app (NatTrans.app  …
      intro i
      -- ⊢ (m ≫ NatTrans.app (NatTrans.app E.π k) (op X)) ≫ (F.obj k).val.map i.f.op =  …
      dsimp only [multiforkEvaluationCone, Presheaf.isLimitOfIsSheaf]
      -- ⊢ (m ≫ NatTrans.app (NatTrans.app E.π k) (op X)) ≫ (F.obj k).val.map i.f.op =  …
      rw [(F.obj k).cond.amalgamate_map]
      -- ⊢ (m ≫ NatTrans.app (NatTrans.app E.π k) (op X)) ≫ (F.obj k).val.map i.f.op =  …
      dsimp [Multifork.ofι]
      -- ⊢ (m ≫ NatTrans.app (NatTrans.app E.π k) (op X)) ≫ (F.obj k).val.map i.f.op =
      change _ = S.ι i ≫ _
      -- ⊢ (m ≫ NatTrans.app (NatTrans.app E.π k) (op X)) ≫ (F.obj k).val.map i.f.op =  …
      erw [← hm, Category.assoc, ← (E.π.app k).naturality, Category.assoc]
      -- ⊢ m ≫ (((Functor.const K).obj E.pt).obj k).map i.f.op ≫ NatTrans.app (NatTrans …
      rfl)
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.is_limit_multifork_of_is_limit CategoryTheory.Sheaf.isLimitMultiforkOfIsLimit

/-- If `E` is a cone which is a limit on the level of presheaves,
then the limit presheaf is again a sheaf.

This is used to show that the forgetful functor from sheaves to presheaves creates limits.
-/
theorem isSheaf_of_isLimit (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D))
    (hE : IsLimit E) : Presheaf.IsSheaf J E.pt := by
  rw [Presheaf.isSheaf_iff_multifork]
  -- ⊢ ∀ (X : C) (S : GrothendieckTopology.Cover J X), Nonempty (IsLimit (Grothendi …
  intro X S
  -- ⊢ Nonempty (IsLimit (GrothendieckTopology.Cover.multifork S E.pt))
  exact ⟨isLimitMultiforkOfIsLimit _ _ hE _ _⟩
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.is_sheaf_of_is_limit CategoryTheory.Sheaf.isSheaf_of_isLimit

instance (F : K ⥤ Sheaf J D) : CreatesLimit F (sheafToPresheaf J D) :=
  createsLimitOfReflectsIso fun E hE =>
    { liftedCone := ⟨⟨E.pt, isSheaf_of_isLimit _ _ hE⟩,
        ⟨fun t => ⟨E.π.app _⟩, fun u v e => Sheaf.Hom.ext _ _ <| E.π.naturality _⟩⟩
      validLift := Cones.ext (eqToIso rfl) fun j => by
        dsimp
        -- ⊢ NatTrans.app E.π j = 𝟙 E.pt ≫ NatTrans.app E.π j
        simp
        -- 🎉 no goals
      makesLimit :=
        { lift := fun S => ⟨hE.lift ((sheafToPresheaf J D).mapCone S)⟩
          fac := fun S j => by
            ext1
            -- ⊢ ((fun S => { val := IsLimit.lift hE ((sheafToPresheaf J D).mapCone S) }) S ≫ …
            apply hE.fac ((sheafToPresheaf J D).mapCone S) j
            -- 🎉 no goals
          uniq := fun S m hm => by
            ext1
            -- ⊢ m.val = ((fun S => { val := IsLimit.lift hE ((sheafToPresheaf J D).mapCone S …
            exact hE.uniq ((sheafToPresheaf J D).mapCone S) m.val fun j =>
              congr_arg Hom.val (hm j) } }

instance createsLimitsOfShape : CreatesLimitsOfShape K (sheafToPresheaf J D) where

instance : HasLimitsOfShape K (Sheaf J D) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J D)

end

instance createsLimits [HasLimits D] : CreatesLimits (sheafToPresheaf J D) :=
  ⟨createsLimitsOfShape⟩

instance [HasLimits D] : HasLimits (Sheaf J D) :=
  hasLimits_of_hasLimits_createsLimits (sheafToPresheaf J D)

end

end Limits

section Colimits

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable {D : Type w} [Category.{max v u} D]

variable {K : Type max v u} [SmallCategory K]

-- Now we need a handful of instances to obtain sheafification...
variable [ConcreteCategory.{max v u} D]

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]

variable [PreservesLimits (forget D)]

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]

variable [ReflectsIsomorphisms (forget D)]

/-- Construct a cocone by sheafifying a cocone point of a cocone `E` of presheaves
over a functor which factors through sheaves.
In `isColimitSheafifyCocone`, we show that this is a colimit cocone when `E` is a colimit. -/
@[simps]
noncomputable def sheafifyCocone {F : K ⥤ Sheaf J D}
    (E : Cocone (F ⋙ sheafToPresheaf J D)) : Cocone F where
  pt := ⟨J.sheafify E.pt, GrothendieckTopology.Plus.isSheaf_plus_plus _ _⟩
  ι :=
    { app := fun k => ⟨E.ι.app k ≫ J.toSheafify E.pt⟩
      naturality := fun i j f => by
        ext1
        -- ⊢ (F.map f ≫ (fun k => { val := NatTrans.app E.ι k ≫ GrothendieckTopology.toSh …
        dsimp
        -- ⊢ (F.map f).val ≫ NatTrans.app E.ι j ≫ GrothendieckTopology.toSheafify J E.pt  …
        erw [Category.comp_id, ← Category.assoc, E.w f] }
        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.sheafify_cocone CategoryTheory.Sheaf.sheafifyCocone

/-- If `E` is a colimit cocone of presheaves, over a diagram factoring through sheaves,
then `sheafifyCocone E` is a colimit cocone. -/
@[simps]
noncomputable def isColimitSheafifyCocone {F : K ⥤ Sheaf J D}
    (E : Cocone (F ⋙ sheafToPresheaf J D)) (hE : IsColimit E) : IsColimit (sheafifyCocone E) where
  desc S := ⟨J.sheafifyLift (hE.desc ((sheafToPresheaf J D).mapCocone S)) S.pt.2⟩
  fac := by
    intro S j
    -- ⊢ NatTrans.app (sheafifyCocone E).ι j ≫ (fun S => { val := GrothendieckTopolog …
    ext1
    -- ⊢ (NatTrans.app (sheafifyCocone E).ι j ≫ (fun S => { val := GrothendieckTopolo …
    dsimp [sheafifyCocone]
    -- ⊢ (NatTrans.app E.ι j ≫ GrothendieckTopology.toSheafify J E.pt) ≫ Grothendieck …
    erw [Category.assoc, J.toSheafify_sheafifyLift, hE.fac]
    -- ⊢ NatTrans.app ((sheafToPresheaf J D).mapCocone S).ι j = (NatTrans.app S.ι j). …
    rfl
    -- 🎉 no goals
  uniq := by
    intro S m hm
    -- ⊢ m = (fun S => { val := GrothendieckTopology.sheafifyLift J (IsColimit.desc h …
    ext1
    -- ⊢ m.val = ((fun S => { val := GrothendieckTopology.sheafifyLift J (IsColimit.d …
    apply J.sheafifyLift_unique
    -- ⊢ GrothendieckTopology.toSheafify J E.pt ≫ m.val = IsColimit.desc hE ((sheafTo …
    apply hE.uniq ((sheafToPresheaf J D).mapCocone S)
    -- ⊢ ∀ (j : K), NatTrans.app E.ι j ≫ GrothendieckTopology.toSheafify J E.pt ≫ m.v …
    intro j
    -- ⊢ NatTrans.app E.ι j ≫ GrothendieckTopology.toSheafify J E.pt ≫ m.val = NatTra …
    dsimp
    -- ⊢ NatTrans.app E.ι j ≫ GrothendieckTopology.toSheafify J E.pt ≫ m.val = (NatTr …
    simp only [← Category.assoc, ← hm] -- Porting note: was `simpa only [...]`
    -- ⊢ (NatTrans.app E.ι j ≫ GrothendieckTopology.toSheafify J E.pt) ≫ m.val = (Nat …
    rfl
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.is_colimit_sheafify_cocone CategoryTheory.Sheaf.isColimitSheafifyCocone

instance [HasColimitsOfShape K D] : HasColimitsOfShape K (Sheaf J D) :=
  ⟨fun _ => HasColimit.mk
    ⟨sheafifyCocone (colimit.cocone _), isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

instance [HasColimits D] : HasColimits (Sheaf J D) :=
  ⟨inferInstance⟩

end Colimits

end Sheaf

end CategoryTheory
