/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.ConcreteCategory.Forget

/-!

In this file we construct the functor `Sheaf J A ⥤ Sheaf J B` between sheaf categories
obtained by composition with a functor `F : A ⥤ B`.

In order for the sheaf condition to be preserved, `F` must preserve the correct limits.
The lemma `Presheaf.IsSheaf.comp` says that composition with such an `F` indeed preserves the
sheaf condition.

The functor between sheaf categories is called `sheafCompose J F`.
Given a natural transformation `η : F ⟶ G`, we obtain a natural transformation
`sheafCompose J F ⟶ sheafCompose J G`, which we call `sheafCompose_map J η`.

-/

@[expose] public section


namespace CategoryTheory

open CategoryTheory.Limits Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable {B : Type u₃} [Category.{v₃} B]
variable (J : GrothendieckTopology C)
variable {U : C} (R : Presieve U)
variable (F G H : A ⥤ B) (η : F ⟶ G) (γ : G ⟶ H)

/-- Describes the property of a functor to "preserve sheaves". -/
class GrothendieckTopology.HasSheafCompose : Prop where
  /-- For every sheaf `P`, `P ⋙ F` is a sheaf. -/
  isSheaf (P : Cᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf J P) : Presheaf.IsSheaf J (P ⋙ F)

variable [J.HasSheafCompose F] [J.HasSheafCompose G] [J.HasSheafCompose H]

/-- Composing a functor which `HasSheafCompose`, yields a functor between sheaf categories. -/
@[simps! obj_obj map_hom]
def sheafCompose : Sheaf J A ⥤ Sheaf J B :=
  ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj F)
      (fun P ↦ GrothendieckTopology.HasSheafCompose.isSheaf _ P.property)

instance [F.Faithful] : (sheafCompose J F ⋙ sheafToPresheaf _ _).Faithful :=
  show (sheafToPresheaf _ _ ⋙ (whiskeringRight Cᵒᵖ A B).obj F).Faithful from inferInstance

instance [F.Faithful] [F.Full] : (sheafCompose J F ⋙ sheafToPresheaf _ _).Full :=
  show (sheafToPresheaf _ _ ⋙ (whiskeringRight Cᵒᵖ A B).obj F).Full from inferInstance

variable {F} in
/-- If `F : A ⥤ B` is fully faithful, then `sheafCompose J F ⋙ sheafToPresheaf J B` is fully
faithful. -/
def fullyFaithfulSheafComposeCompSheafToPresheaf (hF : F.FullyFaithful) :
    (sheafCompose J F ⋙ sheafToPresheaf J B).FullyFaithful :=
  (fullyFaithfulSheafToPresheaf J A).comp (hF.whiskeringRight Cᵒᵖ)

instance [F.Faithful] : (sheafCompose J F).Faithful :=
  Functor.Faithful.of_comp (sheafCompose J F) (sheafToPresheaf _ _)

instance [F.Full] [F.Faithful] : (sheafCompose J F).Full :=
  Functor.Full.of_comp_faithful (sheafCompose J F) (sheafToPresheaf _ _)

variable {F} in
/-- If `F : A ⥤ B` is fully faithful, then `sheafCompose J F` is fully faithful. -/
def fullyFaithfulSheafCompose (hF : F.FullyFaithful) :
    (sheafCompose J F).FullyFaithful :=
  (fullyFaithfulSheafComposeCompSheafToPresheaf J hF).ofCompFaithful

instance [F.ReflectsIsomorphisms] : (sheafCompose J F).ReflectsIsomorphisms where
  reflects {G₁ G₂} f _ := by
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _),
      ← isIso_iff_of_reflects_iso _ ((whiskeringRight Cᵒᵖ A B).obj F)]
    change IsIso ((sheafToPresheaf _ _).map ((sheafCompose J F).map f))
    infer_instance

variable {F G}

set_option backward.defeqAttrib.useBackward true in
/--
If `η : F ⟶ G` is a natural transformation then we obtain a morphism of functors
`sheafCompose J F ⟶ sheafCompose J G` by whiskering with `η` on the level of presheaves.
-/
def sheafCompose_map : sheafCompose J F ⟶ sheafCompose J G where
  app := fun _ => .mk <| whiskerLeft _ η

@[simp]
lemma sheafCompose_id : sheafCompose_map (F := F) J (𝟙 _) = 𝟙 _ := rfl

@[simp]
lemma sheafCompose_comp :
    sheafCompose_map J (η ≫ γ) = sheafCompose_map J η ≫ sheafCompose_map J γ := rfl

namespace GrothendieckTopology.Cover

variable (F G) {J}
variable (P : Cᵒᵖ ⥤ A) {X : C} (S : J.Cover X)

set_option backward.defeqAttrib.useBackward true in
/-- The multicospan associated to a cover `S : J.Cover X` and a presheaf of the form `P ⋙ F`
is isomorphic to the composition of the multicospan associated to `S` and `P`,
composed with `F`. -/
@[simps!]
def multicospanComp : (S.index (P ⋙ F)).multicospan ≅ (S.index P).multicospan ⋙ F :=
  NatIso.ofComponents
    (fun t =>
      match t with
      | WalkingMulticospan.left _ => Iso.refl _
      | WalkingMulticospan.right _ => Iso.refl _)
    (by
      #adaptation_note /-- Proof repaired after leanprover/lean4#13363.
      The body of this `by` block was previously
      ```
      rintro (a | b) (a | b) (f | f | f)
      all_goals cat_disch
      ```
      The replacement proof is a short-term fix, and we request that the authors/maintainers of
      this file review the proof, and either approve it by removing this note,
      revise the proof or the prerequisites appropriately, or minimize a problem in lean4 that
      still needs addressing. -/
      rintro (a | b) (a | b) (f | f | f) <;>
        simp only [WalkingMulticospan.Hom.id_eq_id, Iso.refl_hom, Category.id_comp,
          Category.comp_id, Functor.map_id] <;>
        dsimp [CategoryStruct.comp] <;> simp)

set_option backward.defeqAttrib.useBackward true in
/-- Mapping the multifork associated to a cover `S : J.Cover X` and a presheaf `P` with
respect to a functor `F` is isomorphic (upto a natural isomorphism of the underlying functors)
to the multifork associated to `S` and `P ⋙ F`. -/
def mapMultifork :
    F.mapCone (S.multifork P) ≅
      (Limits.Cone.postcompose (S.multicospanComp F P).hom).obj (S.multifork (P ⋙ F)) :=
  Cone.ext (Iso.refl _)

end GrothendieckTopology.Cover

/--
Composing a sheaf with a functor preserving the limit of `(S.index P).multicospan` yields a functor
between sheaf categories.
-/
instance (priority := high) hasSheafCompose_of_preservesMulticospan (F : A ⥤ B)
    [∀ (X : C) (S : J.Cover X) (P : Cᵒᵖ ⥤ A), PreservesLimit (S.index P).multicospan F] :
    J.HasSheafCompose F where
  isSheaf P hP := by
    rw [Presheaf.isSheaf_iff_multifork] at hP ⊢
    intro X S
    obtain ⟨h⟩ := hP X S
    replace h := isLimitOfPreserves F h
    replace h := Limits.IsLimit.ofIsoLimit h (S.mapMultifork F P)
    exact ⟨Limits.IsLimit.postcomposeHomEquiv (S.multicospanComp F P) _ h⟩

/--
Composing a sheaf with a functor preserving limits of the same size as the hom sets in `C` yields a
functor between sheaf categories.

Note: the size of the limit that `F` is required to preserve in
`hasSheafCompose_of_preservesMulticospan` is in general larger than this.
-/
instance hasSheafCompose_of_preservesLimitsOfSize [PreservesLimitsOfSize.{v₁, max u₁ v₁} F] :
    J.HasSheafCompose F where
  isSheaf _ hP := Presheaf.isSheaf_comp_of_isSheaf J _ F hP

variable {J}

lemma Sheaf.isSeparated {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [J.HasSheafCompose (forget A)]
    (F : Sheaf J A) : Presheaf.IsSeparated J F.obj := by
  rintro X S hS x y h
  exact (((isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose J (forget A)).obj F).2).isSeparated S hS).ext (fun _ _ hf => h _ _ hf)

lemma Presheaf.IsSheaf.isSeparated {F : Cᵒᵖ ⥤ A} {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [J.HasSheafCompose (forget A)] (hF : Presheaf.IsSheaf J F) :
    Presheaf.IsSeparated J F :=
  Sheaf.isSeparated ⟨F, hF⟩

end CategoryTheory
