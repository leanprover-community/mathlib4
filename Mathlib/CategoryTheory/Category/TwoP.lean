/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.Category.Bipointed
import Mathlib.Data.TwoPointing

/-!
# The category of two-pointed types

This defines `TwoP`, the category of two-pointed types.

## References

* [nLab, *coalgebra of the real interval*]
  (https://ncatlab.org/nlab/show/coalgebra+of+the+real+interval)
-/


open CategoryTheory Option

universe u

variable {α β : Type*}


/-- The category of two-pointed types. -/
structure TwoP : Type (u + 1) where
  /-- The underlying type of a two-pointed type. -/
  protected X : Type u
  /-- The two points of a bipointed type, bundled together as a pair of distinct elements. -/
  toTwoPointing : TwoPointing X

namespace TwoP

instance : CoeSort TwoP Type* :=
  ⟨TwoP.X⟩

/-- Turns a two-pointing into a two-pointed type. -/
def of {X : Type*} (toTwoPointing : TwoPointing X) : TwoP :=
  ⟨X, toTwoPointing⟩

@[simp]
theorem coe_of {X : Type*} (toTwoPointing : TwoPointing X) : ↥(of toTwoPointing) = X :=
  rfl

alias _root_.TwoPointing.TwoP := of

instance : Inhabited TwoP :=
  ⟨of TwoPointing.bool⟩

/-- Turns a two-pointed type into a bipointed type, by forgetting that the pointed elements are
distinct. -/
noncomputable def toBipointed (X : TwoP) : Bipointed :=
  X.toTwoPointing.toProd.Bipointed

@[simp]
theorem coe_toBipointed (X : TwoP) : ↥X.toBipointed = ↥X :=
  rfl

noncomputable instance largeCategory : LargeCategory TwoP :=
  InducedCategory.category toBipointed

noncomputable instance concreteCategory : ConcreteCategory TwoP :=
  InducedCategory.concreteCategory toBipointed

noncomputable instance hasForgetToBipointed : HasForget₂ TwoP Bipointed :=
  InducedCategory.hasForget₂ toBipointed

@[ext]
lemma hom_ext {X Y : TwoP} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  InducedCategory.hom_ext h

@[simp]
lemma id_hom (X : TwoP) : InducedCategory.Hom.hom (𝟙 X) = 𝟙 _ := rfl

@[simp, reassoc]
lemma comp_hom {X Y Z : TwoP} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- Swaps the pointed elements of a two-pointed type. `TwoPointing.swap` as a functor. -/
@[simps]
noncomputable def swap : TwoP ⥤ TwoP where
  obj X := ⟨X, X.toTwoPointing.swap⟩
  map f := ⟨f.hom.toFun, f.hom.map_snd, f.hom.map_fst⟩

/-- The equivalence between `TwoP` and itself induced by `Prod.swap` both ways. -/
@[simps!]
noncomputable def swapEquiv : TwoP ≌ TwoP :=
  CategoryTheory.Equivalence.mk swap swap
    (NatIso.ofComponents fun X =>
      { hom := ⟨id, rfl, rfl⟩
        inv := ⟨id, rfl, rfl⟩ })
    (NatIso.ofComponents fun X =>
      { hom := ⟨id, rfl, rfl⟩
        inv := ⟨id, rfl, rfl⟩ })

@[simp]
theorem swapEquiv_symm : swapEquiv.symm = swapEquiv :=
  rfl

end TwoP

@[simp]
theorem TwoP_swap_comp_forget_to_Bipointed :
    TwoP.swap ⋙ forget₂ TwoP Bipointed = forget₂ TwoP Bipointed ⋙ Bipointed.swap :=
  rfl

/-- The functor from `Pointed` to `TwoP` which adds a second point. -/
@[simps]
noncomputable def pointedToTwoPFst : Pointed.{u} ⥤ TwoP where
  obj X := ⟨Option X, ⟨X.point, none⟩, some_ne_none _⟩
  map f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_id _ := by ext1; exact Bipointed.Hom.ext _ _ Option.map_id
  map_comp f g := by ext1; exact Bipointed.Hom.ext _ _ (Option.map_comp_map f.1 g.1).symm

/-- The functor from `Pointed` to `TwoP` which adds a first point. -/
@[simps]
noncomputable def pointedToTwoPSnd : Pointed.{u} ⥤ TwoP where
  obj X := ⟨Option X, ⟨none, X.point⟩, (some_ne_none _).symm⟩
  map f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_id _ := by ext1; exact Bipointed.Hom.ext _ _ Option.map_id
  map_comp f g := by ext1; exact Bipointed.Hom.ext _ _ (Option.map_comp_map f.1 g.1).symm

@[simp]
theorem pointedToTwoPFst_comp_swap : pointedToTwoPFst ⋙ TwoP.swap = pointedToTwoPSnd :=
  rfl

@[simp]
theorem pointedToTwoPSnd_comp_swap : pointedToTwoPSnd ⋙ TwoP.swap = pointedToTwoPFst :=
  rfl

@[simp]
theorem pointedToTwoPFst_comp_forget_to_bipointed :
    pointedToTwoPFst ⋙ forget₂ TwoP Bipointed = pointedToBipointedFst :=
  rfl

@[simp]
theorem pointedToTwoPSnd_comp_forget_to_bipointed :
    pointedToTwoPSnd ⋙ forget₂ TwoP Bipointed = pointedToBipointedSnd :=
  rfl

/-- Adding a second point is left adjoint to forgetting the second point. -/
noncomputable def pointedToTwoPFstForgetCompBipointedToPointedFstAdjunction :
    pointedToTwoPFst ⊣ forget₂ TwoP Bipointed ⋙ bipointedToPointedFst :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.hom.toFun ∘ Option.some, f.hom.map_fst⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.2 f.toFun, f.map_point, rfl⟩
          left_inv := fun f => by
            ext1
            apply Bipointed.Hom.ext
            funext x
            cases x
            · exact f.hom.map_snd.symm
            · rfl
          right_inv := fun f => Pointed.Hom.ext _ _ rfl }
      homEquiv_naturality_left_symm := fun f g => by
        ext1
        apply Bipointed.Hom.ext
        funext x
        cases x <;> rfl }

/-- Adding a first point is left adjoint to forgetting the first point. -/
noncomputable def pointedToTwoPSndForgetCompBipointedToPointedSndAdjunction :
    pointedToTwoPSnd ⊣ forget₂ TwoP Bipointed ⋙ bipointedToPointedSnd :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.hom.toFun ∘ Option.some, f.hom.map_snd⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.1 f.toFun, rfl, f.map_point⟩
          left_inv := fun f => by
            ext1
            apply Bipointed.Hom.ext
            funext x
            cases x
            · exact f.hom.map_fst.symm
            · rfl
          right_inv := fun f => Pointed.Hom.ext _ _ rfl }
      homEquiv_naturality_left_symm := fun f g => by
        ext1
        apply Bipointed.Hom.ext
        funext x
        cases x <;> rfl }
