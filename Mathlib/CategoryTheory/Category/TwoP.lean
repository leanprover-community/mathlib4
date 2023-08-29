/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.Category.Bipointed
import Mathlib.Data.TwoPointing

#align_import category_theory.category.Twop from "leanprover-community/mathlib"@"c8ab806ef73c20cab1d87b5157e43a82c205f28e"

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

set_option linter.uppercaseLean3 false

/-- The category of two-pointed types. -/
structure TwoP : Type (u + 1) where
  protected X : Type u
  toTwoPointing : TwoPointing X
#align Twop TwoP

namespace TwoP

instance : CoeSort TwoP (Type*) :=
  ⟨TwoP.X⟩

/-- Turns a two-pointing into a two-pointed type. -/
def of {X : Type*} (toTwoPointing : TwoPointing X) : TwoP :=
  ⟨X, toTwoPointing⟩
#align Twop.of TwoP.of

@[simp]
theorem coe_of {X : Type*} (toTwoPointing : TwoPointing X) : ↥(of toTwoPointing) = X :=
  rfl
#align Twop.coe_of TwoP.coe_of

alias _root_.TwoPointing.TwoP := of
#align two_pointing.Twop TwoPointing.TwoP

instance : Inhabited TwoP :=
  ⟨of TwoPointing.bool⟩

/-- Turns a two-pointed type into a bipointed type, by forgetting that the pointed elements are
distinct. -/
noncomputable def toBipointed (X : TwoP) : Bipointed :=
  X.toTwoPointing.toProd.Bipointed
#align Twop.to_Bipointed TwoP.toBipointed

@[simp]
theorem coe_toBipointed (X : TwoP) : ↥X.toBipointed = ↥X :=
  rfl
#align Twop.coe_to_Bipointed TwoP.coe_toBipointed

noncomputable instance largeCategory : LargeCategory TwoP :=
  InducedCategory.category toBipointed
#align Twop.large_category TwoP.largeCategory

noncomputable instance concreteCategory : ConcreteCategory TwoP :=
  InducedCategory.concreteCategory toBipointed
#align Twop.concrete_category TwoP.concreteCategory

noncomputable instance hasForgetToBipointed : HasForget₂ TwoP Bipointed :=
  InducedCategory.hasForget₂ toBipointed
#align Twop.has_forget_to_Bipointed TwoP.hasForgetToBipointed


/-- Swaps the pointed elements of a two-pointed type. `TwoPointing.swap` as a functor. -/
@[simps]
noncomputable def swap : TwoP ⥤ TwoP where
  obj X := ⟨X, X.toTwoPointing.swap⟩
  map f := ⟨f.toFun, f.map_snd, f.map_fst⟩
#align Twop.swap TwoP.swap

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
#align Twop.swap_equiv TwoP.swapEquiv

@[simp]
theorem swapEquiv_symm : swapEquiv.symm = swapEquiv :=
  rfl
#align Twop.swap_equiv_symm TwoP.swapEquiv_symm

end TwoP

@[simp]
theorem TwoP_swap_comp_forget_to_Bipointed :
    TwoP.swap ⋙ forget₂ TwoP Bipointed = forget₂ TwoP Bipointed ⋙ Bipointed.swap :=
  rfl
#align Twop_swap_comp_forget_to_Bipointed TwoP_swap_comp_forget_to_Bipointed

/-- The functor from `Pointed` to `TwoP` which adds a second point. -/
@[simps]
noncomputable def pointedToTwoPFst : Pointed.{u} ⥤ TwoP where
  obj X := ⟨Option X, ⟨X.point, none⟩, some_ne_none _⟩
  map f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_id _ := Bipointed.Hom.ext _ _ Option.map_id
  map_comp f g := Bipointed.Hom.ext _ _ (Option.map_comp_map f.1 g.1).symm
#align Pointed_to_Twop_fst pointedToTwoPFst

/-- The functor from `Pointed` to `TwoP` which adds a first point. -/
@[simps]
noncomputable def pointedToTwoPSnd : Pointed.{u} ⥤ TwoP where
  obj X := ⟨Option X, ⟨none, X.point⟩, (some_ne_none _).symm⟩
  map f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_id _ := Bipointed.Hom.ext _ _ Option.map_id
  map_comp f g := Bipointed.Hom.ext _ _ (Option.map_comp_map f.1 g.1).symm
#align Pointed_to_Twop_snd pointedToTwoPSnd

@[simp]
theorem pointedToTwoPFst_comp_swap : pointedToTwoPFst ⋙ TwoP.swap = pointedToTwoPSnd :=
  rfl
#align Pointed_to_Twop_fst_comp_swap pointedToTwoPFst_comp_swap

@[simp]
theorem pointedToTwoPSnd_comp_swap : pointedToTwoPSnd ⋙ TwoP.swap = pointedToTwoPFst :=
  rfl
#align Pointed_to_Twop_snd_comp_swap pointedToTwoPSnd_comp_swap

@[simp]
theorem pointedToTwoPFst_comp_forget_to_bipointed :
    pointedToTwoPFst ⋙ forget₂ TwoP Bipointed = pointedToBipointedFst :=
  rfl
#align Pointed_to_Twop_fst_comp_forget_to_Bipointed pointedToTwoPFst_comp_forget_to_bipointed

@[simp]
theorem pointedToTwoPSnd_comp_forget_to_bipointed :
    pointedToTwoPSnd ⋙ forget₂ TwoP Bipointed = pointedToBipointedSnd :=
  rfl
#align Pointed_to_Twop_snd_comp_forget_to_Bipointed pointedToTwoPSnd_comp_forget_to_bipointed

/-- Adding a second point is left adjoint to forgetting the second point. -/
noncomputable def pointedToTwoPFstForgetCompBipointedToPointedFstAdjunction :
    pointedToTwoPFst ⊣ forget₂ TwoP Bipointed ⋙ bipointedToPointedFst :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_fst⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.2 f.toFun, f.map_point, rfl⟩
          left_inv := fun f => by
            apply Bipointed.Hom.ext
            -- ⊢ ((fun f => { toFun := fun o => Option.elim o Y.toTwoPointing.snd f.toFun, ma …
            funext x
            -- ⊢ Bipointed.Hom.toFun ((fun f => { toFun := fun o => Option.elim o Y.toTwoPoin …
            cases x
            -- ⊢ Bipointed.Hom.toFun ((fun f => { toFun := fun o => Option.elim o Y.toTwoPoin …
            exact f.map_snd.symm
            -- ⊢ Bipointed.Hom.toFun ((fun f => { toFun := fun o => Option.elim o Y.toTwoPoin …
            rfl
            -- 🎉 no goals
          right_inv := fun f => Pointed.Hom.ext _ _ rfl }
      homEquiv_naturality_left_symm := fun f g => by
        apply Bipointed.Hom.ext
        -- ⊢ (↑((fun X Y => { toFun := fun f => { toFun := f.toFun ∘ some, map_point := ( …
        funext x
        -- ⊢ Bipointed.Hom.toFun (↑((fun X Y => { toFun := fun f => { toFun := f.toFun ∘  …
        cases x <;> rfl }
        -- ⊢ Bipointed.Hom.toFun (↑((fun X Y => { toFun := fun f => { toFun := f.toFun ∘  …
                    -- 🎉 no goals
                    -- 🎉 no goals
#align Pointed_to_Twop_fst_forget_comp_Bipointed_to_Pointed_fst_adjunction pointedToTwoPFstForgetCompBipointedToPointedFstAdjunction

/-- Adding a first point is left adjoint to forgetting the first point. -/
noncomputable def pointedToTwoPSndForgetCompBipointedToPointedSndAdjunction :
    pointedToTwoPSnd ⊣ forget₂ TwoP Bipointed ⋙ bipointedToPointedSnd :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_snd⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.1 f.toFun, rfl, f.map_point⟩
          left_inv := fun f => by
            apply Bipointed.Hom.ext
            -- ⊢ ((fun f => { toFun := fun o => Option.elim o Y.toTwoPointing.fst f.toFun, ma …
            funext x
            -- ⊢ Bipointed.Hom.toFun ((fun f => { toFun := fun o => Option.elim o Y.toTwoPoin …
            cases x
            -- ⊢ Bipointed.Hom.toFun ((fun f => { toFun := fun o => Option.elim o Y.toTwoPoin …
            exact f.map_fst.symm
            -- ⊢ Bipointed.Hom.toFun ((fun f => { toFun := fun o => Option.elim o Y.toTwoPoin …
            rfl
            -- 🎉 no goals
          right_inv := fun f => Pointed.Hom.ext _ _ rfl }
      homEquiv_naturality_left_symm := fun f g => by
        apply Bipointed.Hom.ext
        -- ⊢ (↑((fun X Y => { toFun := fun f => { toFun := f.toFun ∘ some, map_point := ( …
        funext x
        -- ⊢ Bipointed.Hom.toFun (↑((fun X Y => { toFun := fun f => { toFun := f.toFun ∘  …
        cases x <;> rfl }
        -- ⊢ Bipointed.Hom.toFun (↑((fun X Y => { toFun := fun f => { toFun := f.toFun ∘  …
                    -- 🎉 no goals
                    -- 🎉 no goals
#align Pointed_to_Twop_snd_forget_comp_Bipointed_to_Pointed_snd_adjunction pointedToTwoPSndForgetCompBipointedToPointedSndAdjunction
