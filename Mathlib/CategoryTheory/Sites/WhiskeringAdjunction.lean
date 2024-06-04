/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# The adjunction of categories of sheaves induced by an adjunction

if `adj : L ⊣ R` is an adjunction between functors `L : A ⥤ B` and `R : B ⥤ A`,
`adj.whiskerRight Cᵒᵖ` is an adjunction between the categories of
presheaves `Cᵒᵖ ⥤ A` and `Cᵒᵖ ⥤ B`. In this file, we consider the
induced adjunction between `Sheaf J A` and `Sheaf J B` when `J` is
a Grothendieck topology on `C`.

The functor `(Cᵒᵖ ⥤ B) ⥤ (Cᵒᵖ ⥤ A)` on presheaves induced by the right
adjoint `R` automatically preserves sheaves: the right adjoint
functor `Sheaf J B ⥤ Sheaf J A` is the induced functor `sheafCompose J R`.
On the left side, we show that the left adjoint functor `L`
preserves sheafification, then the left adjoint functor
`Sheaf J A ⥤ Sheaf J B` of the adjunction shall be
`sheafCompose' J L` (see the isomorphism `sheafCompose'Iso`).

-/

universe v₁ v₂ v u₁ u₂ u

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
  {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

namespace Adjunction

abbrev sheafR : Sheaf J B ⥤ Sheaf J A :=
  letI := adj.isRightAdjoint; sheafCompose J R

lemma preservesSheafification : J.PreservesSheafification L where
  le P Q f hf := by
    have := adj.isRightAdjoint
    rw [MorphismProperty.inverseImage_iff]
    dsimp
    intro F hF
    rw [← ((adj.whiskerRight Cᵒᵖ).homEquiv P F).comp_bijective]
    convert (((adj.whiskerRight Cᵒᵖ).homEquiv Q F).trans
      (hf.homEquiv (F ⋙ R) ((sheafCompose J R).obj ⟨F, hF⟩).cond)).bijective
    ext g X
    dsimp [Adjunction.whiskerRight, mkOfUnitCounit]
    simp

variable [HasWeakSheafify J A] [HasWeakSheafify J B]

noncomputable abbrev sheafL : Sheaf J A ⥤ Sheaf J B :=
  letI := adj.preservesSheafification J; sheafCompose' J L

variable {J} in
noncomputable def sheafHomEquiv {F : Sheaf J A} {G : Sheaf J B} :
    ((adj.sheafL J).obj F ⟶ G) ≃ (F ⟶ (adj.sheafR J).obj G) := by
  letI := adj.preservesSheafification J
  refine ((sheafCompose'Iso J L).app F).homFromEquiv.trans
    ((fullyFaithfulSheafToPresheaf J B).homEquiv.trans
    (((J.W_toSheafify (F.val ⋙ L)).homEquiv _ G.cond).trans
    (((adj.whiskerRight Cᵒᵖ).homEquiv F.val G.val).trans
    (Equiv.symm (fullyFaithfulSheafToPresheaf J A).homEquiv ))))

noncomputable def sheaf : adj.sheafL J ⊣ adj.sheafR J :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦ adj.sheafHomEquiv
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

instance [L.IsLeftAdjoint] : J.PreservesSheafification L :=
  (Adjunction.ofIsLeftAdjoint L).preservesSheafification J

instance [L.IsLeftAdjoint] : (sheafCompose' J L).IsLeftAdjoint :=
  ((Adjunction.ofIsLeftAdjoint L).sheaf J).isLeftAdjoint

instance [R.IsRightAdjoint] : (sheafCompose J R).IsRightAdjoint :=
  ((Adjunction.ofIsRightAdjoint R).sheaf J).isRightAdjoint

instance : (adj.sheafL J).IsLeftAdjoint :=
  (adj.sheaf J).isLeftAdjoint

instance : (adj.sheafR J).IsRightAdjoint :=
  (adj.sheaf J).isRightAdjoint

end Adjunction

end CategoryTheory
