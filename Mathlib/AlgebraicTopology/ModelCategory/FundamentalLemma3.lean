/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma2

/-!
# The fundamental lemma of homotopical algebra

-/

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category C] [ModelCategory C] {H : Type*} [Category H]
  (L : C ⥤ H) [L.IsLocalization (weakEquivalences _)]
  {X Y : C}

def leftHomotopyClassToHom : LeftHomotopyClass X Y → (L.obj X ⟶ L.obj Y) :=
  Quot.lift L.map (fun _ _ h ↦ (factorsThroughLocalization_leftHomotopyRel h).map_eq _)

@[simp]
lemma leftHomotopyClassToHom_mk (f : X ⟶ Y) :
    leftHomotopyClassToHom L (.mk f) = L.map f := rfl

def rightHomotopyClassToHom : RightHomotopyClass X Y → (L.obj X ⟶ L.obj Y) :=
  Quot.lift L.map (fun _ _ h ↦ (factorsThroughLocalization_rightHomotopyRel h).map_eq _)

@[simp]
lemma rightHomotopyClassToHom_mk (f : X ⟶ Y) :
    rightHomotopyClassToHom L (.mk f) = L.map f := rfl

variable (X Y)
lemma bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom
    [IsCofibrant X] [IsFibrant Y] :
    Function.Bijective (leftHomotopyClassToHom L : LeftHomotopyClass X Y → _) ↔
    Function.Bijective (rightHomotopyClassToHom L : RightHomotopyClass X Y → _) := by
  have : (leftHomotopyClassToHom L : LeftHomotopyClass X Y → _) =
      rightHomotopyClassToHom L ∘ leftHomotopyClassEquivRightHomotopyClass := by
    ext f
    obtain ⟨f, rfl⟩ := f.mk_surjective
    simp
  simp [this]

lemma bijective_rightHomotopyClassToHom [IsCofibrant X] [IsFibrant Y] :
    Function.Bijective (rightHomotopyClassToHom L : RightHomotopyClass X Y → _) := by
  wlog _ : IsCofibrant Y generalizing Y
  · obtain ⟨Y', _, p, _, _⟩ := CofibrantObject.π.exists_resolution Y
    have _ : IsFibrant Y' := isFibrant_of_fibration p
    have hY' := this Y' inferInstance
    simp only [← bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom] at hY' ⊢
    have := Localization.inverts L (weakEquivalences _) p
      (by rwa [← weakEquivalence_iff])
    rw [← Function.Bijective.of_comp_iff _
      (LeftHomotopyClass.bijective_postcomp_of_fibration_of_weakEquivalence _ p)]
    convert (Iso.homCongr (Iso.refl (L.obj X)) (asIso (L.map p))).bijective.comp hY'
    ext f
    obtain ⟨f, rfl⟩ := f.mk_surjective
    simp
  wlog _ : IsFibrant X generalizing X
  · obtain ⟨X', i, _, _, _⟩ : ∃ (X' : C) (i : X ⟶ X'), Cofibration i ∧ WeakEquivalence i ∧
      IsFibrant X' :=
      ⟨(CofibrantObject.bifibrantResolutionObj (.mk X)).obj,
        CofibrantObject.ι.map (CofibrantObject.iBifibrantResolutionObj (.mk X)),
        inferInstance, inferInstance, inferInstance⟩
    have _ := isCofibrant_of_cofibration i
    have hX' := this X' inferInstance
    have := Localization.inverts L (weakEquivalences _) i
      (by rwa [← weakEquivalence_iff])
    rw [← Function.Bijective.of_comp_iff _
      (RightHomotopyClass.bijective_precomp_of_cofibration_of_weakEquivalence Y i)]
    convert (Iso.homCongr (asIso (L.map i)) (Iso.refl (L.obj Y))).symm.bijective.comp hX'
    ext f
    obtain ⟨f, rfl⟩ := f.mk_surjective
    simp
  let E := Localization.uniq BifibrantObject.toπ (BifibrantObject.ι ⋙ L) (weakEquivalences _)
  let e : BifibrantObject.toπ ⋙ E.functor ≅ BifibrantObject.ι ⋙ L :=
    Localization.compUniqFunctor BifibrantObject.toπ (BifibrantObject.ι ⋙ L) (weakEquivalences _)
  have : rightHomotopyClassToHom L =
      (BifibrantObject.π.homEquivRight.trans (E.fullyFaithfulFunctor.homEquiv.trans
        (Iso.homCongr (e.app (.mk X)) (e.app (.mk Y))))) := by
    ext f
    obtain ⟨f, rfl⟩ := RightHomotopyClass.mk_surjective f
    exact (NatIso.naturality_1 e (BifibrantObject.homMk f)).symm
  rw [this]
  exact Equiv.bijective _

lemma bijective_leftHomotopyClassToHom [IsCofibrant X] [IsFibrant Y] :
    Function.Bijective (leftHomotopyClassToHom L : LeftHomotopyClass X Y → _) := by
  have : (leftHomotopyClassToHom L : LeftHomotopyClass X Y → _) =
      rightHomotopyClassToHom L ∘ leftHomotopyClassEquivRightHomotopyClass := by
    ext f
    obtain ⟨f, rfl⟩ := f.mk_surjective
    simp
  rw [this]
  exact (bijective_rightHomotopyClassToHom L X Y).comp (Equiv.bijective _)

end HomotopicalAlgebra
