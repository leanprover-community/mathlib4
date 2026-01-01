/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Quotient

/-!
# Certain quotient categories are localizations

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

namespace Quotient

variable (r : HomRel C) (W : MorphismProperty C)
  (hW : W.IsInvertedBy (functor r))
  (hr : ∀ ⦃X Y : C⦄ (f₀ f₁ : X ⟶ Y) (_ : r f₀ f₁),
    ∃ (Cyl : C) (i₀ i₁ : X ⟶ Cyl) (π : Cyl ⟶ X) (_hπ : W π)
      (_hi₀ : i₀ ≫ π = 𝟙 X) (_hi₁ : i₁ ≫ π = 𝟙 X) (φ : Cyl ⟶ Y), i₀ ≫ φ = f₀ ∧ i₁ ≫ φ = f₁)

namespace isLocalization_functor

variable {r W} (E : Type*) [Category E]

include hr
def strictUniversalPropertyFixedTarget :
    Localization.StrictUniversalPropertyFixedTarget (functor r) W E where
  inverts := hW
  lift F hF := Quotient.lift r F (fun X Y f₀ f₁ hf ↦ by
    obtain ⟨Cyl, i₀, i₁, π, hπ, hi₀, hi₁, φ, hφ₀, hφ₁⟩  := hr f₀ f₁ hf
    rw [← hφ₀, ← hφ₁, Functor.map_comp, Functor.map_comp]
    congr 1
    have := hF _ hπ
    rw [← cancel_mono (F.map π), ← Functor.map_comp, ← Functor.map_comp, hi₀, hi₁])
  fac F hF := rfl
  uniq F₁ F₂ h := by
    fapply Functor.ext
    · rintro ⟨X⟩
      exact Functor.congr_obj h X
    · rintro ⟨X⟩ ⟨Y⟩ ⟨f⟩
      exact Functor.congr_hom h f

end isLocalization_functor

include hW hr in
lemma isLocalization_functor : (functor r).IsLocalization W := by
  apply Functor.IsLocalization.mk'
  all_goals apply isLocalization_functor.strictUniversalPropertyFixedTarget hW hr

end Quotient

namespace Functor

lemma isLocalization_of_essSurj_of_full_of_exists_cylinders
    (L : C ⥤ D) [L.EssSurj] [L.Full] (W : MorphismProperty C) (hW : W.IsInvertedBy L)
    (hr : ∀ ⦃X Y : C⦄ (f₀ f₁ : X ⟶ Y) (_ : L.map f₀ = L.map f₁),
      ∃ (Cyl : C) (i₀ i₁ : X ⟶ Cyl) (π : Cyl ⟶ X) (_hπ : W π)
        (_hi₀ : i₀ ≫ π = 𝟙 X) (_hi₁ : i₁ ≫ π = 𝟙 X) (φ : Cyl ⟶ Y), i₀ ≫ φ = f₀ ∧ i₁ ≫ φ = f₁) :
    L.IsLocalization W := by
  let r := L.homRel
  let F : Quotient L.homRel ⥤ D := Quotient.lift _ L (by simp)
  let iso : Quotient.functor L.homRel ⋙ F ≅ L := Iso.refl _
  have : F.EssSurj := ⟨fun Y ↦ by
    have := essSurj_of_iso iso.symm
    obtain ⟨X, ⟨e⟩⟩ := (Quotient.functor L.homRel ⋙ F).exists_of_essSurj Y
    exact ⟨_, ⟨e⟩⟩⟩
  have : F.Full := ⟨by
    rintro ⟨X⟩ ⟨Y⟩ (f : L.obj X ⟶ L.obj Y)
    obtain ⟨f, rfl⟩ := L.map_surjective f
    exact ⟨(Quotient.functor L.homRel).map f, rfl⟩⟩
  have : F.Faithful := ⟨by
    rintro ⟨X⟩ ⟨Y⟩ f₁ f₂ hf
    obtain ⟨f₁, rfl⟩ := (Quotient.functor L.homRel).map_surjective f₁
    obtain ⟨f₂, rfl⟩ := (Quotient.functor L.homRel).map_surjective f₂
    exact Quotient.sound  _ hf⟩
  have : F.IsEquivalence := { }
  have hW' : W.IsInvertedBy (Quotient.functor L.homRel) := fun _ _ f hf ↦ by
    have : IsIso (F.map ((Quotient.functor L.homRel).map f)) := hW _ hf
    apply isIso_of_reflects_iso _ F
  have := Quotient.isLocalization_functor L.homRel W hW' hr
  exact IsLocalization.of_equivalence_target (Quotient.functor L.homRel) W L
    F.asEquivalence iso

end Functor

end CategoryTheory
