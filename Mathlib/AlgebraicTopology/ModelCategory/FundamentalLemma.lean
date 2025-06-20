/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# The fundamental lemma of homotopical algebra

-/

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable (C : Type*) [Category C] [ModelCategory C]

namespace CofibrantObject

def homRel : HomRel (CofibrantObject C) :=
  fun X Y ↦ RightHomotopyRel (X := X.1) (Y := Y.1)

lemma compClosure_homRel :
    Quotient.CompClosure (homRel C) = homRel C := by
  ext X Y f g
  refine ⟨?_, Quotient.CompClosure.of _ _ _⟩
  rintro ⟨i, f', g', p, h⟩
  exact (h.postcomp p).precomp i

end CofibrantObject

namespace FibrantObject

def homRel : HomRel (FibrantObject C) :=
  fun X Y ↦ LeftHomotopyRel (X := X.1) (Y := Y.1)

lemma compClosure_homRel :
    Quotient.CompClosure (homRel C) = homRel C := by
  ext X Y f g
  refine ⟨?_, Quotient.CompClosure.of _ _ _⟩
  rintro ⟨i, f', g', p, h⟩
  exact (h.postcomp p).precomp i

end FibrantObject

namespace BifibrantObject

def homRel : HomRel (BifibrantObject C) :=
  fun X Y ↦ RightHomotopyRel (X := X.1) (Y := Y.1)

instance : Congruence (homRel C) where
  equivalence := RightHomotopyRel.equivalence _ _
  compLeft p _ _ h := h.precomp p
  compRight p h := h.postcomp p

variable {C} {X Y : BifibrantObject C} (f g : X ⟶ Y)

lemma homRel_iff_rightHomotopyRel :
    homRel C f g ↔ RightHomotopyRel (ι.map f) (ι.map g) := Iff.rfl

lemma homRel_iff_leftHomotopyRel :
    homRel C f g ↔ LeftHomotopyRel (ι.map f) (ι.map g) := by
  rw [homRel_iff_rightHomotopyRel, leftHomotopyRel_iff_rightHomotopyRel]

variable (C) in
abbrev π := Quotient (BifibrantObject.homRel C)

def toπ : BifibrantObject C ⥤ π C := Quotient.functor _

section

variable (E : Type*) [Category E]

lemma inverts_iff_factors (F : BifibrantObject C ⥤ E) :
    (weakEquivalences _).IsInvertedBy F ↔
    ∀ ⦃K L : BifibrantObject C⦄ (f g : K ⟶ L)
      (h : homRel C f g), F.map f = F.map g := by
  constructor
  · intro H K L f g h
    obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good
    have := isCofibrant_of_cofibration P.ι
    let γ : K ⟶ mk P.P := h.h
    let p₀ : mk P.P ⟶ L := P.p₀
    let p₁ : mk P.P ⟶ L := P.p₁
    let s : L ⟶ mk P.P := P.ι
    have : IsIso (F.map s) := H _ (by
      rw [← weakEquivalence_iff, weakEquivalence_iff_ι_map]
      exact inferInstanceAs (WeakEquivalence P.ι))
    simp only [← h.h₀, ← h.h₁]
    change F.map (γ ≫ p₀) = F.map (γ ≫ p₁)
    simp only [Functor.map_comp]
    congr 1
    simp only [← cancel_epi (F.map s), ← Functor.map_comp]
    congr 1
    exact ι.map_injective (P.ι_p₀.trans P.ι_p₁.symm)
  · sorry

def strictUniversalPropertyFixedTargetToπ :
    Localization.StrictUniversalPropertyFixedTarget
    toπ (weakEquivalences (BifibrantObject C)) E where
  inverts := by
    rw [inverts_iff_factors]
    intro K L f g h
    exact CategoryTheory.Quotient.sound _ h
  lift F hF := CategoryTheory.Quotient.lift _ F
    (by rwa [inverts_iff_factors] at hF)
  fac F hF := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h

end

instance : toπ.IsLocalization (weakEquivalences (BifibrantObject C)) :=
  .mk' _ _ (strictUniversalPropertyFixedTargetToπ _)
    (strictUniversalPropertyFixedTargetToπ _)

end BifibrantObject

end HomotopicalAlgebra
