/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy
public import Mathlib.AlgebraicTopology.ModelCategory.RightHomotopy
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Quotient

/-!
# Certain quotient categories are localizations

Let `r : HomRel C` be a relation on morphisms in a category `C` and
`W : MorphismProperty C`. We assume that `W` is inverted by the quotient functor
`functor r : C ⥤ quotient r`. If any relation `r f₀ f₁` between morphisms
`f₀ : X ⟶ Y` and `f₁ : X ⟶ Y` can be "explained" by the use of a homotopy
involving a cylinder object (i.e. there exists an object `cylinder : C`,
a morphism `π : cylinder ⟶ X` in `W`, a morphism `φ : cylinder ⟶ Y` and two
sections `i₀` and `i₁` to `π` such that `i₀ ≫ φ = f₀` and `i₁ ≫ φ = f₁`),
then `functor r : C ⥤ quotient r` is a localization functor for `W`.
We also deduce a slightly more general result involving
a full and essentially surjective functor `L : C ⥤ D` instead of the quotient
functor `functor r : C ⥤ quotient r`.
Dual results involving path objects are also obtained.

-/

public section

namespace CategoryTheory

open HomotopicalAlgebra

variable {C D : Type*} [Category* C] [Category* D]

namespace Quotient

variable (r : HomRel C) (W : MorphismProperty C)
  (hW : W.IsInvertedBy (functor r))
  (hr : ∀ ⦃X Y : C⦄ (f₀ f₁ : X ⟶ Y) (_ : r f₀ f₁),
    ∃ (P : Precylinder X) (_ : P.LeftHomotopy f₀ f₁), W P.π)

namespace isLocalization_functor

variable {r W} in
/-- Auxiliary definition for `Quotient.isLocalization_functor`. -/
private def strictUniversalPropertyFixedTarget (E : Type*) [Category* E] :
    Localization.StrictUniversalPropertyFixedTarget (functor r) W E where
  inverts := hW
  lift F hF := Quotient.lift r F (fun X Y f₀ f₁ hf ↦ by
    obtain ⟨P, h, hπ⟩ := hr f₀ f₁ hf
    simp only [← h.h₀, ← h.h₁, Functor.map_comp]
    congr 1
    have := hF _ hπ
    simp [← cancel_mono (F.map P.π), ← Functor.map_comp])
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
      ∃ (P : Precylinder X) (_ : P.LeftHomotopy f₀ f₁), W P.π) :
    L.IsLocalization W := by
  let F := Quotient.lift L.homRel L (by simp)
  have hW' : W.IsInvertedBy (Quotient.functor L.homRel) := fun _ _ f hf ↦ by
    have : IsIso (F.map ((Quotient.functor L.homRel).map f)) := hW _ hf
    apply isIso_of_reflects_iso _ F
  have := Quotient.isLocalization_functor L.homRel W hW' hr
  exact IsLocalization.of_equivalence_target (Quotient.functor L.homRel) W L
    F.asEquivalence (Iso.refl _)

lemma isLocalization_of_essSurj_of_full_of_exists_pathObjects
    (L : C ⥤ D) [L.EssSurj] [L.Full] (W : MorphismProperty C) (hW : W.IsInvertedBy L)
    (hr : ∀ ⦃X Y : C⦄ (f₀ f₁ : X ⟶ Y) (_ : L.map f₀ = L.map f₁),
      ∃ (P : PrepathObject Y) (_ : P.RightHomotopy f₀ f₁), W P.ι) :
    L.IsLocalization W := by
  rw [← Functor.IsLocalization.op_iff]
  refine isLocalization_of_essSurj_of_full_of_exists_cylinders L.op W.op hW.op
    (fun X Y f₀ f₁ hf ↦ ?_)
  obtain ⟨P, h, hι⟩ := hr f₀.unop f₁.unop (Quiver.Hom.op_inj hf)
  exact ⟨P.op, h.op, hι⟩

end Functor

lemma Quotient.isLocalization_functor' (r : HomRel C) [Congruence r] (W : MorphismProperty C)
    (hW : W.IsInvertedBy (functor r))
    (hr : ∀ ⦃X Y : C⦄ (f₀ f₁ : X ⟶ Y) (_ : r f₀ f₁),
      ∃ (P : PrepathObject Y) (_ : P.RightHomotopy f₀ f₁), W P.ι) :
    (functor r).IsLocalization W :=
  (functor r).isLocalization_of_essSurj_of_full_of_exists_pathObjects W hW
    (fun X Y f₀ f₁ hf ↦ by
      rw [functor_map_eq_iff] at hf
      exact hr _ _ hf)

end CategoryTheory
