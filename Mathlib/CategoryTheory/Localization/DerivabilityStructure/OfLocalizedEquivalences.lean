/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
import Mathlib.CategoryTheory.GuitartExact.HorizontalComposition

/-!
# Derivability structures deduced from localized equivalences

-/

namespace CategoryTheory

namespace LocalizerMorphism

variable {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  {W₁ : MorphismProperty C₁} {W₁' : MorphismProperty D₁}
  {W₂ : MorphismProperty C₂} {W₂' : MorphismProperty D₂}
  {T : LocalizerMorphism W₁ W₂} {L : LocalizerMorphism W₁ W₁'}
  {R : LocalizerMorphism W₂ W₂'} {B : LocalizerMorphism W₁' W₂'}
  [T.IsLeftDerivabilityStructure] [W₂'.RespectsIso]
  [L.IsLocalizedEquivalence] [R.IsLocalizedEquivalence] [R.functor.EssSurj]
  (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor)
  [TwoSquare.GuitartExact iso.inv]

include iso in
lemma isLeftDerivabilityStructure_of_isLocalizedEquivalence :
    B.IsLeftDerivabilityStructure := by
  have : B.HasLeftResolutions := fun Y₂ ↦ by
    obtain ⟨X₂, ⟨e₂⟩⟩ := R.functor.exists_of_essSurj Y₂
    have ρ : T.LeftResolution X₂ := Classical.arbitrary _
    exact ⟨{
      X₁ := L.functor.obj ρ.X₁
      w := iso.inv.app _ ≫ R.functor.map ρ.w ≫ e₂.hom
      hw := (W₂'.arrow_mk_iso_iff (Arrow.isoMk (iso.app _) e₂)).1 (R.map _ ρ.hw)
    }⟩
  let F := B.localizedFunctor W₁'.Q W₂'.Q
  let e' := CatCommSq.iso B.functor W₁'.Q W₂'.Q F
  letI iso' : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  letI : CatCommSq T.functor (L.functor ⋙ W₁'.Q) (R.functor ⋙ W₂'.Q) F :=
    CatCommSq.vComp (H₂ := B.functor) _ _ _ _ _ _
  have : (TwoSquare.hComp iso.inv e'.inv).GuitartExact := by
    convert T.guitartExact_of_isLeftDerivabilityStructure' (L.functor ⋙ W₁'.Q)
      (R.functor ⋙ W₂'.Q) F (CatCommSq.iso _ _ _ _)
    ext
    simp [e', CatCommSq.iso, iso']
  rw [B.isLeftDerivabilityStructure_iff W₁'.Q W₂'.Q F e']
  apply TwoSquare.GuitartExact.of_hComp iso.inv

end LocalizerMorphism

end CategoryTheory
