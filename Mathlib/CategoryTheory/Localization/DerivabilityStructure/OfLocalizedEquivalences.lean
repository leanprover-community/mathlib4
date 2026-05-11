/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
public import Mathlib.CategoryTheory.GuitartExact.HorizontalComposition

/-!
# Derivability structures deduced from localized equivalences

Assume that we have a diagram of localizer morphisms, in the
sense that we have an isomorphism `T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor`.
```
      T
 W₁  ---> W₂
 |        |
L|        |R
 v        v
 W₁' ---> W₂'
      B
```
In this file, we obtain the lemma
`LocalizerMorphism.isRightDerivabilityStructure_of_isLocalizedEquivalence` which shows
that if both `L` and `R` are localized equivalences (with `R.functor` essentially surjective),
then `B` is a right derivability structure when `T` is a right derivability structure,
the `2`-square above is Guitart exact (and `W₂'` respects isomorphisms).
In addition, if we require that `L.functor` is also essentially surjective,
that `R.functor` is full and that `W₂` is induced by `W₂'`, then
`B` is a right derivability structure iff `T` is.

The dual results for left derivability structures are also obtained.

This will be particularly useful when `L.functor` and `R.functor` are functors
from a category to a quotient category (e.g. functors from categories of homological
complexes to homotopy categories).

-/

@[expose] public section

namespace CategoryTheory

namespace LocalizerMorphism

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  {W₁ : MorphismProperty C₁} {W₁' : MorphismProperty D₁}
  {W₂ : MorphismProperty C₂} {W₂' : MorphismProperty D₂}
  {T : LocalizerMorphism W₁ W₂} {L : LocalizerMorphism W₁ W₁'}
  {R : LocalizerMorphism W₂ W₂'} {B : LocalizerMorphism W₁' W₂'}

section

variable [W₂'.RespectsIso]
  [L.IsLocalizedEquivalence] [R.IsLocalizedEquivalence] [R.functor.EssSurj]

set_option backward.isDefEq.respectTransparency false in
lemma isLeftDerivabilityStructure_of_isLocalizedEquivalence
    [T.IsLeftDerivabilityStructure]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor)
    [TwoSquare.GuitartExact iso.inv] :
    B.IsLeftDerivabilityStructure := by
  have : B.HasLeftResolutions := fun Y₂ ↦ by
    obtain ⟨X₂, ⟨e₂⟩⟩ := Functor.EssSurj.mem_essImage R.functor Y₂
    have ρ : T.LeftResolution X₂ := Classical.arbitrary _
    exact ⟨{
      X₁ := L.functor.obj ρ.X₁
      w := iso.inv.app _ ≫ R.functor.map ρ.w ≫ e₂.hom
      hw := (W₂'.arrow_mk_iso_iff (Arrow.isoMk (iso.app _) e₂)).1 (R.map _ ρ.hw) }⟩
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

lemma isLeftDerivabilityStructure_iff_of_isLocalizedEquivalence
    [L.functor.EssSurj] [R.functor.Full] [R.IsInduced]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor)
    [TwoSquare.GuitartExact iso.inv] :
    T.IsLeftDerivabilityStructure ↔ B.IsLeftDerivabilityStructure := by
  refine ⟨fun _ ↦ isLeftDerivabilityStructure_of_isLocalizedEquivalence iso, fun _ ↦ ?_⟩
  have : T.HasLeftResolutions := fun X₂ ↦ by
    let ρ : B.LeftResolution (R.functor.obj X₂) := Classical.arbitrary _
    exact ⟨{
      X₁ := L.functor.objPreimage ρ.X₁
      w :=
        R.functor.preimage (iso.hom.app _ ≫
          B.functor.map (L.functor.objObjPreimageIso ρ.X₁).hom ≫ ρ.w)
      hw := by
        simp only [← R.inverseImage_eq, Functor.comp_obj,
          MorphismProperty.inverseImage_iff, Functor.map_preimage]
        refine (W₂'.arrow_mk_iso_iff ?_).2 ρ.hw
        exact Arrow.isoMk (iso.app _ ≪≫ B.functor.mapIso (L.functor.objObjPreimageIso ρ.X₁))
          (Iso.refl _) }⟩
  let F := B.localizedFunctor W₁'.Q W₂'.Q
  let e' := CatCommSq.iso B.functor W₁'.Q W₂'.Q F
  let e : T.functor ⋙ R.functor ⋙ W₂'.Q ≅ (L.functor ⋙ W₁'.Q) ⋙ F :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight iso _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ e' ≪≫ (Functor.associator _ _ _).symm
  have he' : TwoSquare.GuitartExact e'.inv := inferInstance
  have : TwoSquare.hComp iso.inv e'.inv = e.inv := by ext; simp [e]
  rw [T.isLeftDerivabilityStructure_iff (L.functor ⋙ W₁'.Q)
    (R.functor ⋙ W₂'.Q) F e, ← this]
  infer_instance

lemma isRightDerivabilityStructure_of_isLocalizedEquivalence
    [T.IsRightDerivabilityStructure]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor)
    [TwoSquare.GuitartExact iso.hom] :
    B.IsRightDerivabilityStructure := by
  rw [isRightDerivabilityStructure_iff_op]
  let iso' : T.op.functor ⋙ R.op.functor ≅ L.op.functor ⋙ B.op.functor := NatIso.op iso.symm
  have : R.op.functor.EssSurj := by dsimp; infer_instance
  have : TwoSquare.GuitartExact iso'.inv :=
    inferInstanceAs (TwoSquare.op iso.hom).GuitartExact
  exact isLeftDerivabilityStructure_of_isLocalizedEquivalence iso'

lemma isRightDerivabilityStructure_iff_of_isLocalizedEquivalence
    [L.functor.EssSurj] [R.functor.Full] [R.IsInduced]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor)
    [TwoSquare.GuitartExact iso.hom] :
    T.IsRightDerivabilityStructure ↔ B.IsRightDerivabilityStructure := by
  simp only [isRightDerivabilityStructure_iff_op]
  let iso' : T.op.functor ⋙ R.op.functor ≅ L.op.functor ⋙ B.op.functor := NatIso.op iso.symm
  have : R.op.functor.EssSurj := by dsimp; infer_instance
  have : L.op.functor.EssSurj := by dsimp; infer_instance
  have : R.op.functor.Full := by dsimp; infer_instance
  have : TwoSquare.GuitartExact iso'.inv :=
    inferInstanceAs (TwoSquare.op iso.hom).GuitartExact
  exact isLeftDerivabilityStructure_iff_of_isLocalizedEquivalence iso'

end

variable [W₁'.RespectsIso] [W₂'.RespectsIso] [L.IsInduced] [L.functor.IsEquivalence]
  [R.IsInduced] [R.functor.IsEquivalence]
  (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor)

lemma isLeftDerivabilityStructure_of_equivalences
    [T.IsLeftDerivabilityStructure]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    B.IsLeftDerivabilityStructure := by
  have := L.isLocalizedEquivalence_of_isInduced
  have := R.isLocalizedEquivalence_of_isInduced
  exact isLeftDerivabilityStructure_of_isLocalizedEquivalence iso

open Functor in
lemma isLeftDerivabilityStructure_iff_of_equivalences
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    T.IsLeftDerivabilityStructure ↔ B.IsLeftDerivabilityStructure :=
  ⟨fun _ ↦ isLeftDerivabilityStructure_of_equivalences iso, fun _ ↦ by
    let e : B.functor ⋙ R.inv.functor ≅ L.inv.functor ⋙ T.functor :=
      (leftUnitor _).symm ≪≫
        isoWhiskerRight L.functor.asEquivalence.counitIso.symm _ ≪≫
        associator _ _ _ ≪≫ isoWhiskerLeft _ (associator _ _ _).symm ≪≫
        isoWhiskerLeft _ (isoWhiskerRight iso.symm R.inv.functor) ≪≫
        isoWhiskerLeft _ (associator _ _ _) ≪≫
        isoWhiskerLeft _ (isoWhiskerLeft _ R.functor.asEquivalence.unitIso.symm) ≪≫
        (associator _ _ _).symm ≪≫ rightUnitor _
    have : W₁.RespectsIso := by rw [← L.inverseImage_eq]; infer_instance
    have : W₂.RespectsIso := by rw [← R.inverseImage_eq]; infer_instance
    exact isLeftDerivabilityStructure_of_equivalences e⟩

lemma isRightDerivabilityStructure_iff_of_equivalences
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    T.IsRightDerivabilityStructure ↔ B.IsRightDerivabilityStructure := by
  let e : T.op.functor ⋙ R.op.functor ≅ L.op.functor ⋙ B.op.functor := NatIso.op iso.symm
  have : L.op.functor.IsEquivalence := by dsimp; infer_instance
  have : R.op.functor.IsEquivalence := by dsimp; infer_instance
  simp only [isRightDerivabilityStructure_iff_op,
    isLeftDerivabilityStructure_iff_of_equivalences e]

lemma isRightDerivabilityStructure_of_equivalences
    [T.IsRightDerivabilityStructure]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    B.IsRightDerivabilityStructure := by
  rwa [← isRightDerivabilityStructure_iff_of_equivalences iso]

end LocalizerMorphism

end CategoryTheory
