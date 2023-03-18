import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.CatCommSq

namespace CategoryTheory

open Localization Category

variable {C₁ C₂ D₁ D₂ : Type _} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)

/-- If `W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂`, a `LocalizorMorphism W₁ W₂`
is the datum of a functor `C₁ ⥤ C₂` which sends morphisms in `W₁` to morphisms in `W₂` -/
structure LocalizorMorphism where
  /-- a functor between the two categories -/
  functor : C₁ ⥤ C₂
  /-- the functor is compatible with the `MorphismProperty` -/
  map : W₁ ⊆ W₂.inverseImage functor

namespace LocalizorMorphism

variable {W₁ W₂} (Φ : LocalizorMorphism W₁ W₂) (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]

lemma inverts : W₁.IsInvertedBy (Φ.functor ⋙ L₂) :=
  fun _ _ _ hf => Localization.inverts L₂ W₂ _ (Φ.map _ hf)

/-- When `Φ : LocalizorMorphism W₁ W₂` and that `L₁` and `L₂` are localization functors
for `W₁` and `W₂`, then `Φ.localizedFunctor L₁ L₂` is the induced functor on the
localized categories. --/
noncomputable def localizedFunctor : D₁ ⥤ D₂ :=
  lift (Φ.functor ⋙ L₂) (Φ.inverts _) L₁

/-- The 2-commutative square expressing that `Φ.localizedFunctor L₁ L₂` lifts the
functor `Φ.functor`  -/
noncomputable instance catCommSq : CatCommSq L₁ Φ.functor L₂ (Φ.localizedFunctor L₁ L₂) :=
  CatCommSq.mk ((Localization.fac _ _ _).symm)

noncomputable instance : Lifting L₁ W₁ (Φ.functor ⋙ L₂) (Φ.localizedFunctor L₁ L₂) :=
  ⟨Iso.symm (CatCommSq.iso _ _ _ _)⟩

variable {L₁ L₂} {D₁' D₂' : Type _} [Category D₁'] [Category D₂'] {L₁' : C₁ ⥤ D₁'} {L₂' : C₂ ⥤ D₂'}
  {G : D₁ ⥤ D₂} {G' : D₁' ⥤ D₂'} [L₁'.IsLocalization W₁] [L₂'.IsLocalization W₂]
  (c : CatCommSq L₁ Φ.functor L₂ G) (c' : CatCommSq L₁' Φ.functor L₂' G')

/-- If a localizor morphism induces an equivalence on some choice of localized categories,
it will be so for any choice of localized categoriees. -/
noncomputable def isEquivalence_imp [IsEquivalence G] :
  IsEquivalence G' := by
    let E₁ := Localization.uniq L₁ L₁' W₁
    let E₂ := Localization.uniq L₂ L₂' W₂
    letI : Lifting L₁ W₁ (Φ.functor ⋙ L₂') (G ⋙ E₂.functor) :=
      Lifting.mk ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (Iso.symm c.iso) _ ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (compUniqFunctor L₂ L₂' W₂))
    letI : Lifting L₁ W₁ (L₁' ⋙ G') (E₁.functor ⋙ G') :=
      Lifting.mk ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (compUniqFunctor L₁ L₁' W₁) _)
    have φ : CatCommSq E₁.functor G E₂.functor G' :=
      CatCommSq.mk (liftNatIso L₁ W₁ (Φ.functor ⋙ L₂') (L₁' ⋙ G') _ _ c'.iso)
    exact IsEquivalence.cancelCompLeft E₁.functor G' inferInstance
      (IsEquivalence.ofIso φ.iso inferInstance)

lemma nonempty_isEquivalence_iff : Nonempty (IsEquivalence G) ↔ Nonempty (IsEquivalence G') := by
  constructor
  . rintro ⟨e⟩
    exact ⟨Φ.isEquivalence_imp c c'⟩
  . rintro ⟨e'⟩
    exact ⟨Φ.isEquivalence_imp c' c⟩

/-- condition that `LocalizorMorphism` induces an equivalence of localized categories -/
class IsLocalizedEquivalence : Prop :=
  /-- the induced functor on the constructed localized categories is an equivalence -/
  nonempty_isEquivalence : Nonempty (IsEquivalence (Φ.localizedFunctor W₁.Q W₂.Q))

lemma IsLocalizedEquivalence.mk' (c : CatCommSq L₁ Φ.functor L₂ G) [IsEquivalence G] :
  Φ.IsLocalizedEquivalence := by
    constructor
    rw [Φ.nonempty_isEquivalence_iff (Φ.catCommSq W₁.Q W₂.Q) c]
    exact ⟨inferInstance⟩

/-- If a `LocalizorMorphism` is a localized equivalence, then any compatible functor
on the localized categories is an equivalence. -/
noncomputable def isEquivalence [h : Φ.IsLocalizedEquivalence] (c : CatCommSq L₁ Φ.functor L₂ G) :
    IsEquivalence G := by
  apply Nonempty.some
  rw [Φ.nonempty_isEquivalence_iff c (Φ.catCommSq W₁.Q W₂.Q)]
  exact h.nonempty_isEquivalence

variable (L₁ L₂)

/-- If a `LocalizorMorphism` is a localized equivalence, then the induced functor on
the localized categories is an equivalence -/
noncomputable def localizedFunctor_isEquivalence [Φ.IsLocalizedEquivalence] :
    IsEquivalence ((Φ.localizedFunctor L₁ L₂)) :=
  Φ.isEquivalence (Φ.catCommSq L₁ L₂)

end LocalizorMorphism

end CategoryTheory
