/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Morphisms of localizers

A morphism of localizers consists of a functor `F : C₁ ⥤ C₂` between
two categories equipped with morphism properties `W₁` and `W₂` such
that `F` sends morphisms in `W₁` to morphisms in `W₂`.

If `Φ : LocalizerMorphism W₁ W₂`, and that `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂`
are localization functors for `W₁` and `W₂`, the induced functor `D₁ ⥤ D₂`
is denoted `Φ.localizedFunctor L₁ L₂`; we introduce the condition
`Φ.IsLocalizedEquivalence` which expresses that this functor is an equivalence
of categories. This condition is independent of the choice of the
localized categories.

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

universe v₁ v₂ v₃ v₄ v₄' v₅ v₅' v₆ u₁ u₂ u₃ u₄ u₄' u₅ u₅' u₆

namespace CategoryTheory

open Localization

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  {D₁ : Type u₄} {D₂ : Type u₅} {D₃ : Type u₆}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [Category.{v₄} D₁] [Category.{v₅} D₂] [Category.{v₆} D₂]
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)

/-- If `W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂`, a `LocalizerMorphism W₁ W₂`
is the datum of a functor `C₁ ⥤ C₂` which sends morphisms in `W₁` to morphisms in `W₂` -/
structure LocalizerMorphism where
  /-- a functor between the two categories -/
  functor : C₁ ⥤ C₂
  /-- the functor is compatible with the `MorphismProperty` -/
  map : W₁ ≤ W₂.inverseImage functor

namespace LocalizerMorphism

/-- The identity functor as a morphism of localizers. -/
@[simps]
def id : LocalizerMorphism W₁ W₁ where
  functor := 𝟭 C₁
  map _ _ _ hf := hf

variable {W₁ W₂ W₃}

/-- The composition of two localizers morphisms. -/
@[simps]
def comp (Φ : LocalizerMorphism W₁ W₂) (Ψ : LocalizerMorphism W₂ W₃) :
    LocalizerMorphism W₁ W₃ where
  functor := Φ.functor ⋙ Ψ.functor
  map _ _ _ hf := Ψ.map _ (Φ.map _ hf)

variable (Φ : LocalizerMorphism W₁ W₂)

/-- The opposite localizer morphism `LocalizerMorphism W₁.op W₂.op` deduced
from `Φ : LocalizerMorphism W₁ W₂`. -/
@[simps]
def op : LocalizerMorphism W₁.op W₂.op where
  functor := Φ.functor.op
  map _ _ _ hf := Φ.map _ hf

variable (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁] (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]

lemma inverts : W₁.IsInvertedBy (Φ.functor ⋙ L₂) :=
  fun _ _ _ hf => Localization.inverts L₂ W₂ _ (Φ.map _ hf)

/-- When `Φ : LocalizerMorphism W₁ W₂` and that `L₁` and `L₂` are localization functors
for `W₁` and `W₂`, then `Φ.localizedFunctor L₁ L₂` is the induced functor on the
localized categories. --/
noncomputable def localizedFunctor : D₁ ⥤ D₂ :=
  lift (Φ.functor ⋙ L₂) (Φ.inverts _) L₁

noncomputable instance : Lifting L₁ W₁ (Φ.functor ⋙ L₂) (Φ.localizedFunctor L₁ L₂) := by
  dsimp [localizedFunctor]
  infer_instance

/-- The 2-commutative square expressing that `Φ.localizedFunctor L₁ L₂` lifts the
functor `Φ.functor`  -/
noncomputable instance catCommSq : CatCommSq Φ.functor L₁ L₂ (Φ.localizedFunctor L₁ L₂) :=
  CatCommSq.mk (Lifting.iso _ W₁ _ _).symm

variable (G : D₁ ⥤ D₂)

section

variable [CatCommSq Φ.functor L₁ L₂ G]
  {D₁' : Type u₄'} {D₂' : Type u₅'}
  [Category.{v₄'} D₁'] [Category.{v₅'} D₂']
  (L₁' : C₁ ⥤ D₁') (L₂' : C₂ ⥤ D₂') [L₁'.IsLocalization W₁] [L₂'.IsLocalization W₂]
  (G' : D₁' ⥤ D₂') [CatCommSq Φ.functor L₁' L₂' G']

/-- If a localizer morphism induces an equivalence on some choice of localized categories,
it will be so for any choice of localized categoriees. -/
lemma isEquivalence_imp [G.IsEquivalence] : G'.IsEquivalence := by
  let E₁ := Localization.uniq L₁ L₁' W₁
  let E₂ := Localization.uniq L₂ L₂' W₂
  let e : L₁ ⋙ G ⋙ E₂.functor ≅ L₁ ⋙ E₁.functor ⋙ G' :=
    calc
      L₁ ⋙ G ⋙ E₂.functor ≅ Φ.functor ⋙ L₂ ⋙ E₂.functor :=
          (Functor.associator _ _ _).symm ≪≫
            isoWhiskerRight (CatCommSq.iso Φ.functor L₁ L₂ G).symm E₂.functor ≪≫
            Functor.associator _ _ _
      _ ≅ Φ.functor ⋙ L₂' := isoWhiskerLeft Φ.functor (compUniqFunctor L₂ L₂' W₂)
      _ ≅ L₁' ⋙ G' := CatCommSq.iso Φ.functor L₁' L₂' G'
      _ ≅ L₁ ⋙ E₁.functor ⋙ G' :=
            isoWhiskerRight (compUniqFunctor L₁ L₁' W₁).symm G' ≪≫ Functor.associator _ _ _
  have := Functor.isEquivalence_of_iso
    (liftNatIso L₁ W₁ _ _ (G ⋙ E₂.functor) (E₁.functor ⋙ G') e)
  exact Functor.isEquivalence_of_comp_left E₁.functor G'

lemma isEquivalence_iff : G.IsEquivalence ↔ G'.IsEquivalence :=
  ⟨fun _ => Φ.isEquivalence_imp L₁ L₂ G L₁' L₂' G',
    fun _ => Φ.isEquivalence_imp L₁' L₂' G' L₁ L₂ G⟩

end

/-- Condition that a `LocalizerMorphism` induces an equivalence on the localized categories -/
class IsLocalizedEquivalence : Prop :=
  /-- the induced functor on the constructed localized categories is an equivalence -/
  isEquivalence : (Φ.localizedFunctor W₁.Q W₂.Q).IsEquivalence

lemma IsLocalizedEquivalence.mk' [CatCommSq Φ.functor L₁ L₂ G] [G.IsEquivalence] :
    Φ.IsLocalizedEquivalence where
  isEquivalence := by
    rw [Φ.isEquivalence_iff W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) L₁ L₂ G]
    exact inferInstance

/-- If a `LocalizerMorphism` is a localized equivalence, then any compatible functor
between the localized categories is an equivalence. -/
lemma isEquivalence [h : Φ.IsLocalizedEquivalence] [CatCommSq Φ.functor L₁ L₂ G] :
    G.IsEquivalence := (by
  rw [Φ.isEquivalence_iff L₁ L₂ G W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)]
  exact h.isEquivalence)

/-- If a `LocalizerMorphism` is a localized equivalence, then the induced functor on
the localized categories is an equivalence -/
instance localizedFunctor_isEquivalence [Φ.IsLocalizedEquivalence] :
    (Φ.localizedFunctor L₁ L₂).IsEquivalence :=
  Φ.isEquivalence L₁ L₂ _

/-- When `Φ : LocalizerMorphism W₁ W₂`, if the composition `Φ.functor ⋙ L₂` is a
localization functor for `W₁`, then `Φ` is a localized equivalence. -/
lemma IsLocalizedEquivalence.of_isLocalization_of_isLocalization
    [(Φ.functor ⋙ L₂).IsLocalization W₁] :
    IsLocalizedEquivalence Φ := by
  have : CatCommSq Φ.functor (Φ.functor ⋙ L₂) L₂ (𝟭 D₂) :=
    CatCommSq.mk (Functor.rightUnitor _).symm
  exact IsLocalizedEquivalence.mk' Φ (Φ.functor ⋙ L₂) L₂ (𝟭 D₂)

/-- When the underlying functor `Φ.functor` of `Φ : LocalizerMorphism W₁ W₂` is
an equivalence of categories and that `W₁` and `W₂` essentially correspond to each
other via this equivalence, then `Φ` is a localized equivalence. -/
lemma IsLocalizedEquivalence.of_equivalence [Φ.functor.IsEquivalence]
    (h : W₂ ≤ W₁.map Φ.functor) : IsLocalizedEquivalence Φ := by
  haveI : Functor.IsLocalization (Φ.functor ⋙ MorphismProperty.Q W₂) W₁ := by
    refine Functor.IsLocalization.of_equivalence_source W₂.Q W₂ (Φ.functor ⋙ W₂.Q) W₁
      (Functor.asEquivalence Φ.functor).symm ?_ (Φ.inverts W₂.Q)
      ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight ((Equivalence.unitIso _).symm) _ ≪≫
        Functor.leftUnitor _)
    erw [W₁.isoClosure.inverseImage_equivalence_functor_eq_map_inverse
      W₁.isoClosure_respectsIso Φ.functor.asEquivalence]
    rw [MorphismProperty.map_isoClosure]
    exact h
  exact IsLocalizedEquivalence.of_isLocalization_of_isLocalization Φ W₂.Q

end LocalizerMorphism

end CategoryTheory
