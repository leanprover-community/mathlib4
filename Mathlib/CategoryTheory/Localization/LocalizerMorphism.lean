/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Equivalence
public import Mathlib.CategoryTheory.Localization.Opposite

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

@[expose] public section

universe v₁ v₂ v₃ v₄ v₄' v₅ v₅' v₆ u₁ u₂ u₃ u₄ u₄' u₅ u₅' u₆

namespace CategoryTheory

open Localization Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {D₁ : Type u₄} {D₂ : Type u₅}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} D₁] [Category.{v₅} D₂]
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)

/-- If `W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂`, a `LocalizerMorphism W₁ W₂`
is the datum of a functor `C₁ ⥤ C₂` which sends morphisms in `W₁` to morphisms in `W₂` -/
structure LocalizerMorphism where
  /-- a functor between the two categories -/
  functor : C₁ ⥤ C₂
  /-- the functor is compatible with the `MorphismProperty` -/
  map : W₁ ≤ W₂.inverseImage functor

namespace LocalizerMorphism

variable {W₁ W₂} in
/-- Constructor for localizer morphisms given by a functor `F : C₁ ⥤ C₂`
under the stronger assumption that the classes of morphisms `W₁` and `W₂`
satisfy `W₁ = W₂.inverseImage F`. -/
@[simps]
def ofEq {F : C₁ ⥤ C₂} (hW : W₁ = W₂.inverseImage F) : LocalizerMorphism W₁ W₂ where
  functor := F
  map := by rw [hW]

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
localized categories. -/
noncomputable def localizedFunctor : D₁ ⥤ D₂ :=
  lift (Φ.functor ⋙ L₂) (Φ.inverts _) L₁

noncomputable instance liftingLocalizedFunctor :
    Lifting L₁ W₁ (Φ.functor ⋙ L₂) (Φ.localizedFunctor L₁ L₂) :=
  inferInstanceAs <| Lifting L₁ W₁ _ (lift _ _ L₁)

/-- The 2-commutative square expressing that `Φ.localizedFunctor L₁ L₂` lifts the
functor `Φ.functor` -/
noncomputable instance catCommSq : CatCommSq Φ.functor L₁ L₂ (Φ.localizedFunctor L₁ L₂) :=
  CatCommSq.mk (Lifting.iso _ W₁ _ _).symm

variable (G : D₁ ⥤ D₂)

section

variable [CatCommSq Φ.functor L₁ L₂ G]
  {D₁' : Type u₄'} {D₂' : Type u₅'}
  [Category.{v₄'} D₁'] [Category.{v₅'} D₂']
  (L₁' : C₁ ⥤ D₁') (L₂' : C₂ ⥤ D₂') [L₁'.IsLocalization W₁] [L₂'.IsLocalization W₂]
  (G' : D₁' ⥤ D₂') [CatCommSq Φ.functor L₁' L₂' G']
include W₁ W₂ Φ L₁ L₂ L₁' L₂'

/-- If a localizer morphism induces an equivalence on some choice of localized categories,
it will be so for any choice of localized categories. -/
lemma isEquivalence_imp [G.IsEquivalence] : G'.IsEquivalence :=
  let E₁ := Localization.uniq L₁ L₁' W₁
  let E₂ := Localization.uniq L₂ L₂' W₂
  let e : L₁ ⋙ G ⋙ E₂.functor ≅ L₁ ⋙ E₁.functor ⋙ G' :=
    calc
      L₁ ⋙ G ⋙ E₂.functor ≅ Φ.functor ⋙ L₂ ⋙ E₂.functor :=
          (associator _ _ _).symm ≪≫
            isoWhiskerRight (CatCommSq.iso Φ.functor L₁ L₂ G).symm E₂.functor ≪≫
            associator _ _ _
      _ ≅ Φ.functor ⋙ L₂' := isoWhiskerLeft Φ.functor (compUniqFunctor L₂ L₂' W₂)
      _ ≅ L₁' ⋙ G' := CatCommSq.iso Φ.functor L₁' L₂' G'
      _ ≅ L₁ ⋙ E₁.functor ⋙ G' :=
            isoWhiskerRight (compUniqFunctor L₁ L₁' W₁).symm G' ≪≫ associator _ _ _
  have := Functor.isEquivalence_of_iso
    (liftNatIso L₁ W₁ _ _ (G ⋙ E₂.functor) (E₁.functor ⋙ G') e)
  Functor.isEquivalence_of_comp_left E₁.functor G'

lemma isEquivalence_iff : G.IsEquivalence ↔ G'.IsEquivalence :=
  ⟨fun _ => Φ.isEquivalence_imp L₁ L₂ G L₁' L₂' G',
    fun _ => Φ.isEquivalence_imp L₁' L₂' G' L₁ L₂ G⟩

/-- If a localizer morphism induces a fully faithful functor on some choice of
localized categories, it will be so for any choice of localized categories. -/
private noncomputable def fullyFaithfulImp (hG : G.FullyFaithful) : G'.FullyFaithful :=
  let E₁ := Localization.uniq L₁ L₁' W₁
  let E₂ := Localization.uniq L₂ L₂' W₂
  let e : L₁ ⋙ G ⋙ E₂.functor ≅ L₁ ⋙ E₁.functor ⋙ G' :=
    calc
      L₁ ⋙ G ⋙ E₂.functor ≅ Φ.functor ⋙ L₂ ⋙ E₂.functor :=
          (associator _ _ _).symm ≪≫
            isoWhiskerRight (CatCommSq.iso Φ.functor L₁ L₂ G).symm E₂.functor ≪≫
            associator _ _ _
      _ ≅ Φ.functor ⋙ L₂' := isoWhiskerLeft Φ.functor (compUniqFunctor L₂ L₂' W₂)
      _ ≅ L₁' ⋙ G' := CatCommSq.iso Φ.functor L₁' L₂' G'
      _ ≅ L₁ ⋙ E₁.functor ⋙ G' :=
            isoWhiskerRight (compUniqFunctor L₁ L₁' W₁).symm G' ≪≫ associator _ _ _
  (E₁.fullyFaithfulInverse.comp (hG.comp E₂.fullyFaithfulFunctor)).ofIso
    ((isoWhiskerLeft (E₁.inverse) (liftNatIso L₁ W₁ _ _ (G ⋙ E₂.functor) (E₁.functor ⋙ G') e) ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight E₁.counitIso G' ≪≫ G'.leftUnitor))

lemma nonempty_fullyFaithful_iff : Nonempty G.FullyFaithful ↔ Nonempty G'.FullyFaithful :=
  ⟨fun ⟨h⟩ => ⟨Φ.fullyFaithfulImp L₁ L₂ G L₁' L₂' G' h⟩,
    fun ⟨h⟩ => ⟨Φ.fullyFaithfulImp L₁' L₂' G' L₁ L₂ G h⟩⟩

end

/-- Condition that a `LocalizerMorphism` induces an equivalence on the localized categories -/
class IsLocalizedEquivalence : Prop where
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

instance [Φ.IsLocalizedEquivalence] : Φ.op.IsLocalizedEquivalence := by
  let G := Φ.localizedFunctor W₁.Q W₂.Q
  letI : CatCommSq Φ.op.functor W₁.Q.op W₂.Q.op G.op :=
    ⟨NatIso.op (CatCommSq.iso Φ.functor W₁.Q W₂.Q G).symm⟩
  have := Φ.isEquivalence W₁.Q W₂.Q G
  exact IsLocalizedEquivalence.mk' Φ.op W₁.Q.op W₂.Q.op G.op

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
    CatCommSq.mk (rightUnitor _).symm
  exact IsLocalizedEquivalence.mk' Φ (Φ.functor ⋙ L₂) L₂ (𝟭 D₂)

/-- When the underlying functor `Φ.functor` of `Φ : LocalizerMorphism W₁ W₂` is
an equivalence of categories and that `W₁` and `W₂` essentially correspond to each
other via this equivalence, then `Φ` is a localized equivalence. -/
lemma IsLocalizedEquivalence.of_equivalence [Φ.functor.IsEquivalence]
    (h : W₂ ≤ W₁.map Φ.functor) : IsLocalizedEquivalence Φ := by
  haveI : Functor.IsLocalization (Φ.functor ⋙ MorphismProperty.Q W₂) W₁ := by
    refine Functor.IsLocalization.of_equivalence_source W₂.Q W₂ (Φ.functor ⋙ W₂.Q) W₁
      (asEquivalence Φ.functor).symm ?_ (Φ.inverts W₂.Q)
      ((associator _ _ _).symm ≪≫ isoWhiskerRight ((Equivalence.unitIso _).symm) _ ≪≫
        leftUnitor _)
    erw [W₁.isoClosure.inverseImage_equivalence_functor_eq_map_inverse]
    rw [MorphismProperty.map_isoClosure]
    exact h
  exact IsLocalizedEquivalence.of_isLocalization_of_isLocalization Φ W₂.Q

instance IsLocalizedEquivalence.isLocalization [Φ.IsLocalizedEquivalence] :
    (Φ.functor ⋙ L₂).IsLocalization W₁ :=
  Functor.IsLocalization.of_iso _ ((Φ.catCommSq W₁.Q L₂).iso).symm

lemma isLocalizedEquivalence_of_unit_of_unit (Ψ : LocalizerMorphism W₂ W₁)
    (ε₁ : 𝟭 C₁ ⟶ Φ.functor ⋙ Ψ.functor) (ε₂ : 𝟭 C₂ ⟶ Ψ.functor ⋙ Φ.functor)
    (hε₁ : ∀ X₁, W₁ (ε₁.app X₁)) (hε₂ : ∀ X₂, W₂ (ε₂.app X₂)) :
    Φ.IsLocalizedEquivalence where
  isEquivalence := by
    have : IsIso (whiskerRight ε₁ W₁.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ ↦ Localization.inverts W₁.Q W₁ _ (hε₁ _)
    have : IsIso (whiskerRight ε₂ W₂.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ ↦ Localization.inverts W₂.Q W₂ _ (hε₂ _)
    refine (Localization.equivalence W₁.Q W₁ W₂.Q W₂ (Φ.functor ⋙ W₂.Q)
      (Φ.localizedFunctor W₁.Q W₂.Q)
      (Ψ.functor ⋙ W₁.Q) (Ψ.localizedFunctor W₂.Q W₁.Q) ?_ ?_).isEquivalence_functor
    · exact Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (CatCommSq.iso Ψ.functor W₂.Q W₁.Q _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        (asIso (whiskerRight ε₁ W₁.Q)).symm ≪≫ Functor.leftUnitor _
    · exact Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        (asIso (whiskerRight ε₂ W₂.Q)).symm ≪≫ Functor.leftUnitor _

instance IsLocalizedEquivalence.id :
    (id W₁).IsLocalizedEquivalence :=
  have : ((LocalizerMorphism.id W₁).functor ⋙ W₁.Q).IsLocalization W₁ :=
    Functor.IsLocalization.of_iso _ (Functor.leftUnitor _).symm
  of_isLocalization_of_isLocalization _ W₁.Q

instance IsLocalizedEquivalence.comp [Φ.IsLocalizedEquivalence]
    (Ψ : LocalizerMorphism W₂ W₃)
    [Ψ.IsLocalizedEquivalence] :
    (Φ.comp Ψ).IsLocalizedEquivalence :=
  have : ((Φ.comp Ψ).functor ⋙ W₃.Q).IsLocalization W₁ :=
    Functor.IsLocalization.of_iso _ (Functor.associator _ _ _).symm
  of_isLocalization_of_isLocalization _ W₃.Q

/-- Condition that a `LocalizerMorphism` induces a fully faithful functor
on the localized categories. -/
class IsLocalizedFullyFaithful : Prop where
  /-- the induced functor on the constructed localized categories is fully faithful -/
  nonempty_fullyFaithful : Nonempty (Φ.localizedFunctor W₁.Q W₂.Q).FullyFaithful

lemma IsLocalizedFullyFaithful.mk' [CatCommSq Φ.functor L₁ L₂ G] (hG : G.FullyFaithful) :
    Φ.IsLocalizedFullyFaithful where
  nonempty_fullyFaithful := by
    rw [Φ.nonempty_fullyFaithful_iff W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) L₁ L₂ G]
    exact ⟨hG⟩

instance [Φ.IsLocalizedEquivalence] : Φ.IsLocalizedFullyFaithful where
  nonempty_fullyFaithful := ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

/-- If a `LocalizerMorphism` becomes a fully faithful after localization, then any compatible
functor between the localized categories is fully faithful. -/
@[no_expose] noncomputable def fullyFaithful
    [h : Φ.IsLocalizedFullyFaithful] [CatCommSq Φ.functor L₁ L₂ G] :
    G.FullyFaithful :=
  Nonempty.some (by
    rw [Φ.nonempty_fullyFaithful_iff L₁ L₂ G W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)]
    exact h.nonempty_fullyFaithful)

lemma faithful [Φ.IsLocalizedFullyFaithful] [CatCommSq Φ.functor L₁ L₂ G] :
    G.Faithful :=
  (Φ.fullyFaithful L₁ L₂ G).faithful

lemma full [Φ.IsLocalizedFullyFaithful] [CatCommSq Φ.functor L₁ L₂ G] :
    G.Full :=
  (Φ.fullyFaithful L₁ L₂ G).full

/-- If a `LocalizerMorphism` becomes fully faithful after localization,
then the induced functor on the localized categories is fully faithful. -/
noncomputable irreducible_def fullyFaithfulLocalizedFunctor [Φ.IsLocalizedFullyFaithful] :
    (Φ.localizedFunctor L₁ L₂).FullyFaithful :=
  Φ.fullyFaithful L₁ L₂ _

instance [Φ.IsLocalizedFullyFaithful] : (Φ.localizedFunctor L₁ L₂).Full :=
  Φ.full L₁ L₂ _

instance [Φ.IsLocalizedFullyFaithful] : (Φ.localizedFunctor L₁ L₂).Faithful :=
  Φ.faithful L₁ L₂ _

instance [Φ.IsLocalizedFullyFaithful] : Φ.op.IsLocalizedFullyFaithful := by
  let G := Φ.localizedFunctor W₁.Q W₂.Q
  letI : CatCommSq Φ.op.functor W₁.Q.op W₂.Q.op G.op :=
    ⟨NatIso.op (CatCommSq.iso Φ.functor W₁.Q W₂.Q G).symm⟩
  exact IsLocalizedFullyFaithful.mk' Φ.op W₁.Q.op W₂.Q.op G.op
    (Φ.fullyFaithful W₁.Q W₂.Q G).op

/-- Assume that a localizer morphism `Φ : LocalizerMorphism W₁ W₂` induces
a fully faithful functor on the localized categories.
If `L₂ : C₂ ⥤ D₂` is a localization functor for `W₂` and we have a
factorization `iso : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F` as an essentially surjective
functor `L₁ : C₁ ⥤ D₁` followed by a fully faithful functor `F : D₁ ⥤ D₂`,
then `L₁` is a localization functor for `W₁`. -/
lemma isLocalization_of_isLocalizedFullyFaithful
    [Φ.IsLocalizedFullyFaithful] {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂]
    {L₁ : C₁ ⥤ D₁} {F : D₁ ⥤ D₂}
    (iso : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F)
    [F.Full] [F.Faithful] [L₁.EssSurj] :
    L₁.IsLocalization W₁ := by
  have h : W₁.IsInvertedBy L₁ := fun _ _ f hf ↦ by
    rw [← isIso_iff_of_reflects_iso  _ F]
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Arrow.isoOfNatIso iso f)).1 (Localization.inverts L₂ W₂ _ (Φ.map _ hf))
  let G := Localization.lift L₁ h W₁.Q
  let e : W₁.Q ⋙ G ≅ L₁ := Localization.fac L₁ h W₁.Q
  letI : CatCommSq Φ.functor W₁.Q L₂ (G ⋙ F) :=
    ⟨iso ≪≫ isoWhiskerRight e.symm _ ≪≫ associator _ _ _⟩
  have hG : G.FullyFaithful := Functor.FullyFaithful.ofCompFaithful
    (Φ.fullyFaithful W₁.Q L₂ (G ⋙ F))
  have := hG.full
  have := hG.faithful
  have : G.EssSurj :=
    ⟨fun X ↦ ⟨W₁.Q.obj (L₁.objPreimage X), ⟨e.app _ ≪≫ L₁.objObjPreimageIso X⟩⟩⟩
  have : G.IsEquivalence := { }
  exact IsLocalization.of_equivalence_target W₁.Q W₁ L₁ G.asEquivalence e

instance IsLocalizedFullyFaithful.comp
    (Ψ : LocalizerMorphism W₂ W₃)
    [Φ.IsLocalizedFullyFaithful] [Ψ.IsLocalizedFullyFaithful] :
    (Φ.comp Ψ).IsLocalizedFullyFaithful :=
  letI : CatCommSq (Φ.comp Ψ).functor W₁.Q W₃.Q
      (Φ.localizedFunctor W₁.Q W₂.Q ⋙ Ψ.localizedFunctor W₂.Q W₃.Q) :=
    CatCommSq.hComp _ _ _ W₂.Q _ _ _
  IsLocalizedFullyFaithful.mk' _ W₁.Q W₃.Q _
    ((Φ.fullyFaithfulLocalizedFunctor W₁.Q W₂.Q).comp
      (Ψ.fullyFaithfulLocalizedFunctor W₂.Q W₃.Q))

/-- The localizer morphism from `W₁.arrow` to `W₂.arrow` that is induced by
`Φ : LocalizerMorphism W₁ W₂`. -/
@[simps]
def arrow : LocalizerMorphism W₁.arrow W₂.arrow where
  functor := Φ.functor.mapArrow
  map _ _ _ hf := ⟨Φ.map _ hf.1, Φ.map _ hf.2⟩

end LocalizerMorphism

end CategoryTheory
