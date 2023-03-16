/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module category_theory.localization.predicate
! leanprover-community/mathlib commit 8efef279998820353694feb6ff5631ed0d309ecc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Localization.Construction

/-!

# Predicate for localized categories

In this file, a predicate `L.is_localization W` is introduced for a functor `L : C ⥤ D`
and `W : morphism_property C`: it expresses that `L` identifies `D` with the localized
category of `C` with respect to `W` (up to equivalence).

We introduce a universal property `strict_universal_property_fixed_target L W E` which
states that `L` inverts the morphisms in `W` and that all functors `C ⥤ E` inverting
`W` uniquely factors as a composition of `L ⋙ G` with `G : D ⥤ E`. Such universal
properties are inputs for the constructor `is_localization.mk'` for `L.is_localization W`.

When `L : C ⥤ D` is a localization functor for `W : morphism_property` (i.e. when
`[L.is_localization W]` holds), for any category `E`, there is
an equivalence `functor_equivalence L W E : (D ⥤ E) ≌ (W.functors_inverting E)`
that is induced by the composition with the functor `L`. When two functors
`F : C ⥤ E` and `F' : D ⥤ E` correspond via this equivalence, we shall say
that `F'` lifts `F`, and the associated isomorphism `L ⋙ F' ≅ F` is the
datum that is part of the class `lifting L W F F'`. The functions
`lift_nat_trans` and `lift_nat_iso` can be used to lift natural transformations
and natural isomorphisms between functors.

-/


noncomputable section

namespace CategoryTheory

open Category

variable {C D : Type _} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C) (E : Type _)
  [Category E]

namespace Functor

/-- The predicate expressing that, up to equivalence, a functor `L : C ⥤ D`
identifies the category `D` with the localized category of `C` with respect
to `W : morphism_property C`. -/
class IsLocalization : Prop where
  inverts : W.IsInvertedBy L
  nonempty_isEquivalence : Nonempty (IsEquivalence (Localization.Construction.lift L inverts))
#align category_theory.functor.is_localization CategoryTheory.Functor.IsLocalization

instance q_isLocalization : W.q.IsLocalization W
    where
  inverts := W.q_inverts
  nonempty_isEquivalence :=
    by
    suffices localization.construction.lift W.Q W.Q_inverts = 𝟭 _
      by
      apply Nonempty.intro
      rw [this]
      infer_instance
    apply localization.construction.uniq
    simpa only [localization.construction.fac]
#align category_theory.functor.Q_is_localization CategoryTheory.Functor.q_isLocalization

end Functor

namespace Localization

/-- This universal property states that a functor `L : C ⥤ D` inverts morphisms
in `W` and the all functors `D ⥤ E` (for a fixed category `E`) uniquely factors
through `L`. -/
structure StrictUniversalPropertyFixedTarget where
  inverts : W.IsInvertedBy L
  lift : ∀ (F : C ⥤ E) (hF : W.IsInvertedBy F), D ⥤ E
  fac : ∀ (F : C ⥤ E) (hF : W.IsInvertedBy F), L ⋙ lift F hF = F
  uniq : ∀ (F₁ F₂ : D ⥤ E) (h : L ⋙ F₁ = L ⋙ F₂), F₁ = F₂
#align category_theory.localization.strict_universal_property_fixed_target CategoryTheory.Localization.StrictUniversalPropertyFixedTarget

/-- The localized category `W.localization` that was constructed satisfies
the universal property of the localization. -/
@[simps]
def strictUniversalPropertyFixedTargetQ : StrictUniversalPropertyFixedTarget W.q W E
    where
  inverts := W.q_inverts
  lift := Construction.lift
  fac := Construction.fac
  uniq := Construction.uniq
#align category_theory.localization.strict_universal_property_fixed_target_Q CategoryTheory.Localization.strictUniversalPropertyFixedTargetQ

instance : Inhabited (StrictUniversalPropertyFixedTarget W.q W E) :=
  ⟨strictUniversalPropertyFixedTargetQ _ _⟩

/-- When `W` consists of isomorphisms, the identity satisfies the universal property
of the localization. -/
@[simps]
def strictUniversalPropertyFixedTargetId (hW : W ⊆ MorphismProperty.isomorphisms C) :
    StrictUniversalPropertyFixedTarget (𝟭 C) W E
    where
  inverts X Y f hf := hW f hf
  lift F hF := F
  fac F hF := by
    cases F
    rfl
  uniq F₁ F₂ eq := by
    cases F₁
    cases F₂
    exact Eq
#align category_theory.localization.strict_universal_property_fixed_target_id CategoryTheory.Localization.strictUniversalPropertyFixedTargetId

end Localization

namespace Functor

theorem IsLocalization.mk' (h₁ : Localization.StrictUniversalPropertyFixedTarget L W D)
    (h₂ : Localization.StrictUniversalPropertyFixedTarget L W W.Localization) :
    IsLocalization L W :=
  { inverts := h₁.inverts
    nonempty_isEquivalence :=
      Nonempty.intro
        { inverse := h₂.lift W.q W.q_inverts
          unitIso :=
            eqToIso
              (Localization.Construction.uniq _ _
                (by
                  simp only [← functor.assoc, localization.construction.fac, h₂.fac,
                    functor.comp_id]))
          counitIso :=
            eqToIso
              (h₁.uniq _ _
                (by
                  simp only [← functor.assoc, h₂.fac, localization.construction.fac,
                    functor.comp_id]))
          functor_unitIso_comp' := fun X => by
            simpa only [eq_to_iso.hom, eq_to_hom_app, eq_to_hom_map, eq_to_hom_trans,
              eq_to_hom_refl] } }
#align category_theory.functor.is_localization.mk' CategoryTheory.Functor.IsLocalization.mk'

theorem IsLocalization.for_id (hW : W ⊆ MorphismProperty.isomorphisms C) : (𝟭 C).IsLocalization W :=
  IsLocalization.mk' _ _ (Localization.strictUniversalPropertyFixedTargetId W _ hW)
    (Localization.strictUniversalPropertyFixedTargetId W _ hW)
#align category_theory.functor.is_localization.for_id CategoryTheory.Functor.IsLocalization.for_id

end Functor

namespace Localization

variable [L.IsLocalization W]

theorem inverts : W.IsInvertedBy L :=
  (inferInstance : L.IsLocalization W).inverts
#align category_theory.localization.inverts CategoryTheory.Localization.inverts

/-- The isomorphism `L.obj X ≅ L.obj Y` that is deduced from a morphism `f : X ⟶ Y` which
belongs to `W`, when `L.is_localization W`. -/
@[simps]
def isoOfHom {X Y : C} (f : X ⟶ Y) (hf : W f) : L.obj X ≅ L.obj Y :=
  haveI : is_iso (L.map f) := inverts L W f hf
  as_iso (L.map f)
#align category_theory.localization.iso_of_hom CategoryTheory.Localization.isoOfHom

instance : IsEquivalence (Localization.Construction.lift L (inverts L W)) :=
  (inferInstance : L.IsLocalization W).nonempty_isEquivalence.some

/-- A chosen equivalence of categories `W.localization ≅ D` for a functor
`L : C ⥤ D` which satisfies `L.is_localization W`. This shall be used in
order to deduce properties of `L` from properties of `W.Q`. -/
def equivalenceFromModel : W.Localization ≌ D :=
  (Localization.Construction.lift L (inverts L W)).asEquivalence
#align category_theory.localization.equivalence_from_model CategoryTheory.Localization.equivalenceFromModel

/-- Via the equivalence of categories `equivalence_from_model L W : W.localization ≌ D`,
one may identify the functors `W.Q` and `L`. -/
def qCompEquivalenceFromModelFunctorIso : W.q ⋙ (equivalenceFromModel L W).Functor ≅ L :=
  eqToIso (Construction.fac _ _)
#align category_theory.localization.Q_comp_equivalence_from_model_functor_iso CategoryTheory.Localization.qCompEquivalenceFromModelFunctorIso

/-- Via the equivalence of categories `equivalence_from_model L W : W.localization ≌ D`,
one may identify the functors `L` and `W.Q`. -/
def compEquivalenceFromModelInverseIso : L ⋙ (equivalenceFromModel L W).inverse ≅ W.q :=
  calc
    L ⋙ (equivalenceFromModel L W).inverse ≅ _ :=
      isoWhiskerRight (qCompEquivalenceFromModelFunctorIso L W).symm _
    _ ≅ W.q ⋙ (equivalenceFromModel L W).Functor ⋙ (equivalenceFromModel L W).inverse :=
      (Functor.associator _ _ _)
    _ ≅ W.q ⋙ 𝟭 _ := (isoWhiskerLeft _ (equivalenceFromModel L W).unitIso.symm)
    _ ≅ W.q := Functor.rightUnitor _
    
#align category_theory.localization.comp_equivalence_from_model_inverse_iso CategoryTheory.Localization.compEquivalenceFromModelInverseIso

theorem essSurj : EssSurj L :=
  ⟨fun X =>
    ⟨(Construction.objEquiv W).invFun ((equivalenceFromModel L W).inverse.obj X),
      Nonempty.intro
        ((qCompEquivalenceFromModelFunctorIso L W).symm.app _ ≪≫
          (equivalenceFromModel L W).counitIso.app X)⟩⟩
#align category_theory.localization.ess_surj CategoryTheory.Localization.essSurj

/-- The functor `(D ⥤ E) ⥤ W.functors_inverting E` induced by the composition
with a localization functor `L : C ⥤ D` with respect to `W : morphism_property C`. -/
def whiskeringLeftFunctor : (D ⥤ E) ⥤ W.FunctorsInverting E :=
  FullSubcategory.lift _ ((whiskeringLeft _ _ E).obj L)
    (MorphismProperty.IsInvertedBy.of_comp W L (inverts L W))
#align category_theory.localization.whiskering_left_functor CategoryTheory.Localization.whiskeringLeftFunctor

instance : IsEquivalence (whiskeringLeftFunctor L W E) :=
  by
  refine'
    is_equivalence.of_iso _
      (is_equivalence.of_equivalence
        ((equivalence.congr_left (equivalence_from_model L W).symm).trans
          (construction.whiskering_left_equivalence W E)))
  refine'
    nat_iso.of_components
      (fun F =>
        eq_to_iso
          (by
            ext
            change (W.Q ⋙ localization.construction.lift L (inverts L W)) ⋙ F = L ⋙ F
            rw [construction.fac]))
      fun F₁ F₂ τ => by
      ext X
      dsimp [equivalence_from_model, whisker_left, construction.whiskering_left_equivalence,
        construction.whiskering_left_equivalence.functor, whiskering_left_functor,
        morphism_property.Q]
      erw [nat_trans.comp_app, nat_trans.comp_app, eq_to_hom_app, eq_to_hom_app, eq_to_hom_refl,
        eq_to_hom_refl, comp_id, id_comp]
      all_goals
        change (W.Q ⋙ localization.construction.lift L (inverts L W)) ⋙ _ = L ⋙ _
        rw [construction.fac]

/-- The equivalence of categories `(D ⥤ E) ≌ (W.functors_inverting E)` induced by
the composition with a localization functor `L : C ⥤ D` with respect to
`W : morphism_property C`. -/
def functorEquivalence : D ⥤ E ≌ W.FunctorsInverting E :=
  (whiskeringLeftFunctor L W E).asEquivalence
#align category_theory.localization.functor_equivalence CategoryTheory.Localization.functorEquivalence

include W

/-- The functor `(D ⥤ E) ⥤ (C ⥤ E)` given by the composition with a localization
functor `L : C ⥤ D` with respect to `W : morphism_property C`. -/
@[nolint unused_arguments]
def whiskeringLeftFunctor' : (D ⥤ E) ⥤ C ⥤ E :=
  (whiskeringLeft C D E).obj L
#align category_theory.localization.whiskering_left_functor' CategoryTheory.Localization.whiskeringLeftFunctor'

theorem whiskeringLeftFunctor'_eq :
    whiskeringLeftFunctor' L W E = Localization.whiskeringLeftFunctor L W E ⋙ inducedFunctor _ :=
  rfl
#align category_theory.localization.whiskering_left_functor'_eq CategoryTheory.Localization.whiskeringLeftFunctor'_eq

variable {E}

@[simp]
theorem whiskeringLeftFunctor'_obj (F : D ⥤ E) : (whiskeringLeftFunctor' L W E).obj F = L ⋙ F :=
  rfl
#align category_theory.localization.whiskering_left_functor'_obj CategoryTheory.Localization.whiskeringLeftFunctor'_obj

instance : Full (whiskeringLeftFunctor' L W E) :=
  by
  rw [whiskering_left_functor'_eq]
  infer_instance

instance : Faithful (whiskeringLeftFunctor' L W E) :=
  by
  rw [whiskering_left_functor'_eq]
  infer_instance

theorem nat_trans_ext {F₁ F₂ : D ⥤ E} (τ τ' : F₁ ⟶ F₂)
    (h : ∀ X : C, τ.app (L.obj X) = τ'.app (L.obj X)) : τ = τ' :=
  by
  haveI : CategoryTheory.EssSurj L := ess_surj L W
  ext Y
  rw [← cancel_epi (F₁.map (L.obj_obj_preimage_iso Y).Hom), τ.naturality, τ'.naturality, h]
#align category_theory.localization.nat_trans_ext CategoryTheory.Localization.nat_trans_ext

/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`Iso] [] -/
/-- When `L : C ⥤ D` is a localization functor for `W : morphism_property C` and
`F : C ⥤ E` is a functor, we shall say that `F' : D ⥤ E` lifts `F` if the obvious diagram
is commutative up to an isomorphism. -/
class Lifting (F : C ⥤ E) (F' : D ⥤ E) where
  Iso : L ⋙ F' ≅ F
#align category_theory.localization.lifting CategoryTheory.Localization.Lifting

variable {W}

/-- Given a localization functor `L : C ⥤ D` for `W : morphism_property C` and
a functor `F : C ⥤ E` which inverts `W`, this is a choice of functor
`D ⥤ E` which lifts `F`. -/
def lift (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [hL : L.IsLocalization W] : D ⥤ E :=
  (functorEquivalence L W E).inverse.obj ⟨F, hF⟩
#align category_theory.localization.lift CategoryTheory.Localization.lift

instance liftingLift (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [hL : L.IsLocalization W] :
    Lifting L W F (lift F hF L) :=
  ⟨(inducedFunctor _).mapIso ((functorEquivalence L W E).counitIso.app ⟨F, hF⟩)⟩
#align category_theory.localization.lifting_lift CategoryTheory.Localization.liftingLift

/-- The canonical isomorphism `L ⋙ lift F hF L ≅ F` for any functor `F : C ⥤ E`
which inverts `W`, when `L : C ⥤ D` is a localization functor for `W`. -/
@[simps]
def fac (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [hL : L.IsLocalization W] :
    L ⋙ lift F hF L ≅ F :=
  Lifting.iso _ W _ _
#align category_theory.localization.fac CategoryTheory.Localization.fac

instance liftingConstructionLift (F : C ⥤ D) (hF : W.IsInvertedBy F) :
    Lifting W.q W F (Construction.lift F hF) :=
  ⟨eqToIso (Construction.fac F hF)⟩
#align category_theory.localization.lifting_construction_lift CategoryTheory.Localization.liftingConstructionLift

variable (W)

/-- Given a localization functor `L : C ⥤ D` for `W : morphism_property C`,
if `(F₁' F₂' : D ⥤ E)` are functors which lifts functors `(F₁ F₂ : C ⥤ E)`,
a natural transformation `τ : F₁ ⟶ F₂` uniquely lifts to a natural transformation `F₁' ⟶ F₂'`. -/
def liftNatTrans (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [h₂ : Lifting L W F₂ F₂']
    (τ : F₁ ⟶ F₂) : F₁' ⟶ F₂' :=
  (whiskeringLeftFunctor' L W E).preimage
    ((Lifting.iso L W F₁ F₁').Hom ≫ τ ≫ (Lifting.iso L W F₂ F₂').inv)
#align category_theory.localization.lift_nat_trans CategoryTheory.Localization.liftNatTrans

@[simp]
theorem liftNatTrans_app (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    (τ : F₁ ⟶ F₂) (X : C) :
    (liftNatTrans L W F₁ F₂ F₁' F₂' τ).app (L.obj X) =
      (Lifting.iso L W F₁ F₁').Hom.app X ≫ τ.app X ≫ (Lifting.iso L W F₂ F₂').inv.app X :=
  congr_app (Functor.image_preimage (whiskeringLeftFunctor' L W E) _) X
#align category_theory.localization.lift_nat_trans_app CategoryTheory.Localization.liftNatTrans_app

@[simp, reassoc.1]
theorem comp_liftNatTrans (F₁ F₂ F₃ : C ⥤ E) (F₁' F₂' F₃' : D ⥤ E) [h₁ : Lifting L W F₁ F₁']
    [h₂ : Lifting L W F₂ F₂'] [h₃ : Lifting L W F₃ F₃'] (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) :
    liftNatTrans L W F₁ F₂ F₁' F₂' τ ≫ liftNatTrans L W F₂ F₃ F₂' F₃' τ' =
      liftNatTrans L W F₁ F₃ F₁' F₃' (τ ≫ τ') :=
  nat_trans_ext L W _ _ fun X => by
    simp only [nat_trans.comp_app, lift_nat_trans_app, assoc, iso.inv_hom_id_app_assoc]
#align category_theory.localization.comp_lift_nat_trans CategoryTheory.Localization.comp_liftNatTrans

@[simp]
theorem liftNatTrans_id (F : C ⥤ E) (F' : D ⥤ E) [h : Lifting L W F F'] :
    liftNatTrans L W F F F' F' (𝟙 F) = 𝟙 F' :=
  nat_trans_ext L W _ _ fun X => by
    simpa only [lift_nat_trans_app, nat_trans.id_app, id_comp, iso.hom_inv_id_app]
#align category_theory.localization.lift_nat_trans_id CategoryTheory.Localization.liftNatTrans_id

/-- Given a localization functor `L : C ⥤ D` for `W : morphism_property C`,
if `(F₁' F₂' : D ⥤ E)` are functors which lifts functors `(F₁ F₂ : C ⥤ E)`,
a natural isomorphism `τ : F₁ ⟶ F₂` lifts to a natural isomorphism `F₁' ⟶ F₂'`. -/
@[simps]
def liftNatIso (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [h₁ : Lifting L W F₁ F₁'] [h₂ : Lifting L W F₂ F₂']
    (e : F₁ ≅ F₂) : F₁' ≅ F₂'
    where
  Hom := liftNatTrans L W F₁ F₂ F₁' F₂' e.Hom
  inv := liftNatTrans L W F₂ F₁ F₂' F₁' e.inv
#align category_theory.localization.lift_nat_iso CategoryTheory.Localization.liftNatIso

namespace Lifting

@[simps]
instance compRight {E' : Type _} [Category E'] (F : C ⥤ E) (F' : D ⥤ E) [Lifting L W F F']
    (G : E ⥤ E') : Lifting L W (F ⋙ G) (F' ⋙ G) :=
  ⟨isoWhiskerRight (iso L W F F') G⟩
#align category_theory.localization.lifting.comp_right CategoryTheory.Localization.Lifting.compRight

@[simps]
instance id : Lifting L W L (𝟭 D) :=
  ⟨Functor.rightUnitor L⟩
#align category_theory.localization.lifting.id CategoryTheory.Localization.Lifting.id

/-- Given a localization functor `L : C ⥤ D` for `W : morphism_property C`,
if `F₁' : D ⥤ E` lifts a functor `F₁ : C ⥤ D`, then a functor `F₂'` which
is isomorphic to `F₁'` also lifts a functor `F₂` that is isomorphic to `F₁`.  -/
@[simps]
def ofIsos {F₁ F₂ : C ⥤ E} {F₁' F₂' : D ⥤ E} (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') [Lifting L W F₁ F₁'] :
    Lifting L W F₂ F₂' :=
  ⟨isoWhiskerLeft L e'.symm ≪≫ iso L W F₁ F₁' ≪≫ e⟩
#align category_theory.localization.lifting.of_isos CategoryTheory.Localization.Lifting.ofIsos

end Lifting

end Localization

namespace Functor

namespace IsLocalization

open Localization

theorem of_iso {L₁ L₂ : C ⥤ D} (e : L₁ ≅ L₂) [L₁.IsLocalization W] : L₂.IsLocalization W :=
  by
  have h := localization.inverts L₁ W
  rw [morphism_property.is_inverted_by.iff_of_iso W e] at h
  let F₁ := localization.construction.lift L₁ (localization.inverts L₁ W)
  let F₂ := localization.construction.lift L₂ h
  exact
    { inverts := h
      nonempty_isEquivalence :=
        Nonempty.intro (is_equivalence.of_iso (lift_nat_iso W.Q W L₁ L₂ F₁ F₂ e) inferInstance) }
#align category_theory.functor.is_localization.of_iso CategoryTheory.Functor.IsLocalization.of_iso

/-- If `L : C ⥤ D` is a localization for `W : morphism_property C`, then it is also
the case of a functor obtained by post-composing `L` with an equivalence of categories. -/
theorem of_equivalence_target {E : Type _} [Category E] (L' : C ⥤ E) (eq : D ≌ E)
    [L.IsLocalization W] (e : L ⋙ Eq.Functor ≅ L') : L'.IsLocalization W :=
  by
  have h : W.is_inverted_by L' :=
    by
    rw [← morphism_property.is_inverted_by.iff_of_iso W e]
    exact morphism_property.is_inverted_by.of_comp W L (localization.inverts L W) eq.functor
  let F₁ := localization.construction.lift L (localization.inverts L W)
  let F₂ := localization.construction.lift L' h
  let e' : F₁ ⋙ eq.functor ≅ F₂ := lift_nat_iso W.Q W (L ⋙ eq.functor) L' _ _ e
  exact
    { inverts := h
      nonempty_isEquivalence := Nonempty.intro (is_equivalence.of_iso e' inferInstance) }
#align category_theory.functor.is_localization.of_equivalence_target CategoryTheory.Functor.IsLocalization.of_equivalence_target

end IsLocalization

end Functor

end CategoryTheory

