/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.Construction

/-!

# Predicate for localized categories

In this file, a predicate `L.IsLocalization W` is introduced for a functor `L : C ⥤ D`
and `W : MorphismProperty C`: it expresses that `L` identifies `D` with the localized
category of `C` with respect to `W` (up to equivalence).

We introduce a universal property `StrictUniversalPropertyFixedTarget L W E` which
states that `L` inverts the morphisms in `W` and that all functors `C ⥤ E` inverting
`W` uniquely factors as a composition of `L ⋙ G` with `G : D ⥤ E`. Such universal
properties are inputs for the constructor `IsLocalization.mk'` for `L.IsLocalization W`.

When `L : C ⥤ D` is a localization functor for `W : MorphismProperty` (i.e. when
`[L.IsLocalization W]` holds), for any category `E`, there is
an equivalence `FunctorEquivalence L W E : (D ⥤ E) ≌ (W.FunctorsInverting E)`
that is induced by the composition with the functor `L`. When two functors
`F : C ⥤ E` and `F' : D ⥤ E` correspond via this equivalence, we shall say
that `F'` lifts `F`, and the associated isomorphism `L ⋙ F' ≅ F` is the
datum that is part of the class `Lifting L W F F'`. The functions
`liftNatTrans` and `liftNatIso` can be used to lift natural transformations
and natural isomorphisms between functors.

-/


noncomputable section

namespace CategoryTheory

open Category Functor

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C) (E : Type*)
  [Category E]

namespace Functor

/-- The predicate expressing that, up to equivalence, a functor `L : C ⥤ D`
identifies the category `D` with the localized category of `C` with respect
to `W : MorphismProperty C`. -/
class IsLocalization : Prop where
  /-- the functor inverts the given `MorphismProperty` -/
  inverts : W.IsInvertedBy L
  /-- the induced functor from the constructed localized category is an equivalence -/
  isEquivalence : IsEquivalence (Localization.Construction.lift L inverts)

instance q_isLocalization : W.Q.IsLocalization W where
  inverts := W.Q_inverts
  isEquivalence := by
    suffices Localization.Construction.lift W.Q W.Q_inverts = 𝟭 _ by
      rw [this]
      infer_instance
    apply Localization.Construction.uniq
    simp only [Localization.Construction.fac]
    rfl

end Functor

namespace Localization

/-- This universal property states that a functor `L : C ⥤ D` inverts morphisms
in `W` and the all functors `D ⥤ E` (for a fixed category `E`) uniquely factors
through `L`. -/
structure StrictUniversalPropertyFixedTarget where
  /-- the functor `L` inverts `W` -/
  inverts : W.IsInvertedBy L
  /-- any functor `C ⥤ E` which inverts `W` can be lifted as a functor `D ⥤ E` -/
  lift : ∀ (F : C ⥤ E) (_ : W.IsInvertedBy F), D ⥤ E
  /-- there is a factorisation involving the lifted functor -/
  fac : ∀ (F : C ⥤ E) (hF : W.IsInvertedBy F), L ⋙ lift F hF = F
  /-- uniqueness of the lifted functor -/
  uniq : ∀ (F₁ F₂ : D ⥤ E) (_ : L ⋙ F₁ = L ⋙ F₂), F₁ = F₂

/-- The localized category `W.Localization` that was constructed satisfies
the universal property of the localization. -/
@[simps]
def strictUniversalPropertyFixedTargetQ : StrictUniversalPropertyFixedTarget W.Q W E where
  inverts := W.Q_inverts
  lift := Construction.lift
  fac := Construction.fac
  uniq := Construction.uniq

instance : Inhabited (StrictUniversalPropertyFixedTarget W.Q W E) :=
  ⟨strictUniversalPropertyFixedTargetQ _ _⟩

/-- When `W` consists of isomorphisms, the identity satisfies the universal property
of the localization. -/
@[simps]
def strictUniversalPropertyFixedTargetId (hW : W ≤ MorphismProperty.isomorphisms C) :
    StrictUniversalPropertyFixedTarget (𝟭 C) W E where
  inverts _ _ f hf := hW f hf
  lift F _ := F
  fac F hF := by
    cases F
    rfl
  uniq F₁ F₂ eq := by
    cases F₁
    cases F₂
    exact eq

end Localization

namespace Functor

theorem IsLocalization.mk' (h₁ : Localization.StrictUniversalPropertyFixedTarget L W D)
    (h₂ : Localization.StrictUniversalPropertyFixedTarget L W W.Localization) :
    IsLocalization L W :=
  { inverts := h₁.inverts
    isEquivalence := IsEquivalence.mk' (h₂.lift W.Q W.Q_inverts)
      (eqToIso (Localization.Construction.uniq _ _ (by
        simp only [← Functor.assoc, Localization.Construction.fac, h₂.fac, Functor.comp_id])))
      (eqToIso (h₁.uniq _ _ (by
        simp only [← Functor.assoc, h₂.fac, Localization.Construction.fac, Functor.comp_id]))) }

theorem IsLocalization.for_id (hW : W ≤ MorphismProperty.isomorphisms C) : (𝟭 C).IsLocalization W :=
  IsLocalization.mk' _ _ (Localization.strictUniversalPropertyFixedTargetId W _ hW)
    (Localization.strictUniversalPropertyFixedTargetId W _ hW)

end Functor

namespace Localization

variable [L.IsLocalization W]

theorem inverts : W.IsInvertedBy L :=
  (inferInstance : L.IsLocalization W).inverts

/-- The isomorphism `L.obj X ≅ L.obj Y` that is deduced from a morphism `f : X ⟶ Y` which
belongs to `W`, when `L.IsLocalization W`. -/
@[simps! hom]
def isoOfHom {X Y : C} (f : X ⟶ Y) (hf : W f) : L.obj X ≅ L.obj Y :=
  haveI : IsIso (L.map f) := inverts L W f hf
  asIso (L.map f)

@[reassoc (attr := simp)]
lemma isoOfHom_hom_inv_id {X Y : C} (f : X ⟶ Y) (hf : W f) :
    L.map f ≫ (isoOfHom L W f hf).inv = 𝟙 _ :=
  (isoOfHom L W f hf).hom_inv_id

@[reassoc (attr := simp)]
lemma isoOfHom_inv_hom_id {X Y : C} (f : X ⟶ Y) (hf : W f) :
    (isoOfHom L W f hf).inv ≫ L.map f = 𝟙 _ :=
  (isoOfHom L W f hf).inv_hom_id

@[simp]
lemma isoOfHom_id_inv (X : C) (hX : W (𝟙 X)) :
    (isoOfHom L W (𝟙 X) hX).inv = 𝟙 _ := by
  rw [← cancel_mono (isoOfHom L W (𝟙 X) hX).hom, Iso.inv_hom_id, id_comp,
    isoOfHom_hom, Functor.map_id]

variable {W}

lemma Construction.wIso_eq_isoOfHom {X Y : C} (f : X ⟶ Y) (hf : W f) :
    Construction.wIso f hf = isoOfHom W.Q W f hf := by ext; rfl

lemma Construction.wInv_eq_isoOfHom_inv {X Y : C} (f : X ⟶ Y) (hf : W f) :
    Construction.wInv f hf = (isoOfHom W.Q W f hf).inv :=
  congr_arg Iso.inv (wIso_eq_isoOfHom f hf)

instance : (Localization.Construction.lift L (inverts L W)).IsEquivalence :=
  (inferInstance : L.IsLocalization W).isEquivalence

variable (W)

/-- A chosen equivalence of categories `W.Localization ≅ D` for a functor
`L : C ⥤ D` which satisfies `L.IsLocalization W`. This shall be used in
order to deduce properties of `L` from properties of `W.Q`. -/
def equivalenceFromModel : W.Localization ≌ D :=
  (Localization.Construction.lift L (inverts L W)).asEquivalence

/-- Via the equivalence of categories `equivalence_from_model L W : W.localization ≌ D`,
one may identify the functors `W.Q` and `L`. -/
def qCompEquivalenceFromModelFunctorIso : W.Q ⋙ (equivalenceFromModel L W).functor ≅ L :=
  eqToIso (Construction.fac _ _)

/-- Via the equivalence of categories `equivalence_from_model L W : W.localization ≌ D`,
one may identify the functors `L` and `W.Q`. -/
def compEquivalenceFromModelInverseIso : L ⋙ (equivalenceFromModel L W).inverse ≅ W.Q :=
  calc
    L ⋙ (equivalenceFromModel L W).inverse ≅ _ :=
      isoWhiskerRight (qCompEquivalenceFromModelFunctorIso L W).symm _
    _ ≅ W.Q ⋙ (equivalenceFromModel L W).functor ⋙ (equivalenceFromModel L W).inverse :=
      (associator _ _ _)
    _ ≅ W.Q ⋙ 𝟭 _ := isoWhiskerLeft _ (equivalenceFromModel L W).unitIso.symm
    _ ≅ W.Q := rightUnitor _

theorem essSurj (W) [L.IsLocalization W] : L.EssSurj :=
  ⟨fun X =>
    ⟨(Construction.objEquiv W).invFun ((equivalenceFromModel L W).inverse.obj X),
      Nonempty.intro
        ((qCompEquivalenceFromModelFunctorIso L W).symm.app _ ≪≫
          (equivalenceFromModel L W).counitIso.app X)⟩⟩

/-- The functor `(D ⥤ E) ⥤ W.functors_inverting E` induced by the composition
with a localization functor `L : C ⥤ D` with respect to `W : morphism_property C`. -/
def whiskeringLeftFunctor : (D ⥤ E) ⥤ W.FunctorsInverting E :=
  ObjectProperty.lift _ ((whiskeringLeft _ _ E).obj L)
    (MorphismProperty.IsInvertedBy.of_comp W L (inverts L W))

instance : (whiskeringLeftFunctor L W E).IsEquivalence := by
  let iso : (whiskeringLeft (MorphismProperty.Localization W) D E).obj
    (equivalenceFromModel L W).functor ⋙
      (Construction.whiskeringLeftEquivalence W E).functor ≅ whiskeringLeftFunctor L W E :=
    NatIso.ofComponents (fun F => eqToIso (by
      ext
      change (W.Q ⋙ Localization.Construction.lift L (inverts L W)) ⋙ F = L ⋙ F
      rw [Construction.fac])) (fun τ => by
        ext
        dsimp [Construction.whiskeringLeftEquivalence, equivalenceFromModel, whiskerLeft]
        erw [NatTrans.comp_app, NatTrans.comp_app, eqToHom_app, eqToHom_app, eqToHom_refl,
          eqToHom_refl, comp_id, id_comp]
        · rfl
        all_goals
          change (W.Q ⋙ Localization.Construction.lift L (inverts L W)) ⋙ _ = L ⋙ _
          rw [Construction.fac])
  exact Functor.isEquivalence_of_iso iso

/-- The equivalence of categories `(D ⥤ E) ≌ (W.FunctorsInverting E)` induced by
the composition with a localization functor `L : C ⥤ D` with respect to
`W : MorphismProperty C`. -/
def functorEquivalence : D ⥤ E ≌ W.FunctorsInverting E :=
  (whiskeringLeftFunctor L W E).asEquivalence

/-- The functor `(D ⥤ E) ⥤ (C ⥤ E)` given by the composition with a localization
functor `L : C ⥤ D` with respect to `W : MorphismProperty C`. -/
@[nolint unusedArguments]
def whiskeringLeftFunctor' [L.IsLocalization W] (E : Type*) [Category E] :
    (D ⥤ E) ⥤ C ⥤ E :=
  (whiskeringLeft C D E).obj L

theorem whiskeringLeftFunctor'_eq :
    whiskeringLeftFunctor' L W E = Localization.whiskeringLeftFunctor L W E ⋙ inducedFunctor _ :=
  rfl

variable {E} in
@[simp]
theorem whiskeringLeftFunctor'_obj (F : D ⥤ E) : (whiskeringLeftFunctor' L W E).obj F = L ⋙ F :=
  rfl

instance : (whiskeringLeftFunctor' L W E).Full := by
  rw [whiskeringLeftFunctor'_eq]
  apply @Functor.Full.comp _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  apply InducedCategory.full -- why is it not found automatically ???

instance : (whiskeringLeftFunctor' L W E).Faithful := by
  rw [whiskeringLeftFunctor'_eq]
  apply @Functor.Faithful.comp _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  apply InducedCategory.faithful -- why is it not found automatically ???

lemma full_whiskeringLeft (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category E] :
    ((whiskeringLeft C D E).obj L).Full :=
  inferInstanceAs (whiskeringLeftFunctor' L W E).Full

lemma faithful_whiskeringLeft (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category E] :
    ((whiskeringLeft C D E).obj L).Faithful :=
  inferInstanceAs (whiskeringLeftFunctor' L W E).Faithful

variable {E}

theorem natTrans_ext (L : C ⥤ D) (W) [L.IsLocalization W] {F₁ F₂ : D ⥤ E} {τ τ' : F₁ ⟶ F₂}
    (h : ∀ X : C, τ.app (L.obj X) = τ'.app (L.obj X)) : τ = τ' := by
  haveI := essSurj L W
  ext Y
  rw [← cancel_epi (F₁.map (L.objObjPreimageIso Y).hom), τ.naturality, τ'.naturality, h]

-- Porting note: the field `iso` was renamed `Lifting.iso'` and it was redefined as
-- `Lifting.iso` with explicit parameters
/-- When `L : C ⥤ D` is a localization functor for `W : MorphismProperty C` and
`F : C ⥤ E` is a functor, we shall say that `F' : D ⥤ E` lifts `F` if the obvious diagram
is commutative up to an isomorphism. -/
class Lifting (W : MorphismProperty C) (F : C ⥤ E) (F' : D ⥤ E) where
  /-- the isomorphism relating the localization functor and the two other given functors -/
  iso' : L ⋙ F' ≅ F

/-- The distinguished isomorphism `L ⋙ F' ≅ F` given by `[Lifting L W F F']`. -/
def Lifting.iso (F : C ⥤ E) (F' : D ⥤ E) [Lifting L W F F'] :
    L ⋙ F' ≅ F :=
  Lifting.iso' W

variable {W}

/-- Given a localization functor `L : C ⥤ D` for `W : MorphismProperty C` and
a functor `F : C ⥤ E` which inverts `W`, this is a choice of functor
`D ⥤ E` which lifts `F`. -/
def lift (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W] : D ⥤ E :=
  (functorEquivalence L W E).inverse.obj ⟨F, hF⟩

instance liftingLift (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W] :
    Lifting L W F (lift F hF L) :=
  ⟨(inducedFunctor _).mapIso ((functorEquivalence L W E).counitIso.app ⟨F, hF⟩)⟩

-- Porting note: removed the unnecessary @[simps] attribute
/-- The canonical isomorphism `L ⋙ lift F hF L ≅ F` for any functor `F : C ⥤ E`
which inverts `W`, when `L : C ⥤ D` is a localization functor for `W`. -/
def fac (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W] :
    L ⋙ lift F hF L ≅ F :=
  Lifting.iso L W F _

instance liftingConstructionLift (F : C ⥤ D) (hF : W.IsInvertedBy F) :
    Lifting W.Q W F (Construction.lift F hF) :=
  ⟨eqToIso (Construction.fac F hF)⟩

variable (W)

/-- Given a localization functor `L : C ⥤ D` for `W : MorphismProperty C`,
if `(F₁' F₂' : D ⥤ E)` are functors which lifts functors `(F₁ F₂ : C ⥤ E)`,
a natural transformation `τ : F₁ ⟶ F₂` uniquely lifts to a natural transformation `F₁' ⟶ F₂'`. -/
def liftNatTrans (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    (τ : F₁ ⟶ F₂) : F₁' ⟶ F₂' :=
  (whiskeringLeftFunctor' L W E).preimage
    ((Lifting.iso L W F₁ F₁').hom ≫ τ ≫ (Lifting.iso L W F₂ F₂').inv)

@[simp]
theorem liftNatTrans_app (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    (τ : F₁ ⟶ F₂) (X : C) :
    (liftNatTrans L W F₁ F₂ F₁' F₂' τ).app (L.obj X) =
      (Lifting.iso L W F₁ F₁').hom.app X ≫ τ.app X ≫ (Lifting.iso L W F₂ F₂').inv.app X :=
  congr_app (Functor.map_preimage (whiskeringLeftFunctor' L W E) _) X

@[reassoc (attr := simp)]
theorem comp_liftNatTrans (F₁ F₂ F₃ : C ⥤ E) (F₁' F₂' F₃' : D ⥤ E) [h₁ : Lifting L W F₁ F₁']
    [h₂ : Lifting L W F₂ F₂'] [h₃ : Lifting L W F₃ F₃'] (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) :
    liftNatTrans L W F₁ F₂ F₁' F₂' τ ≫ liftNatTrans L W F₂ F₃ F₂' F₃' τ' =
      liftNatTrans L W F₁ F₃ F₁' F₃' (τ ≫ τ') :=
  natTrans_ext L W fun X => by
    simp only [NatTrans.comp_app, liftNatTrans_app, assoc, Iso.inv_hom_id_app_assoc]

@[simp]
theorem liftNatTrans_id (F : C ⥤ E) (F' : D ⥤ E) [h : Lifting L W F F'] :
    liftNatTrans L W F F F' F' (𝟙 F) = 𝟙 F' :=
  natTrans_ext L W fun X => by
    simp only [liftNatTrans_app, NatTrans.id_app, id_comp, Iso.hom_inv_id_app]
    rfl

/-- Given a localization functor `L : C ⥤ D` for `W : MorphismProperty C`,
if `(F₁' F₂' : D ⥤ E)` are functors which lifts functors `(F₁ F₂ : C ⥤ E)`,
a natural isomorphism `τ : F₁ ⟶ F₂` lifts to a natural isomorphism `F₁' ⟶ F₂'`. -/
@[simps]
def liftNatIso (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [h₁ : Lifting L W F₁ F₁'] [h₂ : Lifting L W F₂ F₂']
    (e : F₁ ≅ F₂) : F₁' ≅ F₂' where
  hom := liftNatTrans L W F₁ F₂ F₁' F₂' e.hom
  inv := liftNatTrans L W F₂ F₁ F₂' F₁' e.inv

namespace Lifting

@[simps]
instance compRight {E' : Type*} [Category E'] (F : C ⥤ E) (F' : D ⥤ E) [Lifting L W F F']
    (G : E ⥤ E') : Lifting L W (F ⋙ G) (F' ⋙ G) :=
  ⟨isoWhiskerRight (iso L W F F') G⟩

@[simps]
instance id : Lifting L W L (𝟭 D) :=
  ⟨rightUnitor L⟩

@[simps]
instance compLeft (F : D ⥤ E) : Localization.Lifting L W (L ⋙ F) F := ⟨Iso.refl _⟩

@[simp]
lemma compLeft_iso (W) (F : D ⥤ E) : Localization.Lifting.iso L W (L ⋙ F) F = Iso.refl _ := rfl

/-- Given a localization functor `L : C ⥤ D` for `W : MorphismProperty C`,
if `F₁' : D ⥤ E` lifts a functor `F₁ : C ⥤ D`, then a functor `F₂'` which
is isomorphic to `F₁'` also lifts a functor `F₂` that is isomorphic to `F₁`. -/
@[simps]
def ofIsos {F₁ F₂ : C ⥤ E} {F₁' F₂' : D ⥤ E} (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') [Lifting L W F₁ F₁'] :
    Lifting L W F₂ F₂' :=
  ⟨isoWhiskerLeft L e'.symm ≪≫ iso L W F₁ F₁' ≪≫ e⟩

end Lifting

end Localization

namespace Functor

namespace IsLocalization

open Localization

theorem of_iso {L₁ L₂ : C ⥤ D} (e : L₁ ≅ L₂) [L₁.IsLocalization W] : L₂.IsLocalization W := by
  have h := Localization.inverts L₁ W
  rw [MorphismProperty.IsInvertedBy.iff_of_iso W e] at h
  let F₁ := Localization.Construction.lift L₁ (Localization.inverts L₁ W)
  let F₂ := Localization.Construction.lift L₂ h
  exact
    { inverts := h
      isEquivalence := Functor.isEquivalence_of_iso (liftNatIso W.Q W L₁ L₂ F₁ F₂ e) }

/-- If `L : C ⥤ D` is a localization for `W : MorphismProperty C`, then it is also
the case of a functor obtained by post-composing `L` with an equivalence of categories. -/
theorem of_equivalence_target {E : Type*} [Category E] (L' : C ⥤ E) (eq : D ≌ E)
    [L.IsLocalization W] (e : L ⋙ eq.functor ≅ L') : L'.IsLocalization W := by
  have h : W.IsInvertedBy L' := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso W e]
    exact MorphismProperty.IsInvertedBy.of_comp W L (Localization.inverts L W) eq.functor
  let F₁ := Localization.Construction.lift L (Localization.inverts L W)
  let F₂ := Localization.Construction.lift L' h
  let e' : F₁ ⋙ eq.functor ≅ F₂ := liftNatIso W.Q W (L ⋙ eq.functor) L' _ _ e
  exact
    { inverts := h
      isEquivalence := Functor.isEquivalence_of_iso e' }

instance (F : D ⥤ E) [F.IsEquivalence] [L.IsLocalization W] :
    (L ⋙ F).IsLocalization W :=
  of_equivalence_target L W _ F.asEquivalence (Iso.refl _)

lemma of_isEquivalence (L : C ⥤ D) (W : MorphismProperty C)
    (hW : W ≤ MorphismProperty.isomorphisms C) [IsEquivalence L] :
    L.IsLocalization W := by
  haveI : (𝟭 C).IsLocalization W := for_id W hW
  exact of_equivalence_target (𝟭 C) W L L.asEquivalence L.leftUnitor

end IsLocalization

end Functor

namespace Localization

variable {D₁ D₂ : Type _} [Category D₁] [Category D₂] (L₁ : C ⥤ D₁) (L₂ : C ⥤ D₂)
  (W' : MorphismProperty C) [L₁.IsLocalization W'] [L₂.IsLocalization W']

/-- If `L₁ : C ⥤ D₁` and `L₂ : C ⥤ D₂` are two localization functors for the
same `MorphismProperty C`, this is an equivalence of categories `D₁ ≌ D₂`. -/
def uniq : D₁ ≌ D₂ :=
  (equivalenceFromModel L₁ W').symm.trans (equivalenceFromModel L₂ W')

lemma uniq_symm : (uniq L₁ L₂ W').symm = uniq L₂ L₁ W' := by
  dsimp [uniq, Equivalence.trans]
  ext <;> aesop

/-- The functor of equivalence of localized categories given by `Localization.uniq` is
compatible with the localization functors. -/
def compUniqFunctor : L₁ ⋙ (uniq L₁ L₂ W').functor ≅ L₂ :=
  calc
    L₁ ⋙ (uniq L₁ L₂ W').functor ≅ (L₁ ⋙ (equivalenceFromModel L₁ W').inverse) ⋙
      (equivalenceFromModel L₂ W').functor := (associator _ _ _).symm
    _ ≅ W'.Q ⋙ (equivalenceFromModel L₂ W').functor :=
      isoWhiskerRight (compEquivalenceFromModelInverseIso L₁ W') _
    _ ≅ L₂ := qCompEquivalenceFromModelFunctorIso L₂ W'

/-- The inverse functor of equivalence of localized categories given by `Localization.uniq` is
compatible with the localization functors. -/
def compUniqInverse : L₂ ⋙ (uniq L₁ L₂ W').inverse ≅ L₁ := compUniqFunctor L₂ L₁ W'

instance : Lifting L₁ W' L₂ (uniq L₁ L₂ W').functor := ⟨compUniqFunctor L₁ L₂ W'⟩
instance : Lifting L₂ W' L₁ (uniq L₁ L₂ W').inverse := ⟨compUniqInverse L₁ L₂ W'⟩

/-- If `L₁ : C ⥤ D₁` and `L₂ : C ⥤ D₂` are two localization functors for the
same `MorphismProperty C`, any functor `F : D₁ ⥤ D₂` equipped with an isomorphism
`L₁ ⋙ F ≅ L₂` is isomorphic to the functor of the equivalence given by `uniq`. -/
def isoUniqFunctor (F : D₁ ⥤ D₂) (e : L₁ ⋙ F ≅ L₂) :
    F ≅ (uniq L₁ L₂ W').functor :=
  letI : Lifting L₁ W' L₂ F := ⟨e⟩
  liftNatIso L₁ W' L₂ L₂ F (uniq L₁ L₂ W').functor (Iso.refl L₂)

end Localization

section

variable {X Y : C} (f g : X ⟶ Y)

/-- The property that two morphisms become equal in the localized category. -/
def AreEqualizedByLocalization : Prop := W.Q.map f = W.Q.map g

lemma areEqualizedByLocalization_iff [L.IsLocalization W] :
    AreEqualizedByLocalization W f g ↔ L.map f = L.map g := by
  dsimp [AreEqualizedByLocalization]
  constructor
  · intro h
    let e := Localization.compUniqFunctor W.Q L W
    rw [← NatIso.naturality_1 e f, ← NatIso.naturality_1 e g]
    dsimp
    rw [h]
  · intro h
    let e := Localization.compUniqFunctor L W.Q W
    rw [← NatIso.naturality_1 e f, ← NatIso.naturality_1 e g]
    dsimp
    rw [h]

namespace AreEqualizedByLocalization

lemma mk (L : C ⥤ D) [L.IsLocalization W] (h : L.map f = L.map g) :
    AreEqualizedByLocalization W f g :=
  (areEqualizedByLocalization_iff L W f g).2 h

variable {W f g}

lemma map_eq (h : AreEqualizedByLocalization W f g) (L : C ⥤ D) [L.IsLocalization W] :
    L.map f = L.map g :=
  (areEqualizedByLocalization_iff L W f g).1 h

lemma map_eq_of_isInvertedBy (h : AreEqualizedByLocalization W f g)
    (F : C ⥤ D) (hF : W.IsInvertedBy F) :
    F.map f = F.map g := by
  simp [← NatIso.naturality_1 (Localization.fac F hF W.Q), h.map_eq W.Q]

end AreEqualizedByLocalization

end

end CategoryTheory
