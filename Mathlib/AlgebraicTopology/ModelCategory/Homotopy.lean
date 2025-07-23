/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Cylinder
import Mathlib.AlgebraicTopology.ModelCategory.PathObject
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
import Mathlib.CategoryTheory.Localization.Quotient
import Mathlib.CategoryTheory.Quotient

/-!
# Homotopies in model categories

-/

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category C] [ModelCategory C]

namespace Cylinder

variable {X : C} (P : Cylinder X) {Y : C}

structure LeftHomotopy (f g : X ⟶ Y) where
  h : P.I ⟶ Y
  h₀ : P.i₀ ≫ h = f := by aesop_cat
  h₁ : P.i₁ ≫ h = g := by aesop_cat

namespace LeftHomotopy

attribute [reassoc (attr := simp)] h₀ h₁

variable {P}

@[simps]
def refl (f : X ⟶ Y) : P.LeftHomotopy f f where
  h := P.π ≫ f

@[simps]
def symm {f g : X ⟶ Y} (h : P.LeftHomotopy f g) : P.symm.LeftHomotopy g f where
  h := h.h

@[simps]
noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y} [IsCofibrant X]
    (h : P.LeftHomotopy f₀ f₁) {P' : Cylinder X} [P'.IsGood]
    (h' : P'.LeftHomotopy f₁ f₂) : (P.trans P').LeftHomotopy f₀ f₂ where
  h := pushout.desc h.h h'.h (by simp)

@[simps]
def postcomp {f g : X ⟶ Y} (h : P.LeftHomotopy f g) {Z : C} (p : Y ⟶ Z) :
    P.LeftHomotopy (f ≫ p) (g ≫ p) where
  h := h.h ≫ p

lemma exists_good {f g : X ⟶ Y} (h : P.LeftHomotopy f g) :
    ∃ (P' : Cylinder X), P'.IsGood ∧ Nonempty (P'.LeftHomotopy f g) := by
  have d := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C) P.i
  exact ⟨{
    I := d.Z
    i₀ := coprod.inl ≫ d.i
    i₁ := coprod.inr ≫ d.i
    π := d.p ≫ P.π }, ⟨by
      rw [cofibration_iff]
      convert d.hi
      aesop⟩, ⟨{ h := d.p ≫ h.h }⟩⟩

lemma weakEquivalence_iff {f₀ f₁ : X ⟶ Y} (h : P.LeftHomotopy f₀ f₁) :
    WeakEquivalence f₀ ↔ WeakEquivalence f₁ := by
  revert P f₀ f₁
  suffices ∀ (P : Cylinder X) {f₀ f₁ : X ⟶ Y} (h : P.LeftHomotopy f₀ f₁),
      WeakEquivalence f₀ → WeakEquivalence f₁
    from fun _ _ _ h ↦ ⟨this _ h, this _ h.symm⟩
  intro P f₀ f₁ h h₀
  have := weakEquivalence_of_precomp_of_fac h.h₀
  rw [← h.h₁]
  infer_instance

lemma covering_homotopy {A E B : C} {P : Cylinder A} {f₀ f₁ : A ⟶ B}
    [IsCofibrant A] [P.IsGood]
    (h : P.LeftHomotopy f₀ f₁) (p : E ⟶ B) [Fibration p]
    (l₀ : A ⟶ E) (hl₀ : l₀ ≫ p = f₀) :
    ∃ (l₁ : A ⟶ E) (h' : P.LeftHomotopy l₀ l₁), h'.h ≫ p = h.h := by
  have sq : CommSq l₀ P.i₀ p h.h := ⟨by aesop_cat⟩
  exact ⟨P.i₁ ≫ sq.lift, { h := sq.lift }, by simp⟩

end LeftHomotopy

end Cylinder

namespace PathObject

variable {Y : C} (P : PathObject Y) {X : C}

structure RightHomotopy (f g : X ⟶ Y) where
  h : X ⟶ P.P
  h₀ : h ≫ P.p₀ = f := by aesop_cat
  h₁ : h ≫ P.p₁ = g := by aesop_cat

namespace RightHomotopy

attribute [reassoc (attr := simp)] h₀ h₁

variable {P}

@[simps]
def refl (f : X ⟶ Y) : P.RightHomotopy f f where
  h := f ≫ P.ι

@[simps]
def symm {f g : X ⟶ Y} (h : P.RightHomotopy f g) : P.symm.RightHomotopy g f where
  h := h.h

@[simps]
noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y} [IsFibrant Y]
    (h : P.RightHomotopy f₀ f₁) {P' : PathObject Y} [P'.IsGood]
    (h' : P'.RightHomotopy f₁ f₂) : (P.trans P').RightHomotopy f₀ f₂ where
  h := pullback.lift h.h h'.h (by simp)

@[simps]
def precomp {f g : X ⟶ Y} (h : P.RightHomotopy f g) {Z : C} (i : Z ⟶ X) :
    P.RightHomotopy (i ≫ f) (i ≫ g) where
  h := i ≫ h.h

lemma exists_good {f g : X ⟶ Y} (h : P.RightHomotopy f g) :
    ∃ (P' : PathObject Y), P'.IsGood ∧ Nonempty (P'.RightHomotopy f g) := by
  have d := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) P.p
  exact ⟨{
    P := d.Z
    p₀ := d.p ≫ prod.fst
    p₁ := d.p ≫ prod.snd
    ι := P.ι ≫ d.i }, ⟨by
      rw [fibration_iff]
      convert d.hp
      aesop⟩, ⟨{ h := h.h ≫ d.i }⟩⟩

lemma weakEquivalence_iff {f₀ f₁ : X ⟶ Y} (h : P.RightHomotopy f₀ f₁) :
    WeakEquivalence f₀ ↔ WeakEquivalence f₁ := by
  revert P f₀ f₁
  suffices ∀ (P : PathObject Y) {f₀ f₁ : X ⟶ Y} (h : P.RightHomotopy f₀ f₁),
      WeakEquivalence f₀ → WeakEquivalence f₁
    from fun _ _ _ h ↦ ⟨this _ h, this _ h.symm⟩
  intro P f₀ f₁ h h₀
  have := weakEquivalence_of_postcomp_of_fac h.h₀
  rw [← h.h₁]
  infer_instance

lemma homotopy_extension {A B : C} {f₀ f₁ : A ⟶ Y}
    [IsFibrant Y] [P.IsGood]
    (h : P.RightHomotopy f₀ f₁) (i : A ⟶ B) [Cofibration i]
    (l₀ : B ⟶ Y) (hl₀ : i ≫ l₀ = f₀) :
    ∃ (l₁ : B ⟶ Y) (h' : P.RightHomotopy l₀ l₁), i ≫ h'.h = h.h := by
  have sq : CommSq h.h i P.p₀ l₀ := ⟨by aesop_cat⟩
  exact ⟨sq.lift ≫ P.p₁, { h := sq.lift }, by simp⟩

end RightHomotopy

end PathObject

def LeftHomotopyRel : HomRel C :=
  fun X _ f g ↦ ∃ (P : Cylinder X), Nonempty (P.LeftHomotopy f g)

lemma factorsThroughLocalization_leftHomotopyRel :
    LeftHomotopyRel.FactorsThroughLocalization (weakEquivalences C) := by
  rintro X Y f g ⟨P, ⟨h⟩⟩
  let L := (weakEquivalences C).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map P.i₀ = L.map P.i₁ by
    simp only [← h.h₀, ← h.h₁, L.map_comp, this]
  have := Localization.inverts L (weakEquivalences C) P.π (by
    rw [← weakEquivalence_iff]
    infer_instance)
  simp only [← cancel_mono (L.map P.π), ← L.map_comp, P.i₀_π, P.i₁_π]

lemma Cylinder.LeftHomotopy.leftHomotopyRel {X Y : C} {f g : X ⟶ Y}
    {P : Cylinder X} (h : P.LeftHomotopy f g) :
    LeftHomotopyRel f g :=
  ⟨_, ⟨h⟩⟩

namespace LeftHomotopyRel

variable {X Y : C}

lemma refl (f : X ⟶ Y) : LeftHomotopyRel f f :=
  ⟨Classical.arbitrary _, ⟨.refl _⟩⟩

lemma postcomp {f g : X ⟶ Y} (h : LeftHomotopyRel f g) {Z : C} (p : Y ⟶ Z) :
    LeftHomotopyRel (f ≫ p) (g ≫ p) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact (h.postcomp p).leftHomotopyRel

lemma exists_good {f g : X ⟶ Y} (h : LeftHomotopyRel f g) :
    ∃ (P : Cylinder X), P.IsGood ∧ Nonempty (P.LeftHomotopy f g) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.exists_good

lemma exists_very_good {f g : X ⟶ Y} [IsFibrant Y] (h : LeftHomotopyRel f g) :
    ∃ (P : Cylinder X), P.IsVeryGood ∧ Nonempty (P.LeftHomotopy f g) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good
  have fac := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) P.π
  let P' : Cylinder X :=
    { I := fac.Z
      i₀ := P.i₀ ≫ fac.i
      i₁ := P.i₁ ≫ fac.i
      π := fac.p
      weakEquivalence_π := weakEquivalence_of_precomp_of_fac fac.fac }
  have : Cofibration P'.i := by
    rw [show P'.i = P.i ≫ fac.i by aesop_cat]
    infer_instance
  have sq : CommSq h.h fac.i (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨P', { }, ⟨{ h := sq.lift }⟩ ⟩

lemma symm {f g : X ⟶ Y} (h : LeftHomotopyRel f g) : LeftHomotopyRel g f := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.symm.leftHomotopyRel

lemma trans {f₀ f₁ f₂ : X ⟶ Y} [IsCofibrant X] (h : LeftHomotopyRel f₀ f₁)
    (h' : LeftHomotopyRel f₁ f₂) : LeftHomotopyRel f₀ f₂ := by
  obtain ⟨P, ⟨h⟩⟩ := h
  obtain ⟨P', _, ⟨h'⟩⟩ := h'.exists_good
  exact (h.trans h').leftHomotopyRel

instance equivalence (X Y : C) [IsCofibrant X] :
    _root_.Equivalence (LeftHomotopyRel (X := X) (Y := Y)) where
  refl := .refl
  symm h := h.symm
  trans h h' := h.trans h'

lemma precomp {f g : X ⟶ Y} [IsFibrant Y] (h : LeftHomotopyRel f g)
    {Z : C} (i : Z ⟶ X) : LeftHomotopyRel (i ≫ f) (i ≫ g) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good
  obtain ⟨Q, _⟩ := Cylinder.exists_very_good Z
  have sq : CommSq (coprod.desc (i ≫ P.i₀) (i ≫ P.i₁)) Q.i P.π (Q.π ≫ i) := ⟨by aesop_cat⟩
  exact ⟨Q, ⟨{
    h := sq.lift ≫ h.h
    h₀ := by
      have := coprod.inl ≫= sq.fac_left
      simp only [Q.inl_i_assoc, coprod.inl_desc] at this
      simp [reassoc_of% this]
    h₁ := by
      have := coprod.inr ≫= sq.fac_left
      simp only [Q.inr_i_assoc, coprod.inr_desc] at this
      simp [reassoc_of% this]
  }⟩⟩

end LeftHomotopyRel

def RightHomotopyRel : HomRel C :=
  fun _ Y f g ↦ ∃ (P : PathObject Y), Nonempty (P.RightHomotopy f g)

lemma factorsThroughLocalization_rightHomotopyRel :
    RightHomotopyRel.FactorsThroughLocalization (weakEquivalences C) := by
  rintro X Y f g ⟨P, ⟨h⟩⟩
  let L := (weakEquivalences C).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map P.p₀ = L.map P.p₁ by
    simp only [← h.h₀, ← h.h₁, L.map_comp, this]
  have := Localization.inverts L (weakEquivalences C) P.ι (by
    rw [← weakEquivalence_iff]
    infer_instance)
  simp only [← cancel_epi (L.map P.ι), ← L.map_comp, P.ι_p₀, P.ι_p₁]

lemma PathObject.RightHomotopy.rightHomotopyRel {X Y : C} {f g : X ⟶ Y}
    {P : PathObject Y} (h : P.RightHomotopy f g) :
    RightHomotopyRel f g :=
  ⟨_, ⟨h⟩⟩

namespace RightHomotopyRel

variable {X Y : C}

lemma refl (f : X ⟶ Y) : RightHomotopyRel f f :=
  ⟨Classical.arbitrary _, ⟨.refl _⟩⟩

lemma precomp {f g : X ⟶ Y} (h : RightHomotopyRel f g) {Z : C} (i : Z ⟶ X) :
    RightHomotopyRel (i ≫ f) (i ≫ g) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact (h.precomp i).rightHomotopyRel

lemma exists_good {f g : X ⟶ Y} (h : RightHomotopyRel f g) :
    ∃ (P : PathObject Y), P.IsGood ∧ Nonempty (P.RightHomotopy f g) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.exists_good

lemma exists_very_good {f g : X ⟶ Y} [IsCofibrant X] (h : RightHomotopyRel f g) :
    ∃ (P : PathObject Y), P.IsVeryGood ∧ Nonempty (P.RightHomotopy f g) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good
  have fac := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C) P.ι
  let P' : PathObject Y :=
    { P := fac.Z
      p₀ := fac.p ≫ P.p₀
      p₁ := fac.p ≫ P.p₁
      ι := fac.i
      weakEquivalence_ι := weakEquivalence_of_postcomp_of_fac fac.fac }
  have : Fibration P'.p := by
    rw [show P'.p = fac.p ≫ P.p by aesop_cat]
    infer_instance
  have sq : CommSq (initial.to _) (initial.to _) fac.p h.h := ⟨by simp⟩
  exact ⟨P', { }, ⟨{ h := sq.lift }⟩ ⟩

lemma symm {f g : X ⟶ Y} (h : RightHomotopyRel f g) : RightHomotopyRel g f := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.symm.rightHomotopyRel

lemma trans {f₀ f₁ f₂ : X ⟶ Y} [IsFibrant Y] (h : RightHomotopyRel f₀ f₁)
    (h' : RightHomotopyRel f₁ f₂) : RightHomotopyRel f₀ f₂ := by
  obtain ⟨P, ⟨h⟩⟩ := h
  obtain ⟨P', _, ⟨h'⟩⟩ := h'.exists_good
  exact (h.trans h').rightHomotopyRel

instance equivalence (X Y : C) [IsFibrant Y] :
    _root_.Equivalence (RightHomotopyRel (X := X) (Y := Y)) where
  refl := .refl
  symm h := h.symm
  trans h h' := h.trans h'

lemma postcomp {f g : X ⟶ Y} [IsCofibrant X] (h : RightHomotopyRel f g)
    {Z : C} (p : Y ⟶ Z) : RightHomotopyRel (f ≫ p) (g ≫ p) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good
  obtain ⟨Q, _⟩ := PathObject.exists_very_good Z
  have sq : CommSq (p ≫ Q.ι) P.ι Q.p (prod.lift (P.p₀ ≫ p) (P.p₁ ≫ p)) := ⟨by aesop_cat⟩
  exact ⟨Q, ⟨{
    h := h.h ≫ sq.lift
    h₀ := by
      have := sq.fac_right =≫ prod.fst
      simp only [Category.assoc, Q.p_fst, prod.lift_fst] at this
      simp [this]
    h₁ := by
      have := sq.fac_right =≫ prod.snd
      simp only [Category.assoc, Q.p_snd, prod.lift_snd] at this
      simp [this]
  }⟩⟩

end RightHomotopyRel

namespace LeftHomotopyRel

variable {X Y : C} {f g : X ⟶ Y} [IsCofibrant X]

noncomputable def rightHomotopy (h : LeftHomotopyRel f g) (Q : PathObject Y) [Q.IsGood] :
    Q.RightHomotopy f g := by
  apply Nonempty.some
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good
  have sq : CommSq (f ≫ Q.ι) P.i₀ Q.p (prod.lift (P.π ≫ f) h.h) := ⟨by aesop_cat⟩
  exact ⟨{
    h := P.i₁ ≫ sq.lift
    h₀ := by
      have := sq.fac_right =≫ prod.fst
      rw [Category.assoc, Q.p_fst, prod.lift_fst] at this
      simp [this]
    h₁ := by
      have := sq.fac_right =≫ prod.snd
      rw [Category.assoc, Q.p_snd, prod.lift_snd] at this
      simp [this]
  }⟩

lemma rightHomotopyRel (h : LeftHomotopyRel f g) : RightHomotopyRel f g := by
  obtain ⟨P, _⟩ := PathObject.exists_very_good Y
  exact ⟨P, ⟨h.rightHomotopy P⟩⟩

end LeftHomotopyRel

namespace RightHomotopyRel

variable {X Y : C} {f g : X ⟶ Y} [IsFibrant Y]

noncomputable def leftHomotopy (h : RightHomotopyRel f g) (Q : Cylinder X) [Q.IsGood] :
    Q.LeftHomotopy f g := by
  apply Nonempty.some
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good
  have sq : CommSq (coprod.desc (f ≫ P.ι) h.h) Q.i P.p₀ (Q.π ≫ f) := ⟨by aesop_cat⟩
  exact ⟨{
    h := sq.lift ≫ P.p₁
    h₀ := by
      have := coprod.inl ≫= sq.fac_left
      rw [Q.inl_i_assoc, coprod.inl_desc] at this
      simp [reassoc_of% this]
    h₁ := by
      have := coprod.inr ≫= sq.fac_left
      rw [Q.inr_i_assoc, coprod.inr_desc] at this
      simp [reassoc_of% this]
  }⟩

lemma leftHomotopyRel (h : RightHomotopyRel f g) : LeftHomotopyRel f g := by
  obtain ⟨P, _⟩ := Cylinder.exists_very_good X
  exact ⟨P, ⟨h.leftHomotopy P⟩⟩

end RightHomotopyRel

lemma leftHomotopyRel_iff_rightHomotopyRel {X Y : C} (f g : X ⟶ Y)
    [IsCofibrant X] [IsFibrant Y] :
    LeftHomotopyRel f g ↔ RightHomotopyRel f g :=
  ⟨fun h ↦ h.rightHomotopyRel, fun h ↦ h.leftHomotopyRel⟩

variable (X Y Z : C)

def LeftHomotopyClass :=
  _root_.Quot (LeftHomotopyRel (X := X) (Y := Y))

def RightHomotopyClass (X Y : C) :=
  _root_.Quot (RightHomotopyRel (X := X) (Y := Y))

variable {X Y Z}

def LeftHomotopyClass.mk : (X ⟶ Y) → LeftHomotopyClass X Y := Quot.mk _

def RightHomotopyClass.mk : (X ⟶ Y) → RightHomotopyClass X Y := Quot.mk _

lemma LeftHomotopyClass.mk_surjective : Function.Surjective (mk : (X ⟶ Y) → _) :=
  Quot.mk_surjective

lemma RightHomotopyClass.mk_surjective : Function.Surjective (mk : (X ⟶ Y) → _) :=
  Quot.mk_surjective

namespace LeftHomotopyClass

lemma sound {f g : X ⟶ Y} (h : LeftHomotopyRel f g) : mk f = mk g := Quot.sound h

def postcomp : LeftHomotopyClass X Y → (Y ⟶ Z) → LeftHomotopyClass X Z :=
  fun f g ↦ Quot.lift (fun f ↦ mk (f ≫ g)) (fun _ _ h ↦ sound (h.postcomp g)) f

@[simp]
lemma postcomp_mk (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk f).postcomp g = mk (f ≫ g) := rfl

def comp [IsFibrant Z] :
    LeftHomotopyClass X Y → LeftHomotopyClass Y Z → LeftHomotopyClass X Z :=
  Quot.lift₂ (fun f g ↦ mk (f ≫ g)) (fun f _ _ h ↦ sound (h.precomp f))
    (fun _ _ g h ↦ sound (h.postcomp g))

@[simp]
lemma mk_comp_mk [IsFibrant Z] (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk f).comp (mk g) = mk (f ≫ g) := rfl

lemma mk_eq_mk_iff [IsCofibrant X] (f g : X ⟶ Y) :
    mk f = mk g ↔ LeftHomotopyRel f g := by
  rw [← (LeftHomotopyRel.equivalence X Y).eqvGen_iff ]
  exact Quot.eq

variable (X) in
lemma bijective_postcomp_of_fibration_of_weakEquivalence
    [IsCofibrant X] (g : Y ⟶ Z) [Fibration g] [WeakEquivalence g] :
    Function.Bijective (fun (f : LeftHomotopyClass X Y) ↦ f.postcomp g) := by
  constructor
  · intro f₀ f₁ h
    obtain ⟨f₀, rfl⟩ := f₀.mk_surjective
    obtain ⟨f₁, rfl⟩ := f₁.mk_surjective
    simp only [postcomp_mk, mk_eq_mk_iff] at h
    obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good
    have sq : CommSq (coprod.desc f₀ f₁) P.i g h.h := ⟨by aesop_cat⟩
    rw [mk_eq_mk_iff]
    exact ⟨P, ⟨{
      h := sq.lift
      h₀ := by
        have := coprod.inl ≫= sq.fac_left
        rwa [P.inl_i_assoc, coprod.inl_desc] at this
      h₁ := by
        have := coprod.inr ≫= sq.fac_left
        rwa [P.inr_i_assoc, coprod.inr_desc] at this
    }⟩⟩
  · intro φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    have sq : CommSq (initial.to Y) (initial.to X) g φ := ⟨by simp⟩
    exact ⟨mk sq.lift, by simp⟩

variable (X) in
lemma bijective_postcomp_of_weakEquivalence
    [IsCofibrant X] (g : Y ⟶ Z) [IsFibrant Y] [IsFibrant Z] [WeakEquivalence g] :
    Function.Bijective (fun (f : LeftHomotopyClass X Y) ↦ f.postcomp g) := by
  have h : FibrantBrownFactorization g := Classical.arbitrary _
  have hi : Function.Bijective (fun (f : LeftHomotopyClass X Y) ↦ f.postcomp h.i) := by
    rw [← Function.Bijective.of_comp_iff'
      (bijective_postcomp_of_fibration_of_weakEquivalence X h.r)]
    convert Function.bijective_id
    ext φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    simp
  convert (bijective_postcomp_of_fibration_of_weakEquivalence X h.j).comp hi using 1
  ext φ
  obtain ⟨φ, rfl⟩ := φ.mk_surjective
  simp

end LeftHomotopyClass

namespace RightHomotopyClass

lemma sound {f g : X ⟶ Y} (h : RightHomotopyRel f g) : mk f = mk g := Quot.sound h

def precomp : RightHomotopyClass Y Z → (X ⟶ Y) → RightHomotopyClass X Z :=
  fun f g ↦ Quot.lift (fun f ↦ mk (g ≫ f)) (fun _ _ h ↦ sound (h.precomp g)) f

@[simp]
lemma precomp_mk (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk g).precomp f = mk (f ≫ g) := rfl

def comp [IsCofibrant X] :
    RightHomotopyClass X Y → RightHomotopyClass Y Z → RightHomotopyClass X Z :=
  Quot.lift₂ (fun f g ↦ mk (f ≫ g)) (fun f _ _ h ↦ sound (h.precomp f))
    (fun _ _ g h ↦ sound (h.postcomp g))

@[simp]
lemma mk_comp_mk [IsCofibrant X] (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk f).comp (mk g) = mk (f ≫ g) := rfl

lemma mk_eq_mk_iff [IsFibrant Y] (f g : X ⟶ Y) :
    mk f = mk g ↔ RightHomotopyRel f g := by
  rw [← (RightHomotopyRel.equivalence X Y).eqvGen_iff ]
  exact Quot.eq

variable (Z) in
lemma bijective_precomp_of_cofibration_of_weakEquivalence
    [IsFibrant Z] (f : X ⟶ Y) [Cofibration f] [WeakEquivalence f] :
    Function.Bijective (fun (g : RightHomotopyClass Y Z) ↦ g.precomp f) := by
  constructor
  · intro f₀ f₁ h
    obtain ⟨f₀, rfl⟩ := f₀.mk_surjective
    obtain ⟨f₁, rfl⟩ := f₁.mk_surjective
    simp only [precomp_mk, mk_eq_mk_iff] at h
    obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good
    have sq : CommSq h.h f P.p (prod.lift f₀ f₁) := ⟨by aesop_cat⟩
    rw [mk_eq_mk_iff]
    exact ⟨P, ⟨{
      h := sq.lift
      h₀ := by
        have := sq.fac_right =≫ prod.fst
        rwa [Category.assoc, P.p_fst, prod.lift_fst] at this
      h₁ := by
        have := sq.fac_right =≫ prod.snd
        rwa [Category.assoc, P.p_snd, prod.lift_snd] at this
    }⟩⟩
  · intro φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    have sq : CommSq φ f (terminal.from _) (terminal.from _) := ⟨by simp⟩
    exact ⟨mk sq.lift, by simp⟩

variable (Z) in
lemma bijective_precomp_of_weakEquivalence
    [IsFibrant Z] (f : X ⟶ Y) [IsCofibrant X] [IsCofibrant Y] [WeakEquivalence f] :
    Function.Bijective (fun (g : RightHomotopyClass Y Z) ↦ g.precomp f) := by
  have h : CofibrantBrownFactorization f := Classical.arbitrary _
  have hj : Function.Bijective (fun (g : RightHomotopyClass Y Z) ↦ g.precomp h.j) := by
    rw [← Function.Bijective.of_comp_iff'
      (bijective_precomp_of_cofibration_of_weakEquivalence Z h.s)]
    convert Function.bijective_id
    ext φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    simp
  convert (bijective_precomp_of_cofibration_of_weakEquivalence Z h.i).comp hj using 1
  ext φ
  obtain ⟨φ, rfl⟩ := φ.mk_surjective
  simp

lemma exists_homotopy_inverse [IsCofibrant X] [IsCofibrant Y]
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) [WeakEquivalence f] :
    ∃ (g : Y ⟶ X), RightHomotopyRel (f ≫ g) (𝟙 X) ∧ RightHomotopyRel (g ≫ f) (𝟙 Y) := by
  obtain ⟨g, hg⟩ := (bijective_precomp_of_weakEquivalence X f).2 (.mk (𝟙 X))
  obtain ⟨g, rfl⟩ := g.mk_surjective
  dsimp at hg
  refine ⟨g, by rwa [← mk_eq_mk_iff], ?_⟩
  rw [← mk_eq_mk_iff]
  apply (bijective_precomp_of_weakEquivalence Y f).1
  simp only [precomp_mk, Category.comp_id]
  rw [mk_eq_mk_iff, ← leftHomotopyRel_iff_rightHomotopyRel] at hg ⊢
  simpa using hg.postcomp f

end RightHomotopyClass

lemma LeftHomotopyClass.exists_homotopy_inverse
    [IsCofibrant X] [IsCofibrant Y]
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) [WeakEquivalence f] :
    ∃ (g : Y ⟶ X), LeftHomotopyRel (f ≫ g) (𝟙 X) ∧ LeftHomotopyRel (g ≫ f) (𝟙 Y) := by
  simp only [leftHomotopyRel_iff_rightHomotopyRel]
  apply RightHomotopyClass.exists_homotopy_inverse

section

variable [IsCofibrant X] [IsFibrant Y]

def leftHomotopyClassEquivRightHomotopyClass :
    LeftHomotopyClass X Y ≃ RightHomotopyClass X Y where
  toFun := Quot.lift (fun f ↦ .mk f) (fun _ _ h ↦ by
    dsimp
    rw [RightHomotopyClass.mk_eq_mk_iff]
    exact h.rightHomotopyRel)
  invFun := Quot.lift (fun f ↦ .mk f) (fun _ _ h ↦ by
    dsimp
    rw [LeftHomotopyClass.mk_eq_mk_iff]
    exact h.leftHomotopyRel)
  left_inv := by rintro ⟨f⟩; rfl
  right_inv := by rintro ⟨f⟩; rfl

@[simp]
lemma leftHomotopyClassEquivRightHomotopyClass_mk (f : X ⟶ Y) :
    leftHomotopyClassEquivRightHomotopyClass (.mk f) = .mk f := rfl

@[simp]
lemma leftHomotopyClassEquivRightHomotopyClass_symm_mk (f : X ⟶ Y) :
    leftHomotopyClassEquivRightHomotopyClass.symm (.mk f) = .mk f := rfl

end

end HomotopicalAlgebra
