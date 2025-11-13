/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Cylinder
import Mathlib.CategoryTheory.Localization.Quotient

/-!
# Left homotopies in model categories

We introduce the types `Precylinder.LeftHomotopy` and `Cylinder.LeftHomotopy`
of homotopies between morphisms `X ⟶ Y` relative to a (pre)cylinder of `X`.
Given two morphisms `f` and `g`, we introduce the relation `LeftHomotopyRel f g`
asserting the existence of a cylinder object `P` and
a left homotopy `P.LeftHomotopy f g`, and we define the quotient
type `LeftHomotopyClass X Y`. We show that if `X` is a cofibrant
object in a model category, then `LeftHomotopyRel` is an equivalence
relation on `X ⟶ Y`.

## References
* [Daniel G. Quillen, Homotopical algebra, section I.1][Quillen1967]

-/

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

namespace Precylinder

variable {X : C} (P : Precylinder X) {Y : C}

/-- Given a precylinder `P` for `X`, two maps `f` and `g` in `X ⟶ Y` are
homotopic relative to `P` when there is a morphism `h : P.I ⟶ Y`
such that `P.i₀ ≫ h = f` and `P.i₁ ≫ h = g`. -/
structure LeftHomotopy (f g : X ⟶ Y) where
  /-- a morphism from the (pre)cylinder object to the target -/
  h : P.I ⟶ Y
  h₀ : P.i₀ ≫ h = f := by cat_disch
  h₁ : P.i₁ ≫ h = g := by cat_disch

namespace LeftHomotopy

attribute [reassoc (attr := simp)] h₀ h₁

/-- `f : X ⟶ Y` is left homotopic to itself relative to any precylinder. -/
@[simps]
def refl (f : X ⟶ Y) : P.LeftHomotopy f f where
  h := P.π ≫ f

variable {P}

/-- If `f` and `g` are homotopic relative to a precylinder `P`, then `g` and `f`
are homotopic relative to `P.symm` -/
@[simps]
def symm {f g : X ⟶ Y} (h : P.LeftHomotopy f g) : P.symm.LeftHomotopy g f where
  h := h.h

/-- If `f₀` is homotopic to `f₁` relative to a precylinder `P`,
and `f₁` is homotopic to `f₂` relative to `P'`, then
`f₀` is homotopic to `f₂` relative to `P.trans P'`. -/
@[simps]
noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y}
    (h : P.LeftHomotopy f₀ f₁) {P' : Precylinder X}
    (h' : P'.LeftHomotopy f₁ f₂) [HasPushout P.i₁ P'.i₀] :
    (P.trans P').LeftHomotopy f₀ f₂ where
  h := pushout.desc h.h h'.h (by simp)

/-- Left homotopies are compatible with postcomposition. -/
@[simps]
def postcomp {f g : X ⟶ Y} (h : P.LeftHomotopy f g) {Z : C} (p : Y ⟶ Z) :
    P.LeftHomotopy (f ≫ p) (g ≫ p) where
  h := h.h ≫ p

end LeftHomotopy

end Precylinder

namespace Cylinder

variable {X Y : C}

/-- Given a cylinder `P` for `X`, two maps `f` and `g` in `X ⟶ Y`
are homotopic relative to `P` when there is a morphism `h : P.I ⟶ Y`
such that `P.i₀ ≫ h = f` and `P.i₁ ≫ h = g`. -/
abbrev LeftHomotopy [CategoryWithWeakEquivalences C] (P : Cylinder X) (f g : X ⟶ Y) : Type v :=
  P.toPrecylinder.LeftHomotopy f g

namespace LeftHomotopy

section

variable [CategoryWithWeakEquivalences C] (P : Cylinder X)

/-- `f : X ⟶ Y` is left homotopic to itself relative to any cylinder. -/
abbrev refl (f : X ⟶ Y) : P.LeftHomotopy f f := Precylinder.LeftHomotopy.refl _ f

variable {P} in
/-- If `f` and `g` are homotopic relative to a cylinder `P`, then `g` and `f`
are homotopic relative to `P.symm`. -/
abbrev symm {f g : X ⟶ Y} (h : P.LeftHomotopy f g) : P.symm.LeftHomotopy g f :=
  Precylinder.LeftHomotopy.symm h

variable {P} in
/-- Left homotopies are compatible with postcomposition. -/
abbrev postcomp {f g : X ⟶ Y} (h : P.LeftHomotopy f g) {Z : C} (p : Y ⟶ Z) :
    P.LeftHomotopy (f ≫ p) (g ≫ p) :=
  Precylinder.LeftHomotopy.postcomp h p

lemma weakEquivalence_iff [(weakEquivalences C).HasTwoOutOfThreeProperty]
    [(weakEquivalences C).ContainsIdentities]
    {f₀ f₁ : X ⟶ Y} (h : P.LeftHomotopy f₀ f₁) :
    WeakEquivalence f₀ ↔ WeakEquivalence f₁ := by
  revert P f₀ f₁
  suffices ∀ (P : Cylinder X) {f₀ f₁ : X ⟶ Y} (h : P.LeftHomotopy f₀ f₁),
      WeakEquivalence f₀ → WeakEquivalence f₁
    from fun _ _ _ h ↦ ⟨this _ h, this _ h.symm⟩
  intro P f₀ f₁ h h₀
  have := weakEquivalence_of_precomp_of_fac h.h₀
  rw [← h.h₁]
  infer_instance

end

section

variable [ModelCategory C] {P : Cylinder X}

/-- If `f₀ : X ⟶ Y` is homotopic to `f₁` relative to a cylinder `P`,
and `f₁` is homotopic to `f₂` relative to a good cylinder `P'`,
then `f₀` is homotopic to `f₂` relative to the cylinder `P.trans P'`
when `X` is cofibrant. -/
noncomputable abbrev trans [IsCofibrant X] {f₀ f₁ f₂ : X ⟶ Y}
    (h : P.LeftHomotopy f₀ f₁) {P' : Cylinder X} [P'.IsGood]
    (h' : P'.LeftHomotopy f₁ f₂) [HasPushout P.i₁ P'.i₀] :
    (P.trans P').LeftHomotopy f₀ f₂ :=
  Precylinder.LeftHomotopy.trans h h'

lemma exists_good_cylinder {f g : X ⟶ Y} (h : P.LeftHomotopy f g) :
    ∃ (P' : Cylinder X), P'.IsGood ∧ Nonempty (P'.LeftHomotopy f g) := by
  let d := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C) P.i
  exact
   ⟨{ I := d.Z
      i₀ := coprod.inl ≫ d.i
      i₁ := coprod.inr ≫ d.i
      π := d.p ≫ P.π }, ⟨by
        rw [cofibration_iff]
        convert d.hi
        aesop⟩, ⟨{ h := d.p ≫ h.h }⟩⟩

/-- The covering homotopy theorem: if `p : E ⟶ B` is a fibration,
`l₀ : A ⟶ E` is a morphism, if there is a left homotopy `h` between
the composition `f₀ := l₀ ≫ p` and a morphism `f₁ : A ⟶ B`,
then there exists a morphism `l₁ : A ⟶ E` and a left homotopy `h'` from
`l₀` to `l₁` which is compatible with `h` (in particular, `l₁ ≫ p = f₁`). -/
lemma covering_homotopy {A E B : C} {P : Cylinder A} {f₀ f₁ : A ⟶ B}
    [IsCofibrant A] [P.IsGood]
    (h : P.LeftHomotopy f₀ f₁) (p : E ⟶ B) [Fibration p]
    (l₀ : A ⟶ E) (hl₀ : l₀ ≫ p = f₀ := by cat_disch) :
    ∃ (l₁ : A ⟶ E) (h' : P.LeftHomotopy l₀ l₁), h'.h ≫ p = h.h :=
  have sq : CommSq l₀ P.i₀ p h.h := { }
  ⟨P.i₁ ≫ sq.lift, { h := sq.lift }, by simp⟩

end

end LeftHomotopy

end Cylinder

/-- The left homotopy relation on morphisms in a category with weak equivalences. -/
def LeftHomotopyRel [CategoryWithWeakEquivalences C] : HomRel C :=
  fun X _ f g ↦ ∃ (P : Cylinder X), Nonempty (P.LeftHomotopy f g)

lemma Cylinder.LeftHomotopy.leftHomotopyRel [CategoryWithWeakEquivalences C]
    {X Y : C} {f g : X ⟶ Y}
    {P : Cylinder X} (h : P.LeftHomotopy f g) :
    LeftHomotopyRel f g :=
  ⟨_, ⟨h⟩⟩

namespace LeftHomotopyRel

variable (C) in
lemma factorsThroughLocalization [CategoryWithWeakEquivalences C] :
    LeftHomotopyRel.FactorsThroughLocalization (weakEquivalences C) := by
  rintro X Y f g ⟨P, ⟨h⟩⟩
  let L := (weakEquivalences C).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map P.i₀ = L.map P.i₁ by
    simp only [← h.h₀, ← h.h₁, L.map_comp, this]
  have := Localization.inverts L (weakEquivalences C) P.π (by
    rw [← weakEquivalence_iff]
    infer_instance)
  simp [← cancel_mono (L.map P.π), ← L.map_comp, P.i₀_π, P.i₁_π]

variable {X Y : C}

lemma refl [ModelCategory C] (f : X ⟶ Y) : LeftHomotopyRel f f :=
  ⟨Classical.arbitrary _, ⟨Cylinder.LeftHomotopy.refl _ _⟩⟩

lemma postcomp [CategoryWithWeakEquivalences C]
    {f g : X ⟶ Y} (h : LeftHomotopyRel f g) {Z : C} (p : Y ⟶ Z) :
    LeftHomotopyRel (f ≫ p) (g ≫ p) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact (h.postcomp p).leftHomotopyRel

lemma exists_good_cylinder [ModelCategory C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g) :
    ∃ (P : Cylinder X), P.IsGood ∧ Nonempty (P.LeftHomotopy f g) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.exists_good_cylinder

lemma exists_very_good_cylinder [ModelCategory C] {f g : X ⟶ Y} [IsFibrant Y]
    (h : LeftHomotopyRel f g) :
    ∃ (P : Cylinder X), P.IsVeryGood ∧ Nonempty (P.LeftHomotopy f g) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_cylinder
  let fac := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) P.π
  let P' : Cylinder X :=
    { I := fac.Z
      i₀ := P.i₀ ≫ fac.i
      i₁ := P.i₁ ≫ fac.i
      π := fac.p
      weakEquivalence_π := weakEquivalence_of_precomp_of_fac fac.fac }
  have : Cofibration P'.i := by
    rw [show P'.i = P.i ≫ fac.i by cat_disch]
    infer_instance
  have sq : CommSq h.h fac.i (terminal.from _) (terminal.from _) := { }
  exact ⟨P', { }, ⟨{ h := sq.lift }⟩ ⟩

lemma symm [CategoryWithWeakEquivalences C]
    {f g : X ⟶ Y} (h : LeftHomotopyRel f g) : LeftHomotopyRel g f := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.symm.leftHomotopyRel

lemma trans [ModelCategory C]
    {f₀ f₁ f₂ : X ⟶ Y} [IsCofibrant X] (h : LeftHomotopyRel f₀ f₁)
    (h' : LeftHomotopyRel f₁ f₂) : LeftHomotopyRel f₀ f₂ := by
  obtain ⟨P, ⟨h⟩⟩ := h
  obtain ⟨P', _, ⟨h'⟩⟩ := h'.exists_good_cylinder
  exact (h.trans h').leftHomotopyRel

lemma equivalence [ModelCategory C] (X Y : C) [IsCofibrant X] :
    _root_.Equivalence (LeftHomotopyRel (X := X) (Y := Y)) where
  refl := .refl
  symm h := h.symm
  trans h h' := h.trans h'

lemma precomp [ModelCategory C] {f g : X ⟶ Y} [IsFibrant Y] (h : LeftHomotopyRel f g)
    {Z : C} (i : Z ⟶ X) : LeftHomotopyRel (i ≫ f) (i ≫ g) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_cylinder
  obtain ⟨Q, _⟩ := Cylinder.exists_very_good Z
  have sq : CommSq (coprod.desc (i ≫ P.i₀) (i ≫ P.i₁)) Q.i P.π (Q.π ≫ i) := ⟨by aesop_cat⟩
  exact ⟨Q,
   ⟨{ h := sq.lift ≫ h.h
      h₀ := by
        have := coprod.inl ≫= sq.fac_left
        simp only [Q.inl_i_assoc, coprod.inl_desc] at this
        simp [reassoc_of% this]
      h₁ := by
        have := coprod.inr ≫= sq.fac_left
        simp only [Q.inr_i_assoc, coprod.inr_desc] at this
        simp [reassoc_of% this] }⟩⟩

end LeftHomotopyRel

variable (X Y Z : C)

/-- In a category with weak equivalences, this is the quotient of the type
of morphisms `X ⟶ Y` by the equivalence relation generated by left homotopies. -/
def LeftHomotopyClass [CategoryWithWeakEquivalences C] :=
  _root_.Quot (LeftHomotopyRel (X := X) (Y := Y))

variable {X Y Z}

/-- Given `f : X ⟶ Y`, this is the class of `f` in the quotient `LeftHomotopyClass X Y`. -/
def LeftHomotopyClass.mk [CategoryWithWeakEquivalences C] :
    (X ⟶ Y) → LeftHomotopyClass X Y := Quot.mk _

lemma LeftHomotopyClass.mk_surjective [CategoryWithWeakEquivalences C] :
    Function.Surjective (mk : (X ⟶ Y) → _) :=
  Quot.mk_surjective

namespace LeftHomotopyClass

lemma sound [CategoryWithWeakEquivalences C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g) :
    mk f = mk g := Quot.sound h

/-- The postcomposition map `LeftHomotopyClass X Y → (Y ⟶ Z) → LeftHomotopyClass X Z`. -/
def postcomp [CategoryWithWeakEquivalences C] :
    LeftHomotopyClass X Y → (Y ⟶ Z) → LeftHomotopyClass X Z :=
  fun f g ↦ Quot.lift (fun f ↦ mk (f ≫ g)) (fun _ _ h ↦ sound (h.postcomp g)) f

@[simp]
lemma postcomp_mk [CategoryWithWeakEquivalences C] (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk f).postcomp g = mk (f ≫ g) := rfl

lemma mk_eq_mk_iff [ModelCategory C] [IsCofibrant X] (f g : X ⟶ Y) :
    mk f = mk g ↔ LeftHomotopyRel f g := by
  rw [← (LeftHomotopyRel.equivalence X Y).eqvGen_iff]
  exact Quot.eq

end LeftHomotopyClass

end HomotopicalAlgebra
