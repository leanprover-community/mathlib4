/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Mathlib.CategoryTheory.ConcreteCategory.Basic

#align_import category_theory.morphism_property from "leanprover-community/mathlib"@"7f963633766aaa3ebc8253100a5229dd463040c7"

/-!
# Properties of morphisms

We provide the basic framework for talking about properties of morphisms.
The following meta-properties are defined

* `RespectsIso`: `P` respects isomorphisms if `P f → P (e ≫ f)` and `P f → P (f ≫ e)`, where
  `e` is an isomorphism.
* `StableUnderComposition`: `P` is stable under composition if `P f → P g → P (f ≫ g)`.
* `StableUnderBaseChange`: `P` is stable under base change if in all pullback
  squares, the left map satisfies `P` if the right map satisfies it.
* `StableUnderCobaseChange`: `P` is stable under cobase change if in all pushout
  squares, the right map satisfies `P` if the left map satisfies it.

-/


universe v u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] {D : Type*} [Category D]

/-- A `MorphismProperty C` is a class of morphisms between objects in `C`. -/
def MorphismProperty :=
  ∀ ⦃X Y : C⦄ (_ : X ⟶ Y), Prop

instance : CompleteLattice (MorphismProperty C) := by
  dsimp only [MorphismProperty]
  infer_instance

instance : Inhabited (MorphismProperty C) :=
  ⟨⊤⟩

lemma MorphismProperty.top_eq : (⊤ : MorphismProperty C) = fun _ _ _ => True := rfl

variable {C}

namespace MorphismProperty

lemma top_apply {X Y : C} (f : X ⟶ Y) : (⊤ : MorphismProperty C) f := by
  simp only [top_eq]

instance : HasSubset (MorphismProperty C) :=
  ⟨fun P₁ P₂ => ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (_ : P₁ f), P₂ f⟩

instance : IsTrans (MorphismProperty C) (· ⊆ ·) :=
  ⟨fun _ _ _ h₁₂ h₂₃ _ _ _ h => h₂₃ _ (h₁₂ _ h)⟩

instance : Inter (MorphismProperty C) :=
  ⟨fun P₁ P₂ _ _ f => P₁ f ∧ P₂ f⟩

lemma subset_iff_le (P Q : MorphismProperty C) : P ⊆ Q ↔ P ≤ Q := Iff.rfl

instance : IsAntisymm (MorphismProperty C) (· ⊆ ·) :=
  ⟨fun P Q => by simpa only [subset_iff_le] using le_antisymm⟩

instance : IsRefl (MorphismProperty C) (· ⊆ ·) :=
  ⟨fun P => by simpa only [subset_iff_le] using le_refl P⟩

/-- The morphism property in `Cᵒᵖ` associated to a morphism property in `C` -/
@[simp]
def op (P : MorphismProperty C) : MorphismProperty Cᵒᵖ := fun _ _ f => P f.unop

/-- The morphism property in `C` associated to a morphism property in `Cᵒᵖ` -/
@[simp]
def unop (P : MorphismProperty Cᵒᵖ) : MorphismProperty C := fun _ _ f => P f.op

theorem unop_op (P : MorphismProperty C) : P.op.unop = P :=
  rfl

theorem op_unop (P : MorphismProperty Cᵒᵖ) : P.unop.op = P :=
  rfl

/-- The inverse image of a `MorphismProperty D` by a functor `C ⥤ D` -/
def inverseImage (P : MorphismProperty D) (F : C ⥤ D) : MorphismProperty C := fun _ _ f =>
  P (F.map f)

/-- The image (up to isomorphisms) of a `MorphismProperty C` by a functor `C ⥤ D` -/
def map (P : MorphismProperty C) (F : C ⥤ D) : MorphismProperty D := fun _ _ f =>
  ∃ (X' Y' : C)  (f' : X' ⟶ Y') (_ : P f'), Nonempty (Arrow.mk (F.map f') ≅ Arrow.mk f)

lemma map_mem_map (P : MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f) :
    (P.map F) (F.map f) := ⟨X, Y, f, hf, ⟨Iso.refl _⟩⟩

lemma monotone_map (P Q : MorphismProperty C) (F : C ⥤ D) (h : P ⊆ Q) :
    P.map F ⊆ Q.map F := by
  intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩

/-- A morphism property `RespectsIso` if it still holds when composed with an isomorphism -/
def RespectsIso (P : MorphismProperty C) : Prop :=
  (∀ {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z), P f → P (e.hom ≫ f)) ∧
    ∀ {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y), P f → P (f ≫ e.hom)

theorem RespectsIso.op {P : MorphismProperty C} (h : RespectsIso P) : RespectsIso P.op :=
  ⟨fun e f hf => h.2 e.unop f.unop hf, fun e f hf => h.1 e.unop f.unop hf⟩

theorem RespectsIso.unop {P : MorphismProperty Cᵒᵖ} (h : RespectsIso P) : RespectsIso P.unop :=
  ⟨fun e f hf => h.2 e.op f.op hf, fun e f hf => h.1 e.op f.op hf⟩

/-- The closure by isomorphisms of a `MorphismProperty` -/
def isoClosure (P : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f => ∃ (Y₁ Y₂ : C) (f' : Y₁ ⟶ Y₂) (_ : P f'), Nonempty (Arrow.mk f' ≅ Arrow.mk f)

lemma subset_isoClosure (P : MorphismProperty C) : P ⊆ P.isoClosure :=
  fun _ _ f hf => ⟨_, _, f, hf, ⟨Iso.refl _⟩⟩

lemma isoClosure_respectsIso (P : MorphismProperty C) :
    RespectsIso P.isoClosure :=
  ⟨fun e f ⟨_, _, f', hf', ⟨iso⟩⟩ =>
    ⟨_, _, f', hf', ⟨Arrow.isoMk (asIso iso.hom.left ≪≫ e.symm)
      (asIso iso.hom.right) (by simp)⟩⟩,
  fun e f ⟨_, _, f', hf', ⟨iso⟩⟩ =>
    ⟨_, _, f', hf', ⟨Arrow.isoMk (asIso iso.hom.left)
      (asIso iso.hom.right ≪≫ e) (by simp)⟩⟩⟩

lemma monotone_isoClosure (P Q : MorphismProperty C) (h : P ⊆ Q) :
    P.isoClosure ⊆ Q.isoClosure := by
  intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩

/-- A morphism property is `StableUnderComposition` if the composition of two such morphisms
still falls in the class. -/
def StableUnderComposition (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Z⦄ (f : X ⟶ Y) (g : Y ⟶ Z), P f → P g → P (f ≫ g)

theorem StableUnderComposition.op {P : MorphismProperty C} (h : StableUnderComposition P) :
    StableUnderComposition P.op := fun _ _ _ f g hf hg => h g.unop f.unop hg hf

theorem StableUnderComposition.unop {P : MorphismProperty Cᵒᵖ} (h : StableUnderComposition P) :
    StableUnderComposition P.unop := fun _ _ _ f g hf hg => h g.op f.op hg hf

/-- A morphism property is `StableUnderInverse` if the inverse of a morphism satisfying
the property still falls in the class. -/
def StableUnderInverse (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y⦄ (e : X ≅ Y), P e.hom → P e.inv

theorem StableUnderInverse.op {P : MorphismProperty C} (h : StableUnderInverse P) :
    StableUnderInverse P.op := fun _ _ e he => h e.unop he

theorem StableUnderInverse.unop {P : MorphismProperty Cᵒᵖ} (h : StableUnderInverse P) :
    StableUnderInverse P.unop := fun _ _ e he => h e.op he

/-- A morphism property is `StableUnderBaseChange` if the base change of such a morphism
still falls in the class. -/
def StableUnderBaseChange (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Y' S : C⦄ ⦃f : X ⟶ S⦄ ⦃g : Y ⟶ S⦄ ⦃f' : Y' ⟶ Y⦄ ⦃g' : Y' ⟶ X⦄ (_ : IsPullback f' g' g f)
    (_ : P g), P g'

/-- A morphism property is `StableUnderCobaseChange` if the cobase change of such a morphism
still falls in the class. -/
def StableUnderCobaseChange (P : MorphismProperty C) : Prop :=
  ∀ ⦃A A' B B' : C⦄ ⦃f : A ⟶ A'⦄ ⦃g : A ⟶ B⦄ ⦃f' : B ⟶ B'⦄ ⦃g' : A' ⟶ B'⦄ (_ : IsPushout g f f' g')
    (_ : P f), P f'

theorem StableUnderComposition.respectsIso {P : MorphismProperty C} (hP : StableUnderComposition P)
    (hP' : ∀ {X Y} (e : X ≅ Y), P e.hom) : RespectsIso P :=
  ⟨fun e _ hf => hP _ _ (hP' e) hf, fun e _ hf => hP _ _ hf (hP' e)⟩

theorem RespectsIso.cancel_left_isIso {P : MorphismProperty C} (hP : RespectsIso P) {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g :=
  ⟨fun h => by simpa using hP.1 (asIso f).symm (f ≫ g) h, hP.1 (asIso f) g⟩

theorem RespectsIso.cancel_right_isIso {P : MorphismProperty C} (hP : RespectsIso P) {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f :=
  ⟨fun h => by simpa using hP.2 (asIso g).symm (f ≫ g) h, hP.2 (asIso g) f⟩

theorem RespectsIso.arrow_iso_iff {P : MorphismProperty C} (hP : RespectsIso P) {f g : Arrow C}
    (e : f ≅ g) : P f.hom ↔ P g.hom := by
  rw [← Arrow.inv_left_hom_right e.hom, hP.cancel_left_isIso, hP.cancel_right_isIso]

theorem RespectsIso.arrow_mk_iso_iff {P : MorphismProperty C} (hP : RespectsIso P) {W X Y Z : C}
    {f : W ⟶ X} {g : Y ⟶ Z} (e : Arrow.mk f ≅ Arrow.mk g) : P f ↔ P g :=
  hP.arrow_iso_iff e

theorem RespectsIso.of_respects_arrow_iso (P : MorphismProperty C)
    (hP : ∀ (f g : Arrow C) (_ : f ≅ g) (_ : P f.hom), P g.hom) : RespectsIso P := by
  constructor
  · intro X Y Z e f hf
    refine' hP (Arrow.mk f) (Arrow.mk (e.hom ≫ f)) (Arrow.isoMk e.symm (Iso.refl _) _) hf
    dsimp
    simp only [Iso.inv_hom_id_assoc, Category.comp_id]
  · intro X Y Z e f hf
    refine' hP (Arrow.mk f) (Arrow.mk (f ≫ e.hom)) (Arrow.isoMk (Iso.refl _) e _) hf
    dsimp
    simp only [Category.id_comp]

lemma RespectsIso.isoClosure_eq {P : MorphismProperty C} (hP : P.RespectsIso) :
    P.isoClosure = P := by
  refine' le_antisymm _ (P.subset_isoClosure)
  intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact (hP.arrow_mk_iso_iff e).1 hf'

@[simp]
lemma isoClosure_isoClosure (P : MorphismProperty C) :
    P.isoClosure.isoClosure = P.isoClosure :=
  P.isoClosure_respectsIso.isoClosure_eq

theorem StableUnderBaseChange.mk {P : MorphismProperty C} [HasPullbacks C] (hP₁ : RespectsIso P)
    (hP₂ : ∀ (X Y S : C) (f : X ⟶ S) (g : Y ⟶ S) (_ : P g), P (pullback.fst : pullback f g ⟶ X)) :
    StableUnderBaseChange P := fun X Y Y' S f g f' g' sq hg => by
  let e := sq.flip.isoPullback
  rw [← hP₁.cancel_left_isIso e.inv, sq.flip.isoPullback_inv_fst]
  exact hP₂ _ _ _ f g hg

theorem StableUnderBaseChange.respectsIso {P : MorphismProperty C} (hP : StableUnderBaseChange P) :
    RespectsIso P := by
  apply RespectsIso.of_respects_arrow_iso
  intro f g e
  exact hP (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))

theorem StableUnderBaseChange.fst {P : MorphismProperty C} (hP : StableUnderBaseChange P)
    {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] (H : P g) :
    P (pullback.fst : pullback f g ⟶ X) :=
  hP (IsPullback.of_hasPullback f g).flip H

theorem StableUnderBaseChange.snd {P : MorphismProperty C} (hP : StableUnderBaseChange P)
    {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] (H : P f) :
    P (pullback.snd : pullback f g ⟶ Y) :=
  hP (IsPullback.of_hasPullback f g) H

theorem StableUnderBaseChange.baseChange_obj [HasPullbacks C] {P : MorphismProperty C}
    (hP : StableUnderBaseChange P) {S S' : C} (f : S' ⟶ S) (X : Over S) (H : P X.hom) :
    P ((baseChange f).obj X).hom :=
  hP.snd X.hom f H

theorem StableUnderBaseChange.baseChange_map [HasPullbacks C] {P : MorphismProperty C}
    (hP : StableUnderBaseChange P) {S S' : C} (f : S' ⟶ S) {X Y : Over S} (g : X ⟶ Y)
    (H : P g.left) : P ((baseChange f).map g).left := by
  let e :=
    pullbackRightPullbackFstIso Y.hom f g.left ≪≫
      pullback.congrHom (g.w.trans (Category.comp_id _)) rfl
  have : e.inv ≫ pullback.snd = ((baseChange f).map g).left := by
    ext <;> dsimp <;> simp
  rw [← this, hP.respectsIso.cancel_left_isIso]
  exact hP.snd _ _ H

theorem StableUnderBaseChange.pullback_map [HasPullbacks C] {P : MorphismProperty C}
    (hP : StableUnderBaseChange P) (hP' : StableUnderComposition P) {S X X' Y Y' : C} {f : X ⟶ S}
    {g : Y ⟶ S} {f' : X' ⟶ S} {g' : Y' ⟶ S} {i₁ : X ⟶ X'} {i₂ : Y ⟶ Y'} (h₁ : P i₁) (h₂ : P i₂)
    (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂)) := by
  have :
    pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂) =
      ((pullbackSymmetry _ _).hom ≫
          ((baseChange _).map (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g')).left) ≫
        (pullbackSymmetry _ _).hom ≫
          ((baseChange g').map (Over.homMk _ e₁.symm : Over.mk f ⟶ Over.mk f')).left :=
    by ext <;> dsimp <;> simp
  rw [this]
  apply hP' <;> rw [hP.respectsIso.cancel_left_isIso]
  exacts [hP.baseChange_map _ (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g') h₂,
    hP.baseChange_map _ (Over.homMk _ e₁.symm : Over.mk f ⟶ Over.mk f') h₁]

theorem StableUnderCobaseChange.mk {P : MorphismProperty C} [HasPushouts C] (hP₁ : RespectsIso P)
    (hP₂ : ∀ (A B A' : C) (f : A ⟶ A') (g : A ⟶ B) (_ : P f), P (pushout.inr : B ⟶ pushout f g)) :
    StableUnderCobaseChange P := fun A A' B B' f g f' g' sq hf => by
  let e := sq.flip.isoPushout
  rw [← hP₁.cancel_right_isIso _ e.hom, sq.flip.inr_isoPushout_hom]
  exact hP₂ _ _ _ f g hf

theorem StableUnderCobaseChange.respectsIso {P : MorphismProperty C}
    (hP : StableUnderCobaseChange P) : RespectsIso P :=
  RespectsIso.of_respects_arrow_iso _ fun _ _ e => hP (IsPushout.of_horiz_isIso (CommSq.mk e.hom.w))

theorem StableUnderCobaseChange.inl {P : MorphismProperty C} (hP : StableUnderCobaseChange P)
    {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g] (H : P g) :
    P (pushout.inl : A' ⟶ pushout f g) :=
  hP (IsPushout.of_hasPushout f g) H

theorem StableUnderCobaseChange.inr {P : MorphismProperty C} (hP : StableUnderCobaseChange P)
    {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g] (H : P f) :
    P (pushout.inr : B ⟶ pushout f g) :=
  hP (IsPushout.of_hasPushout f g).flip H

theorem StableUnderCobaseChange.op {P : MorphismProperty C} (hP : StableUnderCobaseChange P) :
    StableUnderBaseChange P.op := fun _ _ _ _ _ _ _ _ sq hg => hP sq.unop hg

theorem StableUnderCobaseChange.unop {P : MorphismProperty Cᵒᵖ} (hP : StableUnderCobaseChange P) :
    StableUnderBaseChange P.unop := fun _ _ _ _ _ _ _ _ sq hg => hP sq.op hg

theorem StableUnderBaseChange.op {P : MorphismProperty C} (hP : StableUnderBaseChange P) :
    StableUnderCobaseChange P.op := fun _ _ _ _ _ _ _ _ sq hf => hP sq.unop hf

theorem StableUnderBaseChange.unop {P : MorphismProperty Cᵒᵖ} (hP : StableUnderBaseChange P) :
    StableUnderCobaseChange P.unop := fun _ _ _ _ _ _ _ _ sq hf => hP sq.op hf

/-- If `P : MorphismProperty C` and `F : C ⥤ D`, then
`P.IsInvertedBy F` means that all morphisms in `P` are mapped by `F`
to isomorphisms in `D`. -/
def IsInvertedBy (P : MorphismProperty C) (F : C ⥤ D) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (_ : P f), IsIso (F.map f)

namespace IsInvertedBy

lemma of_subset (P Q : MorphismProperty C) (F : C ⥤ D) (hQ : Q.IsInvertedBy F) (h : P ⊆ Q) :
    P.IsInvertedBy F :=
  fun _ _ _ hf => hQ _ (h _ hf)

theorem of_comp {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    (W : MorphismProperty C₁) (F : C₁ ⥤ C₂) (hF : W.IsInvertedBy F) (G : C₂ ⥤ C₃) :
    W.IsInvertedBy (F ⋙ G) := fun X Y f hf => by
  haveI := hF f hf
  dsimp
  infer_instance

theorem op {W : MorphismProperty C} {L : C ⥤ D} (h : W.IsInvertedBy L) : W.op.IsInvertedBy L.op :=
  fun X Y f hf => by
  haveI := h f.unop hf
  dsimp
  infer_instance

theorem rightOp {W : MorphismProperty C} {L : Cᵒᵖ ⥤ D} (h : W.op.IsInvertedBy L) :
    W.IsInvertedBy L.rightOp := fun X Y f hf => by
  haveI := h f.op hf
  dsimp
  infer_instance

theorem leftOp {W : MorphismProperty C} {L : C ⥤ Dᵒᵖ} (h : W.IsInvertedBy L) :
    W.op.IsInvertedBy L.leftOp := fun X Y f hf => by
  haveI := h f.unop hf
  dsimp
  infer_instance

theorem unop {W : MorphismProperty C} {L : Cᵒᵖ ⥤ Dᵒᵖ} (h : W.op.IsInvertedBy L) :
    W.IsInvertedBy L.unop := fun X Y f hf => by
  haveI := h f.op hf
  dsimp
  infer_instance

end IsInvertedBy

/-- Given `app : Π X, F₁.obj X ⟶ F₂.obj X` where `F₁` and `F₂` are two functors,
this is the `morphism_property C` satisfied by the morphisms in `C` with respect
to whom `app` is natural. -/
@[simp]
def naturalityProperty {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) : MorphismProperty C :=
  fun X Y f => F₁.map f ≫ app Y = app X ≫ F₂.map f

namespace naturalityProperty

theorem stableUnderComposition {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (naturalityProperty app).StableUnderComposition := fun X Y Z f g hf hg => by
  simp only [naturalityProperty] at hf hg ⊢
  simp only [Functor.map_comp, Category.assoc, hg]
  slice_lhs 1 2 => rw [hf]
  rw [Category.assoc]

theorem stableUnderInverse {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (naturalityProperty app).StableUnderInverse := fun X Y e he => by
  simp only [naturalityProperty] at he ⊢
  rw [← cancel_epi (F₁.map e.hom)]
  slice_rhs 1 2 => rw [he]
  simp only [Category.assoc, ← F₁.map_comp_assoc, ← F₂.map_comp, e.hom_inv_id, Functor.map_id,
    Category.id_comp, Category.comp_id]

end naturalityProperty

theorem RespectsIso.inverseImage {P : MorphismProperty D} (h : RespectsIso P) (F : C ⥤ D) :
    RespectsIso (P.inverseImage F) := by
  constructor
  all_goals
    intro X Y Z e f hf
    dsimp [MorphismProperty.inverseImage]
    rw [F.map_comp]
  exacts [h.1 (F.mapIso e) (F.map f) hf, h.2 (F.mapIso e) (F.map f) hf]

theorem StableUnderComposition.inverseImage {P : MorphismProperty D} (h : StableUnderComposition P)
    (F : C ⥤ D) : StableUnderComposition (P.inverseImage F) := fun X Y Z f g hf hg => by
  simpa only [← F.map_comp] using h (F.map f) (F.map g) hf hg

variable (C)

/-- The `MorphismProperty C` satisfied by isomorphisms in `C`. -/
def isomorphisms : MorphismProperty C := fun _ _ f => IsIso f

/-- The `MorphismProperty C` satisfied by monomorphisms in `C`. -/
def monomorphisms : MorphismProperty C := fun _ _ f => Mono f

/-- The `MorphismProperty C` satisfied by epimorphisms in `C`. -/
def epimorphisms : MorphismProperty C := fun _ _ f => Epi f

section

variable {C}
variable {X Y : C} (f : X ⟶ Y)

@[simp]
theorem isomorphisms.iff : (isomorphisms C) f ↔ IsIso f := by rfl

@[simp]
theorem monomorphisms.iff : (monomorphisms C) f ↔ Mono f := by rfl

@[simp]
theorem epimorphisms.iff : (epimorphisms C) f ↔ Epi f := by rfl

theorem isomorphisms.infer_property [hf : IsIso f] : (isomorphisms C) f :=
  hf

theorem monomorphisms.infer_property [hf : Mono f] : (monomorphisms C) f :=
  hf

theorem epimorphisms.infer_property [hf : Epi f] : (epimorphisms C) f :=
  hf

end

theorem RespectsIso.monomorphisms : RespectsIso (monomorphisms C) := by
  constructor <;>
    · intro X Y Z e f
      simp only [monomorphisms.iff]
      intro
      apply mono_comp

theorem RespectsIso.epimorphisms : RespectsIso (epimorphisms C) := by
  constructor <;>
    · intro X Y Z e f
      simp only [epimorphisms.iff]
      intro
      apply epi_comp

theorem RespectsIso.isomorphisms : RespectsIso (isomorphisms C) := by
  constructor <;>
    · intro X Y Z e f
      simp only [isomorphisms.iff]
      intro
      infer_instance

theorem StableUnderComposition.isomorphisms : StableUnderComposition (isomorphisms C) :=
  fun X Y Z f g hf hg => by
  rw [isomorphisms.iff] at hf hg ⊢
  haveI := hf
  haveI := hg
  infer_instance

theorem StableUnderComposition.monomorphisms : StableUnderComposition (monomorphisms C) :=
  fun X Y Z f g hf hg => by
  rw [monomorphisms.iff] at hf hg ⊢
  haveI := hf
  haveI := hg
  apply mono_comp

theorem StableUnderComposition.epimorphisms : StableUnderComposition (epimorphisms C) :=
  fun X Y Z f g hf hg => by
  rw [epimorphisms.iff] at hf hg ⊢
  haveI := hf
  haveI := hg
  apply epi_comp

variable {C}


-- porting note: removed @[nolint has_nonempty_instance]
/-- The full subcategory of `C ⥤ D` consisting of functors inverting morphisms in `W` -/
def FunctorsInverting (W : MorphismProperty C) (D : Type*) [Category D] :=
  FullSubcategory fun F : C ⥤ D => W.IsInvertedBy F

@[ext]
lemma FunctorsInverting.ext {W : MorphismProperty C} {F₁ F₂ : FunctorsInverting W D}
    (h : F₁.obj = F₂.obj) : F₁ = F₂ := by
  cases F₁
  cases F₂
  subst h
  rfl

instance (W : MorphismProperty C) (D : Type*) [Category D] : Category (FunctorsInverting W D) :=
  FullSubcategory.category _

-- Porting note: add another `@[ext]` lemma
-- since `ext` can't see through the definition to use `NatTrans.ext`.
-- See https://github.com/leanprover-community/mathlib4/issues/5229
@[ext]
lemma FunctorsInverting.hom_ext {W : MorphismProperty C} {F₁ F₂ : FunctorsInverting W D}
    {α β : F₁ ⟶ F₂} (h : α.app = β.app) : α = β :=
  NatTrans.ext _ _ h

/-- A constructor for `W.FunctorsInverting D` -/
def FunctorsInverting.mk {W : MorphismProperty C} {D : Type*} [Category D] (F : C ⥤ D)
    (hF : W.IsInvertedBy F) : W.FunctorsInverting D :=
  ⟨F, hF⟩

theorem IsInvertedBy.iff_of_iso (W : MorphismProperty C) {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) :
    W.IsInvertedBy F₁ ↔ W.IsInvertedBy F₂ := by
  dsimp [IsInvertedBy]
  simp only [NatIso.isIso_map_iff e]

@[simp]
lemma IsInvertedBy.isoClosure_iff (W : MorphismProperty C) (F : C ⥤ D) :
    W.isoClosure.IsInvertedBy F ↔ W.IsInvertedBy F := by
  constructor
  · intro h X Y f hf
    exact h _ (W.subset_isoClosure _ hf)
  · intro h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    have : f = e.inv.left ≫ f' ≫ e.hom.right := by
      erw [← e.hom.w, ← Arrow.comp_left_assoc, e.inv_hom_id, Category.id_comp]
      rfl
    simp only [this, F.map_comp]
    have := h _ hf'
    infer_instance

@[simp]
lemma IsInvertedBy.iff_comp {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    (W : MorphismProperty C₁) (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) [ReflectsIsomorphisms G] :
    W.IsInvertedBy (F ⋙ G) ↔ W.IsInvertedBy F := by
  constructor
  · intro h X Y f hf
    have : IsIso (G.map (F.map f)) := h _ hf
    exact isIso_of_reflects_iso (F.map f) G
  · intro hF
    exact IsInvertedBy.of_comp W F hF G

lemma isoClosure_subset_iff (P Q : MorphismProperty C) (hQ : RespectsIso Q) :
    P.isoClosure ⊆ Q ↔ P ⊆ Q := by
  constructor
  · exact P.subset_isoClosure.trans
  · intro h
    exact (monotone_isoClosure _ _ h).trans (by rw [hQ.isoClosure_eq])

lemma map_respectsIso (P : MorphismProperty C) (F : C ⥤ D) :
    (P.map F).RespectsIso := by
  apply RespectsIso.of_respects_arrow_iso
  intro f g e ⟨X', Y', f', hf', ⟨e'⟩⟩
  exact ⟨X', Y', f', hf', ⟨e' ≪≫ e⟩⟩

lemma map_subset_iff (P : MorphismProperty C) (F : C ⥤ D)
    (Q : MorphismProperty D) (hQ : RespectsIso Q):
    P.map F ⊆ Q ↔ ∀ (X Y : C) (f : X ⟶ Y), P f → Q (F.map f) := by
  constructor
  · intro h X Y f hf
    exact h (F.map f) (map_mem_map P F f hf)
  · intro h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact (hQ.arrow_mk_iso_iff e).1 (h _ _ _ hf')

lemma IsInvertedBy.iff_map_subset_isomorphisms (W : MorphismProperty C) (F : C ⥤ D) :
    W.IsInvertedBy F ↔ W.map F ⊆ isomorphisms D := by
  rw [map_subset_iff _ _ _ (RespectsIso.isomorphisms D)]
  constructor
  · intro h X Y f hf
    exact h f hf
  · intro h X Y f hf
    exact h X Y f hf

@[simp]
lemma map_isoClosure (P : MorphismProperty C) (F : C ⥤ D) :
    P.isoClosure.map F = P.map F := by
  apply subset_antisymm
  · rw [map_subset_iff _ _ _ (P.map_respectsIso F)]
    intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact ⟨_, _, f', hf', ⟨F.mapArrow.mapIso e⟩⟩
  · exact monotone_map _ _ _ (subset_isoClosure P)

lemma map_id_eq_isoClosure (P : MorphismProperty C) :
    P.map (𝟭 _) = P.isoClosure := by
  apply subset_antisymm
  · rw [map_subset_iff _ _ _ P.isoClosure_respectsIso]
    intro X Y f hf
    exact P.subset_isoClosure _ hf
  · intro X Y f hf
    exact hf

lemma map_id (P : MorphismProperty C) (hP : RespectsIso P) :
    P.map (𝟭 _) = P := by
  rw [map_id_eq_isoClosure, hP.isoClosure_eq]

@[simp]
lemma map_map (P : MorphismProperty C) (F : C ⥤ D) {E : Type*} [Category E] (G : D ⥤ E) :
    (P.map F).map G = P.map (F ⋙ G) := by
  apply subset_antisymm
  · rw [map_subset_iff _ _ _ (map_respectsIso _ (F ⋙ G))]
    intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact ⟨X', Y', f', hf', ⟨G.mapArrow.mapIso e⟩⟩
  · rw [map_subset_iff _ _ _ (map_respectsIso _ G)]
    intro X Y f hf
    exact map_mem_map _ _ _ (map_mem_map _ _ _ hf)

lemma IsInvertedBy.map_iff {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    (W : MorphismProperty C₁) (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) :
    (W.map F).IsInvertedBy G ↔ W.IsInvertedBy (F ⋙ G) := by
  simp only [IsInvertedBy.iff_map_subset_isomorphisms, map_map]

lemma map_eq_of_iso (P : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G) :
    P.map F = P.map G := by
  revert F G e
  suffices ∀ {F G : C ⥤ D} (_ : F ≅ G), P.map F ⊆ P.map G from
    fun F G e => le_antisymm (this e) (this e.symm)
  intro F G e X Y f ⟨X', Y', f', hf', ⟨e'⟩⟩
  exact ⟨X', Y', f', hf', ⟨((Functor.mapArrowFunctor _ _).mapIso e.symm).app (Arrow.mk f') ≪≫ e'⟩⟩

lemma map_inverseImage_subset (P : MorphismProperty D) (F : C ⥤ D) :
    (P.inverseImage F).map F ⊆ P.isoClosure :=
  fun _ _ _ ⟨_, _, f, hf, ⟨e⟩⟩ => ⟨_, _, F.map f, hf, ⟨e⟩⟩

lemma inverseImage_equivalence_inverse_eq_map_functor
    (P : MorphismProperty D) (hP : RespectsIso P) (E : C ≌ D) :
    P.inverseImage E.functor = P.map E.inverse := by
  apply subset_antisymm
  · intro X Y f hf
    refine' ⟨_, _, _, hf, ⟨_⟩⟩
    exact ((Functor.mapArrowFunctor _ _).mapIso E.unitIso.symm).app (Arrow.mk f)
  · rw [map_subset_iff _ _ _ (hP.inverseImage E.functor)]
    intro X Y f hf
    exact (hP.arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso E.counitIso).app (Arrow.mk f))).2 hf

lemma inverseImage_equivalence_functor_eq_map_inverse
    (Q : MorphismProperty C) (hQ : RespectsIso Q) (E : C ≌ D) :
    Q.inverseImage E.inverse = Q.map E.functor :=
  inverseImage_equivalence_inverse_eq_map_functor Q hQ E.symm

lemma map_inverseImage_eq_of_isEquivalence
    (P : MorphismProperty D) (hP : P.RespectsIso) (F : C ⥤ D) [IsEquivalence F] :
    (P.inverseImage F).map F = P := by
  erw [P.inverseImage_equivalence_inverse_eq_map_functor hP F.asEquivalence, map_map,
    P.map_eq_of_iso F.asEquivalence.counitIso, map_id _ hP]

lemma inverseImage_map_eq_of_isEquivalence
    (P : MorphismProperty C) (hP : P.RespectsIso) (F : C ⥤ D) [IsEquivalence F] :
    (P.map F).inverseImage F = P := by
  erw [((P.map F).inverseImage_equivalence_inverse_eq_map_functor
    (P.map_respectsIso F) (F.asEquivalence)), map_map,
    P.map_eq_of_iso F.asEquivalence.unitIso.symm, map_id _ hP]

section Diagonal

variable [HasPullbacks C] {P : MorphismProperty C}

/-- For `P : MorphismProperty C`, `P.diagonal` is a morphism property that holds for `f : X ⟶ Y`
whenever `P` holds for `X ⟶ Y xₓ Y`. -/
def diagonal (P : MorphismProperty C) : MorphismProperty C := fun _ _ f => P (pullback.diagonal f)

theorem diagonal_iff {X Y : C} {f : X ⟶ Y} : P.diagonal f ↔ P (pullback.diagonal f) :=
  Iff.rfl

theorem RespectsIso.diagonal (hP : P.RespectsIso) : P.diagonal.RespectsIso := by
  constructor
  · introv H
    rwa [diagonal_iff, pullback.diagonal_comp, hP.cancel_left_isIso, hP.cancel_left_isIso,
      ← hP.cancel_right_isIso _
        (pullback.map (e.hom ≫ f) (e.hom ≫ f) f f e.hom e.hom (𝟙 Z) (by simp) (by simp)),
      ← pullback.condition, hP.cancel_left_isIso]
  · introv H
    delta diagonal
    rwa [pullback.diagonal_comp, hP.cancel_right_isIso]

theorem StableUnderComposition.diagonal (hP : StableUnderComposition P) (hP' : RespectsIso P)
    (hP'' : StableUnderBaseChange P) : P.diagonal.StableUnderComposition := by
  introv X h₁ h₂
  rw [diagonal_iff, pullback.diagonal_comp]
  exact hP _ _ h₁ (by simpa [hP'.cancel_left_isIso] using hP''.snd _ _ h₂)

theorem StableUnderBaseChange.diagonal (hP : StableUnderBaseChange P) (hP' : RespectsIso P) :
    P.diagonal.StableUnderBaseChange :=
  StableUnderBaseChange.mk hP'.diagonal
    (by
      introv h
      rw [diagonal_iff, diagonal_pullback_fst, hP'.cancel_left_isIso, hP'.cancel_right_isIso]
      exact hP.baseChange_map f _ (by simpa))

end Diagonal

section Universally

/-- `P.universally` holds for a morphism `f : X ⟶ Y` iff `P` holds for all `X ×[Y] Y' ⟶ Y'`. -/
def universally (P : MorphismProperty C) : MorphismProperty C := fun X Y f =>
  ∀ ⦃X' Y' : C⦄ (i₁ : X' ⟶ X) (i₂ : Y' ⟶ Y) (f' : X' ⟶ Y') (_ : IsPullback f' i₁ i₂ f), P f'

theorem universally_respectsIso (P : MorphismProperty C) : P.universally.RespectsIso := by
  constructor
  · intro X Y Z e f hf X' Z' i₁ i₂ f' H
    have : IsPullback (𝟙 _) (i₁ ≫ e.hom) i₁ e.inv :=
      IsPullback.of_horiz_isIso
        ⟨by rw [Category.id_comp, Category.assoc, e.hom_inv_id, Category.comp_id]⟩
    exact hf _ _ _
      (by simpa only [Iso.inv_hom_id_assoc, Category.id_comp] using this.paste_horiz H)
  · intro X Y Z e f hf X' Z' i₁ i₂ f' H
    have : IsPullback (𝟙 _) i₂ (i₂ ≫ e.inv) e.inv :=
      IsPullback.of_horiz_isIso ⟨Category.id_comp _⟩
    exact hf _ _ _ (by simpa only [Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.comp_id] using H.paste_horiz this)

theorem universally_stableUnderBaseChange (P : MorphismProperty C) :
    P.universally.StableUnderBaseChange := fun _ _ _ _ _ _ _ _ H h₁ _ _ _ _ _ H' =>
  h₁ _ _ _ (H'.paste_vert H.flip)

theorem StableUnderComposition.universally [HasPullbacks C] {P : MorphismProperty C}
    (hP : P.StableUnderComposition) : P.universally.StableUnderComposition := by
  intro X Y Z f g hf hg X' Z' i₁ i₂ f' H
  have := pullback.lift_fst _ _ (H.w.trans (Category.assoc _ _ _).symm)
  rw [← this] at H ⊢
  apply hP _ _ _ (hg _ _ _ <| IsPullback.of_hasPullback _ _)
  exact hf _ _ _ (H.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback i₂ g))

theorem universally_le (P : MorphismProperty C) : P.universally ≤ P := by
  intro X Y f hf
  exact hf (𝟙 _) (𝟙 _) _ (IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, Category.id_comp]⟩)

theorem StableUnderBaseChange.universally_eq {P : MorphismProperty C}
    (hP : P.StableUnderBaseChange) : P.universally = P :=
  P.universally_le.antisymm fun _ _ _ hf _ _ _ _ _ H => hP H.flip hf

theorem universally_mono : Monotone (universally : MorphismProperty C → MorphismProperty C) :=
  fun _ _ h _ _ _ h₁ _ _ _ _ _ H => h _ _ _ (h₁ _ _ _ H)

end Universally

section Bijective

variable [ConcreteCategory C]

open Function

attribute [local instance] ConcreteCategory.funLike ConcreteCategory.hasCoeToSort

variable (C)

/-- Injectiveness (in a concrete category) as a `MorphismProperty` -/
protected def injective : MorphismProperty C := fun _ _ f => Injective f

/-- Surjectiveness (in a concrete category) as a `MorphismProperty` -/
protected def surjective : MorphismProperty C := fun _ _ f => Surjective f

/-- Bijectiveness (in a concrete category) as a `MorphismProperty` -/
protected def bijective : MorphismProperty C := fun _ _ f => Bijective f

theorem bijective_eq_sup :
    MorphismProperty.bijective C = MorphismProperty.injective C ⊓ MorphismProperty.surjective C :=
  rfl

theorem injective_stableUnderComposition : (MorphismProperty.injective C).StableUnderComposition :=
  fun X Y Z f g hf hg => by
  delta MorphismProperty.injective
  rw [coe_comp]
  exact hg.comp hf

theorem surjective_stableUnderComposition :
    (MorphismProperty.surjective C).StableUnderComposition := fun X Y Z f g hf hg => by
  delta MorphismProperty.surjective
  rw [coe_comp]
  exact hg.comp hf

theorem bijective_stableUnderComposition : (MorphismProperty.bijective C).StableUnderComposition :=
  fun X Y Z f g hf hg => by
  delta MorphismProperty.bijective
  rw [coe_comp]
  exact hg.comp hf

theorem injective_respectsIso : (MorphismProperty.injective C).RespectsIso :=
  (injective_stableUnderComposition C).respectsIso
    (fun e => ((forget C).mapIso e).toEquiv.injective)

theorem surjective_respectsIso : (MorphismProperty.surjective C).RespectsIso :=
  (surjective_stableUnderComposition C).respectsIso
    (fun e => ((forget C).mapIso e).toEquiv.surjective)

theorem bijective_respectsIso : (MorphismProperty.bijective C).RespectsIso :=
  (bijective_stableUnderComposition C).respectsIso
    (fun e => ((forget C).mapIso e).toEquiv.bijective)

end Bijective

/-- Typeclass expressing that a morphism property contain identities. -/
class ContainsIdentities (W : MorphismProperty C) : Prop :=
  /-- for all `X : C`, the identity of `X` satisfies the morphism property -/
  id_mem' : ∀ (X : C), W (𝟙 X)

lemma id_mem (W : MorphismProperty C) [W.ContainsIdentities] (X : C) :
    W (𝟙 X) := ContainsIdentities.id_mem' X

namespace ContainsIdentities

instance op (W : MorphismProperty C) [W.ContainsIdentities] :
    W.op.ContainsIdentities := ⟨fun X => W.id_mem X.unop⟩

instance unop (W : MorphismProperty Cᵒᵖ) [W.ContainsIdentities] :
    W.unop.ContainsIdentities := ⟨fun X => W.id_mem (Opposite.op X)⟩

lemma of_op (W : MorphismProperty C) [W.op.ContainsIdentities] :
    W.ContainsIdentities := (inferInstance : W.op.unop.ContainsIdentities)

lemma of_unop (W : MorphismProperty Cᵒᵖ) [W.unop.ContainsIdentities] :
    W.ContainsIdentities := (inferInstance : W.unop.op.ContainsIdentities)

end ContainsIdentities

/-- A morphism property is multiplicative if it contains identities and is stable by
composition. -/
class IsMultiplicative (W : MorphismProperty C) extends W.ContainsIdentities : Prop :=
  /-- compatibility of  -/
  stableUnderComposition : W.StableUnderComposition

lemma comp_mem (W : MorphismProperty C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g)
    [IsMultiplicative W] : W (f ≫ g) :=
  IsMultiplicative.stableUnderComposition f g hf hg

namespace IsMultiplicative

instance op (W : MorphismProperty C) [IsMultiplicative W] : IsMultiplicative W.op where
  stableUnderComposition := fun _ _ _ f g hf hg => W.comp_mem g.unop f.unop hg hf

instance unop (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W] : IsMultiplicative W.unop where
  id_mem' _ := W.id_mem _
  stableUnderComposition := fun _ _ _ f g hf hg => W.comp_mem g.op f.op hg hf

lemma of_op (W : MorphismProperty C) [IsMultiplicative W.op] : IsMultiplicative W :=
  (inferInstance : IsMultiplicative W.op.unop)

lemma of_unop (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W.unop] : IsMultiplicative W :=
  (inferInstance : IsMultiplicative W.unop.op)

end IsMultiplicative

end MorphismProperty

end CategoryTheory
