/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Properties of morphisms

We provide the basic framework for talking about properties of morphisms.
The following meta-property is defined

* `RespectsIso`: `P` respects isomorphisms if `P f → P (e ≫ f)` and `P f → P (f ≫ e)`, where
  `e` is an isomorphism.

-/


universe w v v' u u'

open CategoryTheory Opposite

noncomputable section

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] {D : Type*} [Category D]

/-- A `MorphismProperty C` is a class of morphisms between objects in `C`. -/
def MorphismProperty :=
  ∀ ⦃X Y : C⦄ (_ : X ⟶ Y), Prop

instance : CompleteBooleanAlgebra (MorphismProperty C) where
  le P₁ P₂ := ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P₁ f → P₂ f
  __ := inferInstanceAs (CompleteBooleanAlgebra (∀ ⦃X Y : C⦄ (_ : X ⟶ Y), Prop))

lemma MorphismProperty.le_def {P Q : MorphismProperty C} :
    P ≤ Q ↔ ∀ {X Y : C} (f : X ⟶ Y), P f → Q f := Iff.rfl

instance : Inhabited (MorphismProperty C) :=
  ⟨⊤⟩

lemma MorphismProperty.top_eq : (⊤ : MorphismProperty C) = fun _ _ _ => True := rfl

variable {C}

namespace MorphismProperty

@[ext]
lemma ext (W W' : MorphismProperty C) (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) :
    W = W' := by
  funext X Y f
  rw [h]

@[simp]
lemma top_apply {X Y : C} (f : X ⟶ Y) : (⊤ : MorphismProperty C) f := by
  simp only [top_eq]

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

@[simp]
lemma inverseImage_iff (P : MorphismProperty D) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    P.inverseImage F f ↔ P (F.map f) := by rfl

/-- The image (up to isomorphisms) of a `MorphismProperty C` by a functor `C ⥤ D` -/
def map (P : MorphismProperty C) (F : C ⥤ D) : MorphismProperty D := fun _ _ f =>
  ∃ (X' Y' : C) (f' : X' ⟶ Y') (_ : P f'), Nonempty (Arrow.mk (F.map f') ≅ Arrow.mk f)

lemma map_mem_map (P : MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f) :
    (P.map F) (F.map f) := ⟨X, Y, f, hf, ⟨Iso.refl _⟩⟩

lemma monotone_map (F : C ⥤ D) :
    Monotone (map · F) := by
  intro P Q h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩

/-- A morphism property `RespectsIso` if it still holds when composed with an isomorphism -/
class RespectsIso (P : MorphismProperty C) : Prop where
  precomp {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z) (hf : P f) : P (e.hom ≫ f)
  postcomp {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y) (hf : P f) : P (f ≫ e.hom)

instance RespectsIso.op (P : MorphismProperty C) [h : RespectsIso P] : RespectsIso P.op :=
  ⟨fun e f hf => h.2 e.unop f.unop hf, fun e f hf => h.1 e.unop f.unop hf⟩

instance RespectsIso.unop (P : MorphismProperty Cᵒᵖ) [h : RespectsIso P] : RespectsIso P.unop :=
  ⟨fun e f hf => h.2 e.op f.op hf, fun e f hf => h.1 e.op f.op hf⟩

/-- The intersection of two isomorphism respecting morphism properties respects isomorphisms. -/
instance RespectsIso.inf (P Q : MorphismProperty C) [RespectsIso P] [RespectsIso Q] :
    RespectsIso (P ⊓ Q) where
  precomp e f hf := ⟨RespectsIso.precomp e f hf.left, RespectsIso.precomp e f hf.right⟩
  postcomp e f hf := ⟨RespectsIso.postcomp e f hf.left, RespectsIso.postcomp e f hf.right⟩

/-- The closure by isomorphisms of a `MorphismProperty` -/
def isoClosure (P : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f => ∃ (Y₁ Y₂ : C) (f' : Y₁ ⟶ Y₂) (_ : P f'), Nonempty (Arrow.mk f' ≅ Arrow.mk f)

lemma le_isoClosure (P : MorphismProperty C) : P ≤ P.isoClosure :=
  fun _ _ f hf => ⟨_, _, f, hf, ⟨Iso.refl _⟩⟩

instance isoClosure_respectsIso (P : MorphismProperty C) :
    RespectsIso P.isoClosure where
  precomp := fun e f ⟨_, _, f', hf', ⟨iso⟩⟩ => ⟨_, _, f', hf',
      ⟨Arrow.isoMk (asIso iso.hom.left ≪≫ e.symm) (asIso iso.hom.right) (by simp)⟩⟩
  postcomp := fun e f ⟨_, _, f', hf', ⟨iso⟩⟩ => ⟨_, _, f', hf',
      ⟨Arrow.isoMk (asIso iso.hom.left) (asIso iso.hom.right ≪≫ e) (by simp)⟩⟩

lemma monotone_isoClosure : Monotone (isoClosure (C := C)) := by
  intro P Q h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩

theorem cancel_left_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g :=
  ⟨fun h => by simpa using hP.1 (asIso f).symm (f ≫ g) h, hP.1 (asIso f) g⟩

theorem cancel_right_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f :=
  ⟨fun h => by simpa using hP.2 (asIso g).symm (f ≫ g) h, hP.2 (asIso g) f⟩

theorem arrow_iso_iff (P : MorphismProperty C) [RespectsIso P] {f g : Arrow C}
    (e : f ≅ g) : P f.hom ↔ P g.hom := by
  simp [← Arrow.inv_left_hom_right e.hom, cancel_left_of_respectsIso,
    cancel_right_of_respectsIso]

theorem arrow_mk_iso_iff (P : MorphismProperty C) [RespectsIso P] {W X Y Z : C}
    {f : W ⟶ X} {g : Y ⟶ Z} (e : Arrow.mk f ≅ Arrow.mk g) : P f ↔ P g :=
  P.arrow_iso_iff e

theorem RespectsIso.of_respects_arrow_iso (P : MorphismProperty C)
    (hP : ∀ (f g : Arrow C) (_ : f ≅ g) (_ : P f.hom), P g.hom) : RespectsIso P := by
  constructor
  · intro X Y Z e f hf
    refine hP (Arrow.mk f) (Arrow.mk (e.hom ≫ f)) (Arrow.isoMk e.symm (Iso.refl _) ?_) hf
    dsimp
    simp only [Iso.inv_hom_id_assoc, Category.comp_id]
  · intro X Y Z e f hf
    refine hP (Arrow.mk f) (Arrow.mk (f ≫ e.hom)) (Arrow.isoMk (Iso.refl _) e ?_) hf
    dsimp
    simp only [Category.id_comp]

lemma isoClosure_eq_iff (P : MorphismProperty C) :
    P.isoClosure = P ↔ P.RespectsIso := by
  refine ⟨(· ▸ P.isoClosure_respectsIso), fun hP ↦ le_antisymm ?_ (P.le_isoClosure)⟩
  intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact (P.arrow_mk_iso_iff e).1 hf'

lemma isoClosure_eq_self (P : MorphismProperty C) [P.RespectsIso] :
    P.isoClosure = P := by rwa [isoClosure_eq_iff]

@[simp]
lemma isoClosure_isoClosure (P : MorphismProperty C) :
    P.isoClosure.isoClosure = P.isoClosure :=
  P.isoClosure.isoClosure_eq_self

lemma isoClosure_le_iff (P Q : MorphismProperty C) [Q.RespectsIso] :
    P.isoClosure ≤ Q ↔ P ≤ Q := by
  constructor
  · exact P.le_isoClosure.trans
  · intro h
    exact (monotone_isoClosure h).trans (by rw [Q.isoClosure_eq_self])

instance map_respectsIso (P : MorphismProperty C) (F : C ⥤ D) :
    (P.map F).RespectsIso := by
  apply RespectsIso.of_respects_arrow_iso
  intro f g e ⟨X', Y', f', hf', ⟨e'⟩⟩
  exact ⟨X', Y', f', hf', ⟨e' ≪≫ e⟩⟩

lemma map_le_iff (P : MorphismProperty C) {F : C ⥤ D} (Q : MorphismProperty D)
    [RespectsIso Q] :
    P.map F ≤ Q ↔ P ≤ Q.inverseImage F := by
  constructor
  · intro h X Y f hf
    exact h (F.map f) (map_mem_map P F f hf)
  · intro h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact (Q.arrow_mk_iso_iff e).1 (h _ hf')

@[simp]
lemma map_isoClosure (P : MorphismProperty C) (F : C ⥤ D) :
    P.isoClosure.map F = P.map F := by
  apply le_antisymm
  · rw [map_le_iff]
    intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact ⟨_, _, f', hf', ⟨F.mapArrow.mapIso e⟩⟩
  · exact monotone_map _ (le_isoClosure P)

lemma map_id_eq_isoClosure (P : MorphismProperty C) :
    P.map (𝟭 _) = P.isoClosure := by
  apply le_antisymm
  · rw [map_le_iff]
    intro X Y f hf
    exact P.le_isoClosure _ hf
  · intro X Y f hf
    exact hf

lemma map_id (P : MorphismProperty C) [RespectsIso P] :
    P.map (𝟭 _) = P := by
  rw [map_id_eq_isoClosure, P.isoClosure_eq_self]

@[simp]
lemma map_map (P : MorphismProperty C) (F : C ⥤ D) {E : Type*} [Category E] (G : D ⥤ E) :
    (P.map F).map G = P.map (F ⋙ G) := by
  apply le_antisymm
  · rw [map_le_iff]
    intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact ⟨X', Y', f', hf', ⟨G.mapArrow.mapIso e⟩⟩
  · rw [map_le_iff]
    intro X Y f hf
    exact map_mem_map _ _ _ (map_mem_map _ _ _ hf)

instance RespectsIso.inverseImage (P : MorphismProperty D) [RespectsIso P] (F : C ⥤ D) :
    RespectsIso (P.inverseImage F) := by
  constructor
  all_goals
    intro X Y Z e f hf
    simpa [MorphismProperty.inverseImage, cancel_left_of_respectsIso,
      cancel_right_of_respectsIso] using hf

lemma map_eq_of_iso (P : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G) :
    P.map F = P.map G := by
  revert F G e
  suffices ∀ {F G : C ⥤ D} (_ : F ≅ G), P.map F ≤ P.map G from
    fun F G e => le_antisymm (this e) (this e.symm)
  intro F G e X Y f ⟨X', Y', f', hf', ⟨e'⟩⟩
  exact ⟨X', Y', f', hf', ⟨((Functor.mapArrowFunctor _ _).mapIso e.symm).app (Arrow.mk f') ≪≫ e'⟩⟩

lemma map_inverseImage_le (P : MorphismProperty D) (F : C ⥤ D) :
    (P.inverseImage F).map F ≤ P.isoClosure :=
  fun _ _ _ ⟨_, _, f, hf, ⟨e⟩⟩ => ⟨_, _, F.map f, hf, ⟨e⟩⟩

lemma inverseImage_equivalence_inverse_eq_map_functor
    (P : MorphismProperty D) [RespectsIso P] (E : C ≌ D) :
    P.inverseImage E.functor = P.map E.inverse := by
  apply le_antisymm
  · intro X Y f hf
    refine ⟨_, _, _, hf, ⟨?_⟩⟩
    exact ((Functor.mapArrowFunctor _ _).mapIso E.unitIso.symm).app (Arrow.mk f)
  · rw [map_le_iff]
    intro X Y f hf
    exact (P.arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso E.counitIso).app (Arrow.mk f))).2 hf

lemma inverseImage_equivalence_functor_eq_map_inverse
    (Q : MorphismProperty C) [RespectsIso Q] (E : C ≌ D) :
    Q.inverseImage E.inverse = Q.map E.functor :=
  inverseImage_equivalence_inverse_eq_map_functor Q E.symm

lemma map_inverseImage_eq_of_isEquivalence
    (P : MorphismProperty D) [P.RespectsIso] (F : C ⥤ D) [F.IsEquivalence] :
    (P.inverseImage F).map F = P := by
  erw [P.inverseImage_equivalence_inverse_eq_map_functor F.asEquivalence, map_map,
    P.map_eq_of_iso F.asEquivalence.counitIso, map_id]

lemma inverseImage_map_eq_of_isEquivalence
    (P : MorphismProperty C) [P.RespectsIso] (F : C ⥤ D) [F.IsEquivalence] :
    (P.map F).inverseImage F = P := by
  erw [((P.map F).inverseImage_equivalence_inverse_eq_map_functor (F.asEquivalence)), map_map,
    P.map_eq_of_iso F.asEquivalence.unitIso.symm, map_id]


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

instance RespectsIso.monomorphisms : RespectsIso (monomorphisms C) := by
  constructor <;>
    · intro X Y Z e f
      simp only [monomorphisms.iff]
      intro
      apply mono_comp

instance RespectsIso.epimorphisms : RespectsIso (epimorphisms C) := by
  constructor <;>
    · intro X Y Z e f
      simp only [epimorphisms.iff]
      intro
      apply epi_comp

instance RespectsIso.isomorphisms : RespectsIso (isomorphisms C) := by
  constructor <;>
    · intro X Y Z e f
      simp only [isomorphisms.iff]
      intro
      exact IsIso.comp_isIso

@[deprecated (since := "2024-07-02")] alias RespectsIso.cancel_left_isIso :=
  cancel_left_of_respectsIso
@[deprecated (since := "2024-07-02")] alias RespectsIso.cancel_right_isIso :=
  cancel_right_of_respectsIso
@[deprecated (since := "2024-07-02")] alias RespectsIso.arrow_iso_iff := arrow_iso_iff
@[deprecated (since := "2024-07-02")] alias RespectsIso.arrow_mk_iso_iff := arrow_mk_iso_iff
@[deprecated (since := "2024-07-02")] alias RespectsIso.isoClosure_eq := isoClosure_eq_self

/-- If `W₁` and `W₂` are morphism properties on two categories `C₁` and `C₂`,
this is the induced morphism property on `C₁ × C₂`. -/
def prod {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) :
    MorphismProperty (C₁ × C₂) :=
  fun _ _ f => W₁ f.1 ∧ W₂ f.2

/-- If `W j` are morphism properties on categories `C j` for all `j`, this is the
induced morphism property on the category `∀ j, C j`. -/
def pi {J : Type w} {C : J → Type u} [∀ j, Category.{v} (C j)]
    (W : ∀ j, MorphismProperty (C j)) : MorphismProperty (∀ j, C j) :=
  fun _ _ f => ∀ j, (W j) (f j)

variable {C}

/-- The morphism property on `J ⥤ C` which is defined objectwise
from `W : MorphismProperty C`. -/
def functorCategory (W : MorphismProperty C) (J : Type*) [Category J] :
    MorphismProperty (J ⥤ C) :=
  fun _ _ f => ∀ (j : J), W (f.app j)

/-- Given `W : MorphismProperty C`, this is the morphism property on `Arrow C` of morphisms
whose left and right parts are in `W`. -/
def arrow (W : MorphismProperty C) :
    MorphismProperty (Arrow C) :=
  fun _ _ f => W f.left ∧ W f.right

end MorphismProperty

namespace NatTrans

lemma isIso_app_iff_of_iso {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) :
    IsIso (α.app X) ↔ IsIso (α.app Y) :=
  (MorphismProperty.isomorphisms D).arrow_mk_iso_iff
    (Arrow.isoMk (F.mapIso e) (G.mapIso e) (by simp))

end NatTrans

end CategoryTheory
