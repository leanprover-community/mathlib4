/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Compatibilities of properties of morphisms with respect to composition

Given `P : MorphismProperty C`, we define the predicate `P.StableUnderComposition`
which means that `P f → P g → P (f ≫ g)`. We also introduce the type classes
`W.ContainsIdentities` and `W.IsMultiplicative`.

## TODO
* define the type class of morphism properties that satisfy the 2-out-of-3 property
(which may require transforming `StableUnderComposition` into a type class)

-/


universe w v v' u u'

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

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

instance Prod.containsIdentities {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    [W₁.ContainsIdentities] [W₂.ContainsIdentities] : (prod W₁ W₂).ContainsIdentities :=
  ⟨fun _ => ⟨W₁.id_mem _, W₂.id_mem _⟩⟩

instance Pi.containsIdentities {J : Type w} {C : J → Type u}
  [∀ j, Category.{v} (C j)] (W : ∀ j, MorphismProperty (C j)) [∀ j, (W j).ContainsIdentities] :
    (pi W).ContainsIdentities :=
  ⟨fun _ _ => MorphismProperty.id_mem _ _⟩

/-- A morphism property is `StableUnderComposition` if the composition of two such morphisms
still falls in the class. -/
def StableUnderComposition (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Z⦄ (f : X ⟶ Y) (g : Y ⟶ Z), P f → P g → P (f ≫ g)
#align category_theory.morphism_property.stable_under_composition CategoryTheory.MorphismProperty.StableUnderComposition

theorem StableUnderComposition.op {P : MorphismProperty C} (h : StableUnderComposition P) :
    StableUnderComposition P.op := fun _ _ _ f g hf hg => h g.unop f.unop hg hf
#align category_theory.morphism_property.stable_under_composition.op CategoryTheory.MorphismProperty.StableUnderComposition.op

theorem StableUnderComposition.unop {P : MorphismProperty Cᵒᵖ} (h : StableUnderComposition P) :
    StableUnderComposition P.unop := fun _ _ _ f g hf hg => h g.op f.op hg hf
#align category_theory.morphism_property.stable_under_composition.unop CategoryTheory.MorphismProperty.StableUnderComposition.unop

/-- A morphism property is `StableUnderInverse` if the inverse of a morphism satisfying
the property still falls in the class. -/
def StableUnderInverse (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y⦄ (e : X ≅ Y), P e.hom → P e.inv
#align category_theory.morphism_property.stable_under_inverse CategoryTheory.MorphismProperty.StableUnderInverse

theorem StableUnderInverse.op {P : MorphismProperty C} (h : StableUnderInverse P) :
    StableUnderInverse P.op := fun _ _ e he => h e.unop he
#align category_theory.morphism_property.stable_under_inverse.op CategoryTheory.MorphismProperty.StableUnderInverse.op

theorem StableUnderInverse.unop {P : MorphismProperty Cᵒᵖ} (h : StableUnderInverse P) :
    StableUnderInverse P.unop := fun _ _ e he => h e.op he
#align category_theory.morphism_property.stable_under_inverse.unop CategoryTheory.MorphismProperty.StableUnderInverse.unop

theorem StableUnderComposition.respectsIso {P : MorphismProperty C} (hP : StableUnderComposition P)
    (hP' : ∀ {X Y} (e : X ≅ Y), P e.hom) : RespectsIso P :=
  ⟨fun e _ hf => hP _ _ (hP' e) hf, fun e _ hf => hP _ _ hf (hP' e)⟩
#align category_theory.morphism_property.stable_under_composition.respects_iso CategoryTheory.MorphismProperty.StableUnderComposition.respectsIso

theorem StableUnderComposition.isomorphisms : StableUnderComposition (isomorphisms C) :=
  fun X Y Z f g hf hg => by
  rw [isomorphisms.iff] at hf hg ⊢
  haveI := hf
  haveI := hg
  infer_instance
#align category_theory.morphism_property.stable_under_composition.isomorphisms CategoryTheory.MorphismProperty.StableUnderComposition.isomorphisms

theorem StableUnderComposition.monomorphisms : StableUnderComposition (monomorphisms C) :=
  fun X Y Z f g hf hg => by
  rw [monomorphisms.iff] at hf hg ⊢
  haveI := hf
  haveI := hg
  apply mono_comp
#align category_theory.morphism_property.stable_under_composition.monomorphisms CategoryTheory.MorphismProperty.StableUnderComposition.monomorphisms

theorem StableUnderComposition.epimorphisms : StableUnderComposition (epimorphisms C) :=
  fun X Y Z f g hf hg => by
  rw [epimorphisms.iff] at hf hg ⊢
  haveI := hf
  haveI := hg
  apply epi_comp
#align category_theory.morphism_property.stable_under_composition.epimorphisms CategoryTheory.MorphismProperty.StableUnderComposition.epimorphisms

theorem StableUnderComposition.inverseImage {P : MorphismProperty D} (h : StableUnderComposition P)
    (F : C ⥤ D) : StableUnderComposition (P.inverseImage F) := fun X Y Z f g hf hg => by
  simpa only [← F.map_comp] using h (F.map f) (F.map g) hf hg
#align category_theory.morphism_property.stable_under_composition.inverse_image CategoryTheory.MorphismProperty.StableUnderComposition.inverseImage

/-- Given `app : Π X, F₁.obj X ⟶ F₂.obj X` where `F₁` and `F₂` are two functors,
this is the `morphism_property C` satisfied by the morphisms in `C` with respect
to whom `app` is natural. -/
@[simp]
def naturalityProperty {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) : MorphismProperty C :=
  fun X Y f => F₁.map f ≫ app Y = app X ≫ F₂.map f
#align category_theory.morphism_property.naturality_property CategoryTheory.MorphismProperty.naturalityProperty

namespace naturalityProperty

theorem stableUnderComposition {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (naturalityProperty app).StableUnderComposition := fun X Y Z f g hf hg => by
  simp only [naturalityProperty] at hf hg ⊢
  simp only [Functor.map_comp, Category.assoc, hg]
  slice_lhs 1 2 => rw [hf]
  rw [Category.assoc]
#align category_theory.morphism_property.naturality_property.is_stable_under_composition CategoryTheory.MorphismProperty.naturalityProperty.stableUnderComposition

theorem stableUnderInverse {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (naturalityProperty app).StableUnderInverse := fun X Y e he => by
  simp only [naturalityProperty] at he ⊢
  rw [← cancel_epi (F₁.map e.hom)]
  slice_rhs 1 2 => rw [he]
  simp only [Category.assoc, ← F₁.map_comp_assoc, ← F₂.map_comp, e.hom_inv_id, Functor.map_id,
    Category.id_comp, Category.comp_id]
#align category_theory.morphism_property.naturality_property.is_stable_under_inverse CategoryTheory.MorphismProperty.naturalityProperty.stableUnderInverse

end naturalityProperty

/-- A morphism property is multiplicative if it contains identities and is stable by
composition. -/
class IsMultiplicative (W : MorphismProperty C) extends W.ContainsIdentities : Prop :=
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
