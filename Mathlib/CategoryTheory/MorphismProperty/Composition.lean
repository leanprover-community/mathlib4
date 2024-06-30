/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Compatibilities of properties of morphisms with respect to composition

Given `P : MorphismProperty C`, we define the predicate `P.IsStableUnderComposition`
which means that `P f → P g → P (f ≫ g)`. We also introduce the type classes
`W.ContainsIdentities`, `W.IsMultiplicative`, and `W.HasTwoOutOfThreeProperty`.

-/


universe w v v' u u'

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Typeclass expressing that a morphism property contain identities. -/
class ContainsIdentities (W : MorphismProperty C) : Prop :=
  /-- for all `X : C`, the identity of `X` satisfies the morphism property -/
  id_mem : ∀ (X : C), W (𝟙 X)

lemma id_mem (W : MorphismProperty C) [W.ContainsIdentities] (X : C) :
    W (𝟙 X) := ContainsIdentities.id_mem X

namespace ContainsIdentities

instance op (W : MorphismProperty C) [W.ContainsIdentities] :
    W.op.ContainsIdentities := ⟨fun X => W.id_mem X.unop⟩

instance unop (W : MorphismProperty Cᵒᵖ) [W.ContainsIdentities] :
    W.unop.ContainsIdentities := ⟨fun X => W.id_mem (Opposite.op X)⟩

lemma of_op (W : MorphismProperty C) [W.op.ContainsIdentities] :
    W.ContainsIdentities := (inferInstance : W.op.unop.ContainsIdentities)

lemma of_unop (W : MorphismProperty Cᵒᵖ) [W.unop.ContainsIdentities] :
    W.ContainsIdentities := (inferInstance : W.unop.op.ContainsIdentities)

instance inverseImage {P : MorphismProperty D} [P.ContainsIdentities] (F : C ⥤ D) :
    (P.inverseImage F).ContainsIdentities where
  id_mem X := by simpa only [← F.map_id] using P.id_mem (F.obj X)

end ContainsIdentities

instance Prod.containsIdentities {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    [W₁.ContainsIdentities] [W₂.ContainsIdentities] : (prod W₁ W₂).ContainsIdentities :=
  ⟨fun _ => ⟨W₁.id_mem _, W₂.id_mem _⟩⟩

instance Pi.containsIdentities {J : Type w} {C : J → Type u}
  [∀ j, Category.{v} (C j)] (W : ∀ j, MorphismProperty (C j)) [∀ j, (W j).ContainsIdentities] :
    (pi W).ContainsIdentities :=
  ⟨fun _ _ => MorphismProperty.id_mem _ _⟩

/-- A morphism property satisfies `IsStableUnderComposition` if the composition of
two such morphisms still falls in the class. -/
class IsStableUnderComposition (P : MorphismProperty C) : Prop :=
  comp_mem {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) : P f → P g → P (f ≫ g)
#align category_theory.morphism_property.stable_under_composition CategoryTheory.MorphismProperty.IsStableUnderComposition

lemma comp_mem (W : MorphismProperty C) [W.IsStableUnderComposition]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g) : W (f ≫ g) :=
  IsStableUnderComposition.comp_mem f g hf hg

instance IsStableUnderComposition.op {P : MorphismProperty C} [P.IsStableUnderComposition] :
    P.op.IsStableUnderComposition where
  comp_mem f g hf hg := P.comp_mem g.unop f.unop hg hf
#align category_theory.morphism_property.stable_under_composition.op CategoryTheory.MorphismProperty.IsStableUnderComposition.op

instance IsStableUnderComposition.unop {P : MorphismProperty Cᵒᵖ} [P.IsStableUnderComposition] :
    P.unop.IsStableUnderComposition where
  comp_mem f g hf hg := P.comp_mem g.op f.op hg hf
#align category_theory.morphism_property.stable_under_composition.unop CategoryTheory.MorphismProperty.IsStableUnderComposition.unop

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

theorem respectsIso_of_isStableUnderComposition {P : MorphismProperty C}
    [P.IsStableUnderComposition] (hP : isomorphisms C ≤ P) :
    RespectsIso P :=
  ⟨fun _ _ hf => P.comp_mem _ _ (hP _ (isomorphisms.infer_property _)) hf,
    fun _ _ hf => P.comp_mem _ _ hf (hP _ (isomorphisms.infer_property _))⟩
#align category_theory.morphism_property.stable_under_composition.respects_iso CategoryTheory.MorphismProperty.respectsIso_of_isStableUnderComposition

instance IsStableUnderComposition.inverseImage {P : MorphismProperty D} [P.IsStableUnderComposition]
    (F : C ⥤ D) : (P.inverseImage F).IsStableUnderComposition where
  comp_mem f g hf hg := by simpa only [← F.map_comp] using P.comp_mem _ _ hf hg

/-- Given `app : Π X, F₁.obj X ⟶ F₂.obj X` where `F₁` and `F₂` are two functors,
this is the `morphism_property C` satisfied by the morphisms in `C` with respect
to whom `app` is natural. -/
@[simp]
def naturalityProperty {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) : MorphismProperty C :=
  fun X Y f => F₁.map f ≫ app Y = app X ≫ F₂.map f
#align category_theory.morphism_property.naturality_property CategoryTheory.MorphismProperty.naturalityProperty

namespace naturalityProperty

instance isStableUnderComposition {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (naturalityProperty app).IsStableUnderComposition where
  comp_mem f g hf hg := by
    simp only [naturalityProperty] at hf hg ⊢
    simp only [Functor.map_comp, Category.assoc, hg]
    slice_lhs 1 2 => rw [hf]
    rw [Category.assoc]
#align category_theory.morphism_property.naturality_property.is_stable_under_composition CategoryTheory.MorphismProperty.naturalityProperty.isStableUnderComposition

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
class IsMultiplicative (W : MorphismProperty C)
    extends W.ContainsIdentities, W.IsStableUnderComposition : Prop :=

namespace IsMultiplicative

instance op (W : MorphismProperty C) [IsMultiplicative W] : IsMultiplicative W.op where
  comp_mem f g hf hg := W.comp_mem g.unop f.unop hg hf

instance unop (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W] : IsMultiplicative W.unop where
  id_mem _ := W.id_mem _
  comp_mem f g hf hg := W.comp_mem g.op f.op hg hf

lemma of_op (W : MorphismProperty C) [IsMultiplicative W.op] : IsMultiplicative W :=
  (inferInstance : IsMultiplicative W.op.unop)

lemma of_unop (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W.unop] : IsMultiplicative W :=
  (inferInstance : IsMultiplicative W.unop.op)

instance : (isomorphisms C).IsMultiplicative where
  id_mem _ := isomorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [isomorphisms.iff] at hf hg ⊢
    infer_instance

instance : (monomorphisms C).IsMultiplicative where
  id_mem _ := monomorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [monomorphisms.iff] at hf hg ⊢
    apply mono_comp

instance : (epimorphisms C).IsMultiplicative where
  id_mem _ := epimorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [epimorphisms.iff] at hf hg ⊢
    apply epi_comp

instance {P : MorphismProperty D} [P.IsMultiplicative] (F : C ⥤ D) :
    (P.inverseImage F).IsMultiplicative where

end IsMultiplicative

/-- A class of morphisms `W` has the two-out-of-three property if whenever two out
of three maps in `f`, `g`, `f ≫ g` are in `W`, then the third map is also in `W`. -/
class HasTwoOutOfThreeProperty (W : MorphismProperty C)
    extends W.IsStableUnderComposition : Prop where
  of_postcomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W g → W (f ≫ g) → W f
  of_precomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W f → W (f ≫ g) → W g

section

variable (W : MorphismProperty C) [W.HasTwoOutOfThreeProperty]

lemma of_postcomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W g) (hfg : W (f ≫ g)) :
    W f :=
  HasTwoOutOfThreeProperty.of_postcomp f g hg hfg

lemma of_precomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hfg : W (f ≫ g)) :
    W g :=
  HasTwoOutOfThreeProperty.of_precomp f g hf hfg

lemma postcomp_iff {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W g) :
    W (f ≫ g) ↔ W f :=
  ⟨W.of_postcomp f g hg, fun hf => W.comp_mem _ _ hf hg⟩

lemma precomp_iff {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) :
    W (f ≫ g) ↔ W g :=
  ⟨W.of_precomp f g hf, fun hg => W.comp_mem _ _ hf hg⟩

end

instance : (isomorphisms C).HasTwoOutOfThreeProperty where
  of_postcomp f g := fun (hg : IsIso g) (hfg : IsIso (f ≫ g)) =>
    by simpa using (inferInstance : IsIso ((f ≫ g) ≫ inv g))
  of_precomp f g := fun (hf : IsIso f) (hfg : IsIso (f ≫ g)) =>
    by simpa using (inferInstance : IsIso (inv f ≫ (f ≫ g)))

instance (F : C ⥤ D) (W : MorphismProperty D) [W.HasTwoOutOfThreeProperty] :
    (W.inverseImage F).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := W.of_postcomp (F.map f) (F.map g) hg (by simpa using hfg)
  of_precomp f g hf hfg := W.of_precomp (F.map f) (F.map g) hf (by simpa using hfg)

end MorphismProperty

end CategoryTheory
