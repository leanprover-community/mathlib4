/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Compatibilities of properties of morphisms with respect to composition

Given `P : MorphismProperty C`, we define the predicate `P.IsStableUnderComposition`
which means that `P f → P g → P (f ≫ g)`. We also introduce the type classes
`W.ContainsIdentities`, `W.IsMultiplicative`, and `W.HasTwoOutOfThreeProperty`.

-/

@[expose] public section


universe w v v' u u'

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Typeclass expressing that a morphism property contains identities. -/
class ContainsIdentities (W : MorphismProperty C) : Prop where
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

lemma eqToHom (W : MorphismProperty C) [W.ContainsIdentities] {x y : C} (h : x = y) :
    W (eqToHom h) := by
  subst h
  rw [eqToHom_refl]
  exact id_mem x

instance inverseImage {P : MorphismProperty D} [P.ContainsIdentities] (F : C ⥤ D) :
    (P.inverseImage F).ContainsIdentities where
  id_mem X := by simpa only [← F.map_id] using P.id_mem (F.obj X)

instance inf {P Q : MorphismProperty C} [P.ContainsIdentities] [Q.ContainsIdentities] :
    (P ⊓ Q).ContainsIdentities where
  id_mem X := ⟨P.id_mem X, Q.id_mem X⟩

end ContainsIdentities

instance Prod.containsIdentities {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    [W₁.ContainsIdentities] [W₂.ContainsIdentities] : (prod W₁ W₂).ContainsIdentities :=
  ⟨fun _ => ⟨W₁.id_mem _, W₂.id_mem _⟩⟩

instance Pi.containsIdentities {J : Type w} {C : J → Type u}
    [∀ j, Category.{v} (C j)] (W : ∀ j, MorphismProperty (C j)) [∀ j, (W j).ContainsIdentities] :
    (pi W).ContainsIdentities :=
  ⟨fun _ _ => MorphismProperty.id_mem _ _⟩

lemma of_isIso (P : MorphismProperty C) [P.ContainsIdentities] [P.RespectsIso] {X Y : C} (f : X ⟶ Y)
    [IsIso f] : P f :=
  Category.id_comp f ▸ RespectsIso.postcomp P f (𝟙 X) (P.id_mem X)

lemma isomorphisms_le_of_containsIdentities (P : MorphismProperty C) [P.ContainsIdentities]
    [P.RespectsIso] :
    isomorphisms C ≤ P := fun _ _ f (_ : IsIso f) ↦ P.of_isIso f

/-- A morphism property satisfies `IsStableUnderComposition` if the composition of
two such morphisms still falls in the class. -/
class IsStableUnderComposition (P : MorphismProperty C) : Prop where
  comp_mem {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) : P f → P g → P (f ≫ g)

lemma comp_mem (W : MorphismProperty C) [W.IsStableUnderComposition]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g) : W (f ≫ g) :=
  IsStableUnderComposition.comp_mem f g hf hg

instance (priority := 900) (W : MorphismProperty C) [W.IsStableUnderComposition] :
    W.Respects W where
  precomp _ hi _ hf := W.comp_mem _ _ hi hf
  postcomp _ hi _ hf := W.comp_mem _ _ hf hi

instance IsStableUnderComposition.op {P : MorphismProperty C} [P.IsStableUnderComposition] :
    P.op.IsStableUnderComposition where
  comp_mem f g hf hg := P.comp_mem g.unop f.unop hg hf

instance IsStableUnderComposition.unop {P : MorphismProperty Cᵒᵖ} [P.IsStableUnderComposition] :
    P.unop.IsStableUnderComposition where
  comp_mem f g hf hg := P.comp_mem g.op f.op hg hf

instance IsStableUnderComposition.inf {P Q : MorphismProperty C} [P.IsStableUnderComposition]
    [Q.IsStableUnderComposition] :
    (P ⊓ Q).IsStableUnderComposition where
  comp_mem f g hf hg := ⟨P.comp_mem f g hf.left hg.left, Q.comp_mem f g hf.right hg.right⟩

/-- A morphism property is `StableUnderInverse` if the inverse of a morphism satisfying
the property still falls in the class. -/
def StableUnderInverse (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y⦄ (e : X ≅ Y), P e.hom → P e.inv

theorem StableUnderInverse.op {P : MorphismProperty C} (h : StableUnderInverse P) :
    StableUnderInverse P.op := fun _ _ e he => h e.unop he

theorem StableUnderInverse.unop {P : MorphismProperty Cᵒᵖ} (h : StableUnderInverse P) :
    StableUnderInverse P.unop := fun _ _ e he => h e.op he

theorem respectsIso_of_isStableUnderComposition {P : MorphismProperty C}
    [P.IsStableUnderComposition] (hP : isomorphisms C ≤ P) :
    RespectsIso P := RespectsIso.mk _
  (fun _ _ hf => P.comp_mem _ _ (hP _ (isomorphisms.infer_property _)) hf)
    (fun _ _ hf => P.comp_mem _ _ hf (hP _ (isomorphisms.infer_property _)))

instance IsStableUnderComposition.inverseImage {P : MorphismProperty D} [P.IsStableUnderComposition]
    (F : C ⥤ D) : (P.inverseImage F).IsStableUnderComposition where
  comp_mem f g hf hg := by simpa only [← F.map_comp] using P.comp_mem _ _ hf hg

/-- Given `app : Π X, F₁.obj X ⟶ F₂.obj X` where `F₁` and `F₂` are two functors,
this is the `MorphismProperty C` satisfied by the morphisms in `C` with respect
to which `app` is natural. -/
@[simp]
def naturalityProperty {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) : MorphismProperty C :=
  fun X Y f => F₁.map f ≫ app Y = app X ≫ F₂.map f

namespace naturalityProperty

instance isStableUnderComposition {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (naturalityProperty app).IsStableUnderComposition where
  comp_mem f g hf hg := by
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

/-- A morphism property is multiplicative if it contains identities and is stable by
composition. -/
class IsMultiplicative (W : MorphismProperty C) : Prop
    extends W.ContainsIdentities, W.IsStableUnderComposition

namespace IsMultiplicative

instance op (W : MorphismProperty C) [IsMultiplicative W] : IsMultiplicative W.op where
  comp_mem f g hf hg := W.comp_mem g.unop f.unop hg hf

instance unop (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W] : IsMultiplicative W.unop where
  id_mem _ := W.id_mem _
  comp_mem f g hf hg := W.comp_mem g.op f.op hg hf

lemma of_op (W : MorphismProperty C) [IsMultiplicative W.op] : IsMultiplicative W :=
  inferInstanceAs <| IsMultiplicative W.op.unop

lemma of_unop (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W.unop] : IsMultiplicative W :=
  inferInstanceAs <| IsMultiplicative W.unop.op

instance : MorphismProperty.IsMultiplicative (⊤ : MorphismProperty C) where
  comp_mem _ _ _ _ := trivial
  id_mem _ := trivial

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

instance inf {P Q : MorphismProperty C} [P.IsMultiplicative] [Q.IsMultiplicative] :
    (P ⊓ Q).IsMultiplicative where

instance naturalityProperty {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (naturalityProperty app).IsMultiplicative where
  id_mem _ := by simp

end IsMultiplicative

/-- Given a morphism property `W`, the `multiplicativeClosure W` is the smallest
multiplicative property greater than or equal to `W`. -/
inductive multiplicativeClosure (W : MorphismProperty C) : MorphismProperty C
  | of {x y : C} (f : x ⟶ y) (hf : W f) : multiplicativeClosure W f
  | id (x : C) : multiplicativeClosure W (𝟙 x)
  | comp_of {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (hf : multiplicativeClosure W f) (hg : W g) :
    multiplicativeClosure W (f ≫ g)

/-- A variant of `multiplicativeClosure` in which compositions are taken on the left rather than
on the right. It is not intended to be used directly, and one should rather access this via
`multiplicativeClosure_eq_multiplicativeClosure'` in cases where the inductive principle of this
variant is needed. -/
inductive multiplicativeClosure' (W : MorphismProperty C) : MorphismProperty C
  | of {x y : C} (f : x ⟶ y) (hf : W f) : multiplicativeClosure' W f
  | id (x : C) : multiplicativeClosure' W (𝟙 x)
  | of_comp {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (hf : W f) (hg : multiplicativeClosure' W g) :
    multiplicativeClosure' W (f ≫ g)

variable (W : MorphismProperty C)

/-- `multiplicativeClosure W` is multiplicative. -/
instance : IsMultiplicative W.multiplicativeClosure where
  id_mem x := .id x
  comp_mem f g hf hg := by
    induction hg with
    | of _ hf₀ => exact .comp_of f _ hf hf₀
    | id _ => rwa [Category.comp_id]
    | comp_of f' g hf' hg h_rec =>
      rw [← Category.assoc]
      exact .comp_of (f ≫ f') g (h_rec f hf) hg

/-- `multiplicativeClosure' W` is multiplicative. -/
instance : IsMultiplicative W.multiplicativeClosure' where
  id_mem x := .id x
  comp_mem f g hf hg := by
    induction hf with
    | of _ h => exact .of_comp _ g h hg
    | id _ => rwa [Category.id_comp]
    | of_comp g' f hg' hf h_rec =>
      rw [Category.assoc]
      exact .of_comp g' (f ≫ g) hg' (h_rec g hg)

/-- The multiplicative closure is greater than or equal to the original property. -/
lemma le_multiplicativeClosure : W ≤ W.multiplicativeClosure := fun {_ _} _ hf ↦ .of _ hf

/-- The multiplicative closure of a multiplicative property is equal to itself. -/
@[simp]
lemma multiplicativeClosure_eq_self [W.IsMultiplicative] : W.multiplicativeClosure = W := by
  apply le_antisymm _ <| le_multiplicativeClosure W
  intro _ _ _ hf
  induction hf with
  | of _ hf₀ => exact hf₀
  | id x => exact W.id_mem x
  | comp_of _ _ _ hg hf => exact W.comp_mem _ _ hf hg

lemma multiplicativeClosure_eq_self_iff : W.multiplicativeClosure = W ↔ W.IsMultiplicative where
  mp h := by
    rw [← h]
    infer_instance
  mpr h := multiplicativeClosure_eq_self W

/-- The multiplicative closure of `W` is the smallest multiplicative property greater than or equal
to `W`. -/
@[simp]
lemma multiplicativeClosure_le_iff (W' : MorphismProperty C) [W'.IsMultiplicative] :
    multiplicativeClosure W ≤ W' ↔ W ≤ W' where
  mp h := le_multiplicativeClosure W |>.trans h
  mpr h := by
    intro _ _ _ hf
    induction hf with
    | of _ hf => exact h _ hf
    | id x => exact W'.id_mem _
    | comp_of _ _ _ hg hf => exact W'.comp_mem _ _ hf (h _ hg)

lemma multiplicativeClosure_monotone :
    Monotone (multiplicativeClosure (C := C)) :=
  fun _ W' h ↦ by simpa using h.trans W'.le_multiplicativeClosure

lemma multiplicativeClosure_eq_multiplicativeClosure' :
    W.multiplicativeClosure = W.multiplicativeClosure' :=
  le_antisymm
    ((multiplicativeClosure_le_iff _ _).mpr (fun _ _ f hf ↦ .of f hf)) <|
    fun x y f hf ↦ by induction hf with
      | of _ h => exact .of _ h
      | id x => exact .id x
      | of_comp f g hf hg hr => exact W.multiplicativeClosure.comp_mem f g (.of f hf) hr

lemma strictMap_multiplicativeClosure_le (F : C ⥤ D) :
    W.multiplicativeClosure.strictMap F ≤ (W.strictMap F).multiplicativeClosure := by
  intro _ _ f hf
  induction hf with | map hf
  induction hf with
  | of f hf => exact le_multiplicativeClosure _ _ ⟨hf⟩
  | id x => simpa using .id (F.obj x)
  | comp_of _ _ hf hg h =>
    simpa using multiplicativeClosure.comp_of _ _ h (strictMap.map hg)

/-- A class of morphisms `W` has the of-postcomp property w.r.t. `W'` if whenever
`g` is in `W'` and `f ≫ g` is in `W`, also `f` is in `W`. -/
class HasOfPostcompProperty (W W' : MorphismProperty C) : Prop where
  of_postcomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W' g → W (f ≫ g) → W f

/-- A class of morphisms `W` has the of-precomp property w.r.t. `W'` if whenever
`f` is in `W'` and `f ≫ g` is in `W`, also `g` is in `W`. -/
class HasOfPrecompProperty (W W' : MorphismProperty C) : Prop where
  of_precomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W' f → W (f ≫ g) → W g

/-- A class of morphisms `W` has the two-out-of-three property if whenever two out
of three maps in `f`, `g`, `f ≫ g` are in `W`, then the third map is also in `W`. -/
class HasTwoOutOfThreeProperty (W : MorphismProperty C) : Prop
    extends W.IsStableUnderComposition, W.HasOfPostcompProperty W, W.HasOfPrecompProperty W where

section

variable (W W' : MorphismProperty C) {W'}

lemma of_postcomp [W.HasOfPostcompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g)
    (hfg : W (f ≫ g)) : W f :=
  HasOfPostcompProperty.of_postcomp f g hg hfg

lemma of_precomp [W.HasOfPrecompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f)
    (hfg : W (f ≫ g)) : W g :=
  HasOfPrecompProperty.of_precomp f g hf hfg

lemma postcomp_iff [W.RespectsRight W'] [W.HasOfPostcompProperty W']
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) : W (f ≫ g) ↔ W f :=
  ⟨W.of_postcomp f g hg, fun hf ↦ RespectsRight.postcomp _ hg _ hf⟩

lemma precomp_iff [W.RespectsLeft W'] [W.HasOfPrecompProperty W']
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f) :
    W (f ≫ g) ↔ W g :=
  ⟨W.of_precomp f g hf, fun hg ↦ RespectsLeft.precomp _ hf _ hg⟩

lemma HasOfPostcompProperty.of_le (Q : MorphismProperty C) [W.HasOfPostcompProperty Q]
    (hle : W' ≤ Q) : W.HasOfPostcompProperty W' where
  of_postcomp f g hg hfg := W.of_postcomp (W' := Q) f g (hle _ hg) hfg

lemma HasOfPrecompProperty.of_le (Q : MorphismProperty C) [W.HasOfPrecompProperty Q]
    (hle : W' ≤ Q) : W.HasOfPrecompProperty W' where
  of_precomp f g hg hfg := W.of_precomp (W' := Q) f g (hle _ hg) hfg

instance [W.HasOfPostcompProperty W'] : W.op.HasOfPrecompProperty W'.op where
  of_precomp _ _ hf hfg := W.of_postcomp _ _ hf hfg

instance [W.HasOfPrecompProperty W'] : W.op.HasOfPostcompProperty W'.op where
  of_postcomp _ _ hg hfg := W.of_precomp _ _ hg hfg

instance [W.HasTwoOutOfThreeProperty] : W.op.HasTwoOutOfThreeProperty where

instance : (⊤ : MorphismProperty C).HasOfPostcompProperty W where
  of_postcomp _ _ _ _ := trivial

instance : (⊤ : MorphismProperty C).HasOfPrecompProperty W where
  of_precomp _ _ _ _ := trivial

instance : (⊤ : MorphismProperty C).HasTwoOutOfThreeProperty where

variable (P Q : MorphismProperty C)

instance [P.HasOfPostcompProperty W] [Q.HasOfPostcompProperty W] :
    (P ⊓ Q).HasOfPostcompProperty W where
  of_postcomp f g hg hfg := ⟨P.of_postcomp f g hg hfg.1, Q.of_postcomp f g hg hfg.2⟩

instance [P.HasOfPrecompProperty W] [Q.HasOfPrecompProperty W] :
    (P ⊓ Q).HasOfPrecompProperty W where
  of_precomp f g hg hfg := ⟨P.of_precomp f g hg hfg.1, Q.of_precomp f g hg hfg.2⟩

instance [P.HasTwoOutOfThreeProperty] [Q.HasTwoOutOfThreeProperty] :
    (P ⊓ Q).HasTwoOutOfThreeProperty := by
  have : P.HasOfPostcompProperty (P ⊓ Q) := .of_le _ _ inf_le_left
  have : P.HasOfPrecompProperty (P ⊓ Q) := .of_le _ _ inf_le_left
  have : Q.HasOfPostcompProperty (P ⊓ Q) := .of_le _ _ inf_le_right
  have : Q.HasOfPrecompProperty (P ⊓ Q) := .of_le _ _ inf_le_right
  constructor

end

section

variable (W₁ W₂ : MorphismProperty Cᵒᵖ)

instance [W₁.HasOfPostcompProperty W₂] : W₁.unop.HasOfPrecompProperty W₂.unop where
  of_precomp _ _ hf hfg := W₁.of_postcomp _ _ hf hfg

instance [W₁.HasOfPrecompProperty W₂] : W₁.unop.HasOfPostcompProperty W₂.unop where
  of_postcomp _ _ hg hfg := W₁.of_precomp _ _ hg hfg

instance [W₁.HasTwoOutOfThreeProperty] : W₁.unop.HasTwoOutOfThreeProperty where

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

instance [W.RespectsIso] : W.HasOfPrecompProperty (isomorphisms C) where
  of_precomp _ _ (_ : IsIso _) := (W.cancel_left_of_respectsIso _ _).mp

instance [W.RespectsIso] : W.HasOfPostcompProperty (isomorphisms C) where
  of_postcomp _ _ (_ : IsIso _) := (W.cancel_right_of_respectsIso _ _).mp

end MorphismProperty

end CategoryTheory
