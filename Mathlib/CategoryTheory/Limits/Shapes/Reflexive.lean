/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

/-!
# Reflexive coequalizers

This file deals with reflexive pairs, which are pairs of morphisms with a common section.

A reflexive coequalizer is a coequalizer of such a pair. These kind of coequalizers often enjoy
nicer properties than general coequalizers, and feature heavily in some versions of the monadicity
theorem.

We also give some examples of reflexive pairs: for an adjunction `F ⊣ G` with counit `ε`, the pair
`(FGε_B, ε_FGB)` is reflexive. If a pair `f,g` is a kernel pair for some morphism, then it is
reflexive.

## Main definitions

* `IsReflexivePair` is the predicate that f and g have a common section.
* `WalkingReflexivePair` is the diagram indexing pairs with a common section.
* A `reflexiveCofork` is a cocone on a diagram indexed by `WalkingReflexivePair`.
* `WalkingReflexivePair.inclusionWalkingReflexivePair` is the inclusion functor from
  `WalkingParallelPair` to `WalkingReflexivePair`. It acts on reflexive pairs as forgetting
  the common section.
* `HasReflexiveCoequalizers` is the predicate that a category has all colimits of reflexive pairs.
* `reflexiveCoequalizerIsoCoequalizer`: an isomorphism promoting the coequalizer of a reflexive pair
  to the colimit of a diagram out of the walking reflexive pair.

## Main statements

* `IsKernelPair.isReflexivePair`: A kernel pair is a reflexive pair
* `WalkingParallelPair.inclusionWalkingReflexivePair_final`: The inclusion functor is final.
* `hasReflexiveCoequalizers_iff`: A category has coequalizers of reflexive pairs if and only if it
  has all colimits of shape `WalkingReflexivePair`.

## TODO
* If `C` has binary coproducts and reflexive coequalizers, then it has all coequalizers.
* If `T` is a monad on cocomplete category `C`, then `Algebra T` is cocomplete iff it has reflexive
  coequalizers.
* If `C` is locally Cartesian closed and has reflexive coequalizers, then it has images: in fact
  regular epi (and hence strong epi) images.
* Bundle the reflexive pairs of kernel pairs and of adjunction as functors out of the walking
  reflexive pair.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


namespace CategoryTheory

universe v v₂ u u₂

variable {C : Type u} [Category.{v} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A B : C} {f g : A ⟶ B}

/-- The pair `f g : A ⟶ B` is reflexive if there is a morphism `B ⟶ A` which is a section for both.
-/
class IsReflexivePair (f g : A ⟶ B) : Prop where
  common_section' : ∃ s : B ⟶ A, s ≫ f = 𝟙 B ∧ s ≫ g = 𝟙 B

theorem IsReflexivePair.common_section (f g : A ⟶ B) [IsReflexivePair f g] :
    ∃ s : B ⟶ A, s ≫ f = 𝟙 B ∧ s ≫ g = 𝟙 B := IsReflexivePair.common_section'

/--
The pair `f g : A ⟶ B` is coreflexive if there is a morphism `B ⟶ A` which is a retraction for both.
-/
class IsCoreflexivePair (f g : A ⟶ B) : Prop where
  common_retraction' : ∃ s : B ⟶ A, f ≫ s = 𝟙 A ∧ g ≫ s = 𝟙 A

theorem IsCoreflexivePair.common_retraction (f g : A ⟶ B) [IsCoreflexivePair f g] :
    ∃ s : B ⟶ A, f ≫ s = 𝟙 A ∧ g ≫ s = 𝟙 A := IsCoreflexivePair.common_retraction'

theorem IsReflexivePair.mk' (s : B ⟶ A) (sf : s ≫ f = 𝟙 B) (sg : s ≫ g = 𝟙 B) :
    IsReflexivePair f g :=
  ⟨⟨s, sf, sg⟩⟩

theorem IsCoreflexivePair.mk' (s : B ⟶ A) (fs : f ≫ s = 𝟙 A) (gs : g ≫ s = 𝟙 A) :
    IsCoreflexivePair f g :=
  ⟨⟨s, fs, gs⟩⟩

/-- Get the common section for a reflexive pair. -/
noncomputable def commonSection (f g : A ⟶ B) [IsReflexivePair f g] : B ⟶ A :=
  (IsReflexivePair.common_section f g).choose

@[reassoc (attr := simp)]
theorem section_comp_left (f g : A ⟶ B) [IsReflexivePair f g] : commonSection f g ≫ f = 𝟙 B :=
  (IsReflexivePair.common_section f g).choose_spec.1

@[reassoc (attr := simp)]
theorem section_comp_right (f g : A ⟶ B) [IsReflexivePair f g] : commonSection f g ≫ g = 𝟙 B :=
  (IsReflexivePair.common_section f g).choose_spec.2

/-- Get the common retraction for a coreflexive pair. -/
noncomputable def commonRetraction (f g : A ⟶ B) [IsCoreflexivePair f g] : B ⟶ A :=
  (IsCoreflexivePair.common_retraction f g).choose

@[reassoc (attr := simp)]
theorem left_comp_retraction (f g : A ⟶ B) [IsCoreflexivePair f g] :
    f ≫ commonRetraction f g = 𝟙 A :=
  (IsCoreflexivePair.common_retraction f g).choose_spec.1

@[reassoc (attr := simp)]
theorem right_comp_retraction (f g : A ⟶ B) [IsCoreflexivePair f g] :
    g ≫ commonRetraction f g = 𝟙 A :=
  (IsCoreflexivePair.common_retraction f g).choose_spec.2

/-- If `f,g` is a kernel pair for some morphism `q`, then it is reflexive. -/
theorem IsKernelPair.isReflexivePair {R : C} {f g : R ⟶ A} {q : A ⟶ B} (h : IsKernelPair q f g) :
    IsReflexivePair f g :=
  IsReflexivePair.mk' _ (h.lift' _ _ rfl).2.1 (h.lift' _ _ _).2.2

-- This shouldn't be an instance as it would instantly loop.
/-- If `f,g` is reflexive, then `g,f` is reflexive. -/
theorem IsReflexivePair.swap [IsReflexivePair f g] : IsReflexivePair g f :=
  IsReflexivePair.mk' _ (section_comp_right f g) (section_comp_left f g)

-- This shouldn't be an instance as it would instantly loop.
/-- If `f,g` is coreflexive, then `g,f` is coreflexive. -/
theorem IsCoreflexivePair.swap [IsCoreflexivePair f g] : IsCoreflexivePair g f :=
  IsCoreflexivePair.mk' _ (right_comp_retraction f g) (left_comp_retraction f g)

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

set_option backward.isDefEq.respectTransparency false in
/-- For an adjunction `F ⊣ G` with counit `ε`, the pair `(FGε_B, ε_FGB)` is reflexive. -/
instance (B : D) :
    IsReflexivePair (F.map (G.map (adj.counit.app B))) (adj.counit.app (F.obj (G.obj B))) :=
  IsReflexivePair.mk' (F.map (adj.unit.app (G.obj B)))
    (by
      rw [← F.map_comp, adj.right_triangle_components]
      apply F.map_id)
    (adj.left_triangle_components _)

namespace Limits

variable (C)

/-- `C` has reflexive coequalizers if it has coequalizers for every reflexive pair. -/
class HasReflexiveCoequalizers : Prop where
  has_coeq : ∀ ⦃A B : C⦄ (f g : A ⟶ B) [IsReflexivePair f g], HasCoequalizer f g

/-- `C` has coreflexive equalizers if it has equalizers for every coreflexive pair. -/
class HasCoreflexiveEqualizers : Prop where
  has_eq : ∀ ⦃A B : C⦄ (f g : A ⟶ B) [IsCoreflexivePair f g], HasEqualizer f g

attribute [instance 1] HasReflexiveCoequalizers.has_coeq

attribute [instance 1] HasCoreflexiveEqualizers.has_eq

theorem hasCoequalizer_of_common_section [HasReflexiveCoequalizers C] {A B : C} {f g : A ⟶ B}
    (r : B ⟶ A) (rf : r ≫ f = 𝟙 _) (rg : r ≫ g = 𝟙 _) : HasCoequalizer f g := by
  letI := IsReflexivePair.mk' r rf rg
  infer_instance

theorem hasEqualizer_of_common_retraction [HasCoreflexiveEqualizers C] {A B : C} {f g : A ⟶ B}
    (r : B ⟶ A) (fr : f ≫ r = 𝟙 _) (gr : g ≫ r = 𝟙 _) : HasEqualizer f g := by
  letI := IsCoreflexivePair.mk' r fr gr
  infer_instance

/-- If `C` has coequalizers, then it has reflexive coequalizers. -/
instance (priority := 100) hasReflexiveCoequalizers_of_hasCoequalizers [HasCoequalizers C] :
    HasReflexiveCoequalizers C where has_coeq A B f g _ := by infer_instance

/-- If `C` has equalizers, then it has coreflexive equalizers. -/
instance (priority := 100) hasCoreflexiveEqualizers_of_hasEqualizers [HasEqualizers C] :
    HasCoreflexiveEqualizers C where has_eq A B f g _ := by infer_instance

end Limits

end CategoryTheory

namespace CategoryTheory

universe v v₂ u u₂

namespace Limits

/-- The type of objects for the diagram indexing reflexive (co)equalizers -/
inductive WalkingReflexivePair : Type where
  | zero
  | one
  deriving DecidableEq, Inhabited

open WalkingReflexivePair

namespace WalkingReflexivePair

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- The type of morphisms for the diagram indexing reflexive (co)equalizers -/
inductive Hom : (WalkingReflexivePair → WalkingReflexivePair → Type)
  | left : Hom one zero
  | right : Hom one zero
  | reflexion : Hom zero one
  | leftCompReflexion : Hom one one
  | rightCompReflexion : Hom one one
  | id (X : WalkingReflexivePair) : Hom X X
  deriving DecidableEq

/-- Composition of morphisms in the diagram indexing reflexive (co)equalizers -/
def Hom.comp :
    ∀ {X Y Z : WalkingReflexivePair} (_ : Hom X Y)
      (_ : Hom Y Z), Hom X Z
  | _, _, _, id _, h => h
  | _, _, _, h, id _ => h
  | _, _, _, reflexion, left => id zero
  | _, _, _, reflexion, right => id zero
  | _, _, _, reflexion, rightCompReflexion => reflexion
  | _, _, _, reflexion, leftCompReflexion => reflexion
  | _, _, _, left, reflexion => leftCompReflexion
  | _, _, _, right, reflexion => rightCompReflexion
  | _, _, _, rightCompReflexion, rightCompReflexion => rightCompReflexion
  | _, _, _, rightCompReflexion, leftCompReflexion => rightCompReflexion
  | _, _, _, rightCompReflexion, right => right
  | _, _, _, rightCompReflexion, left => right
  | _, _, _, leftCompReflexion, left => left
  | _, _, _, leftCompReflexion, right => left
  | _, _, _, leftCompReflexion, rightCompReflexion => leftCompReflexion
  | _, _, _, leftCompReflexion, leftCompReflexion => leftCompReflexion

instance category : SmallCategory WalkingReflexivePair where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  comp_id := by intro _ _ f; cases f <;> rfl
  id_comp := by intro _ _ f; cases f <;> rfl
  assoc := by intro _ _ _ _ f g h; cases f <;> cases g <;> cases h <;> rfl

open Hom

@[simp]
lemma Hom.id_eq (X : WalkingReflexivePair) :
    Hom.id X = 𝟙 X := rfl

@[reassoc (attr := simp)]
lemma reflexion_comp_left : reflexion ≫ left = 𝟙 zero := rfl

@[reassoc (attr := simp)]
lemma reflexion_comp_right : reflexion ≫ right = 𝟙 zero := rfl

@[simp]
lemma leftCompReflexion_eq : leftCompReflexion = (left ≫ reflexion : one ⟶ one) := rfl

@[simp]
lemma rightCompReflexion_eq : rightCompReflexion = (right ≫ reflexion : one ⟶ one) := rfl

section FunctorsOutOfWalkingReflexivePair

variable {C : Type u} [Category.{v} C]

@[reassoc (attr := simp)]
lemma map_reflexion_comp_map_left (F : WalkingReflexivePair ⥤ C) :
    F.map reflexion ≫ F.map left = 𝟙 (F.obj zero) := by
  rw [← F.map_comp, reflexion_comp_left, F.map_id]

@[reassoc (attr := simp)]
lemma map_reflexion_comp_map_right (F : WalkingReflexivePair ⥤ C) :
    F.map reflexion ≫ F.map right = 𝟙 (F.obj zero) := by
  rw [← F.map_comp, reflexion_comp_right, F.map_id]

end FunctorsOutOfWalkingReflexivePair

end WalkingReflexivePair

namespace WalkingParallelPair

/-- The inclusion functor forgetting the common section -/
@[simps!]
def inclusionWalkingReflexivePair : WalkingParallelPair ⥤ WalkingReflexivePair where
  obj := fun x => match x with
    | one => WalkingReflexivePair.zero
    | zero => WalkingReflexivePair.one
  map := fun f => match f with
    | .left => WalkingReflexivePair.Hom.left
    | .right => WalkingReflexivePair.Hom.right
    | .id _ => WalkingReflexivePair.Hom.id _
  map_comp := by
    intro _ _ _ f g; cases f <;> cases g <;> rfl

variable {C : Type u} [Category.{v} C]

instance (X : WalkingReflexivePair) :
    Nonempty (StructuredArrow X inclusionWalkingReflexivePair) := by
  cases X with
  | zero => exact ⟨StructuredArrow.mk (Y := one) (𝟙 _)⟩
  | one => exact ⟨StructuredArrow.mk (Y := zero) (𝟙 _)⟩

open WalkingReflexivePair.Hom in
instance (X : WalkingReflexivePair) :
    IsConnected (StructuredArrow X inclusionWalkingReflexivePair) := by
  cases X with
  | zero =>
      refine IsConnected.of_induct (j₀ := StructuredArrow.mk (Y := one) (𝟙 _)) ?_
      rintro p h₁ h₂ ⟨⟨⟨⟩⟩, (_ | _), ⟨_⟩⟩
      · exact (h₂ (StructuredArrow.homMk .left)).2 h₁
      · exact h₁
  | one =>
      refine IsConnected.of_induct (j₀ := StructuredArrow.mk (Y := zero) (𝟙 _))
        (fun p h₁ h₂ ↦ ?_)
      have hₗ : StructuredArrow.mk left ∈ p := (h₂ (StructuredArrow.homMk .left)).1 h₁
      have hᵣ : StructuredArrow.mk right ∈ p := (h₂ (StructuredArrow.homMk .right)).1 h₁
      rintro ⟨⟨⟨⟩⟩, (_ | _), ⟨_⟩⟩
      · exact (h₂ (StructuredArrow.homMk .left)).2 hₗ
      · exact (h₂ (StructuredArrow.homMk .right)).2 hᵣ
      all_goals assumption

/-- The inclusion functor is a final functor -/
instance inclusionWalkingReflexivePair_final : Functor.Final inclusionWalkingReflexivePair where
  out := inferInstance

end WalkingParallelPair

end Limits

namespace Limits

open WalkingReflexivePair

variable {C : Type u} [Category.{v} C]

variable {A B : C}

/-- Bundle the data of a parallel pair along with a common section as a functor out of the walking
reflexive pair -/
def reflexivePair (f g : A ⟶ B) (s : B ⟶ A)
    (sl : s ≫ f = 𝟙 B := by cat_disch) (sr : s ≫ g = 𝟙 B := by cat_disch) :
    (WalkingReflexivePair ⥤ C) where
  obj x :=
    match x with
    | zero => B
    | one => A
  map h :=
    match h with
    | .id _ => 𝟙 _
    | .left => f
    | .right => g
    | .reflexion => s
    | .rightCompReflexion => g ≫ s
    | .leftCompReflexion => f ≫ s
  map_comp := by
    rintro _ _ _ ⟨⟩ g <;> cases g <;>
      simp only [Category.id_comp, Category.comp_id, Category.assoc, sl, sr,
        reassoc_of% sl, reassoc_of% sr] <;> rfl

section

variable {A B : C}
variable (f g : A ⟶ B) (s : B ⟶ A) {sl : s ≫ f = 𝟙 B} {sr : s ≫ g = 𝟙 B}

@[simp] lemma reflexivePair_obj_zero : (reflexivePair f g s sl sr).obj zero = B := rfl

@[simp] lemma reflexivePair_obj_one : (reflexivePair f g s sl sr).obj one = A := rfl

@[simp] lemma reflexivePair_map_right : (reflexivePair f g s sl sr).map .left = f := rfl

@[simp] lemma reflexivePair_map_left : (reflexivePair f g s sl sr).map .right = g := rfl

@[simp] lemma reflexivePair_map_reflexion : (reflexivePair f g s sl sr).map .reflexion = s := rfl

end

/-- (Noncomputably) bundle the data of a reflexive pair as a functor out of the walking reflexive
pair -/
noncomputable def ofIsReflexivePair (f g : A ⟶ B) [IsReflexivePair f g] :
    WalkingReflexivePair ⥤ C := reflexivePair f g (commonSection f g)

@[simp]
lemma ofIsReflexivePair_map_left (f g : A ⟶ B) [IsReflexivePair f g] :
    (ofIsReflexivePair f g).map .left = f := rfl

@[simp]
lemma ofIsReflexivePair_map_right (f g : A ⟶ B) [IsReflexivePair f g] :
    (ofIsReflexivePair f g).map .right = g := rfl

/-- The natural isomorphism between the diagram obtained by forgetting the reflexion of
`ofIsReflexivePair f g` and the original parallel pair. -/
noncomputable def inclusionWalkingReflexivePairOfIsReflexivePairIso
    (f g : A ⟶ B) [IsReflexivePair f g] :
    WalkingParallelPair.inclusionWalkingReflexivePair ⋙ (ofIsReflexivePair f g) ≅
      parallelPair f g :=
  diagramIsoParallelPair _

end Limits

namespace Limits

variable {C : Type u} [Category.{v} C]

namespace reflexivePair

open WalkingReflexivePair WalkingReflexivePair.Hom

section
section NatTrans

variable {F G : WalkingReflexivePair ⥤ C}
  (e₀ : F.obj zero ⟶ G.obj zero) (e₁ : F.obj one ⟶ G.obj one)
  (h₁ : F.map left ≫ e₀ = e₁ ≫ G.map left := by cat_disch)
  (h₂ : F.map right ≫ e₀ = e₁ ≫ G.map right := by cat_disch)
  (h₃ : F.map reflexion ≫ e₁ = e₀ ≫ G.map reflexion := by cat_disch)

set_option backward.privateInPublic true in
/-- A constructor for natural transformations between functors from `WalkingReflexivePair`. -/
def mkNatTrans : F ⟶ G where
  app := fun x ↦ match x with
    | zero => e₀
    | one => e₁
  naturality _ _ f := by
    cases f
    all_goals
      dsimp
      simp only [Functor.map_id, Category.id_comp, Category.comp_id, Functor.map_comp, h₁, h₂, h₃,
        reassoc_of% h₁, reassoc_of% h₂, Category.assoc]

set_option backward.privateInPublic true in
@[simp]
lemma mkNatTrans_app_zero : (mkNatTrans e₀ e₁ h₁ h₂ h₃).app zero = e₀ := rfl

set_option backward.privateInPublic true in
@[simp]
lemma mkNatTrans_app_one : (mkNatTrans e₀ e₁ h₁ h₂ h₃).app one = e₁ := rfl

end NatTrans
section NatIso

variable {F G : WalkingReflexivePair ⥤ C}
/-- Constructor for natural isomorphisms between functors out of `WalkingReflexivePair`. -/
@[simps!]
def mkNatIso (e₀ : F.obj zero ≅ G.obj zero) (e₁ : F.obj one ≅ G.obj one)
    (h₁ : F.map left ≫ e₀.hom = e₁.hom ≫ G.map left := by cat_disch)
    (h₂ : F.map right ≫ e₀.hom = e₁.hom ≫ G.map right := by cat_disch)
    (h₃ : F.map reflexion ≫ e₁.hom = e₀.hom ≫ G.map reflexion := by cat_disch) :
    F ≅ G where
  hom := mkNatTrans e₀.hom e₁.hom
  inv := mkNatTrans e₀.inv e₁.inv
        (by rw [← cancel_epi e₁.hom, e₁.hom_inv_id_assoc, ← reassoc_of% h₁, e₀.hom_inv_id,
            Category.comp_id])
        (by rw [← cancel_epi e₁.hom, e₁.hom_inv_id_assoc, ← reassoc_of% h₂, e₀.hom_inv_id,
            Category.comp_id])
        (by rw [← cancel_epi e₀.hom, e₀.hom_inv_id_assoc, ← reassoc_of% h₃, e₁.hom_inv_id,
            Category.comp_id])
  hom_inv_id := by ext x; cases x <;> simp
  inv_hom_id := by ext x; cases x <;> simp

variable (F)

/-- Every functor out of `WalkingReflexivePair` is isomorphic to the `reflexivePair` given by
its components -/
@[simps!]
def diagramIsoReflexivePair :
    F ≅ reflexivePair (F.map left) (F.map right) (F.map reflexion) :=
  mkNatIso (Iso.refl _) (Iso.refl _)

end NatIso

/-- A `reflexivePair` composed with a functor is isomorphic to the `reflexivePair` obtained by
applying the functor at each map. -/
@[simps!]
def compRightIso {D : Type u₂} [Category.{v₂} D] {A B : C}
    (f g : A ⟶ B) (s : B ⟶ A) (sl : s ≫ f = 𝟙 B) (sr : s ≫ g = 𝟙 B) (F : C ⥤ D) :
    (reflexivePair f g s sl sr) ⋙ F ≅ reflexivePair (F.map f) (F.map g) (F.map s)
      (by simp only [← Functor.map_comp, sl, Functor.map_id])
      (by simp only [← Functor.map_comp, sr, Functor.map_id]) :=
  mkNatIso (Iso.refl _) (Iso.refl _)

lemma whiskerRightMkNatTrans {F G : WalkingReflexivePair ⥤ C}
    (e₀ : F.obj zero ⟶ G.obj zero) (e₁ : F.obj one ⟶ G.obj one)
    {h₁ : F.map left ≫ e₀ = e₁ ≫ G.map left}
    {h₂ : F.map right ≫ e₀ = e₁ ≫ G.map right}
    {h₃ : F.map reflexion ≫ e₁ = e₀ ≫ G.map reflexion}
    {D : Type u₂} [Category.{v₂} D] (H : C ⥤ D) :
    Functor.whiskerRight (mkNatTrans e₀ e₁ : F ⟶ G) H =
      mkNatTrans (H.map e₀) (H.map e₁)
          (by simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, h₁])
          (by simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, h₂])
          (by simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, h₃]) := by
  ext x; cases x <;> simp

end

/-- Any functor out of the WalkingReflexivePair yields a reflexive pair -/
instance to_isReflexivePair {F : WalkingReflexivePair ⥤ C} :
    IsReflexivePair (F.map .left) (F.map .right) :=
  ⟨F.map .reflexion, map_reflexion_comp_map_left F, map_reflexion_comp_map_right F⟩

end reflexivePair

/-- A `ReflexiveCofork` is a cocone over a `WalkingReflexivePair`-shaped diagram. -/
abbrev ReflexiveCofork (F : WalkingReflexivePair ⥤ C) := Cocone F

namespace ReflexiveCofork

open WalkingReflexivePair WalkingReflexivePair.Hom

variable {F : WalkingReflexivePair ⥤ C}

/-- The tail morphism of a reflexive cofork. -/
abbrev π (G : ReflexiveCofork F) : F.obj zero ⟶ G.pt := G.ι.app zero

/-- Constructor for `ReflexiveCofork` -/
@[simps pt]
def mk {X : C} (π : F.obj zero ⟶ X) (h : F.map left ≫ π = F.map right ≫ π) :
    ReflexiveCofork F where
  pt := X
  ι := reflexivePair.mkNatTrans π (F.map left ≫ π)

@[simp]
lemma mk_π {X : C} (π : F.obj zero ⟶ X) (h : F.map left ≫ π = F.map right ≫ π) :
    (mk π h).π = π := rfl

lemma condition (G : ReflexiveCofork F) : F.map left ≫ G.π = F.map right ≫ G.π := by
  rw [Cocone.w G left, Cocone.w G right]

@[simp]
lemma app_one_eq_π (G : ReflexiveCofork F) : G.ι.app zero = G.π := rfl

/-- The underlying `Cofork` of a `ReflexiveCofork`. -/
abbrev toCofork (G : ReflexiveCofork F) : Cofork (F.map left) (F.map right) :=
  Cofork.ofπ G.π (by simp)

end ReflexiveCofork

noncomputable section
open WalkingReflexivePair WalkingReflexivePair.Hom

variable (F : WalkingReflexivePair ⥤ C)

/-- Forgetting the reflexion yields an equivalence between cocones over a bundled reflexive pair and
coforks on the underlying parallel pair. -/
@[simps! functor_obj_pt inverse_obj_pt]
def reflexiveCoforkEquivCofork :
    ReflexiveCofork F ≌ Cofork (F.map left) (F.map right) :=
  (Functor.Final.coconesEquiv _ F).symm.trans (Cocone.precomposeEquivalence
    (diagramIsoParallelPair (WalkingParallelPair.inclusionWalkingReflexivePair ⋙ F)))

@[simp]
lemma reflexiveCoforkEquivCofork_functor_obj_π (G : ReflexiveCofork F) :
    ((reflexiveCoforkEquivCofork F).functor.obj G).π = G.π := by
  dsimp [reflexiveCoforkEquivCofork]
  rw [ReflexiveCofork.π, Cofork.π]
  simp

@[simp]
lemma reflexiveCoforkEquivCofork_inverse_obj_π
    (G : Cofork (F.map left) (F.map right)) :
    ((reflexiveCoforkEquivCofork F).inverse.obj G).π = G.π := by
  dsimp only [reflexiveCoforkEquivCofork, Equivalence.symm, Equivalence.trans,
    ReflexiveCofork.π, Cocone.precomposeEquivalence, Cocone.precompose,
    Functor.comp, Functor.Final.coconesEquiv]
  rw [Functor.Final.extendCocone_obj_ι_app' (Y := .one) (f := 𝟙 zero)]
  simp

/-- The equivalence between reflexive coforks and coforks sends a reflexive cofork to its underlying
cofork. -/
def reflexiveCoforkEquivCoforkObjIso (G : ReflexiveCofork F) :
    (reflexiveCoforkEquivCofork F).functor.obj G ≅ G.toCofork :=
  Cofork.ext (Iso.refl _)
    (by simp [reflexiveCoforkEquivCofork, Cofork.π])

lemma hasReflexiveCoequalizer_iff_hasCoequalizer :
    HasColimit F ↔ HasCoequalizer (F.map left) (F.map right) := by
  simpa only [hasColimit_iff_hasInitial_cocone]
    using Equivalence.hasInitial_iff (reflexiveCoforkEquivCofork F)

instance reflexivePair_hasColimit_of_hasCoequalizer
    [h : HasCoequalizer (F.map left) (F.map right)] : HasColimit F :=
  hasReflexiveCoequalizer_iff_hasCoequalizer _ |>.mpr h

/-- A reflexive cofork is a colimit cocone if and only if the underlying cofork is. -/
def ReflexiveCofork.isColimitEquiv (G : ReflexiveCofork F) :
    IsColimit (G.toCofork) ≃ IsColimit G :=
  IsColimit.equivIsoColimit (reflexiveCoforkEquivCoforkObjIso F G).symm |>.trans <|
    (IsColimit.precomposeHomEquiv (diagramIsoParallelPair _).symm (G.whisker _)).trans <|
      Functor.Final.isColimitWhiskerEquiv _ _

section

variable [HasCoequalizer (F.map left) (F.map right)]

/-- The colimit of a functor out of the walking reflexive pair is the same as the colimit of the
underlying parallel pair. -/
def reflexiveCoequalizerIsoCoequalizer :
    colimit F ≅ coequalizer (F.map left) (F.map right) :=
  ((ReflexiveCofork.isColimitEquiv _ _).symm (colimit.isColimit F)).coconePointUniqueUpToIso
    (colimit.isColimit _)

@[reassoc (attr := simp)]
lemma ι_reflexiveCoequalizerIsoCoequalizer_hom :
    colimit.ι F zero ≫ (reflexiveCoequalizerIsoCoequalizer F).hom =
      coequalizer.π (F.map left) (F.map right) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    ((ReflexiveCofork.isColimitEquiv F _).symm _) _ WalkingParallelPair.one

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma π_reflexiveCoequalizerIsoCoequalizer_inv :
    coequalizer.π _ _ ≫ (reflexiveCoequalizerIsoCoequalizer F).inv = colimit.ι F _ := by
  rw [reflexiveCoequalizerIsoCoequalizer]
  simp only [colimit.comp_coconePointUniqueUpToIso_inv, Cofork.ofπ_pt, colimit.cocone_x,
    Cofork.ofπ_ι_app, colimit.cocone_ι]

end

variable {A B : C} {f g : A ⟶ B} [IsReflexivePair f g] [h : HasCoequalizer f g]

instance ofIsReflexivePair_hasColimit_of_hasCoequalizer :
    HasColimit (ofIsReflexivePair f g) :=
  hasReflexiveCoequalizer_iff_hasCoequalizer _ |>.mpr h

/-- The coequalizer of a reflexive pair can be promoted to the colimit of a diagram out of the
walking reflexive pair -/
def colimitOfIsReflexivePairIsoCoequalizer :
    colimit (ofIsReflexivePair f g) ≅ coequalizer f g :=
  @reflexiveCoequalizerIsoCoequalizer _ _ (ofIsReflexivePair f g) h


@[reassoc (attr := simp)]
lemma ι_colimitOfIsReflexivePairIsoCoequalizer_hom :
    colimit.ι (ofIsReflexivePair f g) zero ≫ colimitOfIsReflexivePairIsoCoequalizer.hom =
      coequalizer.π f g := @ι_reflexiveCoequalizerIsoCoequalizer_hom _ _ _ h

@[reassoc (attr := simp)]
lemma π_colimitOfIsReflexivePairIsoCoequalizer_inv :
    coequalizer.π f g ≫ colimitOfIsReflexivePairIsoCoequalizer.inv =
      colimit.ι (ofIsReflexivePair f g) zero :=
  @π_reflexiveCoequalizerIsoCoequalizer_inv _ _ (ofIsReflexivePair f g) h

end
end Limits

namespace Limits

open WalkingReflexivePair

variable {C : Type u} [Category.{v} C]

/-- A category has coequalizers of reflexive pairs if and only if it has all colimits indexed by the
walking reflexive pair. -/
theorem hasReflexiveCoequalizers_iff :
    HasColimitsOfShape WalkingReflexivePair C ↔ HasReflexiveCoequalizers C :=
  ⟨fun _ ↦ ⟨fun _ _ f g _ ↦ (hasReflexiveCoequalizer_iff_hasCoequalizer
      (reflexivePair f g (commonSection f g))).1 inferInstance⟩,
    fun _ ↦ ⟨inferInstance⟩⟩

end Limits

end CategoryTheory
