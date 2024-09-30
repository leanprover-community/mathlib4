/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

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
* `WalkingReflexivePair.inclusionWalkingReflexivePair` is the inclustion functor from
  `WalkingParallelPair` to `WalkingReflexivePair`. It acts on reflexive pairs as forgetting
  the common section.
* `HasReflexiveCoequalizers` is the predicate that a category has all colimits of reflexive pairs.
* `ofIsReflexivePairColimitEquiv`: an isomorphism promoting the coequalizer of a reflexive pair to
  the colimit of a diagram out of the walking reflexive pair

## Main statements

* `IsKernelPair.isReflexivePair`: A kernel pair is a reflexive pair
* `WalkingParallelPair.inclusionWalkingReflexivePair_final`: The inclusion functor is final.
* `hasReflexiveCoequalizers_iff`: A category has coequalizers of reflexive pairs if and only iff it
  has all colimits of shape `WalkingReflexivePair`.

# TODO
* If `C` has binary coproducts and reflexive coequalizers, then it has all coequalizers.
* If `T` is a monad on cocomplete category `C`, then `Algebra T` is cocomplete iff it has reflexive
  coequalizers.
* If `C` is locally cartesian closed and has reflexive coequalizers, then it has images: in fact
  regular epi (and hence strong epi) images.
* Bundle the reflexive pairs of kernel pairs and of adjunction as functors out of the walking
  reflexive pair.
-/


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

/-- The type of morphisms for the diagram indexing reflexive (co)equalizers -/
inductive WalkingReflexivePairHom : (WalkingReflexivePair → WalkingReflexivePair → Type)
  | left : WalkingReflexivePairHom one zero
  | right : WalkingReflexivePairHom one zero
  | reflexion : WalkingReflexivePairHom zero one
  | left_reflexion : WalkingReflexivePairHom one one
  | right_reflexion : WalkingReflexivePairHom one one
  | id (X : WalkingReflexivePair) : WalkingReflexivePairHom X X
  deriving DecidableEq

attribute [-simp, nolint simpNF] WalkingReflexivePairHom.id.sizeOf_spec

open WalkingReflexivePairHom

/-- Composition of morphisms in the diagram indexing reflexive (co)equalizers -/
def WalkingReflexivePairHom.comp :
    ∀ { X Y Z : WalkingReflexivePair } (_ : WalkingReflexivePairHom X Y)
      (_ : WalkingReflexivePairHom Y Z), WalkingReflexivePairHom X Z
  | _, _, _, id _, h => h
  | _, _, _, h, id _ => h
  | _, _, _, reflexion, left => id zero
  | _, _, _, reflexion, right => id zero
  | _, _, _, reflexion, right_reflexion => reflexion
  | _, _, _, reflexion, left_reflexion => reflexion
  | _, _, _, left, reflexion => left_reflexion
  | _, _, _, right, reflexion => right_reflexion
  | _, _, _, right_reflexion, right_reflexion => right_reflexion
  | _, _, _, right_reflexion, left_reflexion => right_reflexion
  | _, _, _, right_reflexion, right => right
  | _, _, _, right_reflexion, left => right
  | _, _, _, left_reflexion, left => left
  | _, _, _, left_reflexion, right => left
  | _, _, _, left_reflexion, right_reflexion => left_reflexion
  | _, _, _, left_reflexion, left_reflexion => left_reflexion

theorem WalkingReflexivePairHom.id_comp
    {X Y : WalkingReflexivePair} (g : WalkingReflexivePairHom X Y) : comp (id X) g = g := by
  cases g <;> rfl

theorem WalkingReflexivePairHom.comp_id
    {X Y : WalkingReflexivePair} (f : WalkingReflexivePairHom X Y) : comp f (id Y) = f := by
  cases f <;> rfl

theorem WalkingReflexivePairHom.assoc {X Y Z W : WalkingReflexivePair}
    (f : WalkingReflexivePairHom X Y) (g: WalkingReflexivePairHom Y Z)
    (h : WalkingReflexivePairHom Z W) : comp (comp f g) h = comp f (comp g h) := by
  cases f <;> cases g <;> cases h <;> rfl

instance walkingReflexivePairCategory : SmallCategory WalkingReflexivePair where
  Hom := WalkingReflexivePairHom
  id := id
  comp := comp
  comp_id := comp_id
  id_comp := id_comp
  assoc := assoc

@[simp]
theorem walkingReflexivePairHom_id (X : WalkingReflexivePair) :
    WalkingReflexivePairHom.id X = 𝟙 X := by rfl

@[simp]
theorem walkingReflexivePairHom_left_comp_reflexion : left.comp reflexion = left_reflexion := rfl

@[simp]
theorem walkingReflexivePairHom_right_comp_reflexion : right.comp reflexion = right_reflexion := rfl

namespace WalkingParallelPair

/-- The forgetful functor forgetting the common section -/
def inclusionWalkingReflexivePair : WalkingParallelPair ⥤ WalkingReflexivePair :=
  { obj := fun x => match x with
      | one => WalkingReflexivePair.zero
      | zero => WalkingReflexivePair.one
    map := fun f => match f with
      | WalkingParallelPairHom.left => left
      | WalkingParallelPairHom.right => right
      | WalkingParallelPairHom.id _ => WalkingReflexivePairHom.id _
    map_comp := by
      intro _ _ _ f g; cases f <;> cases g <;> rfl }

variable {C : Type u} [Category.{v} C]

@[simp]
lemma whisker_inclusionWalkingReflexivePair_zero (F : WalkingReflexivePair ⥤ C) :
    F.obj (inclusionWalkingReflexivePair.obj WalkingParallelPair.one) =
      F.obj WalkingReflexivePair.zero :=
  rfl

@[simp]
lemma whisker_inclusionWalkingReflexivePair_one (F : WalkingReflexivePair ⥤ C) :
    F.obj (inclusionWalkingReflexivePair.obj WalkingParallelPair.zero) =
      F.obj WalkingReflexivePair.one :=
  rfl

@[simp]
lemma whisker_inclusionWalkingReflexivePair_left (F : WalkingReflexivePair ⥤ C) :
    F.map (inclusionWalkingReflexivePair.map WalkingParallelPairHom.left) = F.map left := rfl

@[simp]
lemma whisker_inclusionWalkingReflexivePair_right (F : WalkingReflexivePair ⥤ C) :
    F.map (inclusionWalkingReflexivePair.map WalkingParallelPairHom.right) = F.map right := rfl

/-- The forgetful functor is a final functor -/
instance inclusionWalkingReflexivePair_final : Functor.Final inclusionWalkingReflexivePair := by
  constructor
  set e₀ : (StructuredArrow WalkingReflexivePair.one inclusionWalkingReflexivePair) :=
    StructuredArrow.mk (Y := WalkingParallelPair.zero) (id WalkingReflexivePair.one)
  set e₁ : (StructuredArrow WalkingReflexivePair.zero inclusionWalkingReflexivePair) :=
    StructuredArrow.mk (Y := WalkingParallelPair.one) (id WalkingReflexivePair.zero)
  intro x
  have h : Inhabited (StructuredArrow x inclusionWalkingReflexivePair) := by
    · constructor
      cases x with
      | one => exact e₀
      | zero => exact e₁
  cases x with
    | zero => apply IsConnected.of_induct (j₀ := e₁)
              intro p h₁ h₂ t
              rcases t with ⟨l, y, f⟩
              cases y <;> cases f
              · set r : StructuredArrow WalkingReflexivePair.zero inclusionWalkingReflexivePair :=
                  StructuredArrow.mk (Y := WalkingParallelPair.zero) reflexion
                change r ∈ p
                suffices f : r ⟶  e₁ by exact (h₂ f).mpr h₁
                exact StructuredArrow.homMk (WalkingParallelPairHom.left)
              · exact h₁
    | one => apply IsConnected.of_induct (j₀ := e₀)
             intro p h₁ h₂ t
             rcases t with ⟨l, y, f⟩
             set rₗ : StructuredArrow WalkingReflexivePair.one inclusionWalkingReflexivePair :=
                StructuredArrow.mk (Y := WalkingParallelPair.one) left
             set rᵣ : StructuredArrow WalkingReflexivePair.one inclusionWalkingReflexivePair :=
                StructuredArrow.mk (Y := WalkingParallelPair.one) right
             have hrₗ : rₗ ∈ p := by
              · suffices f : e₀ ⟶  rₗ by exact (h₂ f).mp h₁
                exact StructuredArrow.homMk WalkingParallelPairHom.left
             have hrᵣ : rᵣ ∈ p := by
              · suffices f : e₀ ⟶  rᵣ by exact (h₂ f).mp h₁
                exact StructuredArrow.homMk WalkingParallelPairHom.right
             cases y <;> cases f
             rotate_right 3
             · exact h₁
             · exact hrₗ
             · exact hrᵣ
             · set v : StructuredArrow WalkingReflexivePair.one inclusionWalkingReflexivePair :=
                StructuredArrow.mk (Y := WalkingParallelPair.zero) left_reflexion
               suffices f : v ⟶  rₗ by exact (h₂ f).mpr hrₗ
               exact StructuredArrow.homMk (WalkingParallelPairHom.left)
             · set v : StructuredArrow WalkingReflexivePair.one inclusionWalkingReflexivePair :=
                StructuredArrow.mk (Y := WalkingParallelPair.zero) right_reflexion
               suffices f : v ⟶  rᵣ by exact (h₂ f).mpr hrᵣ
               exact StructuredArrow.homMk (WalkingParallelPairHom.right)

end WalkingParallelPair

end Limits

namespace Limits

open WalkingReflexivePair

open WalkingReflexivePairHom

variable {C : Type u} [Category.{v} C]

variable {A B : C}

/-- Bundle the data of a parallel pair along with a common section as a functor out of the walking
reflexive pair -/
def reflexivePair (f g : A ⟶ B) (s : B ⟶ A) (sl : s ≫ f = 𝟙 B) (sr : s ≫ g = 𝟙 B) :
    (WalkingReflexivePair ⥤ C) where
  obj x :=
    match x with
    | zero => B
    | one => A
  map h :=
    match h with
    | WalkingReflexivePairHom.id _ => 𝟙 _
    | left => f
    | right => g
    | reflexion => s
    | right_reflexion => g ≫ s
    | left_reflexion => f ≫ s
  map_comp := by
    rintro _ _ _ ⟨⟩ g <;> cases g <;>
    simp only [Category.id_comp, Category.comp_id, Category.assoc, sl, sr] <;>
    try {rfl}
    iterate simp only [Category.id_comp, Category.comp_id, ← Category.assoc, sl, sr] <;> try {rfl}

/-- (Noncomputably) bundle the data of a reflexive pair as a functor out of the walking reflexive
pair -/
noncomputable def ofIsReflexivePair (f g : A ⟶ B) [IsReflexivePair f g] :
    (WalkingReflexivePair ⥤ C) :=
  reflexivePair f g (commonSection f g) (section_comp_left f g) (section_comp_right f g)

/-- The natural isomorphism between the diagram obtained by forgetting the reflexion of
`ofIsReflexivePair f g` and the original parallel pair. -/
noncomputable def inclusionWalkingReflexivePairOfIsReflexivePairIso
    (f g : A ⟶ B) [IsReflexivePair f g] :
    WalkingParallelPair.inclusionWalkingReflexivePair ⋙ (ofIsReflexivePair f g) ≅
      parallelPair f g :=
  diagramIsoParallelPair _

end Limits

namespace Limits

open WalkingReflexivePair

open WalkingReflexivePairHom

variable {C : Type u} [Category.{v} C]

@[simp]
theorem reflexivePair_reflexion_comp_left (F : WalkingReflexivePair ⥤ C) :
    F.map reflexion ≫ F.map left = 𝟙 F.obj zero :=
  (F.map_id zero).symm.trans (F.map_comp reflexion left)|>.symm

@[simp]
theorem reflexivePair_reflexion_comp_right (F : WalkingReflexivePair ⥤ C) :
    F.map reflexion ≫ F.map right = 𝟙 F.obj zero :=
  (F.map_id zero).symm.trans (F.map_comp reflexion right)|>.symm

@[simp]
theorem reflexivePair_left_comp_reflexion (F : WalkingReflexivePair ⥤ C) :
    F.map left_reflexion = F.map left ≫ F.map reflexion := F.map_comp left reflexion

@[simp]
theorem reflexivePair_right_comp_reflexion (F : WalkingReflexivePair ⥤ C) :
    F.map right_reflexion = F.map right ≫ F.map reflexion := F.map_comp right reflexion

/-- Any functor out of `WalkingReflexivePair` is isomorphic to the reflexive pair built out of the
images of its morphisms -/
def diagramIsoReflexivePair (F : WalkingReflexivePair ⥤ C) :
    F ≅ reflexivePair (F.map left) (F.map right) (F.map reflexion)
    ((F.map_id zero).symm.trans (F.map_comp reflexion left)).symm
    ((F.map_id zero).symm.trans (F.map_comp reflexion right)).symm :=
  NatIso.ofComponents (fun j => eqToIso <| by cases j <;> rfl) <| by
      rintro _ _ f; cases f <;> aesop_cat

variable {F : WalkingReflexivePair ⥤ C}

/-- Any functor out of the WalkingReflexivePair yields a reflexive pair -/
instance to_isReflexivePair :
    IsReflexivePair (F.map left) (F.map right) :=
  ⟨F.map reflexion, reflexivePair_reflexion_comp_left F, reflexivePair_reflexion_comp_right F⟩

/-- A `ReflexiveCofork` is a cocone over a `WalkingReflexivePair`-shaped diagram. -/
abbrev ReflexiveCofork (F : WalkingReflexivePair ⥤ C) := Cocone F

namespace ReflexiveCofork

/-- The tail morphism of a reflexive cofork. -/
def π (G : ReflexiveCofork F) := G.ι.app zero

lemma condition (G : ReflexiveCofork F) : F.map left ≫ G.π = F.map right ≫ G.π := by
  erw [Cocone.w G left, Cocone.w G right]

@[simp]
lemma app_one_eq_π (G : ReflexiveCofork F) : G.ι.app zero = G.π := rfl

/-- The underlying `Cofork` of a `ReflexiveCofork`. -/
def toCofork (G : ReflexiveCofork F) : (Cofork (F.map left) (F.map right)) :=
  Cocones.precompose (diagramIsoParallelPair (_ ⋙ F)).symm.hom |>.obj
    <| G.whisker WalkingParallelPair.inclusionWalkingReflexivePair

@[simp]
lemma toCofork.π (G : ReflexiveCofork F) : Cofork.π (G.toCofork) = G.π := by
  dsimp only [toCofork, Cofork.π]
  aesop_cat

end ReflexiveCofork

/-- Forgetting the reflexion yields an equivalence between cocones over a bundled reflexive pair and
coforks on the underlying parallel pair. -/
noncomputable def inclusionWalkingReflexivePairEquivCocone :
    Cocone F ≌ Cofork (F.map left) (F.map right) :=
  (Functor.Final.coconesEquiv _ F).symm.trans
    (Cocones.precomposeEquivalence
      (diagramIsoParallelPair (WalkingParallelPair.inclusionWalkingReflexivePair ⋙ F))).symm

instance reflexivePair_hasColimit_of_hasCoequalizer
    [h : HasCoequalizer (F.map left) (F.map right)] : HasColimit F := by
  suffices _ : HasColimit (WalkingParallelPair.inclusionWalkingReflexivePair ⋙ F) by
    · apply Functor.Final.hasColimit_of_comp WalkingParallelPair.inclusionWalkingReflexivePair
  exact @Limits.hasColimitOfIso _ _ _ _ _ _ h <| diagramIsoParallelPair _

/-- The colimit of a functor out of the walking reflexive pair is the same as the colimit of the
underlying parallel pair. -/
noncomputable def inclusionWalkingReflexivePairColimitEquiv
    [HasCoequalizer (F.map left) (F.map right)] :
    colimit F ≅ coequalizer (F.map left) (F.map right) :=
  (Functor.Final.colimitIso WalkingParallelPair.inclusionWalkingReflexivePair F).symm.trans
    <| HasColimit.isoOfNatIso
      <| diagramIsoParallelPair
        <| WalkingParallelPair.inclusionWalkingReflexivePair ⋙ F

@[simp]
lemma inclusionWalkingReflexivePairEquiv_obj (G : ReflexiveCofork F) :
    inclusionWalkingReflexivePairEquivCocone.functor.obj G = G.toCofork := rfl

/-- A reflexive cofork is a colimit cocone if and only if the underlying cofork is. -/
noncomputable def ReflexiveCofork.isColimitEquiv (G : ReflexiveCofork F) :
    IsColimit (G.toCofork) ≃ IsColimit G :=
  (IsColimit.precomposeHomEquiv (diagramIsoParallelPair _).symm (G.whisker _)).trans
    <| Functor.Final.isColimitWhiskerEquiv _ _

variable {A B : C} {f g : A ⟶ B} [IsReflexivePair f g]

instance ofIsReflexivePairHasColimit_of_hasCoequalizer [HasCoequalizer f g] :
    HasColimit (ofIsReflexivePair f g) := by
  suffices _ : HasColimit
      <| WalkingParallelPair.inclusionWalkingReflexivePair ⋙ (ofIsReflexivePair f g) by
    · apply Functor.Final.hasColimit_of_comp WalkingParallelPair.inclusionWalkingReflexivePair
  exact Limits.hasColimitOfIso <| inclusionWalkingReflexivePairOfIsReflexivePairIso f g

/-- The coequalizer of a reflexive pair can be promoted to the colimit of a diagram out of the
walking reflexive pair -/
noncomputable def ofIsReflexivePairColimitEquiv [HasCoequalizer f g] :
    colimit (ofIsReflexivePair f g) ≅ coequalizer f g :=
  (Functor.Final.colimitIso _ _).symm.trans
    <| HasColimit.isoOfNatIso <| inclusionWalkingReflexivePairOfIsReflexivePairIso _ _

end Limits

namespace Limits

open WalkingReflexivePair

open WalkingReflexivePairHom

variable {C : Type u} [Category.{v} C]

/-- A category has coequalizers of reflexive pairs if and only if it has all colimits indexed by the
walking reflexive pair. -/
theorem hasReflexiveCoequalizers_iff :
    (HasColimitsOfShape WalkingReflexivePair C) ↔ (HasReflexiveCoequalizers C) := by
  constructor
  · intro h
    constructor
    intro _ _ f g h₁
    set F := @ofIsReflexivePair _ _ _ _ _ _ h₁
    exact @Limits.hasColimitOfIso _ _ _ _ _ _
      (Functor.Final.comp_hasColimit _)
      (diagramIsoParallelPair (WalkingParallelPair.inclusionWalkingReflexivePair ⋙ F)).symm
  · intro h
    exact ⟨by infer_instance⟩

end Limits

open Limits

end CategoryTheory
