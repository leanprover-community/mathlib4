/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Kim Morrison
-/
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Additive Functors

A functor between two preadditive categories is called *additive*
provided that the induced map on hom types is a morphism of abelian
groups.

An additive functor between preadditive categories creates and preserves biproducts.
Conversely, if `F : C ⥤ D` is a functor between preadditive categories, where `C` has binary
biproducts, and if `F` preserves binary biproducts, then `F` is additive.

We also define the category of bundled additive functors.

# Implementation details

`Functor.Additive` is a `Prop`-valued class, defined by saying that for every two objects `X` and
`Y`, the map `F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of abelian groups.

-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-- A functor `F` is additive provided `F.map` is an additive homomorphism. -/
@[stacks 00ZY]
class Functor.Additive {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) : Prop where
  /-- the addition of two morphisms is mapped to the sum of their images -/
  map_add : ∀ {X Y : C} {f g : X ⟶ Y}, F.map (f + g) = F.map f + F.map g := by cat_disch

section Preadditive

namespace Functor

section

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E] (F : C ⥤ D) [Functor.Additive F]

@[simp]
theorem map_add {X Y : C} {f g : X ⟶ Y} : F.map (f + g) = F.map f + F.map g :=
  Functor.Additive.map_add

/-- `F.mapAddHom` is an additive homomorphism whose underlying function is `F.map`. -/
@[simps!]
def mapAddHom {X Y : C} : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y) :=
  AddMonoidHom.mk' (fun f => F.map f) fun _ _ => F.map_add

theorem coe_mapAddHom {X Y : C} : ⇑(F.mapAddHom : (X ⟶ Y) →+ _) = F.map :=
  rfl

instance (priority := 100) preservesZeroMorphisms_of_additive : PreservesZeroMorphisms F where
  map_zero _ _ := F.mapAddHom.map_zero

instance : Additive (𝟭 C) where

instance {E : Type*} [Category E] [Preadditive E] (G : D ⥤ E) [Functor.Additive G] :
    Additive (F ⋙ G) where

instance {J : Type*} [Category J] (j : J) : ((evaluation J C).obj j).Additive where

@[simp]
theorem map_neg {X Y : C} {f : X ⟶ Y} : F.map (-f) = -F.map f :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_neg _

@[simp]
theorem map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_sub _ _

theorem map_nsmul {X Y : C} {f : X ⟶ Y} {n : ℕ} : F.map (n • f) = n • F.map f :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_nsmul _ _

-- You can alternatively just use `Functor.map_smul` here, with an explicit `(r : ℤ)` argument.
theorem map_zsmul {X Y : C} {f : X ⟶ Y} {r : ℤ} : F.map (r • f) = r • F.map f :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_zsmul _ _

@[simp]
nonrec theorem map_sum {X Y : C} {α : Type*} (f : α → (X ⟶ Y)) (s : Finset α) :
    F.map (∑ a ∈ s, f a) = ∑ a ∈ s, F.map (f a) :=
  map_sum F.mapAddHom f s

variable {F}

lemma additive_of_iso {G : C ⥤ D} (e : F ≅ G) : G.Additive := by
  constructor
  intro X Y f g
  simp only [← NatIso.naturality_1 e (f + g), map_add, Preadditive.add_comp,
    NatTrans.naturality, Preadditive.comp_add, Iso.inv_hom_id_app_assoc]

variable (F)

lemma additive_of_full_essSurj_comp [Full F] [EssSurj F] (G : D ⥤ E)
    [(F ⋙ G).Additive] : G.Additive where
  map_add {X Y f g} := by
    obtain ⟨f', hf'⟩ := F.map_surjective ((F.objObjPreimageIso X).hom ≫ f ≫
      (F.objObjPreimageIso Y).inv)
    obtain ⟨g', hg'⟩ := F.map_surjective ((F.objObjPreimageIso X).hom ≫ g ≫
      (F.objObjPreimageIso Y).inv)
    simp only [← cancel_mono (G.map (F.objObjPreimageIso Y).inv),
      ← cancel_epi (G.map (F.objObjPreimageIso X).hom),
      Preadditive.add_comp, Preadditive.comp_add, ← Functor.map_comp]
    erw [← hf', ← hg', ← (F ⋙ G).map_add]
    dsimp
    rw [F.map_add]

lemma additive_of_comp_faithful
    (F : C ⥤ D) (G : D ⥤ E) [G.Additive] [(F ⋙ G).Additive] [Faithful G] :
    F.Additive where
  map_add {_ _ f₁ f₂} := G.map_injective (by
    rw [← Functor.comp_map, G.map_add, (F ⋙ G).map_add, Functor.comp_map, Functor.comp_map])

open ZeroObject Limits in
include F in
lemma hasZeroObject_of_additive [HasZeroObject C] :
    HasZeroObject D where
  zero := ⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩

end

section InducedCategory

variable {C : Type*} {D : Type*} [Category D] [Preadditive D] (F : C → D)

instance inducedFunctor_additive : Functor.Additive (inducedFunctor F) where

end InducedCategory

instance fullSubcategoryInclusion_additive {C : Type*} [Category C] [Preadditive C]
    (Z : ObjectProperty C) : Z.ι.Additive where

section

-- To talk about preservation of biproducts we need to specify universes explicitly.
noncomputable section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
  [Preadditive D] (F : C ⥤ D)

open CategoryTheory.Limits

open CategoryTheory.Preadditive

instance (priority := 100) preservesFiniteBiproductsOfAdditive [Additive F] :
    PreservesFiniteBiproducts F where
  preserves := fun {J} _ =>
    let ⟨_⟩ := nonempty_fintype J
    { preserves :=
      { preserves := fun hb =>
          ⟨isBilimitOfTotal _ (by
            simp_rw [F.mapBicone_π, F.mapBicone_ι, ← F.map_comp]
            erw [← F.map_sum, ← F.map_id, IsBilimit.total hb])⟩ } }

instance (priority := 100) preservesFiniteCoproductsOfAdditive [Additive F] :
    PreservesFiniteCoproducts F where
  preserves _ := preservesCoproductsOfShape_of_preservesBiproductsOfShape F

instance (priority := 100) preservesFiniteProductsOfAdditive [Additive F] :
    PreservesFiniteProducts F where
  preserves _ := preservesProductsOfShape_of_preservesBiproductsOfShape F

theorem additive_of_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F]
    [PreservesBinaryBiproducts F] : Additive F where
  map_add {X Y f g} := by
    rw [biprod.add_eq_lift_id_desc, F.map_comp, ← biprod.lift_mapBiprod,
      ← biprod.mapBiprod_hom_desc, Category.assoc, Iso.inv_hom_id_assoc, F.map_id,
      biprod.add_eq_lift_id_desc]

lemma additive_of_preserves_binary_products
    [HasBinaryProducts C] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [F.PreservesZeroMorphisms] : F.Additive := by
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryProducts
  have := preservesBinaryBiproducts_of_preservesBinaryProducts F
  exact Functor.additive_of_preservesBinaryBiproducts F

end

end

end Functor

namespace Equivalence

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]

instance inverse_additive (e : C ≌ D) [e.functor.Additive] : e.inverse.Additive where
  map_add {f g} := e.functor.map_injective (by simp)

end Equivalence

section

variable (C D : Type*) [Category C] [Category D] [Preadditive C] [Preadditive D]

/-- Bundled additive functors. -/
def AdditiveFunctor :=
  ObjectProperty.FullSubcategory fun F : C ⥤ D => F.Additive

instance : Category (AdditiveFunctor C D) :=
  ObjectProperty.FullSubcategory.category _

/-- the category of additive functors is denoted `C ⥤+ D` -/
infixr:26 " ⥤+ " => AdditiveFunctor

instance : Preadditive (C ⥤+ D) :=
  Preadditive.inducedCategory _

/-- An additive functor is in particular a functor. -/
def AdditiveFunctor.forget : (C ⥤+ D) ⥤ C ⥤ D :=
  ObjectProperty.ι _

instance : (AdditiveFunctor.forget C D).Full :=
  ObjectProperty.full_ι _

instance : (AdditiveFunctor.forget C D).Faithful :=
  ObjectProperty.faithful_ι _

variable {C D}

/-- Turn an additive functor into an object of the category `AdditiveFunctor C D`. -/
def AdditiveFunctor.of (F : C ⥤ D) [F.Additive] : C ⥤+ D :=
  ⟨F, inferInstance⟩

@[simp]
theorem AdditiveFunctor.of_fst (F : C ⥤ D) [F.Additive] : (AdditiveFunctor.of F).1 = F :=
  rfl

@[simp]
theorem AdditiveFunctor.forget_obj (F : C ⥤+ D) : (AdditiveFunctor.forget C D).obj F = F.1 :=
  rfl

theorem AdditiveFunctor.forget_obj_of (F : C ⥤ D) [F.Additive] :
    (AdditiveFunctor.forget C D).obj (AdditiveFunctor.of F) = F :=
  rfl

@[simp]
theorem AdditiveFunctor.forget_map (F G : C ⥤+ D) (α : F ⟶ G) :
    (AdditiveFunctor.forget C D).map α = α :=
  rfl

instance : Functor.Additive (AdditiveFunctor.forget C D) where map_add := rfl

instance (F : C ⥤+ D) : Functor.Additive F.1 :=
  F.2

end

section Exact

open CategoryTheory.Limits

variable (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
variable [Preadditive D] [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts C]

section

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

/-- Turn a left exact functor into an additive functor. -/
def AdditiveFunctor.ofLeftExact : (C ⥤ₗ D) ⥤ C ⥤+ D :=
  ObjectProperty.ιOfLE fun F ⟨_⟩ =>
    Functor.additive_of_preservesBinaryBiproducts F

instance : (AdditiveFunctor.ofLeftExact C D).Full := ObjectProperty.full_ιOfLE _
instance : (AdditiveFunctor.ofLeftExact C D).Faithful := ObjectProperty.faithful_ιOfLE _

/-- Turn a right exact functor into an additive functor. -/
def AdditiveFunctor.ofRightExact : (C ⥤ᵣ D) ⥤ C ⥤+ D :=
  ObjectProperty.ιOfLE fun F ⟨_⟩ =>
    Functor.additive_of_preservesBinaryBiproducts F

instance : (AdditiveFunctor.ofRightExact C D).Full := ObjectProperty.full_ιOfLE _
instance : (AdditiveFunctor.ofRightExact C D).Faithful := ObjectProperty.faithful_ιOfLE _

/-- Turn an exact functor into an additive functor. -/
def AdditiveFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤+ D :=
  ObjectProperty.ιOfLE fun F ⟨⟨_⟩, _⟩ =>
    Functor.additive_of_preservesBinaryBiproducts F

instance : (AdditiveFunctor.ofExact C D).Full := ObjectProperty.full_ιOfLE _
instance : (AdditiveFunctor.ofExact C D).Faithful := ObjectProperty.faithful_ιOfLE _

end

variable {C D}

@[simp]
theorem AdditiveFunctor.ofLeftExact_obj_fst (F : C ⥤ₗ D) :
    ((AdditiveFunctor.ofLeftExact C D).obj F).obj = F.obj :=
  rfl

@[simp]
theorem AdditiveFunctor.ofRightExact_obj_fst (F : C ⥤ᵣ D) :
    ((AdditiveFunctor.ofRightExact C D).obj F).obj = F.obj :=
  rfl

@[simp]
theorem AdditiveFunctor.ofExact_obj_fst (F : C ⥤ₑ D) :
    ((AdditiveFunctor.ofExact C D).obj F).obj = F.obj :=
  rfl

@[simp]
theorem AdditiveFunctor.ofLeftExact_map {F G : C ⥤ₗ D} (α : F ⟶ G) :
    (AdditiveFunctor.ofLeftExact C D).map α = α :=
  rfl

@[simp]
theorem AdditiveFunctor.ofRightExact_map {F G : C ⥤ᵣ D} (α : F ⟶ G) :
    (AdditiveFunctor.ofRightExact C D).map α = α :=
  rfl

@[simp]
theorem AdditiveFunctor.ofExact_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
    (AdditiveFunctor.ofExact C D).map α = α :=
  rfl

end Exact

end Preadditive

end CategoryTheory
