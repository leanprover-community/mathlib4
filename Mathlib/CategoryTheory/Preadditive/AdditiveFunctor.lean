/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Scott Morrison
-/
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

#align_import category_theory.preadditive.additive_functor from "leanprover-community/mathlib"@"ee89acdf96a0b45afe3eea493bceb2a80a0f2efa"

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
class Functor.Additive {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) : Prop where
  /-- the addition of two morphisms is mapped to the sum of their images -/
  map_add : ∀ {X Y : C} {f g : X ⟶ Y}, F.map (f + g) = F.map f + F.map g := by aesop_cat
#align category_theory.functor.additive CategoryTheory.Functor.Additive

section Preadditive

namespace Functor

section

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E] (F : C ⥤ D) [Functor.Additive F]

@[simp]
theorem map_add {X Y : C} {f g : X ⟶ Y} : F.map (f + g) = F.map f + F.map g :=
  Functor.Additive.map_add
#align category_theory.functor.map_add CategoryTheory.Functor.map_add

-- Porting note: it was originally @[simps (config := .asFn)]
/-- `F.mapAddHom` is an additive homomorphism whose underlying function is `F.map`. -/
@[simps!]
def mapAddHom {X Y : C} : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y) :=
  AddMonoidHom.mk' (fun f => F.map f) fun _ _ => F.map_add
#align category_theory.functor.map_add_hom CategoryTheory.Functor.mapAddHom

theorem coe_mapAddHom {X Y : C} : ⇑(F.mapAddHom : (X ⟶ Y) →+ _) = F.map :=
  rfl
#align category_theory.functor.coe_map_add_hom CategoryTheory.Functor.coe_mapAddHom

instance (priority := 100) preservesZeroMorphisms_of_additive : PreservesZeroMorphisms F where
  map_zero _ _ := F.mapAddHom.map_zero
#align category_theory.functor.preserves_zero_morphisms_of_additive CategoryTheory.Functor.preservesZeroMorphisms_of_additive

instance : Additive (𝟭 C) where

instance {E : Type*} [Category E] [Preadditive E] (G : D ⥤ E) [Functor.Additive G] :
    Additive (F ⋙ G) where

@[simp]
theorem map_neg {X Y : C} {f : X ⟶ Y} : F.map (-f) = -F.map f :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_neg _
#align category_theory.functor.map_neg CategoryTheory.Functor.map_neg

@[simp]
theorem map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_sub _ _
#align category_theory.functor.map_sub CategoryTheory.Functor.map_sub

theorem map_nsmul {X Y : C} {f : X ⟶ Y} {n : ℕ} : F.map (n • f) = n • F.map f :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_nsmul _ _
#align category_theory.functor.map_nsmul CategoryTheory.Functor.map_nsmul

-- You can alternatively just use `Functor.map_smul` here, with an explicit `(r : ℤ)` argument.
theorem map_zsmul {X Y : C} {f : X ⟶ Y} {r : ℤ} : F.map (r • f) = r • F.map f :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_zsmul _ _
#align category_theory.functor.map_zsmul CategoryTheory.Functor.map_zsmul

@[simp]
nonrec theorem map_sum {X Y : C} {α : Type*} (f : α → (X ⟶ Y)) (s : Finset α) :
    F.map (∑ a ∈ s, f a) = ∑ a ∈ s, F.map (f a) :=
  map_sum F.mapAddHom f s
#align category_theory.functor.map_sum CategoryTheory.Functor.map_sum

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

end

section InducedCategory

variable {C : Type*} {D : Type*} [Category D] [Preadditive D] (F : C → D)

instance inducedFunctor_additive : Functor.Additive (inducedFunctor F) where
#align category_theory.functor.induced_functor_additive CategoryTheory.Functor.inducedFunctor_additive

end InducedCategory

instance fullSubcategoryInclusion_additive {C : Type*} [Category C] [Preadditive C]
    (Z : C → Prop) : (fullSubcategoryInclusion Z).Additive where
#align category_theory.functor.full_subcategory_inclusion_additive CategoryTheory.Functor.fullSubcategoryInclusion_additive

section

-- To talk about preservation of biproducts we need to specify universes explicitly.
noncomputable section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
  [Preadditive D] (F : C ⥤ D)

open CategoryTheory.Limits

open CategoryTheory.Preadditive

instance (priority := 100) preservesFiniteBiproductsOfAdditive [Additive F] :
    PreservesFiniteBiproducts F where
  preserves :=
    { preserves :=
      { preserves := fun hb =>
          isBilimitOfTotal _ (by
            simp_rw [F.mapBicone_π, F.mapBicone_ι, ← F.map_comp]
            erw [← F.map_sum, ← F.map_id, IsBilimit.total hb])} }
#align category_theory.functor.preserves_finite_biproducts_of_additive CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive

theorem additive_of_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F]
    [PreservesBinaryBiproducts F] : Additive F where
  map_add {X Y f g} := by
    rw [biprod.add_eq_lift_id_desc, F.map_comp, ← biprod.lift_mapBiprod,
      ← biprod.mapBiprod_hom_desc, Category.assoc, Iso.inv_hom_id_assoc, F.map_id,
      biprod.add_eq_lift_id_desc]
#align category_theory.functor.additive_of_preserves_binary_biproducts CategoryTheory.Functor.additive_of_preservesBinaryBiproducts

lemma additive_of_preserves_binary_products
    [HasBinaryProducts C] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [F.PreservesZeroMorphisms] : F.Additive := by
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryProducts
  have := preservesBinaryBiproductsOfPreservesBinaryProducts F
  exact Functor.additive_of_preservesBinaryBiproducts F

end

end

end Functor

namespace Equivalence

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]

instance inverse_additive (e : C ≌ D) [e.functor.Additive] : e.inverse.Additive where
  map_add {f g} := e.functor.map_injective (by simp)
#align category_theory.equivalence.inverse_additive CategoryTheory.Equivalence.inverse_additive

end Equivalence

section

variable (C D : Type*) [Category C] [Category D] [Preadditive C] [Preadditive D]

-- porting note (#5171): removed @[nolint has_nonempty_instance]
/-- Bundled additive functors. -/
def AdditiveFunctor :=
  FullSubcategory fun F : C ⥤ D => F.Additive
set_option linter.uppercaseLean3 false in
#align category_theory.AdditiveFunctor CategoryTheory.AdditiveFunctor

instance : Category (AdditiveFunctor C D) :=
  FullSubcategory.category _

/-- the category of additive functors is denoted `C ⥤+ D` -/
infixr:26 " ⥤+ " => AdditiveFunctor

instance : Preadditive (C ⥤+ D) :=
  Preadditive.inducedCategory _

/-- An additive functor is in particular a functor. -/
def AdditiveFunctor.forget : (C ⥤+ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _
set_option linter.uppercaseLean3 false in
#align category_theory.AdditiveFunctor.forget CategoryTheory.AdditiveFunctor.forget

instance : (AdditiveFunctor.forget C D).Full :=
  FullSubcategory.full _

variable {C D}

/-- Turn an additive functor into an object of the category `AdditiveFunctor C D`. -/
def AdditiveFunctor.of (F : C ⥤ D) [F.Additive] : C ⥤+ D :=
  ⟨F, inferInstance⟩
set_option linter.uppercaseLean3 false in
#align category_theory.AdditiveFunctor.of CategoryTheory.AdditiveFunctor.of

@[simp]
theorem AdditiveFunctor.of_fst (F : C ⥤ D) [F.Additive] : (AdditiveFunctor.of F).1 = F :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.AdditiveFunctor.of_fst CategoryTheory.AdditiveFunctor.of_fst

@[simp]
theorem AdditiveFunctor.forget_obj (F : C ⥤+ D) : (AdditiveFunctor.forget C D).obj F = F.1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.AdditiveFunctor.forget_obj CategoryTheory.AdditiveFunctor.forget_obj

theorem AdditiveFunctor.forget_obj_of (F : C ⥤ D) [F.Additive] :
    (AdditiveFunctor.forget C D).obj (AdditiveFunctor.of F) = F :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.AdditiveFunctor.forget_obj_of CategoryTheory.AdditiveFunctor.forget_obj_of

@[simp]
theorem AdditiveFunctor.forget_map (F G : C ⥤+ D) (α : F ⟶ G) :
    (AdditiveFunctor.forget C D).map α = α :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.AdditiveFunctor.forget_map CategoryTheory.AdditiveFunctor.forget_map

instance : Functor.Additive (AdditiveFunctor.forget C D) where map_add := rfl

instance (F : C ⥤+ D) : Functor.Additive F.1 :=
  F.2

end

section Exact

open CategoryTheory.Limits

variable (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
variable [Preadditive D] [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts C]

section

attribute [local instance] preservesBinaryBiproductsOfPreservesBinaryProducts

attribute [local instance] preservesBinaryBiproductsOfPreservesBinaryCoproducts

/-- Turn a left exact functor into an additive functor. -/
def AdditiveFunctor.ofLeftExact : (C ⥤ₗ D) ⥤ C ⥤+ D :=
  FullSubcategory.map fun F ⟨_⟩ =>
    Functor.additive_of_preservesBinaryBiproducts F
set_option linter.uppercaseLean3 false in
#align category_theory.AdditiveFunctor.of_left_exact CategoryTheory.AdditiveFunctor.ofLeftExact

instance : (AdditiveFunctor.ofLeftExact C D).Full := FullSubcategory.full_map _
instance : (AdditiveFunctor.ofLeftExact C D).Faithful := FullSubcategory.faithful_map _

/-- Turn a right exact functor into an additive functor. -/
def AdditiveFunctor.ofRightExact : (C ⥤ᵣ D) ⥤ C ⥤+ D :=
  FullSubcategory.map fun F ⟨_⟩ =>
    Functor.additive_of_preservesBinaryBiproducts F
set_option linter.uppercaseLean3 false in
#align category_theory.AdditiveFunctor.of_right_exact CategoryTheory.AdditiveFunctor.ofRightExact

instance : (AdditiveFunctor.ofRightExact C D).Full := FullSubcategory.full_map _
instance : (AdditiveFunctor.ofRightExact C D).Faithful := FullSubcategory.faithful_map _

/-- Turn an exact functor into an additive functor. -/
def AdditiveFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤+ D :=
  FullSubcategory.map fun F ⟨⟨_⟩, _⟩ =>
    Functor.additive_of_preservesBinaryBiproducts F
set_option linter.uppercaseLean3 false in
#align category_theory.AdditiveFunctor.of_exact CategoryTheory.AdditiveFunctor.ofExact

instance : (AdditiveFunctor.ofExact C D).Full := FullSubcategory.full_map _
instance : (AdditiveFunctor.ofExact C D).Faithful := FullSubcategory.faithful_map _

end

variable {C D}

@[simp]
theorem AdditiveFunctor.ofLeftExact_obj_fst (F : C ⥤ₗ D) :
    ((AdditiveFunctor.ofLeftExact C D).obj F).obj = F.obj :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.AdditiveFunctor.of_left_exact_obj_fst CategoryTheory.AdditiveFunctor.ofLeftExact_obj_fst

@[simp]
theorem AdditiveFunctor.ofRightExact_obj_fst (F : C ⥤ᵣ D) :
    ((AdditiveFunctor.ofRightExact C D).obj F).obj = F.obj :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.AdditiveFunctor.of_right_exact_obj_fst CategoryTheory.AdditiveFunctor.ofRightExact_obj_fst

@[simp]
theorem AdditiveFunctor.ofExact_obj_fst (F : C ⥤ₑ D) :
    ((AdditiveFunctor.ofExact C D).obj F).obj = F.obj :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.AdditiveFunctor.of_exact_obj_fst CategoryTheory.AdditiveFunctor.ofExact_obj_fst

@[simp]
theorem AdditiveFunctor.ofLeftExact_map {F G : C ⥤ₗ D} (α : F ⟶ G) :
    (AdditiveFunctor.ofLeftExact C D).map α = α :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Additive_Functor.of_left_exact_map CategoryTheory.AdditiveFunctor.ofLeftExact_map

@[simp]
theorem AdditiveFunctor.ofRightExact_map {F G : C ⥤ᵣ D} (α : F ⟶ G) :
    (AdditiveFunctor.ofRightExact C D).map α = α :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Additive_Functor.of_right_exact_map CategoryTheory.AdditiveFunctor.ofRightExact_map

@[simp]
theorem AdditiveFunctor.ofExact_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
    (AdditiveFunctor.ofExact C D).map α = α :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Additive_Functor.of_exact_map CategoryTheory.AdditiveFunctor.ofExact_map

end Exact

end Preadditive

end CategoryTheory
