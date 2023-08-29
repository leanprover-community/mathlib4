/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Types.Symmetric
import Mathlib.CategoryTheory.Monoidal.Types.Coyoneda
import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.Tactic.ApplyFun

#align_import category_theory.enriched.basic from "leanprover-community/mathlib"@"95a87616d63b3cb49d3fe678d416fbe9c4217bf4"

/-!
# Enriched categories

We set up the basic theory of `V`-enriched categories,
for `V` an arbitrary monoidal category.

We do not assume here that `V` is a concrete category,
so there does not need to be an "honest" underlying category!

Use `X ⟶[V] Y` to obtain the `V` object of morphisms from `X` to `Y`.

This file contains the definitions of `V`-enriched categories and
`V`-functors.

We don't yet define the `V`-object of natural transformations
between a pair of `V`-functors (this requires limits in `V`),
but we do provide a presheaf isomorphic to the Yoneda embedding of this object.

We verify that when `V = Type v`, all these notion reduce to the usual ones.
-/


universe w v u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Opposite

open MonoidalCategory

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

/-- A `V`-category is a category enriched in a monoidal category `V`.

Note that we do not assume that `V` is a concrete category,
so there may not be an "honest" underlying category at all!
-/
class EnrichedCategory (C : Type u₁) where
  Hom : C → C → V
  id (X : C) : 𝟙_ V ⟶ Hom X X
  comp (X Y Z : C) : Hom X Y ⊗ Hom Y Z ⟶ Hom X Z
  id_comp (X Y : C) : (λ_ (Hom X Y)).inv ≫ (id X ⊗ 𝟙 _) ≫ comp X X Y = 𝟙 _ := by aesop_cat
  comp_id (X Y : C) : (ρ_ (Hom X Y)).inv ≫ (𝟙 _ ⊗ id Y) ≫ comp X Y Y = 𝟙 _ := by aesop_cat
  assoc (W X Y Z : C) : (α_ _ _ _).inv ≫ (comp W X Y ⊗ 𝟙 _) ≫ comp W Y Z =
    (𝟙 _ ⊗ comp X Y Z) ≫ comp W X Z := by aesop_cat
#align category_theory.enriched_category CategoryTheory.EnrichedCategory

notation X " ⟶[" V "] " Y:10 => (EnrichedCategory.Hom X Y : V)

variable {C : Type u₁} [EnrichedCategory V C]

/-- The `𝟙_ V`-shaped generalized element giving the identity in a `V`-enriched category.
-/
def eId (X : C) : 𝟙_ V ⟶ X ⟶[V] X :=
  EnrichedCategory.id X
#align category_theory.e_id CategoryTheory.eId

/-- The composition `V`-morphism for a `V`-enriched category.
-/
def eComp (X Y Z : C) : ((X ⟶[V] Y) ⊗ Y ⟶[V] Z) ⟶ X ⟶[V] Z :=
  EnrichedCategory.comp X Y Z
#align category_theory.e_comp CategoryTheory.eComp

-- We don't just use `restate_axiom` here; that would leave `V` as an implicit argument.
@[reassoc (attr := simp)]
theorem e_id_comp (X Y : C) :
    (λ_ (X ⟶[V] Y)).inv ≫ (eId V X ⊗ 𝟙 _) ≫ eComp V X X Y = 𝟙 (X ⟶[V] Y) :=
  EnrichedCategory.id_comp X Y
#align category_theory.e_id_comp CategoryTheory.e_id_comp

@[reassoc (attr := simp)]
theorem e_comp_id (X Y : C) :
    (ρ_ (X ⟶[V] Y)).inv ≫ (𝟙 _ ⊗ eId V Y) ≫ eComp V X Y Y = 𝟙 (X ⟶[V] Y) :=
  EnrichedCategory.comp_id X Y
#align category_theory.e_comp_id CategoryTheory.e_comp_id

@[reassoc (attr := simp)]
theorem e_assoc (W X Y Z : C) :
    (α_ _ _ _).inv ≫ (eComp V W X Y ⊗ 𝟙 _) ≫ eComp V W Y Z =
      (𝟙 _ ⊗ eComp V X Y Z) ≫ eComp V W X Z :=
  EnrichedCategory.assoc W X Y Z
#align category_theory.e_assoc CategoryTheory.e_assoc

section

variable {V} {W : Type v} [Category.{w} W] [MonoidalCategory W]

-- porting note: removed `@[nolint hasNonemptyInstance]`
/-- A type synonym for `C`, which should come equipped with a `V`-enriched category structure.
In a moment we will equip this with the `W`-enriched category structure
obtained by applying the functor `F : LaxMonoidalFunctor V W` to each hom object.
-/
@[nolint unusedArguments]
def TransportEnrichment (_ : LaxMonoidalFunctor V W) (C : Type u₁) :=
  C
#align category_theory.transport_enrichment CategoryTheory.TransportEnrichment

instance (F : LaxMonoidalFunctor V W) : EnrichedCategory W (TransportEnrichment F C) where
  Hom := fun X Y : C => F.obj (X ⟶[V] Y)
  id := fun X : C => F.ε ≫ F.map (eId V X)
  comp := fun X Y Z : C => F.μ _ _ ≫ F.map (eComp V X Y Z)
  id_comp X Y := by
    rw [comp_tensor_id, Category.assoc, ← F.toFunctor.map_id, F.μ_natural_assoc,
      F.toFunctor.map_id, F.left_unitality_inv_assoc, ← F.toFunctor.map_comp, ←
      F.toFunctor.map_comp, e_id_comp, F.toFunctor.map_id]
  comp_id X Y := by
    rw [id_tensor_comp, Category.assoc, ← F.toFunctor.map_id, F.μ_natural_assoc,
      F.toFunctor.map_id, F.right_unitality_inv_assoc, ← F.toFunctor.map_comp, ←
      F.toFunctor.map_comp, e_comp_id, F.toFunctor.map_id]
  assoc P Q R S := by
    rw [comp_tensor_id, Category.assoc, ← F.toFunctor.map_id, F.μ_natural_assoc,
      F.toFunctor.map_id, ← F.associativity_inv_assoc, ← F.toFunctor.map_comp, ←
      F.toFunctor.map_comp, e_assoc, id_tensor_comp, Category.assoc, ← F.toFunctor.map_id,
      F.μ_natural_assoc, F.toFunctor.map_comp]

end

/-- Construct an honest category from a `Type v`-enriched category.
-/
def categoryOfEnrichedCategoryType (C : Type u₁) [𝒞 : EnrichedCategory (Type v) C] : Category.{v} C
    where
  Hom := 𝒞.Hom
  id X := eId (Type v) X PUnit.unit
  comp f g := eComp (Type v) _ _ _ ⟨f, g⟩
  id_comp f := congr_fun (e_id_comp (Type v) _ _) f
  comp_id f := congr_fun (e_comp_id (Type v) _ _) f
  assoc f g h := (congr_fun (e_assoc (Type v) _ _ _ _) ⟨f, g, h⟩ : _)
#align category_theory.category_of_enriched_category_Type CategoryTheory.categoryOfEnrichedCategoryType

/-- Construct a `Type v`-enriched category from an honest category.
-/
def enrichedCategoryTypeOfCategory (C : Type u₁) [𝒞 : Category.{v} C] : EnrichedCategory (Type v) C
    where
  Hom := 𝒞.Hom
  id X _ := 𝟙 X
  comp X Y Z p := p.1 ≫ p.2
  id_comp X Y := by ext; simp
                    -- ⊢ ((λ_ (X ⟶ Y)).inv ≫ ((fun X x => 𝟙 X) X ⊗ 𝟙 (X ⟶ Y)) ≫ (fun X Y Z p => p.fst …
                         -- 🎉 no goals
  comp_id X Y := by ext; simp
                    -- ⊢ ((ρ_ (X ⟶ Y)).inv ≫ (𝟙 (X ⟶ Y) ⊗ (fun X x => 𝟙 X) Y) ≫ (fun X Y Z p => p.fst …
                         -- 🎉 no goals
  assoc W X Y Z := by ext ⟨f, g, h⟩; simp
                      -- ⊢ ((α_ (W ⟶ X) (X ⟶ Y) (Y ⟶ Z)).inv ≫ ((fun X Y Z p => p.fst ≫ p.snd) W X Y ⊗  …
                                     -- 🎉 no goals
#align category_theory.enriched_category_Type_of_category CategoryTheory.enrichedCategoryTypeOfCategory

/-- We verify that an enriched category in `Type u` is just the same thing as an honest category.
-/
def enrichedCategoryTypeEquivCategory (C : Type u₁) : EnrichedCategory (Type v) C ≃ Category.{v} C
    where
  toFun _ := categoryOfEnrichedCategoryType C
  invFun _ := enrichedCategoryTypeOfCategory C
  left_inv _ := rfl
  right_inv _ := rfl
#align category_theory.enriched_category_Type_equiv_category CategoryTheory.enrichedCategoryTypeEquivCategory

section

variable {W : Type (v + 1)} [Category.{v} W] [MonoidalCategory W] [EnrichedCategory W C]

-- porting note: removed `@[nolint has_nonempty_instance]`
/-- A type synonym for `C`, which should come equipped with a `V`-enriched category structure.
In a moment we will equip this with the (honest) category structure
so that `X ⟶ Y` is `(𝟙_ W) ⟶ (X ⟶[W] Y)`.

We obtain this category by
transporting the enrichment in `V` along the lax monoidal functor `coyonedaTensorUnit`,
then using the equivalence of `Type`-enriched categories with honest categories.

This is sometimes called the "underlying" category of an enriched category,
although some care is needed as the functor `coyonedaTensorUnit`,
which always exists, does not necessarily coincide with
"the forgetful functor" from `V` to `Type`, if such exists.
When `V` is any of `Type`, `Top`, `AddCommGroup`, or `Module R`,
`coyonedaTensorUnit` is just the usual forgetful functor, however.
For `V = Algebra R`, the usual forgetful functor is coyoneda of `R[X]`, not of `R`.
(Perhaps we should have a typeclass for this situation: `ConcreteMonoidal`?)
-/
@[nolint unusedArguments]
def ForgetEnrichment (W : Type (v + 1)) [Category.{v} W] [MonoidalCategory W] (C : Type u₁)
    [EnrichedCategory W C] :=
  C
#align category_theory.forget_enrichment CategoryTheory.ForgetEnrichment

variable (W)

/-- Typecheck an object of `C` as an object of `ForgetEnrichment W C`. -/
def ForgetEnrichment.of (X : C) : ForgetEnrichment W C :=
  X
#align category_theory.forget_enrichment.of CategoryTheory.ForgetEnrichment.of

/-- Typecheck an object of `ForgetEnrichment W C` as an object of `C`. -/
def ForgetEnrichment.to (X : ForgetEnrichment W C) : C :=
  X
#align category_theory.forget_enrichment.to CategoryTheory.ForgetEnrichment.to

@[simp]
theorem ForgetEnrichment.to_of (X : C) : ForgetEnrichment.to W (ForgetEnrichment.of W X) = X :=
  rfl
#align category_theory.forget_enrichment.to_of CategoryTheory.ForgetEnrichment.to_of

@[simp]
theorem ForgetEnrichment.of_to (X : ForgetEnrichment W C) :
    ForgetEnrichment.of W (ForgetEnrichment.to W X) = X :=
  rfl
#align category_theory.forget_enrichment.of_to CategoryTheory.ForgetEnrichment.of_to

instance categoryForgetEnrichment : Category (ForgetEnrichment W C) := by
  let I : EnrichedCategory (Type v) (TransportEnrichment (coyonedaTensorUnit W) C) :=
    inferInstance
  exact enrichedCategoryTypeEquivCategory C I
  -- 🎉 no goals
#align category_theory.category_forget_enrichment CategoryTheory.categoryForgetEnrichment

/-- We verify that the morphism types in `ForgetEnrichment W C` are `(𝟙_ W) ⟶ (X ⟶[W] Y)`.
-/
example (X Y : ForgetEnrichment W C) :
    (X ⟶ Y) = (𝟙_ W ⟶ ForgetEnrichment.to W X ⟶[W] ForgetEnrichment.to W Y) :=
  rfl

/-- Typecheck a `(𝟙_ W)`-shaped `W`-morphism as a morphism in `ForgetEnrichment W C`. -/
def ForgetEnrichment.homOf {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y) :
    ForgetEnrichment.of W X ⟶ ForgetEnrichment.of W Y :=
  f
#align category_theory.forget_enrichment.hom_of CategoryTheory.ForgetEnrichment.homOf

/-- Typecheck a morphism in `ForgetEnrichment W C` as a `(𝟙_ W)`-shaped `W`-morphism. -/
def ForgetEnrichment.homTo {X Y : ForgetEnrichment W C} (f : X ⟶ Y) :
    𝟙_ W ⟶ ForgetEnrichment.to W X ⟶[W] ForgetEnrichment.to W Y :=
  f
#align category_theory.forget_enrichment.hom_to CategoryTheory.ForgetEnrichment.homTo

@[simp]
theorem ForgetEnrichment.homTo_homOf {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y) :
    ForgetEnrichment.homTo W (ForgetEnrichment.homOf W f) = f :=
  rfl
#align category_theory.forget_enrichment.hom_to_hom_of CategoryTheory.ForgetEnrichment.homTo_homOf

@[simp]
theorem ForgetEnrichment.homOf_homTo {X Y : ForgetEnrichment W C} (f : X ⟶ Y) :
    ForgetEnrichment.homOf W (ForgetEnrichment.homTo W f) = f :=
  rfl
#align category_theory.forget_enrichment.hom_of_hom_to CategoryTheory.ForgetEnrichment.homOf_homTo

/-- The identity in the "underlying" category of an enriched category. -/
@[simp]
theorem forgetEnrichment_id (X : ForgetEnrichment W C) :
    ForgetEnrichment.homTo W (𝟙 X) = eId W (ForgetEnrichment.to W X : C) :=
  Category.id_comp _
#align category_theory.forget_enrichment_id CategoryTheory.forgetEnrichment_id

@[simp]
theorem forgetEnrichment_id' (X : C) :
    ForgetEnrichment.homOf W (eId W X) = 𝟙 (ForgetEnrichment.of W X : C) :=
  (forgetEnrichment_id W (ForgetEnrichment.of W X)).symm
#align category_theory.forget_enrichment_id' CategoryTheory.forgetEnrichment_id'

/-- Composition in the "underlying" category of an enriched category. -/
@[simp]
theorem forgetEnrichment_comp {X Y Z : ForgetEnrichment W C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ForgetEnrichment.homTo W (f ≫ g) =
      ((λ_ (𝟙_ W)).inv ≫ (ForgetEnrichment.homTo W f ⊗ ForgetEnrichment.homTo W g)) ≫
        eComp W _ _ _ :=
  rfl
#align category_theory.forget_enrichment_comp CategoryTheory.forgetEnrichment_comp

end

/-- A `V`-functor `F` between `V`-enriched categories
has a `V`-morphism from `X ⟶[V] Y` to `F.obj X ⟶[V] F.obj Y`,
satisfying the usual axioms.
-/
structure EnrichedFunctor (C : Type u₁) [EnrichedCategory V C] (D : Type u₂)
    [EnrichedCategory V D] where
  obj : C → D
  map : ∀ X Y : C, (X ⟶[V] Y) ⟶ obj X ⟶[V] obj Y
  map_id : ∀ X : C, eId V X ≫ map X X = eId V (obj X) := by aesop_cat
  map_comp :
    ∀ X Y Z : C,
      eComp V X Y Z ≫ map X Z = (map X Y ⊗ map Y Z) ≫ eComp V (obj X) (obj Y) (obj Z) := by
    aesop_cat
#align category_theory.enriched_functor CategoryTheory.EnrichedFunctor

attribute [reassoc (attr := simp)] EnrichedFunctor.map_id

attribute [reassoc (attr := simp)] EnrichedFunctor.map_comp

/-- The identity enriched functor. -/
@[simps]
def EnrichedFunctor.id (C : Type u₁) [EnrichedCategory V C] : EnrichedFunctor V C C where
  obj X := X
  map X Y := 𝟙 _
#align category_theory.enriched_functor.id CategoryTheory.EnrichedFunctor.id

instance : Inhabited (EnrichedFunctor V C C) :=
  ⟨EnrichedFunctor.id V C⟩

/-- Composition of enriched functors. -/
@[simps]
def EnrichedFunctor.comp {C : Type u₁} {D : Type u₂} {E : Type u₃} [EnrichedCategory V C]
    [EnrichedCategory V D] [EnrichedCategory V E] (F : EnrichedFunctor V C D)
    (G : EnrichedFunctor V D E) : EnrichedFunctor V C E where
  obj X := G.obj (F.obj X)
  map X Y := F.map _ _ ≫ G.map _ _
#align category_theory.enriched_functor.comp CategoryTheory.EnrichedFunctor.comp

section

variable {W : Type (v + 1)} [Category.{v} W] [MonoidalCategory W]

/-- An enriched functor induces an honest functor of the underlying categories,
by mapping the `(𝟙_ W)`-shaped morphisms.
-/
def EnrichedFunctor.forget {C : Type u₁} {D : Type u₂} [EnrichedCategory W C] [EnrichedCategory W D]
    (F : EnrichedFunctor W C D) : ForgetEnrichment W C ⥤ ForgetEnrichment W D where
  obj X := ForgetEnrichment.of W (F.obj (ForgetEnrichment.to W X))
  map f :=
    ForgetEnrichment.homOf W
      (ForgetEnrichment.homTo W f ≫ F.map (ForgetEnrichment.to W _) (ForgetEnrichment.to W _))
  map_comp f g := by
    dsimp
    -- ⊢ ForgetEnrichment.homOf W ((((λ_ (𝟙_ W)).inv ≫ (ForgetEnrichment.homTo W f ⊗  …
    apply_fun ForgetEnrichment.homTo W
    -- ⊢ ForgetEnrichment.homTo W (ForgetEnrichment.homOf W ((((λ_ (𝟙_ W)).inv ≫ (For …
    · simp only [Iso.cancel_iso_inv_left, Category.assoc, tensor_comp,
        ForgetEnrichment.homTo_homOf, EnrichedFunctor.map_comp, forgetEnrichment_comp]
      rfl
      -- 🎉 no goals
    · intro f g w; apply_fun ForgetEnrichment.homOf W at w; simpa using w
      -- ⊢ f = g
                   -- ⊢ f = g
                                                            -- 🎉 no goals
#align category_theory.enriched_functor.forget CategoryTheory.EnrichedFunctor.forget

end

section

variable {V}

variable {D : Type u₂} [EnrichedCategory V D]

/-!
We now turn to natural transformations between `V`-functors.

The mostly commonly encountered definition of an enriched natural transformation
is a collection of morphisms
```
(𝟙_ W) ⟶ (F.obj X ⟶[V] G.obj X)
```
satisfying an appropriate analogue of the naturality square.
(c.f. https://ncatlab.org/nlab/show/enriched+natural+transformation)

This is the same thing as a natural transformation `F.forget ⟶ G.forget`.

We formalize this as `EnrichedNatTrans F G`, which is a `Type`.

However, there's also something much nicer: with appropriate additional hypotheses,
there is a `V`-object `EnrichedNatTransObj F G` which contains more information,
and from which one can recover `EnrichedNatTrans F G ≃ (𝟙_ V) ⟶ EnrichedNatTransObj F G`.

Using these as the hom-objects, we can build a `V`-enriched category
with objects the `V`-functors.

For `EnrichedNatTransObj` to exist, it suffices to have `V` braided and complete.

Before assuming `V` is complete, we assume it is braided and
define a presheaf `enrichedNatTransYoneda F G`
which is isomorphic to the Yoneda embedding of `EnrichedNatTransObj F G`
whether or not that object actually exists.

This presheaf has components `(enrichedNatTransYoneda F G).obj A`
what we call the `A`-graded enriched natural transformations,
which are collections of morphisms
```
A ⟶ (F.obj X ⟶[V] G.obj X)
```
satisfying a similar analogue of the naturality square,
this time incorporating a half-braiding on `A`.

(We actually define `EnrichedNatTrans F G`
as the special case `A := 𝟙_ V` with the trivial half-braiding,
and when defining `enrichedNatTransYoneda F G` we use the half-braidings
coming from the ambient braiding on `V`.)
-/


-- porting note: removed `@[nolint has_nonempty_instance]`
/-- The type of `A`-graded natural transformations between `V`-functors `F` and `G`.
This is the type of morphisms in `V` from `A` to the `V`-object of natural transformations.
-/
@[ext]
structure GradedNatTrans (A : Center V) (F G : EnrichedFunctor V C D) where
  app : ∀ X : C, A.1 ⟶ F.obj X ⟶[V] G.obj X
  naturality :
    ∀ X Y : C,
      (A.2.β (X ⟶[V] Y)).hom ≫ (F.map X Y ⊗ app Y) ≫ eComp V _ _ _ =
        (app X ⊗ G.map X Y) ≫ eComp V _ _ _
#align category_theory.graded_nat_trans CategoryTheory.GradedNatTrans

variable [BraidedCategory V]

open BraidedCategory

/-- A presheaf isomorphic to the Yoneda embedding of
the `V`-object of natural transformations from `F` to `G`.
-/
@[simps]
def enrichedNatTransYoneda (F G : EnrichedFunctor V C D) : Vᵒᵖ ⥤ Type max u₁ w where
  obj A := GradedNatTrans ((Center.ofBraided V).obj (unop A)) F G
  map f σ :=
    { app := fun X => f.unop ≫ σ.app X
      naturality := fun X Y => by
        have p := σ.naturality X Y
        -- ⊢ (HalfBraiding.β ((Center.ofBraided V).toLaxMonoidalFunctor.toFunctor.obj Y✝. …
        dsimp at p ⊢
        -- ⊢ (β_ Y✝.unop (EnrichedCategory.Hom X Y)).hom ≫ (EnrichedFunctor.map F X Y ⊗ f …
        rw [← id_tensor_comp_tensor_id (f.unop ≫ σ.app Y) _, id_tensor_comp, Category.assoc,
          Category.assoc, ← braiding_naturality_assoc, id_tensor_comp_tensor_id_assoc, p, ←
          tensor_comp_assoc, Category.id_comp] }
#align category_theory.enriched_nat_trans_yoneda CategoryTheory.enrichedNatTransYoneda

-- TODO assuming `[HasLimits C]` construct the actual object of natural transformations
-- and show that the functor category is `V`-enriched.
end

section

attribute [local instance] categoryOfEnrichedCategoryType

/-- We verify that an enriched functor between `Type v` enriched categories
is just the same thing as an honest functor.
-/
@[simps]
def enrichedFunctorTypeEquivFunctor {C : Type u₁} [𝒞 : EnrichedCategory (Type v) C] {D : Type u₂}
    [𝒟 : EnrichedCategory (Type v) D] : EnrichedFunctor (Type v) C D ≃ C ⥤ D where
  toFun F :=
    { obj := fun X => F.obj X
      map := fun f => F.map _ _ f
      map_id := fun X => congr_fun (F.map_id X) PUnit.unit
      map_comp := fun f g => congr_fun (F.map_comp _ _ _) ⟨f, g⟩ }
  invFun F :=
    { obj := fun X => F.obj X
      map := fun X Y f => F.map f
      map_id := fun X => by ext ⟨⟩; exact F.map_id X
                            -- ⊢ (eId (Type v) X ≫ (fun X Y f => F.map f) X X) PUnit.unit = eId (Type v) ((fu …
                                    -- 🎉 no goals
      map_comp := fun X Y Z => by ext ⟨f, g⟩; exact F.map_comp f g }
                                  -- ⊢ (eComp (Type v) X Y Z ≫ (fun X Y f => F.map f) X Z) (f, g) = (((fun X Y f => …
                                              -- 🎉 no goals
  left_inv _ := rfl
  right_inv _ := rfl
#align category_theory.enriched_functor_Type_equiv_functor CategoryTheory.enrichedFunctorTypeEquivFunctor

/-- We verify that the presheaf representing natural transformations
between `Type v`-enriched functors is actually represented by
the usual type of natural transformations!
-/
def enrichedNatTransYonedaTypeIsoYonedaNatTrans {C : Type v} [EnrichedCategory (Type v) C]
    {D : Type v} [EnrichedCategory (Type v) D] (F G : EnrichedFunctor (Type v) C D) :
    enrichedNatTransYoneda F G ≅
      yoneda.obj (enrichedFunctorTypeEquivFunctor F ⟶ enrichedFunctorTypeEquivFunctor G) :=
  NatIso.ofComponents
    (fun α =>
      { hom := fun σ x =>
          { app := fun X => σ.app X x
            naturality := fun X Y f => congr_fun (σ.naturality X Y) ⟨x, f⟩ }
        inv := fun σ =>
          { app := fun X x => (σ x).app X
            naturality := fun X Y => by ext ⟨x, f⟩; exact (σ x).naturality f } })
                                        -- ⊢ ((HalfBraiding.β ((Center.ofBraided (Type v)).toLaxMonoidalFunctor.toFunctor …
                                                    -- 🎉 no goals
    (by aesop_cat)
        -- 🎉 no goals
#align category_theory.enriched_nat_trans_yoneda_Type_iso_yoneda_nat_trans CategoryTheory.enrichedNatTransYonedaTypeIsoYonedaNatTrans

end

end CategoryTheory
