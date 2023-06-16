/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.enriched.basic
! leanprover-community/mathlib commit 95a87616d63b3cb49d3fe678d416fbe9c4217bf4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Types.Symmetric
import Mathbin.CategoryTheory.Monoidal.Types.Coyoneda
import Mathbin.CategoryTheory.Monoidal.Center
import Mathbin.Tactic.ApplyFun

/-!
# Enriched categories

We set up the basic theory of `V`-enriched categories,
for `V` an arbitrary monoidal category.

We do not assume here that `V` is a concrete category,
so there does not need to be a "honest" underlying category!

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

/- ./././Mathport/Syntax/Translate/Command.lean:406:24: unsupported: (notation) in structure -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⟶[] » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⟶[] » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⟶[] » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⟶[] » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⟶[] » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr ⟶[] » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A `V`-category is a category enriched in a monoidal category `V`.

Note that we do not assume that `V` is a concrete category,
so there may not be an "honest" underlying category at all!
-/
class EnrichedCategory (C : Type u₁) where
  Hom : C → C → V
  id : ∀ X, 𝟙_ V ⟶ «expr ⟶[] » X X
  comp : ∀ X Y Z, «expr ⟶[] » X Y ⊗ «expr ⟶[] » Y Z ⟶ «expr ⟶[] » X Z
  id_comp : ∀ X Y, (λ_ («expr ⟶[] » X Y)).inv ≫ (id X ⊗ 𝟙 _) ≫ comp X X Y = 𝟙 _ := by obviously
  comp_id : ∀ X Y, (ρ_ («expr ⟶[] » X Y)).inv ≫ (𝟙 _ ⊗ id Y) ≫ comp X Y Y = 𝟙 _ := by obviously
  and_assoc :
    ∀ W X Y Z,
      (α_ _ _ _).inv ≫ (comp W X Y ⊗ 𝟙 _) ≫ comp W Y Z = (𝟙 _ ⊗ comp X Y Z) ≫ comp W X Z := by
    obviously
#align category_theory.enriched_category CategoryTheory.EnrichedCategory

notation X " ⟶[" V "] " Y:10 => (EnrichedCategory.hom X Y : V)

variable (V) {C : Type u₁} [EnrichedCategory V C]

/-- The `𝟙_ V`-shaped generalized element giving the identity in a `V`-enriched category.
-/
def eId (X : C) : 𝟙_ V ⟶ X ⟶[V] X :=
  EnrichedCategory.id X
#align category_theory.e_id CategoryTheory.eId

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The composition `V`-morphism for a `V`-enriched category.
-/
def eComp (X Y Z : C) : ((X ⟶[V] Y) ⊗ Y ⟶[V] Z) ⟶ X ⟶[V] Z :=
  EnrichedCategory.comp X Y Z
#align category_theory.e_comp CategoryTheory.eComp

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- We don't just use `restate_axiom` here; that would leave `V` as an implicit argument.
@[simp, reassoc]
theorem eId_comp (X Y : C) : (λ_ (X ⟶[V] Y)).inv ≫ (eId V X ⊗ 𝟙 _) ≫ eComp V X X Y = 𝟙 (X ⟶[V] Y) :=
  EnrichedCategory.id_comp X Y
#align category_theory.e_id_comp CategoryTheory.eId_comp

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, reassoc]
theorem eComp_id (X Y : C) : (ρ_ (X ⟶[V] Y)).inv ≫ (𝟙 _ ⊗ eId V Y) ≫ eComp V X Y Y = 𝟙 (X ⟶[V] Y) :=
  EnrichedCategory.comp_id X Y
#align category_theory.e_comp_id CategoryTheory.eComp_id

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, reassoc]
theorem e_assoc (W X Y Z : C) :
    (α_ _ _ _).inv ≫ (eComp V W X Y ⊗ 𝟙 _) ≫ eComp V W Y Z =
      (𝟙 _ ⊗ eComp V X Y Z) ≫ eComp V W X Z :=
  EnrichedCategory.assoc W X Y Z
#align category_theory.e_assoc CategoryTheory.e_assoc

section

variable {V} {W : Type v} [Category.{w} W] [MonoidalCategory W]

/-- A type synonym for `C`, which should come equipped with a `V`-enriched category structure.
In a moment we will equip this with the `W`-enriched category structure
obtained by applying the functor `F : lax_monoidal_functor V W` to each hom object.
-/
@[nolint has_nonempty_instance unused_arguments]
def TransportEnrichment (F : LaxMonoidalFunctor V W) (C : Type u₁) :=
  C
#align category_theory.transport_enrichment CategoryTheory.TransportEnrichment

instance (F : LaxMonoidalFunctor V W) : EnrichedCategory W (TransportEnrichment F C)
    where
  Hom := fun X Y : C => F.obj (X ⟶[V] Y)
  id := fun X : C => F.ε ≫ F.map (eId V X)
  comp := fun X Y Z : C => F.μ _ _ ≫ F.map (eComp V X Y Z)
  id_comp X Y := by
    rw [comp_tensor_id, category.assoc, ← F.to_functor.map_id, F.μ_natural_assoc,
      F.to_functor.map_id, F.left_unitality_inv_assoc, ← F.to_functor.map_comp, ←
      F.to_functor.map_comp, e_id_comp, F.to_functor.map_id]
  comp_id X Y := by
    rw [id_tensor_comp, category.assoc, ← F.to_functor.map_id, F.μ_natural_assoc,
      F.to_functor.map_id, F.right_unitality_inv_assoc, ← F.to_functor.map_comp, ←
      F.to_functor.map_comp, e_comp_id, F.to_functor.map_id]
  and_assoc P Q R S := by
    rw [comp_tensor_id, category.assoc, ← F.to_functor.map_id, F.μ_natural_assoc,
      F.to_functor.map_id, ← F.associativity_inv_assoc, ← F.to_functor.map_comp, ←
      F.to_functor.map_comp, e_assoc, id_tensor_comp, category.assoc, ← F.to_functor.map_id,
      F.μ_natural_assoc, F.to_functor.map_comp]

end

/-- Construct an honest category from a `Type v`-enriched category.
-/
def categoryOfEnrichedCategoryType (C : Type u₁) [𝒞 : EnrichedCategory (Type v) C] : Category.{v} C
    where
  Hom := 𝒞.Hom
  id X := eId (Type v) X PUnit.unit
  comp X Y Z f g := eComp (Type v) X Y Z ⟨f, g⟩
  id_comp' X Y f := congr_fun (eId_comp (Type v) X Y) f
  comp_id' X Y f := congr_fun (eComp_id (Type v) X Y) f
  assoc' W X Y Z f g h := (congr_fun (e_assoc (Type v) W X Y Z) ⟨f, g, h⟩ : _)
#align category_theory.category_of_enriched_category_Type CategoryTheory.categoryOfEnrichedCategoryType

/-- Construct a `Type v`-enriched category from an honest category.
-/
def enrichedCategoryTypeOfCategory (C : Type u₁) [𝒞 : Category.{v} C] : EnrichedCategory (Type v) C
    where
  Hom := 𝒞.Hom
  id X p := 𝟙 X
  comp X Y Z p := p.1 ≫ p.2
  id_comp X Y := by ext; simp
  comp_id X Y := by ext; simp
  and_assoc W X Y Z := by ext ⟨f, g, h⟩; simp
#align category_theory.enriched_category_Type_of_category CategoryTheory.enrichedCategoryTypeOfCategory

/-- We verify that an enriched category in `Type u` is just the same thing as an honest category.
-/
def enrichedCategoryTypeEquivCategory (C : Type u₁) : EnrichedCategory (Type v) C ≃ Category.{v} C
    where
  toFun 𝒞 := category_of_enriched_category_Type C
  invFun 𝒞 := enriched_category_Type_of_category C
  left_inv 𝒞 := by
    cases 𝒞
    dsimp [enriched_category_Type_of_category]
    congr
    · ext (X⟨⟩); rfl
    · ext (X Y Z⟨f, g⟩); rfl
  right_inv 𝒞 := by rcases 𝒞 with @⟨@⟨⟨⟩⟩⟩; dsimp; congr
#align category_theory.enriched_category_Type_equiv_category CategoryTheory.enrichedCategoryTypeEquivCategory

section

variable {W : Type (v + 1)} [Category.{v} W] [MonoidalCategory W] [EnrichedCategory W C]

/-- A type synonym for `C`, which should come equipped with a `V`-enriched category structure.
In a moment we will equip this with the (honest) category structure
so that `X ⟶ Y` is `(𝟙_ W) ⟶ (X ⟶[W] Y)`.

We obtain this category by
transporting the enrichment in `V` along the lax monoidal functor `coyoneda_tensor_unit`,
then using the equivalence of `Type`-enriched categories with honest categories.

This is sometimes called the "underlying" category of an enriched category,
although some care is needed as the functor `coyoneda_tensor_unit`,
which always exists, does not necessarily coincide with
"the forgetful functor" from `V` to `Type`, if such exists.
When `V` is any of `Type`, `Top`, `AddCommGroup`, or `Module R`,
`coyoneda_tensor_unit` is just the usual forgetful functor, however.
For `V = Algebra R`, the usual forgetful functor is coyoneda of `R[X]`, not of `R`.
(Perhaps we should have a typeclass for this situation: `concrete_monoidal`?)
-/
@[nolint has_nonempty_instance unused_arguments]
def ForgetEnrichment (W : Type (v + 1)) [Category.{v} W] [MonoidalCategory W] (C : Type u₁)
    [EnrichedCategory W C] :=
  C
#align category_theory.forget_enrichment CategoryTheory.ForgetEnrichment

variable (W)

/-- Typecheck an object of `C` as an object of `forget_enrichment W C`. -/
def ForgetEnrichment.of (X : C) : ForgetEnrichment W C :=
  X
#align category_theory.forget_enrichment.of CategoryTheory.ForgetEnrichment.of

/-- Typecheck an object of `forget_enrichment W C` as an object of `C`. -/
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

instance categoryForgetEnrichment : Category (ForgetEnrichment W C) :=
  by
  let I : enriched_category (Type v) (transport_enrichment (coyoneda_tensor_unit W) C) :=
    inferInstance
  exact enriched_category_Type_equiv_category C I
#align category_theory.category_forget_enrichment CategoryTheory.categoryForgetEnrichment

/-- We verify that the morphism types in `forget_enrichment W C` are `(𝟙_ W) ⟶ (X ⟶[W] Y)`.
-/
example (X Y : ForgetEnrichment W C) :
    (X ⟶ Y) = (𝟙_ W ⟶ ForgetEnrichment.to W X ⟶[W] ForgetEnrichment.to W Y) :=
  rfl

/-- Typecheck a `(𝟙_ W)`-shaped `W`-morphism as a morphism in `forget_enrichment W C`. -/
def ForgetEnrichment.homOf {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y) :
    ForgetEnrichment.of W X ⟶ ForgetEnrichment.of W Y :=
  f
#align category_theory.forget_enrichment.hom_of CategoryTheory.ForgetEnrichment.homOf

/-- Typecheck a morphism in `forget_enrichment W C` as a `(𝟙_ W)`-shaped `W`-morphism. -/
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

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Composition in the "underlying" category of an enriched category. -/
@[simp]
theorem forgetEnrichment_comp {X Y Z : ForgetEnrichment W C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ForgetEnrichment.homTo W (f ≫ g) =
      ((λ_ (𝟙_ W)).inv ≫ (ForgetEnrichment.homTo W f ⊗ ForgetEnrichment.homTo W g)) ≫
        eComp W _ _ _ :=
  rfl
#align category_theory.forget_enrichment_comp CategoryTheory.forgetEnrichment_comp

end

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A `V`-functor `F` between `V`-enriched categories
has a `V`-morphism from `X ⟶[V] Y` to `F.obj X ⟶[V] F.obj Y`,
satisfying the usual axioms.
-/
structure EnrichedFunctor (C : Type u₁) [EnrichedCategory V C] (D : Type u₂)
    [EnrichedCategory V D] where
  obj : C → D
  map : ∀ X Y : C, (X ⟶[V] Y) ⟶ obj X ⟶[V] obj Y
  map_id' : ∀ X : C, eId V X ≫ map X X = eId V (obj X) := by obviously
  map_comp' :
    ∀ X Y Z : C,
      eComp V X Y Z ≫ map X Z = (map X Y ⊗ map Y Z) ≫ eComp V (obj X) (obj Y) (obj Z) := by
    obviously
#align category_theory.enriched_functor CategoryTheory.EnrichedFunctor

restate_axiom enriched_functor.map_id'

restate_axiom enriched_functor.map_comp'

attribute [simp, reassoc] enriched_functor.map_id

attribute [simp, reassoc] enriched_functor.map_comp

/-- The identity enriched functor. -/
@[simps]
def EnrichedFunctor.id (C : Type u₁) [EnrichedCategory V C] : EnrichedFunctor V C C
    where
  obj X := X
  map X Y := 𝟙 _
#align category_theory.enriched_functor.id CategoryTheory.EnrichedFunctor.id

instance : Inhabited (EnrichedFunctor V C C) :=
  ⟨EnrichedFunctor.id V C⟩

/-- Composition of enriched functors. -/
@[simps]
def EnrichedFunctor.comp {C : Type u₁} {D : Type u₂} {E : Type u₃} [EnrichedCategory V C]
    [EnrichedCategory V D] [EnrichedCategory V E] (F : EnrichedFunctor V C D)
    (G : EnrichedFunctor V D E) : EnrichedFunctor V C E
    where
  obj X := G.obj (F.obj X)
  map X Y := F.map _ _ ≫ G.map _ _
#align category_theory.enriched_functor.comp CategoryTheory.EnrichedFunctor.comp

section

variable {W : Type (v + 1)} [Category.{v} W] [MonoidalCategory W]

/-- An enriched functor induces an honest functor of the underlying categories,
by mapping the `(𝟙_ W)`-shaped morphisms.
-/
def EnrichedFunctor.forget {C : Type u₁} {D : Type u₂} [EnrichedCategory W C] [EnrichedCategory W D]
    (F : EnrichedFunctor W C D) : ForgetEnrichment W C ⥤ ForgetEnrichment W D
    where
  obj X := ForgetEnrichment.of W (F.obj (ForgetEnrichment.to W X))
  map X Y f :=
    ForgetEnrichment.homOf W
      (ForgetEnrichment.homTo W f ≫ F.map (ForgetEnrichment.to W X) (ForgetEnrichment.to W Y))
  map_comp' X Y Z f g := by
    dsimp
    apply_fun forget_enrichment.hom_to W
    · simp only [iso.cancel_iso_inv_left, category.assoc, tensor_comp,
        forget_enrichment.hom_to_hom_of, enriched_functor.map_comp, forget_enrichment_comp]
      rfl
    · intro f g w; apply_fun forget_enrichment.hom_of W at w ; simpa using w
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

We formalize this as `enriched_nat_trans F G`, which is a `Type`.

However, there's also something much nicer: with appropriate additional hypotheses,
there is a `V`-object `enriched_nat_trans_obj F G` which contains more information,
and from which one can recover `enriched_nat_trans F G ≃ (𝟙_ V) ⟶ enriched_nat_trans_obj F G`.

Using these as the hom-objects, we can build a `V`-enriched category
with objects the `V`-functors.

For `enriched_nat_trans_obj` to exist, it suffices to have `V` braided and complete.

Before assuming `V` is complete, we assume it is braided and
define a presheaf `enriched_nat_trans_yoneda F G`
which is isomorphic to the Yoneda embedding of `enriched_nat_trans_obj F G`
whether or not that object actually exists.

This presheaf has components `(enriched_nat_trans_yoneda F G).obj A`
what we call the `A`-graded enriched natural transformations,
which are collections of morphisms
```
A ⟶ (F.obj X ⟶[V] G.obj X)
```
satisfying a similar analogue of the naturality square,
this time incorporating a half-braiding on `A`.

(We actually define `enriched_nat_trans F G`
as the special case `A := 𝟙_ V` with the trivial half-braiding,
and when defining `enriched_nat_trans_yoneda F G` we use the half-braidings
coming from the ambient braiding on `V`.)
-/


/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The type of `A`-graded natural transformations between `V`-functors `F` and `G`.
This is the type of morphisms in `V` from `A` to the `V`-object of natural transformations.
-/
@[ext, nolint has_nonempty_instance]
structure GradedNatTrans (A : Center V) (F G : EnrichedFunctor V C D) where
  app : ∀ X : C, A.1 ⟶ F.obj X ⟶[V] G.obj X
  naturality :
    ∀ X Y : C,
      (A.2.β (X ⟶[V] Y)).Hom ≫ (F.map X Y ⊗ app Y) ≫ eComp V _ _ _ =
        (app X ⊗ G.map X Y) ≫ eComp V _ _ _
#align category_theory.graded_nat_trans CategoryTheory.GradedNatTrans

variable [BraidedCategory V]

open BraidedCategory

/-- A presheaf isomorphic to the Yoneda embedding of
the `V`-object of natural transformations from `F` to `G`.
-/
@[simps]
def enrichedNatTransYoneda (F G : EnrichedFunctor V C D) : Vᵒᵖ ⥤ Type max u₁ w
    where
  obj A := GradedNatTrans ((Center.ofBraided V).obj (unop A)) F G
  map A A' f σ :=
    { app := fun X => f.unop ≫ σ.app X
      naturality := fun X Y => by
        have p := σ.naturality X Y
        dsimp at p ⊢
        rw [← id_tensor_comp_tensor_id (f.unop ≫ σ.app Y) _, id_tensor_comp, category.assoc,
          category.assoc, ← braiding_naturality_assoc, id_tensor_comp_tensor_id_assoc, p, ←
          tensor_comp_assoc, category.id_comp] }
#align category_theory.enriched_nat_trans_yoneda CategoryTheory.enrichedNatTransYoneda

-- TODO assuming `[has_limits C]` construct the actual object of natural transformations
-- and show that the functor category is `V`-enriched.
end

section

attribute [local instance] category_of_enriched_category_Type

/-- We verify that an enriched functor between `Type v` enriched categories
is just the same thing as an honest functor.
-/
@[simps]
def enrichedFunctorTypeEquivFunctor {C : Type u₁} [𝒞 : EnrichedCategory (Type v) C] {D : Type u₂}
    [𝒟 : EnrichedCategory (Type v) D] : EnrichedFunctor (Type v) C D ≃ C ⥤ D
    where
  toFun F :=
    { obj := fun X => F.obj X
      map := fun X Y f => F.map X Y f
      map_id' := fun X => congr_fun (F.map_id X) PUnit.unit
      map_comp' := fun X Y Z f g => congr_fun (F.map_comp X Y Z) ⟨f, g⟩ }
  invFun F :=
    { obj := fun X => F.obj X
      map := fun X Y f => F.map f
      map_id' := fun X => by ext ⟨⟩; exact F.map_id X
      map_comp' := fun X Y Z => by ext ⟨f, g⟩; exact F.map_comp f g }
  left_inv F := by cases F; simp
  right_inv F := by cases F; simp
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
      { Hom := fun σ x =>
          { app := fun X => σ.app X x
            naturality' := fun X Y f => congr_fun (σ.naturality X Y) ⟨x, f⟩ }
        inv := fun σ =>
          { app := fun X x => (σ x).app X
            naturality := fun X Y => by ext ⟨x, f⟩; exact (σ x).naturality f } })
    (by tidy)
#align category_theory.enriched_nat_trans_yoneda_Type_iso_yoneda_nat_trans CategoryTheory.enrichedNatTransYonedaTypeIsoYonedaNatTrans

end

end CategoryTheory

