/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Types.Coyoneda
public import Mathlib.CategoryTheory.Monoidal.Center
public import Mathlib.Tactic.ApplyFun

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

We verify that when `V = Type v`, all these notions reduce to the usual ones.

## References

* [Kim Morrison, David Penneys, _Monoidal Categories Enriched in Braided Monoidal Categories_]
  [morrison-penney-enriched]
-/

@[expose] public section


universe w w' v v' u₁ u₂ u₃

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
  /-- `X ⟶[V] Y` is the `V` object of morphisms from `X` to `Y`. -/
  Hom : C → C → V
  /-- The identity morphism of this category -/
  id (X : C) : 𝟙_ V ⟶ Hom X X
  /-- Composition of two morphisms in this category -/
  comp (X Y Z : C) : Hom X Y ⊗ Hom Y Z ⟶ Hom X Z
  id_comp (X Y : C) : (λ_ (Hom X Y)).inv ≫ id X ▷ _ ≫ comp X X Y = 𝟙 _ := by cat_disch
  comp_id (X Y : C) : (ρ_ (Hom X Y)).inv ≫ _ ◁ id Y ≫ comp X Y Y = 𝟙 _ := by cat_disch
  assoc (W X Y Z : C) : (α_ _ _ _).inv ≫ comp W X Y ▷ _ ≫ comp W Y Z =
    _ ◁ comp X Y Z ≫ comp W X Z := by cat_disch

@[inherit_doc EnrichedCategory.Hom] notation3 X " ⟶[" V "] " Y:10 => (EnrichedCategory.Hom X Y : V)

variable {C : Type u₁} [EnrichedCategory V C]

/-- The `𝟙_ V`-shaped generalized element giving the identity in a `V`-enriched category.
-/
def eId (X : C) : 𝟙_ V ⟶ X ⟶[V] X :=
  EnrichedCategory.id X

/-- The composition `V`-morphism for a `V`-enriched category.
-/
def eComp (X Y Z : C) : ((X ⟶[V] Y) ⊗ Y ⟶[V] Z) ⟶ X ⟶[V] Z :=
  EnrichedCategory.comp X Y Z

@[reassoc (attr := simp)]
theorem e_id_comp (X Y : C) :
    (λ_ (X ⟶[V] Y)).inv ≫ eId V X ▷ _ ≫ eComp V X X Y = 𝟙 (X ⟶[V] Y) :=
  EnrichedCategory.id_comp X Y

@[reassoc (attr := simp)]
theorem e_comp_id (X Y : C) :
    (ρ_ (X ⟶[V] Y)).inv ≫ _ ◁ eId V Y ≫ eComp V X Y Y = 𝟙 (X ⟶[V] Y) :=
  EnrichedCategory.comp_id X Y

@[reassoc (attr := simp)]
theorem e_assoc (W X Y Z : C) :
    (α_ _ _ _).inv ≫ eComp V W X Y ▷ _ ≫ eComp V W Y Z =
      _ ◁ eComp V X Y Z ≫ eComp V W X Z :=
  EnrichedCategory.assoc W X Y Z

@[reassoc]
theorem e_assoc' (W X Y Z : C) :
    (α_ _ _ _).hom ≫ _ ◁ eComp V X Y Z ≫ eComp V W X Z =
      eComp V W X Y ▷ _ ≫ eComp V W Y Z := by
  rw [← e_assoc V W X Y Z, Iso.hom_inv_id_assoc]

section

variable {V} {W : Type v'} [Category.{w'} W] [MonoidalCategory W]

/-- A type synonym for `C`, which should come equipped with a `V`-enriched category structure.
In a moment we will equip this with the `W`-enriched category structure
obtained by applying the functor `F : LaxMonoidalFunctor V W` to each hom object.
-/
@[nolint unusedArguments]
def TransportEnrichment (F : V ⥤ W) [F.LaxMonoidal] (C : Type u₁) :=
  C

variable (F : V ⥤ W) [F.LaxMonoidal]

open Functor.LaxMonoidal

instance : EnrichedCategory W (TransportEnrichment F C) where
  Hom := fun X Y : C => F.obj (X ⟶[V] Y)
  id := fun X : C => ε F ≫ F.map (eId V X)
  comp := fun X Y Z : C => μ F _ _ ≫ F.map (eComp V X Y Z)
  id_comp X Y := by
    simp only [comp_whiskerRight, Category.assoc, Functor.LaxMonoidal.μ_natural_left_assoc,
      Functor.LaxMonoidal.left_unitality_inv_assoc]
    simp_rw [← F.map_comp]
    convert F.map_id _
    simp
  comp_id X Y := by
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Functor.LaxMonoidal.μ_natural_right_assoc,
      Functor.LaxMonoidal.right_unitality_inv_assoc]
    simp_rw [← F.map_comp]
    convert F.map_id _
    simp
  assoc P Q R S := by
    rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
      ← associativity_inv_assoc, ← F.map_comp, ← F.map_comp, e_assoc,
      F.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Functor.LaxMonoidal.μ_natural_right_assoc]

lemma TransportEnrichment.eId_eq (X : TransportEnrichment F C) :
    eId W X = ε F ≫ F.map (eId (C := C) V X) :=
  rfl

lemma TransportEnrichment.eComp_eq (X Y Z : TransportEnrichment F C) :
    eComp W X Y Z = μ F _ _ ≫ F.map (eComp V _ _ _) :=
  rfl

end

/-- Construct an honest category from a `Type v`-enriched category.
-/
@[instance_reducible]
def categoryOfEnrichedCategoryType (C : Type u₁) [𝒞 : EnrichedCategory (Type v) C] :
    Category.{v} C where
  Hom := 𝒞.Hom
  id X := eId (Type v) X PUnit.unit
  comp f g := eComp (Type v) _ _ _ ⟨f, g⟩
  id_comp f := congr_fun (e_id_comp (Type v) _ _) f
  comp_id f := congr_fun (e_comp_id (Type v) _ _) f
  assoc f g h := (congr_fun (e_assoc (Type v) _ _ _ _) ⟨f, g, h⟩ :)

/-- Construct a `Type v`-enriched category from an honest category.
-/
def enrichedCategoryTypeOfCategory (C : Type u₁) [𝒞 : Category.{v} C] :
    EnrichedCategory (Type v) C where
  Hom := 𝒞.Hom
  id X _ := 𝟙 X
  comp _ _ _ p := p.1 ≫ p.2
  id_comp X Y := by ext; simp
  comp_id X Y := by ext; simp
  assoc W X Y Z := by ext ⟨f, g, h⟩; simp

/-- We verify that an enriched category in `Type u` is just the same thing as an honest category.
-/
def enrichedCategoryTypeEquivCategory (C : Type u₁) :
    EnrichedCategory (Type v) C ≃ Category.{v} C where
  toFun _ := categoryOfEnrichedCategoryType C
  invFun _ := enrichedCategoryTypeOfCategory C

section

variable {W : Type v} [Category.{w} W] [MonoidalCategory W] [EnrichedCategory W C]

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
def ForgetEnrichment (W : Type v) [Category.{w} W] [MonoidalCategory W] (C : Type u₁)
    [EnrichedCategory W C] :=
  C

variable (W)

/-- Typecheck an object of `C` as an object of `ForgetEnrichment W C`. -/
def ForgetEnrichment.of (X : C) : ForgetEnrichment W C :=
  X

/-- Typecheck an object of `ForgetEnrichment W C` as an object of `C`. -/
def ForgetEnrichment.to (X : ForgetEnrichment W C) : C :=
  X

@[simp]
theorem ForgetEnrichment.to_of (X : C) : ForgetEnrichment.to W (ForgetEnrichment.of W X) = X :=
  rfl

@[simp]
theorem ForgetEnrichment.of_to (X : ForgetEnrichment W C) :
    ForgetEnrichment.of W (ForgetEnrichment.to W X) = X :=
  rfl

instance categoryForgetEnrichment : Category (ForgetEnrichment W C) :=
  enrichedCategoryTypeEquivCategory C (inferInstanceAs% (EnrichedCategory (Type w)
      (TransportEnrichment (coyoneda.obj (op (𝟙_ W))) C)))

/-- We verify that the morphism types in `ForgetEnrichment W C` are `(𝟙_ W) ⟶ (X ⟶[W] Y)`.
-/
example (X Y : ForgetEnrichment W C) :
    (X ⟶ Y) = (𝟙_ W ⟶ ForgetEnrichment.to W X ⟶[W] ForgetEnrichment.to W Y) :=
  rfl

/-- Typecheck a `(𝟙_ W)`-shaped `W`-morphism as a morphism in `ForgetEnrichment W C`. -/
def ForgetEnrichment.homOf {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y) :
    ForgetEnrichment.of W X ⟶ ForgetEnrichment.of W Y :=
  f

/-- Typecheck a morphism in `ForgetEnrichment W C` as a `(𝟙_ W)`-shaped `W`-morphism. -/
def ForgetEnrichment.homTo {X Y : ForgetEnrichment W C} (f : X ⟶ Y) :
    𝟙_ W ⟶ ForgetEnrichment.to W X ⟶[W] ForgetEnrichment.to W Y :=
  f

@[simp]
theorem ForgetEnrichment.homTo_homOf {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y) :
    ForgetEnrichment.homTo W (ForgetEnrichment.homOf W f) = f :=
  rfl

@[simp]
theorem ForgetEnrichment.homOf_homTo {X Y : ForgetEnrichment W C} (f : X ⟶ Y) :
    ForgetEnrichment.homOf W (ForgetEnrichment.homTo W f) = f :=
  rfl

/-- The identity in the "underlying" category of an enriched category. -/
@[simp]
theorem ForgetEnrichment.homTo_id (X : ForgetEnrichment W C) :
    ForgetEnrichment.homTo W (𝟙 X) = eId W (ForgetEnrichment.to W X : C) :=
  Category.id_comp _

@[simp]
theorem ForgetEnrichment.homOf_eId (X : C) :
    ForgetEnrichment.homOf W (eId W X) = 𝟙 (of W X : C) :=
  (homTo_id W (ForgetEnrichment.of W X)).symm

/-- Composition in the "underlying" category of an enriched category. -/
@[simp]
theorem ForgetEnrichment.homTo_comp {X Y Z : ForgetEnrichment W C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homTo W (f ≫ g) = ((λ_ (𝟙_ W)).inv ≫ (homTo W f ⊗ₘ homTo W g)) ≫ eComp W _ _ _ :=
  rfl

@[simp]
theorem ForgetEnrichment.homOf_comp {X Y Z : C} (f : 𝟙_ W ⟶ (X ⟶[W] Y)) (g : 𝟙_ W ⟶ (Y ⟶[W] Z)) :
    homOf W ((λ_ _).inv ≫ (f ⊗ₘ g) ≫ eComp W ..) = homOf W f ≫ homOf W g := by
  rw [← Category.assoc]
  rfl

end

/-- A `V`-functor `F` between `V`-enriched categories
has a `V`-morphism from `X ⟶[V] Y` to `F.obj X ⟶[V] F.obj Y`,
satisfying the usual axioms.
-/
structure EnrichedFunctor (C : Type u₁) [EnrichedCategory V C] (D : Type u₂)
    [EnrichedCategory V D] where
  /-- The application of this functor to an object -/
  obj : C → D
  /-- The `V`-morphism from `X ⟶[V] Y` to `F.obj X ⟶[V] F.obj Y`, for all `X Y : C` -/
  map : ∀ X Y : C, (X ⟶[V] Y) ⟶ obj X ⟶[V] obj Y
  map_id : ∀ X : C, eId V X ≫ map X X = eId V (obj X) := by cat_disch
  map_comp :
    ∀ X Y Z : C,
      eComp V X Y Z ≫ map X Z = (map X Y ⊗ₘ map Y Z) ≫ eComp V (obj X) (obj Y) (obj Z) := by
    cat_disch

attribute [reassoc (attr := simp)] EnrichedFunctor.map_id

attribute [reassoc (attr := simp)] EnrichedFunctor.map_comp

namespace EnrichedFunctor

/-- The identity enriched functor. -/
@[simps]
def id (C : Type u₁) [EnrichedCategory V C] : EnrichedFunctor V C C where
  obj X := X
  map _ _ := 𝟙 _

instance : Inhabited (EnrichedFunctor V C C) :=
  ⟨EnrichedFunctor.id V C⟩

/-- Composition of enriched functors. -/
@[simps]
def comp {C : Type u₁} {D : Type u₂} {E : Type u₃} [EnrichedCategory V C]
    [EnrichedCategory V D] [EnrichedCategory V E] (F : EnrichedFunctor V C D)
    (G : EnrichedFunctor V D E) : EnrichedFunctor V C E where
  obj X := G.obj (F.obj X)
  map _ _ := F.map _ _ ≫ G.map _ _

lemma ext {C : Type u₁} {D : Type u₂} [EnrichedCategory V C]
    [EnrichedCategory V D] {F G : EnrichedFunctor V C D} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y : C), F.map X Y ≫ eqToHom (by rw [h_obj, h_obj]) = G.map X Y) : F = G := by
  match F, G with
  | mk F_obj F_map _ _, mk G_obj G_map _ _ =>
    obtain rfl : F_obj = G_obj := funext fun X ↦ h_obj X
    congr
    ext X Y
    simpa using h_map X Y

section

variable {W : Type v'} [Category.{w'} W] [MonoidalCategory W]
  {C : Type u₁} [EnrichedCategory W C]
  {D : Type u₂} [EnrichedCategory W D]
  {E : Type u₃} [EnrichedCategory W E]

set_option backward.isDefEq.respectTransparency false in
/-- An enriched functor induces an honest functor of the underlying categories,
by mapping the `(𝟙_ W)`-shaped morphisms.
-/
@[simps]
def forget (F : EnrichedFunctor W C D) :
    ForgetEnrichment W C ⥤ ForgetEnrichment W D where
  obj X := ForgetEnrichment.of W (F.obj (ForgetEnrichment.to W X))
  map f :=
    ForgetEnrichment.homOf W
      (ForgetEnrichment.homTo W f ≫ F.map (ForgetEnrichment.to W _) (ForgetEnrichment.to W _))
  map_comp f g := by
    dsimp
    apply_fun ForgetEnrichment.homTo W
    · simp only [Iso.cancel_iso_inv_left, Category.assoc, ← tensorHom_comp_tensorHom,
        ForgetEnrichment.homTo_homOf, EnrichedFunctor.map_comp, ForgetEnrichment.homTo_comp]
      rfl
    · intro f g w; apply_fun ForgetEnrichment.homOf W at w; simpa using w

/-- `EnrichedFunctor.forget` distributes over composition of enriched functors up to isomorphism. -/
@[simps!]
def forgetComp (F : EnrichedFunctor W C D) (G : EnrichedFunctor W D E) :
    (F.comp W G).forget ≅ F.forget ⋙ G.forget :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [comp, forget])

variable (W) (C) in
/-- `EnrichedFunctor.forget` maps the identity enriched functor to a functor isomorphic to
`Functor.id`. -/
@[simps!]
def forgetId : (EnrichedFunctor.id W C).forget ≅ Functor.id _ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [forget])

end

end EnrichedFunctor

section

variable {V}
variable {D : Type u₂} [EnrichedCategory V D]

/-!
We now turn to natural transformations between `V`-functors.

The most commonly encountered definition of an enriched natural transformation
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


/-- The type of `A`-graded natural transformations between `V`-functors `F` and `G`.
This is the type of morphisms in `V` from `A` to the `V`-object of natural transformations.
-/
@[ext]
structure GradedNatTrans (A : Center V) (F G : EnrichedFunctor V C D) where
  /-- The `A`-graded transformation from `F` to `G` -/
  app : ∀ X : C, A.1 ⟶ F.obj X ⟶[V] G.obj X
  /-- `app` is a natural transformation. -/
  naturality :
    ∀ X Y : C,
      (A.2.β (X ⟶[V] Y)).hom ≫ (F.map X Y ⊗ₘ app Y) ≫ eComp V _ _ _ =
        (app X ⊗ₘ G.map X Y) ≫ eComp V _ _ _

attribute [reassoc] GradedNatTrans.naturality

/-- A natural transformation between two enriched functors is a `𝟙_ V`-graded natural
transformation. -/
structure EnrichedNatTrans (F G : EnrichedFunctor V C D) where
  /-- The underlying natural transformation of an enriched transformation. -/
  out : F.forget ⟶ G.forget

namespace EnrichedFunctor

/-- Enriched functors form a category with the morphisms between functors `F` and `G` being
enriched natural transformations, i.e. natural transformations `F.forget ⟶ G.forget`. -/
@[simps]
instance category : Category (EnrichedFunctor V C D) where
  Hom F G := EnrichedNatTrans F G
  id F := ⟨𝟙 _⟩
  comp F G := ⟨F.out ≫ G.out⟩

@[ext]
lemma hom_ext {F G : EnrichedFunctor V C D} {α β : F ⟶ G}
    (h : ∀ X : C, α.out.app X = β.out.app X) : α = β := by
  rcases α with ⟨α⟩
  rcases β with ⟨β⟩
  congr
  ext
  apply h

/-- To construct an isomorphism between enriched functors `F` and `G`, it suffices to construct
a natural isomorphism between `F.forget` and `G.forget`. -/
@[simps]
def isoMk {F G : EnrichedFunctor V C D} (h : F.forget ≅ G.forget) : F ≅ G where
  hom := ⟨h.hom⟩
  inv := ⟨h.inv⟩

end EnrichedFunctor

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
        dsimp at p ⊢
        rw [← id_tensor_comp_tensor_id (f.unop ≫ σ.app Y) _, id_tensor_comp, Category.assoc,
          Category.assoc, ← braiding_naturality_assoc, id_tensor_comp_tensor_id_assoc, p,
          tensorHom_comp_tensorHom_assoc, Category.id_comp] }

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
      map := fun _ _ f => F.map f
      map_id := fun X => by ext ⟨⟩; exact F.map_id X
      map_comp := fun X Y Z => by ext ⟨f, g⟩; exact F.map_comp f g }

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
    (by cat_disch)

end

end CategoryTheory
