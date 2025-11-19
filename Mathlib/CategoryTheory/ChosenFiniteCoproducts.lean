/-
Copyright (c) 2024 Jad Elkhaleq Ghalayini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jad Elkhaleq Ghalayini
-/
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts


/-!

# Chosen finite coproducts

## Main definitions

A category `C` has chosen finite coproducts if:
- There exists a function `· ⊕ₒ · : C → C → C` such that `X ⊕ₒ Y` is a coproduct of `X` and `Y` in
  `C`
- `𝟘_ C : C` is an initial object in `C`

Unlike `Limits.HasBinaryCoproducts`, this definition fixes a choice of coproducts and initial
object, which can be useful e.g. when working with subcategories, where we may want the coproduct in
the subcategory to agree with the coproduct in the ambient category.

## Implementation Details

We define a typeclass `ChosenFiniteCoproducts C` that bundles an explicit choice of a binary
coproduct of two objects of `C`, and a terminal object in `C`.
-/

namespace CategoryTheory

universe v v₁ v₂ u u₁ u₂

/--
An instance of `ChosenFiniteCoproducts C` bundles an explicit choice of a binary
product of two objects of `C`, and a terminal object in `C`.

Users should use the monoidal notation: `X ⊕ₒ Y` for the product and `𝟘_ C` for
the initial object.
-/
class ChosenFiniteCoproducts (C : Type u) [Category.{v} C] where
  /-- A choice of a colimit binary cofan for any two objects of the category. -/
  coproduct : (X Y : C) → Limits.ColimitCocone (Limits.pair X Y)
  /-- A choice of an initial object. -/
  initial : Limits.ColimitCocone (Functor.empty.{0} C)

namespace ChosenFiniteCoproducts

/-- The chosen initial object -/
abbrev initialObj (C : Type u) [Category.{v} C] [ChosenFiniteCoproducts C] : C := initial.cocone.pt

-- TODO: if `AddMonoidalCategory` is added, switch to use notation from there, analogously to how
-- `ChosenFiniteProducts` uses notation from `MonoidalCategory`

/-- Notation for the chosen initial object -/
scoped notation "𝟘_" => initialObj

variable {C : Type u} [Category.{v} C] [ChosenFiniteCoproducts C]

/-- The chosen coproduct of two objects -/
abbrev coprodObj (X Y : C) : C := (coproduct X Y).cocone.pt

/-- Notation for the chosen coproduct of two objects -/
scoped infixr:70 " ⊕ₒ " => coprodObj

/--
The unique map from the initial object.
-/
def fromZero (X : C) : 𝟘_ C ⟶ X :=
  initial.isColimit.desc <| .mk _ <| .mk (fun x => x.as.elim) fun x => x.as.elim

instance (X : C) : Unique (𝟘_ C ⟶ X) where
  default := fromZero _
  uniq _ := initial.isColimit.hom_ext fun ⟨j⟩ => j.elim

/--
This lemma follows from the preexisting `Unique` instance, but
it is often convenient to use it directly as `apply fromZero_unique` forcing
lean to do the necessary elaboration.
-/
lemma fromZero_unique {X : C} (f g : 𝟘_ _ ⟶ X) : f = g :=
  Subsingleton.elim _ _

/--
Construct a morphism from the coproduct given its two components.
-/
def desc {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T) : X ⊕ₒ Y ⟶ T :=
  (coproduct X Y).isColimit.desc <| Limits.BinaryCofan.mk f g

/--
The first injection into the coproduct
-/
def inl (X Y : C) : X ⟶ X ⊕ₒ Y :=
  letI F : Limits.BinaryCofan X Y := (coproduct X Y).cocone
  F.inl

/--
The second injection into the coproduct
-/
def inr (X Y : C) : Y ⟶ X ⊕ₒ Y :=
  letI F : Limits.BinaryCofan X Y := (coproduct X Y).cocone
  F.inr

@[simp, reassoc]
lemma inl_desc {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T) : inl X Y ≫ desc f g = f := by
  simp [inl, desc]

@[simp, reassoc]
lemma inr_desc {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T) : inr X Y ≫ desc f g = g := by
  simp [inr, desc]

instance epi_desc_of_epi_left {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T)
    [Epi f] : Epi (desc f g) :=
  epi_of_epi_fac <| inl_desc _ _

instance epi_desc_of_epi_right {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T)
    [Epi g] : Epi (desc f g) :=
  epi_of_epi_fac <| inr_desc _ _

@[ext 1050]
lemma hom_ext {T X Y : C} (f g : X ⊕ₒ Y ⟶ T)
    (h_inl : inl X Y ≫ f = inl X Y ≫ g)
    (h_inr : inr X Y ≫ f = inr X Y ≫ g) :
    f = g :=
  (coproduct X Y).isColimit.hom_ext fun ⟨j⟩ => j.recOn h_inl h_inr

-- Similarly to `CategoryTheory.Limits.coprod.desc_comp`, we do not make the `assoc` version a simp
-- lemma
@[reassoc, simp]
lemma desc_comp {V W X Y : C} (f : V ⟶ W) (g : X ⟶ V) (h : Y ⟶ V) :
    desc g h ≫ f = desc (g ≫ f) (h ≫ f) := by ext <;> simp [inl_desc_assoc, inr_desc_assoc]

@[simp]
lemma desc_inl_inr {X Y : C} : desc (inl X Y) (inr X Y) = 𝟙 (X ⊕ₒ Y) := by ext <;> simp

@[simp]
lemma desc_inl_comp_inr_comp {X Y Z : C} (f : Y ⊕ₒ Z ⟶ X) :
    desc (inl Y Z ≫ f) (inr Y Z ≫ f) = f := by ext <;> simp

-- TODO: if `AddMonoidalCategory` is added, switch to using `addHom` from there, analogously to how
-- `ChosenFiniteProducts` uses `tensorHom` from `MonoidalCategory`

/-- The coproduct of two morphisms -/
def addHom {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : X ⊕ₒ X' ⟶ Y ⊕ₒ Y' :=
  desc (f ≫ inl Y Y') (g ≫ inr Y Y')

/-- Notation for the chosen coproduct of two morphisms -/
scoped infixr:70 " ⊕ₕ " => addHom

@[reassoc (attr := simp)]
lemma inl_addHom {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    inl X X' ≫ (f ⊕ₕ g) = f ≫ inl Y Y' := by simp [addHom]

@[reassoc (attr := simp)]
lemma inr_addHom {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    inr X X' ≫ (f ⊕ₕ g) = g ≫ inr Y Y' := by simp [addHom]

@[reassoc]
lemma addHom_desc {S T U V W : C} (f : U ⟶ S) (g : W ⟶ S) (h : T ⟶ U) (k : V ⟶ W) :
    (h ⊕ₕ k) ≫ desc f g = desc (h ≫ f) (k ≫ g) := by simp [addHom]

@[simp]
lemma desc_comp_inl_inr {W X Y Z : C} (g : X ⟶ W) (g' : Z ⟶ Y) :
    desc (g ≫ inl _ _) (g' ≫ inr _ _) = g ⊕ₕ g' := rfl

/--
Construct an instance of `ChosenFiniteCoproducts C` given an instance of `HasFiniteCoproducts C`.
-/
noncomputable
def ofFiniteCoproducts
    (C : Type u) [Category.{v} C] [Limits.HasFiniteCoproducts C] :
    ChosenFiniteCoproducts C where
  coproduct X Y := Limits.getColimitCocone (Limits.pair X Y)
  initial := Limits.getColimitCocone (Functor.empty C)

instance (priority := 100) : Limits.HasFiniteCoproducts C :=
  letI : ∀ (X Y : C), Limits.HasColimit (Limits.pair X Y) := fun _ _ =>
    .mk <| ChosenFiniteCoproducts.coproduct _ _
  letI : Limits.HasBinaryCoproducts C := Limits.hasBinaryCoproducts_of_hasColimit_pair _
  letI : Limits.HasInitial C := Limits.hasInitial_of_unique (𝟘_ C)
  hasFiniteCoproducts_of_has_binary_and_initial

section ChosenFiniteCoproductsComparison

variable {D : Type u₁} [Category.{v₁} D] [ChosenFiniteCoproducts D] (F : C ⥤ D)

section initialComparison

/-- When `C` and `D` have chosen finite coproducts and `F : C ⥤ D` is any functor,
`initialComparison F` is the unique map `𝟘_ D ⟶ F (𝟘_ C)`. -/
abbrev initialComparison : 𝟘_ D ⟶ F.obj (𝟘_ C) := fromZero _

@[reassoc (attr := simp)]
lemma initialComparison_comp_map_fromZero (A : C) :
    initialComparison F ≫ F.map (fromZero A) = fromZero _ := fromZero_unique _ _

open Limits

/-- If `initialComparison F` is an Iso, then `F` preserves initial objects. -/
lemma preservesColimit_empty_of_isIso_initialComparison [IsIso (initialComparison F)] :
    PreservesColimit (Functor.empty.{0} C) F := by
  apply preservesColimit_of_preserves_colimit_cocone initial.isColimit
  apply isColimitChangeEmptyCocone D initial.isColimit
  exact asIso (initialComparison F)

/-- If `F` preserves initial objects, then `initialComparison F` is an isomorphism. -/
noncomputable def preservesInitialIso [h : PreservesColimit (Functor.empty.{0} C) F] :
    F.obj (𝟘_ C) ≅ 𝟘_ D :=
  (isColimitChangeEmptyCocone D (isColimitOfPreserves _ initial.isColimit)
    (asEmptyCocone (F.obj (𝟘_ C))) (Iso.refl _)).coconePointUniqueUpToIso initial.isColimit

@[simp]
lemma preservesInitialIso_inv [PreservesColimit (Functor.empty.{0} C) F] :
    (preservesInitialIso F).inv = initialComparison F := fromZero_unique _ _

instance initialComparison_isIso_of_preservesColimits [PreservesColimit (Functor.empty.{0} C) F] :
    IsIso (initialComparison F) := by
  rw [← preservesInitialIso_inv]
  infer_instance

end initialComparison

section coprodComparison

variable (A B : C)

/-- When `C` and `D` have chosen finite products and `F : C ⥤ D` is any functor,
`coprodComparison F A B` is the canonical comparison morphism from `F(A) ⊕ₒ F(B)` to `F (A ⊕ₒ B)`.
-/
def coprodComparison (A B : C) : F.obj A ⊕ₒ F.obj B ⟶ F.obj (A ⊕ₒ B) :=
  desc (F.map (inl A B)) (F.map (inr A B))

@[reassoc (attr := simp)]
theorem inl_coprodComparison : inl _ _ ≫ coprodComparison F A B = F.map (inl A B) :=
  inl_desc _ _

@[reassoc (attr := simp)]
theorem inr_coprodComparison : inr _ _ ≫ coprodComparison F A B = F.map (inr A B) :=
  inr_desc _ _

@[reassoc (attr := simp)]
theorem map_inl_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map (inl _ _) ≫ inv (coprodComparison F A B) = inl _ _ := by simp

@[reassoc (attr := simp)]
theorem map_inr_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map (inr _ _) ≫ inv (coprodComparison F A B) = inr _ _ := by simp

variable {A B} {A' B' : C}

/-- Naturality of the `coprodComparison` morphism in both arguments. -/
@[reassoc]
theorem coprodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    coprodComparison F A B ≫ F.map (f ⊕ₕ g) =
      (F.map f ⊕ₕ F.map g) ≫ coprodComparison F A' B' := by
  apply hom_ext <;>
  simp only [Category.assoc, addHom, coprodComparison, inl_desc_assoc, inl_desc, inr_desc_assoc,
    inr_desc, ← F.map_comp]

section
variable [IsIso (coprodComparison F A B)]

/-- If the coproduct comparison morphism is an iso, its inverse is natural in both arguments. -/
@[reassoc]
theorem coprodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (coprodComparison F A' B')] :
    inv (coprodComparison F A B) ≫ (F.map f ⊕ₕ F.map g) =
      F.map (f ⊕ₕ g) ≫ inv (coprodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, coprodComparison_natural]

end

theorem coprodComparison_comp {E : Type u₂} [Category.{v₂} E] [ChosenFiniteCoproducts E]
  (G : D ⥤ E) :
    coprodComparison (F ⋙ G) A B =
      coprodComparison G (F.obj A) (F.obj B) ≫ G.map (coprodComparison F A B) := by
  unfold coprodComparison
  ext <;> simp [← G.map_comp]

@[simp]
lemma coprodComparison_id :
    coprodComparison (𝟭 C) A B = 𝟙 (A ⊕ₒ B) := desc_inl_inr

end coprodComparison

end ChosenFiniteCoproductsComparison

end ChosenFiniteCoproducts

end CategoryTheory
