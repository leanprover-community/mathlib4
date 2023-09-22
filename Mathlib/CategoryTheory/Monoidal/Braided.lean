/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Monoidal.Discrete

#align_import category_theory.monoidal.braided from "leanprover-community/mathlib"@"2efd2423f8d25fa57cf7a179f5d8652ab4d0df44"

/-!
# Braided and symmetric monoidal categories

The basic definitions of braided monoidal categories, and symmetric monoidal categories,
as well as braided functors.

## Implementation note

We make `BraidedCategory` another typeclass, but then have `SymmetricCategory` extend this.
The rationale is that we are not carrying any additional data, just requiring a property.

## Future work

* Construct the Drinfeld center of a monoidal category as a braided monoidal category.
* Say something about pseudo-natural transformations.

-/


open CategoryTheory MonoidalCategory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace CategoryTheory

/-- A braided monoidal category is a monoidal category equipped with a braiding isomorphism
`β_ X Y : X ⊗ Y ≅ Y ⊗ X`
which is natural in both arguments,
and also satisfies the two hexagon identities.
-/
class BraidedCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  -- braiding natural iso:
  braiding : ∀ X Y : C, X ⊗ Y ≅ Y ⊗ X
  braiding_naturality :
    ∀ {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
      (f ⊗ g) ≫ (braiding Y Y').hom = (braiding X X').hom ≫ (g ⊗ f) := by
    aesop_cat
  -- hexagon identities:
  hexagon_forward :
    ∀ X Y Z : C,
      (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
        ((braiding X Y).hom ⊗ 𝟙 Z) ≫ (α_ Y X Z).hom ≫ (𝟙 Y ⊗ (braiding X Z).hom) := by
    aesop_cat
  hexagon_reverse :
    ∀ X Y Z : C,
      (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
        (𝟙 X ⊗ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braiding X Z).hom ⊗ 𝟙 Y) := by
    aesop_cat
#align category_theory.braided_category CategoryTheory.BraidedCategory

attribute [reassoc (attr := simp)] BraidedCategory.braiding_naturality
attribute [reassoc] BraidedCategory.hexagon_forward BraidedCategory.hexagon_reverse

open Category

open MonoidalCategory

open BraidedCategory

notation "β_" => braiding

/--
Verifying the axioms for a braiding by checking that the candidate braiding is sent to a braiding
by a faithful monoidal functor.
-/
def braidedCategoryOfFaithful {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] (F : MonoidalFunctor C D) [Faithful F.toFunctor] [BraidedCategory D]
    (β : ∀ X Y : C, X ⊗ Y ≅ Y ⊗ X)
    (w : ∀ X Y, F.μ _ _ ≫ F.map (β X Y).hom = (β_ _ _).hom ≫ F.μ _ _) : BraidedCategory C where
  braiding := β
  braiding_naturality := by
    intros
    apply F.map_injective
    refine (cancel_epi (F.μ ?_ ?_)).1 ?_
    rw [Functor.map_comp, ← LaxMonoidalFunctor.μ_natural_assoc, w, Functor.map_comp, reassoc_of% w,
      braiding_naturality_assoc, LaxMonoidalFunctor.μ_natural]
  hexagon_forward := by
    intros
    apply F.map_injective
    refine (cancel_epi (F.μ _ _)).1 ?_
    refine (cancel_epi (F.μ _ _ ⊗ 𝟙 _)).1 ?_
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, ←
      LaxMonoidalFunctor.μ_natural_assoc, Functor.map_id, ← comp_tensor_id_assoc, w,
      comp_tensor_id, assoc, LaxMonoidalFunctor.associativity_assoc,
      LaxMonoidalFunctor.associativity_assoc, ← LaxMonoidalFunctor.μ_natural, Functor.map_id, ←
      id_tensor_comp_assoc, w, id_tensor_comp_assoc, reassoc_of% w, braiding_naturality_assoc,
      LaxMonoidalFunctor.associativity, hexagon_forward_assoc]
  hexagon_reverse := by
    intros
    apply F.toFunctor.map_injective
    refine (cancel_epi (F.μ _ _)).1 ?_
    refine (cancel_epi (𝟙 _ ⊗ F.μ _ _)).1 ?_
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, ←
      LaxMonoidalFunctor.μ_natural_assoc, Functor.map_id, ← id_tensor_comp_assoc, w,
      id_tensor_comp_assoc, LaxMonoidalFunctor.associativity_inv_assoc,
      LaxMonoidalFunctor.associativity_inv_assoc, ← LaxMonoidalFunctor.μ_natural,
      Functor.map_id, ← comp_tensor_id_assoc, w, comp_tensor_id_assoc, reassoc_of% w,
      braiding_naturality_assoc, LaxMonoidalFunctor.associativity_inv, hexagon_reverse_assoc]
#align category_theory.braided_category_of_faithful CategoryTheory.braidedCategoryOfFaithful

/-- Pull back a braiding along a fully faithful monoidal functor. -/
noncomputable def braidedCategoryOfFullyFaithful {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : MonoidalFunctor C D) [Full F.toFunctor]
    [Faithful F.toFunctor] [BraidedCategory D] : BraidedCategory C :=
  braidedCategoryOfFaithful F
    (fun X Y => F.toFunctor.preimageIso
      ((asIso (F.μ _ _)).symm ≪≫ β_ (F.obj X) (F.obj Y) ≪≫ asIso (F.μ _ _)))
    (by aesop_cat)
#align category_theory.braided_category_of_fully_faithful CategoryTheory.braidedCategoryOfFullyFaithful

section

/-!
We now establish how the braiding interacts with the unitors.

I couldn't find a detailed proof in print, but this is discussed in:

* Proposition 1 of André Joyal and Ross Street,
  "Braided monoidal categories", Macquarie Math Reports 860081 (1986).
* Proposition 2.1 of André Joyal and Ross Street,
  "Braided tensor categories" , Adv. Math. 102 (1993), 20–78.
* Exercise 8.1.6 of Etingof, Gelaki, Nikshych, Ostrik,
  "Tensor categories", vol 25, Mathematical Surveys and Monographs (2015), AMS.
-/

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]

theorem braiding_leftUnitor_aux₁ (X : C) :
    (α_ (𝟙_ C) (𝟙_ C) X).hom ≫
        (𝟙 (𝟙_ C) ⊗ (β_ X (𝟙_ C)).inv) ≫ (α_ _ X _).inv ≫ ((λ_ X).hom ⊗ 𝟙 _) =
      ((λ_ _).hom ⊗ 𝟙 X) ≫ (β_ X (𝟙_ C)).inv :=
  by rw [← leftUnitor_tensor, leftUnitor_naturality]; simp
#align category_theory.braiding_left_unitor_aux₁ CategoryTheory.braiding_leftUnitor_aux₁

theorem braiding_leftUnitor_aux₂ (X : C) :
    ((β_ X (𝟙_ C)).hom ⊗ 𝟙 (𝟙_ C)) ≫ ((λ_ X).hom ⊗ 𝟙 (𝟙_ C)) = (ρ_ X).hom ⊗ 𝟙 (𝟙_ C) :=
  calc
    ((β_ X (𝟙_ C)).hom ⊗ 𝟙 (𝟙_ C)) ≫ ((λ_ X).hom ⊗ 𝟙 (𝟙_ C)) =
      ((β_ X (𝟙_ C)).hom ⊗ 𝟙 (𝟙_ C)) ≫ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫ ((λ_ X).hom ⊗ 𝟙 (𝟙_ C)) :=
      by coherence
    _ = ((β_ X (𝟙_ C)).hom ⊗ 𝟙 (𝟙_ C)) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (β_ X _).hom) ≫
          (𝟙 _ ⊗ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫ ((λ_ X).hom ⊗ 𝟙 (𝟙_ C)) :=
      by (slice_rhs 3 4 => rw [← id_tensor_comp, Iso.hom_inv_id, tensor_id]); rw [id_comp]
    _ = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫
          ((λ_ X).hom ⊗ 𝟙 (𝟙_ C)) :=
      by (slice_lhs 1 3 => rw [← hexagon_forward]); simp only [assoc]
    _ = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ ((λ_ _).hom ⊗ 𝟙 X) ≫ (β_ X _).inv :=
      by rw [braiding_leftUnitor_aux₁]
    _ = (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (λ_ _).hom) ≫ (β_ _ _).hom ≫ (β_ X _).inv :=
      by (slice_lhs 2 3 => rw [← braiding_naturality]); simp only [assoc]
    _ = (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (λ_ _).hom) := by rw [Iso.hom_inv_id, comp_id]
    _ = (ρ_ X).hom ⊗ 𝟙 (𝟙_ C) := by rw [triangle]

#align category_theory.braiding_left_unitor_aux₂ CategoryTheory.braiding_leftUnitor_aux₂

@[simp]
theorem braiding_leftUnitor (X : C) : (β_ X (𝟙_ C)).hom ≫ (λ_ X).hom = (ρ_ X).hom := by
  rw [← tensor_right_iff, comp_tensor_id, braiding_leftUnitor_aux₂]
#align category_theory.braiding_left_unitor CategoryTheory.braiding_leftUnitor

theorem braiding_rightUnitor_aux₁ (X : C) :
    (α_ X (𝟙_ C) (𝟙_ C)).inv ≫
        ((β_ (𝟙_ C) X).inv ⊗ 𝟙 (𝟙_ C)) ≫ (α_ _ X _).hom ≫ (𝟙 _ ⊗ (ρ_ X).hom) =
      (𝟙 X ⊗ (ρ_ _).hom) ≫ (β_ (𝟙_ C) X).inv :=
  by rw [← rightUnitor_tensor, rightUnitor_naturality]; simp
#align category_theory.braiding_right_unitor_aux₁ CategoryTheory.braiding_rightUnitor_aux₁

theorem braiding_rightUnitor_aux₂ (X : C) :
    (𝟙 (𝟙_ C) ⊗ (β_ (𝟙_ C) X).hom) ≫ (𝟙 (𝟙_ C) ⊗ (ρ_ X).hom) = 𝟙 (𝟙_ C) ⊗ (λ_ X).hom :=
  calc
    (𝟙 (𝟙_ C) ⊗ (β_ (𝟙_ C) X).hom) ≫ (𝟙 (𝟙_ C) ⊗ (ρ_ X).hom) =
      (𝟙 (𝟙_ C) ⊗ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).hom ≫ (𝟙 (𝟙_ C) ⊗ (ρ_ X).hom) :=
      by coherence
    _ = (𝟙 (𝟙_ C) ⊗ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ ((β_ _ X).hom ⊗ 𝟙 _) ≫
          ((β_ _ X).inv ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 (𝟙_ C) ⊗ (ρ_ X).hom) :=
      by (slice_rhs 3 4 => rw [← comp_tensor_id, Iso.hom_inv_id, tensor_id]); rw [id_comp]
    _ = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (α_ _ _ _).inv ≫ ((β_ _ X).inv ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫
          (𝟙 (𝟙_ C) ⊗ (ρ_ X).hom) :=
      by (slice_lhs 1 3 => rw [← hexagon_reverse]); simp only [assoc]
    _ = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (𝟙 X ⊗ (ρ_ _).hom) ≫ (β_ _ X).inv :=
      by rw [braiding_rightUnitor_aux₁]
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).hom ⊗ 𝟙 _) ≫ (β_ _ X).hom ≫ (β_ _ _).inv :=
      by (slice_lhs 2 3 => rw [← braiding_naturality]); simp only [assoc]
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).hom ⊗ 𝟙 _) := by rw [Iso.hom_inv_id, comp_id]
    _ = 𝟙 (𝟙_ C) ⊗ (λ_ X).hom := by rw [triangle_assoc_comp_right]

#align category_theory.braiding_right_unitor_aux₂ CategoryTheory.braiding_rightUnitor_aux₂

@[simp]
theorem braiding_rightUnitor (X : C) : (β_ (𝟙_ C) X).hom ≫ (ρ_ X).hom = (λ_ X).hom := by
  rw [← tensor_left_iff, id_tensor_comp, braiding_rightUnitor_aux₂]
#align category_theory.braiding_right_unitor CategoryTheory.braiding_rightUnitor

@[simp]
theorem leftUnitor_inv_braiding (X : C) : (λ_ X).inv ≫ (β_ (𝟙_ C) X).hom = (ρ_ X).inv := by
  apply (cancel_mono (ρ_ X).hom).1
  simp only [assoc, braiding_rightUnitor, Iso.inv_hom_id]
#align category_theory.left_unitor_inv_braiding CategoryTheory.leftUnitor_inv_braiding

@[simp]
theorem rightUnitor_inv_braiding (X : C) : (ρ_ X).inv ≫ (β_ X (𝟙_ C)).hom = (λ_ X).inv := by
  apply (cancel_mono (λ_ X).hom).1
  simp only [assoc, braiding_leftUnitor, Iso.inv_hom_id]
#align category_theory.right_unitor_inv_braiding CategoryTheory.rightUnitor_inv_braiding

end

/--
A symmetric monoidal category is a braided monoidal category for which the braiding is symmetric.

See <https://stacks.math.columbia.edu/tag/0FFW>.
-/
class SymmetricCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] extends
    BraidedCategory.{v} C where
  -- braiding symmetric:
  symmetry : ∀ X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) := by aesop_cat
#align category_theory.symmetric_category CategoryTheory.SymmetricCategory

attribute [reassoc (attr := simp)] SymmetricCategory.symmetry

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
variable (E : Type u₃) [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]

/-- A lax braided functor between braided monoidal categories is a lax monoidal functor
which preserves the braiding.
-/
structure LaxBraidedFunctor extends LaxMonoidalFunctor C D where
  braided : ∀ X Y : C, μ X Y ≫ map (β_ X Y).hom = (β_ (obj X) (obj Y)).hom ≫ μ Y X := by aesop_cat
#align category_theory.lax_braided_functor CategoryTheory.LaxBraidedFunctor

namespace LaxBraidedFunctor

/-- The identity lax braided monoidal functor. -/
@[simps!]
def id : LaxBraidedFunctor C C :=
  { MonoidalFunctor.id C with }
#align category_theory.lax_braided_functor.id CategoryTheory.LaxBraidedFunctor.id

instance : Inhabited (LaxBraidedFunctor C C) :=
  ⟨id C⟩

variable {C D E}

/-- The composition of lax braided monoidal functors. -/
@[simps!]
def comp (F : LaxBraidedFunctor C D) (G : LaxBraidedFunctor D E) : LaxBraidedFunctor C E :=
  { LaxMonoidalFunctor.comp F.toLaxMonoidalFunctor G.toLaxMonoidalFunctor with
    braided := fun X Y => by
      dsimp
      slice_lhs 2 3 =>
        rw [← CategoryTheory.Functor.map_comp, F.braided, CategoryTheory.Functor.map_comp]
      slice_lhs 1 2 => rw [G.braided]
      simp only [Category.assoc] }
#align category_theory.lax_braided_functor.comp CategoryTheory.LaxBraidedFunctor.comp

instance categoryLaxBraidedFunctor : Category (LaxBraidedFunctor C D) :=
  InducedCategory.category LaxBraidedFunctor.toLaxMonoidalFunctor
#align category_theory.lax_braided_functor.category_lax_braided_functor CategoryTheory.LaxBraidedFunctor.categoryLaxBraidedFunctor

-- Porting note: added, as `MonoidalNatTrans.ext` does not apply to morphisms.
@[ext]
lemma ext' {F G : LaxBraidedFunctor C D} {α β : F ⟶ G} (w : ∀ X : C, α.hom.app X = β.hom.app X) :
    α = β :=
  InducedCategory.hom_ext <| MonoidalNatTrans.ext _ _ (funext w)

@[simp]
theorem comp_toNatTrans {F G H : LaxBraidedFunctor C D} {α : F ⟶ G} {β : G ⟶ H} :
    (α ≫ β).hom.toNatTrans =
      @CategoryStruct.comp (C ⥤ D) _ _ _ _ α.hom.toNatTrans β.hom.toNatTrans :=
  rfl
#align category_theory.lax_braided_functor.comp_to_nat_trans CategoryTheory.LaxBraidedFunctor.comp_toNatTrans

/-- Interpret a natural isomorphism of the underlying lax monoidal functors as an
isomorphism of the lax braided monoidal functors.
-/
@[simp]
def mkIso {F G : LaxBraidedFunctor C D} (i : F.toLaxMonoidalFunctor ≅ G.toLaxMonoidalFunctor) :
    F ≅ G :=
  (inducedFunctor _).preimageIso i
#align category_theory.lax_braided_functor.mk_iso CategoryTheory.LaxBraidedFunctor.mkIso

end LaxBraidedFunctor

/-- A braided functor between braided monoidal categories is a monoidal functor
which preserves the braiding.
-/
structure BraidedFunctor extends MonoidalFunctor C D where
  -- Note this is stated differently than for `LaxBraidedFunctor`.
  -- We move the `μ X Y` to the right hand side,
  -- so that this makes a good `@[simp]` lemma.
  braided : ∀ X Y : C, map (β_ X Y).hom = inv (μ X Y) ≫ (β_ (obj X) (obj Y)).hom ≫ μ Y X := by
    aesop_cat
#align category_theory.braided_functor CategoryTheory.BraidedFunctor

attribute [simp] BraidedFunctor.braided

/--
A braided category with a faithful braided functor to a symmetric category is itself symmetric.
-/
def symmetricCategoryOfFaithful {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [SymmetricCategory D] (F : BraidedFunctor C D)
    [Faithful F.toFunctor] : SymmetricCategory C where
  symmetry X Y := F.map_injective (by simp)
#align category_theory.symmetric_category_of_faithful CategoryTheory.symmetricCategoryOfFaithful

namespace BraidedFunctor

/-- Turn a braided functor into a lax braided functor. -/
@[simps toLaxMonoidalFunctor]
def toLaxBraidedFunctor (F : BraidedFunctor C D) : LaxBraidedFunctor C D :=
  { toLaxMonoidalFunctor := F.toLaxMonoidalFunctor
    braided := fun X Y => by rw [F.braided]; simp }
#align category_theory.braided_functor.to_lax_braided_functor CategoryTheory.BraidedFunctor.toLaxBraidedFunctor

/-- The identity braided monoidal functor. -/
@[simps!]
def id : BraidedFunctor C C :=
  { MonoidalFunctor.id C with }
#align category_theory.braided_functor.id CategoryTheory.BraidedFunctor.id

instance : Inhabited (BraidedFunctor C C) :=
  ⟨id C⟩

variable {C D E}

/-- The composition of braided monoidal functors. -/
@[simps!]
def comp (F : BraidedFunctor C D) (G : BraidedFunctor D E) : BraidedFunctor C E :=
  { MonoidalFunctor.comp F.toMonoidalFunctor G.toMonoidalFunctor with }
#align category_theory.braided_functor.comp CategoryTheory.BraidedFunctor.comp

instance categoryBraidedFunctor : Category (BraidedFunctor C D) :=
  InducedCategory.category BraidedFunctor.toMonoidalFunctor
#align category_theory.braided_functor.category_braided_functor CategoryTheory.BraidedFunctor.categoryBraidedFunctor

-- Porting note: added, as `MonoidalNatTrans.ext` does not apply to morphisms.
@[ext]
lemma ext' {F G : BraidedFunctor C D} {α β : F ⟶ G}
    (w : ∀ X : C, α.hom.hom.app X = β.hom.hom.app X) : α = β :=
  InducedCategory.hom_ext <| InducedCategory.hom_ext <| MonoidalNatTrans.ext _ _ (funext w)

@[simp]
theorem comp_toNatTrans {F G H : BraidedFunctor C D} {α : F ⟶ G} {β : G ⟶ H} :
    (α ≫ β).hom.hom.toNatTrans =
      @CategoryStruct.comp (C ⥤ D) _ _ _ _ α.hom.hom.toNatTrans β.hom.hom.toNatTrans :=
  rfl
#align category_theory.braided_functor.comp_to_nat_trans CategoryTheory.BraidedFunctor.comp_toNatTrans

/-- Interpret a natural isomorphism of the underlying monoidal functors as an
isomorphism of the braided monoidal functors.
-/
@[simp]
def mkIso {F G : BraidedFunctor C D} (i : F.toMonoidalFunctor ≅ G.toMonoidalFunctor) : F ≅ G :=
  (inducedFunctor _).preimageIso i
#align category_theory.braided_functor.mk_iso CategoryTheory.BraidedFunctor.mkIso

end BraidedFunctor

section CommMonoid

variable (M : Type u) [CommMonoid M]

instance : BraidedCategory (Discrete M) where
  braiding X Y := Discrete.eqToIso (mul_comm X.as Y.as)

variable {M} {N : Type u} [CommMonoid N]

/-- A multiplicative morphism between commutative monoids gives a braided functor between
the corresponding discrete braided monoidal categories.
-/
@[simps!]
def Discrete.braidedFunctor (F : M →* N) : BraidedFunctor (Discrete M) (Discrete N) :=
  { Discrete.monoidalFunctor F with }
#align category_theory.discrete.braided_functor CategoryTheory.Discrete.braidedFunctor

end CommMonoid

section Tensor

/-- The strength of the tensor product functor from `C × C` to `C`. -/
def tensor_μ (X Y : C × C) : (tensor C).obj X ⊗ (tensor C).obj Y ⟶ (tensor C).obj (X ⊗ Y) :=
  (α_ X.1 X.2 (Y.1 ⊗ Y.2)).hom ≫
    (𝟙 X.1 ⊗ (α_ X.2 Y.1 Y.2).inv) ≫
      (𝟙 X.1 ⊗ (β_ X.2 Y.1).hom ⊗ 𝟙 Y.2) ≫
        (𝟙 X.1 ⊗ (α_ Y.1 X.2 Y.2).hom) ≫ (α_ X.1 Y.1 (X.2 ⊗ Y.2)).inv
#align category_theory.tensor_μ CategoryTheory.tensor_μ

theorem tensor_μ_def₁ (X₁ X₂ Y₁ Y₂ : C) :
    tensor_μ C (X₁, X₂) (Y₁, Y₂) ≫ (α_ X₁ Y₁ (X₂ ⊗ Y₂)).hom ≫ (𝟙 X₁ ⊗ (α_ Y₁ X₂ Y₂).inv) =
      (α_ X₁ X₂ (Y₁ ⊗ Y₂)).hom ≫ (𝟙 X₁ ⊗ (α_ X₂ Y₁ Y₂).inv) ≫ (𝟙 X₁ ⊗ (β_ X₂ Y₁).hom ⊗ 𝟙 Y₂) :=
  by dsimp [tensor_μ]; simp
#align category_theory.tensor_μ_def₁ CategoryTheory.tensor_μ_def₁

theorem tensor_μ_def₂ (X₁ X₂ Y₁ Y₂ : C) :
    (𝟙 X₁ ⊗ (α_ X₂ Y₁ Y₂).hom) ≫ (α_ X₁ X₂ (Y₁ ⊗ Y₂)).inv ≫ tensor_μ C (X₁, X₂) (Y₁, Y₂) =
      (𝟙 X₁ ⊗ (β_ X₂ Y₁).hom ⊗ 𝟙 Y₂) ≫ (𝟙 X₁ ⊗ (α_ Y₁ X₂ Y₂).hom) ≫ (α_ X₁ Y₁ (X₂ ⊗ Y₂)).inv :=
  by dsimp [tensor_μ]; simp
#align category_theory.tensor_μ_def₂ CategoryTheory.tensor_μ_def₂

theorem tensor_μ_natural {X₁ X₂ Y₁ Y₂ U₁ U₂ V₁ V₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : U₁ ⟶ V₁)
    (g₂ : U₂ ⟶ V₂) :
    ((f₁ ⊗ f₂) ⊗ g₁ ⊗ g₂) ≫ tensor_μ C (Y₁, Y₂) (V₁, V₂) =
      tensor_μ C (X₁, X₂) (U₁, U₂) ≫ ((f₁ ⊗ g₁) ⊗ f₂ ⊗ g₂) := by
  dsimp [tensor_μ]
  slice_lhs 1 2 => rw [associator_naturality]
  slice_lhs 2 3 =>
    rw [← tensor_comp, comp_id f₁, ← id_comp f₁, associator_inv_naturality, tensor_comp]
  slice_lhs 3 4 =>
    rw [← tensor_comp, ← tensor_comp, comp_id f₁, ← id_comp f₁, comp_id g₂, ← id_comp g₂,
      braiding_naturality, tensor_comp, tensor_comp]
  slice_lhs 4 5 => rw [← tensor_comp, comp_id f₁, ← id_comp f₁, associator_naturality, tensor_comp]
  slice_lhs 5 6 => rw [associator_inv_naturality]
  simp only [assoc]
#align category_theory.tensor_μ_natural CategoryTheory.tensor_μ_natural

theorem tensor_left_unitality (X₁ X₂ : C) :
    (λ_ (X₁ ⊗ X₂)).hom =
      ((λ_ (𝟙_ C)).inv ⊗ 𝟙 (X₁ ⊗ X₂)) ≫
        tensor_μ C (𝟙_ C, 𝟙_ C) (X₁, X₂) ≫ ((λ_ X₁).hom ⊗ (λ_ X₂).hom) := by
  dsimp [tensor_μ]
  have :
    ((λ_ (𝟙_ C)).inv ⊗ 𝟙 (X₁ ⊗ X₂)) ≫
        (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫ (𝟙 (𝟙_ C) ⊗ (α_ (𝟙_ C) X₁ X₂).inv) =
      𝟙 (𝟙_ C) ⊗ (λ_ X₁).inv ⊗ 𝟙 X₂ :=
    by pure_coherence
  slice_rhs 1 3 => rw [this]
  clear this
  slice_rhs 1 2 => rw [← tensor_comp, ← tensor_comp, comp_id, comp_id, leftUnitor_inv_braiding]
  simp only [assoc]
  coherence
#align category_theory.tensor_left_unitality CategoryTheory.tensor_left_unitality

theorem tensor_right_unitality (X₁ X₂ : C) :
    (ρ_ (X₁ ⊗ X₂)).hom =
      (𝟙 (X₁ ⊗ X₂) ⊗ (λ_ (𝟙_ C)).inv) ≫
        tensor_μ C (X₁, X₂) (𝟙_ C, 𝟙_ C) ≫ ((ρ_ X₁).hom ⊗ (ρ_ X₂).hom) := by
  dsimp [tensor_μ]
  have :
    (𝟙 (X₁ ⊗ X₂) ⊗ (λ_ (𝟙_ C)).inv) ≫
        (α_ X₁ X₂ (𝟙_ C ⊗ 𝟙_ C)).hom ≫ (𝟙 X₁ ⊗ (α_ X₂ (𝟙_ C) (𝟙_ C)).inv) =
      (α_ X₁ X₂ (𝟙_ C)).hom ≫ (𝟙 X₁ ⊗ (ρ_ X₂).inv ⊗ 𝟙 (𝟙_ C)) :=
    by pure_coherence
  slice_rhs 1 3 => rw [this]
  clear this
  slice_rhs 2 3 => rw [← tensor_comp, ← tensor_comp, comp_id, comp_id, rightUnitor_inv_braiding]
  simp only [assoc]
  coherence
#align category_theory.tensor_right_unitality CategoryTheory.tensor_right_unitality

/-
Diagram B6 from Proposition 1 of [Joyal and Street, *Braided monoidal categories*][Joyal_Street].
-/
theorem tensor_associativity_aux (W X Y Z : C) :
    ((β_ W X).hom ⊗ 𝟙 (Y ⊗ Z)) ≫
        (α_ X W (Y ⊗ Z)).hom ≫
          (𝟙 X ⊗ (α_ W Y Z).inv) ≫ (𝟙 X ⊗ (β_ (W ⊗ Y) Z).hom) ≫ (𝟙 X ⊗ (α_ Z W Y).inv) =
      (𝟙 (W ⊗ X) ⊗ (β_ Y Z).hom) ≫
        (α_ (W ⊗ X) Z Y).inv ≫
          ((α_ W X Z).hom ⊗ 𝟙 Y) ≫
            ((β_ W (X ⊗ Z)).hom ⊗ 𝟙 Y) ≫ ((α_ X Z W).hom ⊗ 𝟙 Y) ≫ (α_ X (Z ⊗ W) Y).hom := by
  slice_rhs 3 5 => rw [← tensor_comp, ← tensor_comp, hexagon_forward, tensor_comp, tensor_comp]
  slice_rhs 5 6 => rw [associator_naturality]
  slice_rhs 2 3 => rw [← associator_inv_naturality]
  slice_rhs 3 5 => rw [← pentagon_hom_inv]
  slice_rhs 1 2 => rw [tensor_id, id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
  slice_rhs 2 3 => rw [← tensor_id, associator_naturality]
  slice_rhs 3 5 => rw [← tensor_comp, ← tensor_comp, ← hexagon_reverse, tensor_comp, tensor_comp]
#align category_theory.tensor_associativity_aux CategoryTheory.tensor_associativity_aux

set_option maxHeartbeats 400000 in
theorem tensor_associativity (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C) :
    (tensor_μ C (X₁, X₂) (Y₁, Y₂) ⊗ 𝟙 (Z₁ ⊗ Z₂)) ≫
        tensor_μ C (X₁ ⊗ Y₁, X₂ ⊗ Y₂) (Z₁, Z₂) ≫ ((α_ X₁ Y₁ Z₁).hom ⊗ (α_ X₂ Y₂ Z₂).hom) =
      (α_ (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (Z₁ ⊗ Z₂)).hom ≫
        (𝟙 (X₁ ⊗ X₂) ⊗ tensor_μ C (Y₁, Y₂) (Z₁, Z₂)) ≫ tensor_μ C (X₁, X₂) (Y₁ ⊗ Z₁, Y₂ ⊗ Z₂) := by
  have :
    (α_ X₁ Y₁ Z₁).hom ⊗ (α_ X₂ Y₂ Z₂).hom =
      (α_ (X₁ ⊗ Y₁) Z₁ ((X₂ ⊗ Y₂) ⊗ Z₂)).hom ≫
        (𝟙 (X₁ ⊗ Y₁) ⊗ (α_ Z₁ (X₂ ⊗ Y₂) Z₂).inv) ≫
          (α_ X₁ Y₁ ((Z₁ ⊗ X₂ ⊗ Y₂) ⊗ Z₂)).hom ≫
            (𝟙 X₁ ⊗ (α_ Y₁ (Z₁ ⊗ X₂ ⊗ Y₂) Z₂).inv) ≫
              (α_ X₁ (Y₁ ⊗ Z₁ ⊗ X₂ ⊗ Y₂) Z₂).inv ≫
                ((𝟙 X₁ ⊗ 𝟙 Y₁ ⊗ (α_ Z₁ X₂ Y₂).inv) ⊗ 𝟙 Z₂) ≫
                  ((𝟙 X₁ ⊗ (α_ Y₁ (Z₁ ⊗ X₂) Y₂).inv) ⊗ 𝟙 Z₂) ≫
                    ((𝟙 X₁ ⊗ (α_ Y₁ Z₁ X₂).inv ⊗ 𝟙 Y₂) ⊗ 𝟙 Z₂) ≫
                      (α_ X₁ (((Y₁ ⊗ Z₁) ⊗ X₂) ⊗ Y₂) Z₂).hom ≫
                        (𝟙 X₁ ⊗ (α_ ((Y₁ ⊗ Z₁) ⊗ X₂) Y₂ Z₂).hom) ≫
                          (𝟙 X₁ ⊗ (α_ (Y₁ ⊗ Z₁) X₂ (Y₂ ⊗ Z₂)).hom) ≫
                            (α_ X₁ (Y₁ ⊗ Z₁) (X₂ ⊗ Y₂ ⊗ Z₂)).inv :=
    by pure_coherence
  rw [this]; clear this
  slice_lhs 2 4 => rw [tensor_μ_def₁]
  slice_lhs 4 5 => rw [← tensor_id, associator_naturality]
  slice_lhs 5 6 => rw [← tensor_comp, associator_inv_naturality, tensor_comp]
  slice_lhs 6 7 => rw [associator_inv_naturality]
  have :
    (α_ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) (Z₁ ⊗ Z₂)).hom ≫
        (𝟙 (X₁ ⊗ Y₁) ⊗ (α_ (X₂ ⊗ Y₂) Z₁ Z₂).inv) ≫
          (α_ X₁ Y₁ (((X₂ ⊗ Y₂) ⊗ Z₁) ⊗ Z₂)).hom ≫
            (𝟙 X₁ ⊗ (α_ Y₁ ((X₂ ⊗ Y₂) ⊗ Z₁) Z₂).inv) ≫ (α_ X₁ (Y₁ ⊗ (X₂ ⊗ Y₂) ⊗ Z₁) Z₂).inv =
      ((α_ X₁ Y₁ (X₂ ⊗ Y₂)).hom ⊗ 𝟙 (Z₁ ⊗ Z₂)) ≫
        ((𝟙 X₁ ⊗ (α_ Y₁ X₂ Y₂).inv) ⊗ 𝟙 (Z₁ ⊗ Z₂)) ≫
          (α_ (X₁ ⊗ (Y₁ ⊗ X₂) ⊗ Y₂) Z₁ Z₂).inv ≫
            ((α_ X₁ ((Y₁ ⊗ X₂) ⊗ Y₂) Z₁).hom ⊗ 𝟙 Z₂) ≫
              ((𝟙 X₁ ⊗ (α_ (Y₁ ⊗ X₂) Y₂ Z₁).hom) ⊗ 𝟙 Z₂) ≫
                ((𝟙 X₁ ⊗ (α_ Y₁ X₂ (Y₂ ⊗ Z₁)).hom) ⊗ 𝟙 Z₂) ≫
                  ((𝟙 X₁ ⊗ 𝟙 Y₁ ⊗ (α_ X₂ Y₂ Z₁).inv) ⊗ 𝟙 Z₂) :=
    by pure_coherence
  slice_lhs 2 6 => rw [this]
  clear this
  slice_lhs 1 3 => rw [← tensor_comp, ← tensor_comp, tensor_μ_def₁, tensor_comp, tensor_comp]
  slice_lhs 3 4 => rw [← tensor_id, associator_inv_naturality]
  slice_lhs 4 5 => rw [← tensor_comp, associator_naturality, tensor_comp]
  slice_lhs 5 6 =>
    rw [← tensor_comp, ← tensor_comp, associator_naturality, tensor_comp, tensor_comp]
  slice_lhs 6 10 =>
    rw [← tensor_comp, ← tensor_comp, ← tensor_comp, ← tensor_comp, ← tensor_comp, ← tensor_comp, ←
      tensor_comp, ← tensor_comp, tensor_id, tensor_associativity_aux, ← tensor_id, ←
      id_comp (𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁), ← id_comp (𝟙 Z₂ ≫ 𝟙 Z₂ ≫ 𝟙 Z₂ ≫ 𝟙 Z₂ ≫ 𝟙 Z₂),
      tensor_comp, tensor_comp, tensor_comp, tensor_comp, tensor_comp, tensor_comp, tensor_comp,
      tensor_comp, tensor_comp, tensor_comp]
  slice_lhs 11 12 =>
    rw [← tensor_comp, ← tensor_comp, Iso.hom_inv_id]
    simp
  simp only [assoc, id_comp]
  slice_lhs 10 11 =>
    rw [← tensor_comp, ← tensor_comp, ← tensor_comp, Iso.hom_inv_id]
    simp
  simp only [assoc, id_comp]
  slice_lhs 9 10 => rw [associator_naturality]
  slice_lhs 10 11 => rw [← tensor_comp, associator_naturality, tensor_comp]
  slice_lhs 11 13 => rw [tensor_id, ← tensor_μ_def₂]
  have :
    ((𝟙 X₁ ⊗ (α_ (X₂ ⊗ Y₁) Z₁ Y₂).inv) ⊗ 𝟙 Z₂) ≫
        ((𝟙 X₁ ⊗ (α_ X₂ Y₁ Z₁).hom ⊗ 𝟙 Y₂) ⊗ 𝟙 Z₂) ≫
          (α_ X₁ ((X₂ ⊗ Y₁ ⊗ Z₁) ⊗ Y₂) Z₂).hom ≫
            (𝟙 X₁ ⊗ (α_ (X₂ ⊗ Y₁ ⊗ Z₁) Y₂ Z₂).hom) ≫
              (𝟙 X₁ ⊗ (α_ X₂ (Y₁ ⊗ Z₁) (Y₂ ⊗ Z₂)).hom) ≫ (α_ X₁ X₂ ((Y₁ ⊗ Z₁) ⊗ Y₂ ⊗ Z₂)).inv =
      (α_ X₁ ((X₂ ⊗ Y₁) ⊗ Z₁ ⊗ Y₂) Z₂).hom ≫
        (𝟙 X₁ ⊗ (α_ (X₂ ⊗ Y₁) (Z₁ ⊗ Y₂) Z₂).hom) ≫
          (𝟙 X₁ ⊗ (α_ X₂ Y₁ ((Z₁ ⊗ Y₂) ⊗ Z₂)).hom) ≫
            (α_ X₁ X₂ (Y₁ ⊗ (Z₁ ⊗ Y₂) ⊗ Z₂)).inv ≫
              (𝟙 (X₁ ⊗ X₂) ⊗ 𝟙 Y₁ ⊗ (α_ Z₁ Y₂ Z₂).hom) ≫ (𝟙 (X₁ ⊗ X₂) ⊗ (α_ Y₁ Z₁ (Y₂ ⊗ Z₂)).inv) :=
    by pure_coherence
  slice_lhs 7 12 => rw [this]
  clear this
  slice_lhs 6 7 => rw [associator_naturality]
  slice_lhs 7 8 => rw [← tensor_comp, associator_naturality, tensor_comp]
  slice_lhs 8 9 => rw [← tensor_comp, associator_naturality, tensor_comp]
  slice_lhs 9 10 => rw [associator_inv_naturality]
  slice_lhs 10 12 => rw [← tensor_comp, ← tensor_comp, ← tensor_μ_def₂, tensor_comp, tensor_comp]
  dsimp
  coherence
#align category_theory.tensor_associativity CategoryTheory.tensor_associativity

/-- The tensor product functor from `C × C` to `C` as a monoidal functor. -/
@[simps!]
def tensorMonoidal : MonoidalFunctor (C × C) C :=
  { tensor C with
    ε := (λ_ (𝟙_ C)).inv
    μ := fun X Y => tensor_μ C X Y
    μ_natural := fun f g => tensor_μ_natural C f.1 f.2 g.1 g.2
    associativity := fun X Y Z => tensor_associativity C X.1 X.2 Y.1 Y.2 Z.1 Z.2
    left_unitality := fun ⟨X₁, X₂⟩ => tensor_left_unitality C X₁ X₂
    right_unitality := fun ⟨X₁, X₂⟩ => tensor_right_unitality C X₁ X₂
    μ_isIso := by dsimp [tensor_μ]; infer_instance }
#align category_theory.tensor_monoidal CategoryTheory.tensorMonoidal

theorem leftUnitor_monoidal (X₁ X₂ : C) :
    (λ_ X₁).hom ⊗ (λ_ X₂).hom =
      tensor_μ C (𝟙_ C, X₁) (𝟙_ C, X₂) ≫ ((λ_ (𝟙_ C)).hom ⊗ 𝟙 (X₁ ⊗ X₂)) ≫ (λ_ (X₁ ⊗ X₂)).hom := by
  dsimp [tensor_μ]
  have :
    (λ_ X₁).hom ⊗ (λ_ X₂).hom =
      (α_ (𝟙_ C) X₁ (𝟙_ C ⊗ X₂)).hom ≫
        (𝟙 (𝟙_ C) ⊗ (α_ X₁ (𝟙_ C) X₂).inv) ≫ (λ_ ((X₁ ⊗ 𝟙_ C) ⊗ X₂)).hom ≫ ((ρ_ X₁).hom ⊗ 𝟙 X₂) :=
    by pure_coherence
  rw [this]; clear this
  rw [← braiding_leftUnitor]
  slice_lhs 3 4 => rw [← id_comp (𝟙 X₂), tensor_comp]
  slice_lhs 3 4 => rw [← leftUnitor_naturality]
  coherence
#align category_theory.left_unitor_monoidal CategoryTheory.leftUnitor_monoidal

theorem rightUnitor_monoidal (X₁ X₂ : C) :
    (ρ_ X₁).hom ⊗ (ρ_ X₂).hom =
      tensor_μ C (X₁, 𝟙_ C) (X₂, 𝟙_ C) ≫ (𝟙 (X₁ ⊗ X₂) ⊗ (λ_ (𝟙_ C)).hom) ≫ (ρ_ (X₁ ⊗ X₂)).hom := by
  dsimp [tensor_μ]
  have :
    (ρ_ X₁).hom ⊗ (ρ_ X₂).hom =
      (α_ X₁ (𝟙_ C) (X₂ ⊗ 𝟙_ C)).hom ≫
        (𝟙 X₁ ⊗ (α_ (𝟙_ C) X₂ (𝟙_ C)).inv) ≫ (𝟙 X₁ ⊗ (ρ_ (𝟙_ C ⊗ X₂)).hom) ≫ (𝟙 X₁ ⊗ (λ_ X₂).hom) :=
    by pure_coherence
  rw [this]; clear this
  rw [← braiding_rightUnitor]
  slice_lhs 3 4 => rw [← id_comp (𝟙 X₁), tensor_comp, id_comp]
  slice_lhs 3 4 => rw [← tensor_comp, ← rightUnitor_naturality, tensor_comp]
  coherence
#align category_theory.right_unitor_monoidal CategoryTheory.rightUnitor_monoidal

theorem associator_monoidal_aux (W X Y Z : C) :
    (𝟙 W ⊗ (β_ X (Y ⊗ Z)).hom) ≫
        (𝟙 W ⊗ (α_ Y Z X).hom) ≫ (α_ W Y (Z ⊗ X)).inv ≫ ((β_ W Y).hom ⊗ 𝟙 (Z ⊗ X)) =
      (α_ W X (Y ⊗ Z)).inv ≫
        (α_ (W ⊗ X) Y Z).inv ≫
          ((β_ (W ⊗ X) Y).hom ⊗ 𝟙 Z) ≫
            ((α_ Y W X).inv ⊗ 𝟙 Z) ≫ (α_ (Y ⊗ W) X Z).hom ≫ (𝟙 (Y ⊗ W) ⊗ (β_ X Z).hom) := by
  slice_rhs 1 2 => rw [← pentagon_inv]
  slice_rhs 3 5 => rw [← tensor_comp, ← tensor_comp, hexagon_reverse, tensor_comp, tensor_comp]
  slice_rhs 5 6 => rw [associator_naturality]
  slice_rhs 6 7 => rw [tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  slice_rhs 2 3 => rw [← associator_inv_naturality]
  slice_rhs 3 5 => rw [pentagon_inv_inv_hom]
  slice_rhs 4 5 => rw [← tensor_id, ← associator_inv_naturality]
  slice_rhs 2 4 => rw [← tensor_comp, ← tensor_comp, ← hexagon_forward, tensor_comp, tensor_comp]
  simp
#align category_theory.associator_monoidal_aux CategoryTheory.associator_monoidal_aux

set_option maxHeartbeats 400000 in
theorem associator_monoidal (X₁ X₂ X₃ Y₁ Y₂ Y₃ : C) :
    tensor_μ C (X₁ ⊗ X₂, X₃) (Y₁ ⊗ Y₂, Y₃) ≫
        (tensor_μ C (X₁, X₂) (Y₁, Y₂) ⊗ 𝟙 (X₃ ⊗ Y₃)) ≫ (α_ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) (X₃ ⊗ Y₃)).hom =
      ((α_ X₁ X₂ X₃).hom ⊗ (α_ Y₁ Y₂ Y₃).hom) ≫
        tensor_μ C (X₁, X₂ ⊗ X₃) (Y₁, Y₂ ⊗ Y₃) ≫ (𝟙 (X₁ ⊗ Y₁) ⊗ tensor_μ C (X₂, X₃) (Y₂, Y₃)) := by
  have :
    (α_ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) (X₃ ⊗ Y₃)).hom =
      ((α_ X₁ Y₁ (X₂ ⊗ Y₂)).hom ⊗ 𝟙 (X₃ ⊗ Y₃)) ≫
        ((𝟙 X₁ ⊗ (α_ Y₁ X₂ Y₂).inv) ⊗ 𝟙 (X₃ ⊗ Y₃)) ≫
          (α_ (X₁ ⊗ (Y₁ ⊗ X₂) ⊗ Y₂) X₃ Y₃).inv ≫
            ((α_ X₁ ((Y₁ ⊗ X₂) ⊗ Y₂) X₃).hom ⊗ 𝟙 Y₃) ≫
              ((𝟙 X₁ ⊗ (α_ (Y₁ ⊗ X₂) Y₂ X₃).hom) ⊗ 𝟙 Y₃) ≫
                (α_ X₁ ((Y₁ ⊗ X₂) ⊗ Y₂ ⊗ X₃) Y₃).hom ≫
                  (𝟙 X₁ ⊗ (α_ (Y₁ ⊗ X₂) (Y₂ ⊗ X₃) Y₃).hom) ≫
                    (𝟙 X₁ ⊗ (α_ Y₁ X₂ ((Y₂ ⊗ X₃) ⊗ Y₃)).hom) ≫
                      (α_ X₁ Y₁ (X₂ ⊗ (Y₂ ⊗ X₃) ⊗ Y₃)).inv ≫
                        (𝟙 (X₁ ⊗ Y₁) ⊗ 𝟙 X₂ ⊗ (α_ Y₂ X₃ Y₃).hom) ≫
                          (𝟙 (X₁ ⊗ Y₁) ⊗ (α_ X₂ Y₂ (X₃ ⊗ Y₃)).inv) :=
    by pure_coherence
  rw [this]; clear this
  slice_lhs 2 4 => rw [← tensor_comp, ← tensor_comp, tensor_μ_def₁, tensor_comp, tensor_comp]
  slice_lhs 4 5 => rw [← tensor_id, associator_inv_naturality]
  slice_lhs 5 6 => rw [← tensor_comp, associator_naturality, tensor_comp]
  slice_lhs 6 7 =>
    rw [← tensor_comp, ← tensor_comp, associator_naturality, tensor_comp, tensor_comp]
  have :
    ((α_ X₁ X₂ (Y₁ ⊗ Y₂)).hom ⊗ 𝟙 (X₃ ⊗ Y₃)) ≫
        ((𝟙 X₁ ⊗ (α_ X₂ Y₁ Y₂).inv) ⊗ 𝟙 (X₃ ⊗ Y₃)) ≫
          (α_ (X₁ ⊗ (X₂ ⊗ Y₁) ⊗ Y₂) X₃ Y₃).inv ≫
            ((α_ X₁ ((X₂ ⊗ Y₁) ⊗ Y₂) X₃).hom ⊗ 𝟙 Y₃) ≫ ((𝟙 X₁ ⊗ (α_ (X₂ ⊗ Y₁) Y₂ X₃).hom) ⊗ 𝟙 Y₃) =
      (α_ (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (X₃ ⊗ Y₃)).hom ≫
        (𝟙 (X₁ ⊗ X₂) ⊗ (α_ (Y₁ ⊗ Y₂) X₃ Y₃).inv) ≫
          (α_ X₁ X₂ (((Y₁ ⊗ Y₂) ⊗ X₃) ⊗ Y₃)).hom ≫
            (𝟙 X₁ ⊗ (α_ X₂ ((Y₁ ⊗ Y₂) ⊗ X₃) Y₃).inv) ≫
              (α_ X₁ (X₂ ⊗ (Y₁ ⊗ Y₂) ⊗ X₃) Y₃).inv ≫
                ((𝟙 X₁ ⊗ 𝟙 X₂ ⊗ (α_ Y₁ Y₂ X₃).hom) ⊗ 𝟙 Y₃) ≫
                  ((𝟙 X₁ ⊗ (α_ X₂ Y₁ (Y₂ ⊗ X₃)).inv) ⊗ 𝟙 Y₃) :=
    by pure_coherence
  slice_lhs 2 6 => rw [this]
  clear this
  slice_lhs 1 3 => rw [tensor_μ_def₁]
  slice_lhs 3 4 => rw [← tensor_id, associator_naturality]
  slice_lhs 4 5 => rw [← tensor_comp, associator_inv_naturality, tensor_comp]
  slice_lhs 5 6 => rw [associator_inv_naturality]
  slice_lhs 6 9 =>
    rw [← tensor_comp, ← tensor_comp, ← tensor_comp, ← tensor_comp, ← tensor_comp, ← tensor_comp,
      tensor_id, associator_monoidal_aux, ← id_comp (𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁), ←
      id_comp (𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁), ← id_comp (𝟙 Y₃ ≫ 𝟙 Y₃ ≫ 𝟙 Y₃ ≫ 𝟙 Y₃), ←
      id_comp (𝟙 Y₃ ≫ 𝟙 Y₃ ≫ 𝟙 Y₃ ≫ 𝟙 Y₃ ≫ 𝟙 Y₃), tensor_comp, tensor_comp, tensor_comp,
      tensor_comp, tensor_comp, tensor_comp, tensor_comp, tensor_comp, tensor_comp, tensor_comp]
  slice_lhs 11 12 => rw [associator_naturality]
  slice_lhs 12 13 => rw [← tensor_comp, associator_naturality, tensor_comp]
  slice_lhs 13 14 => rw [← tensor_comp, ← tensor_id, associator_naturality, tensor_comp]
  slice_lhs 14 15 => rw [associator_inv_naturality]
  slice_lhs 15 17 =>
    rw [tensor_id, ← tensor_comp, ← tensor_comp, ← tensor_μ_def₂, tensor_comp, tensor_comp]
  have :
    ((𝟙 X₁ ⊗ (α_ Y₁ X₂ X₃).inv ⊗ 𝟙 Y₂) ⊗ 𝟙 Y₃) ≫
        ((𝟙 X₁ ⊗ (α_ (Y₁ ⊗ X₂) X₃ Y₂).hom) ⊗ 𝟙 Y₃) ≫
          (α_ X₁ ((Y₁ ⊗ X₂) ⊗ X₃ ⊗ Y₂) Y₃).hom ≫
            (𝟙 X₁ ⊗ (α_ (Y₁ ⊗ X₂) (X₃ ⊗ Y₂) Y₃).hom) ≫
              (𝟙 X₁ ⊗ (α_ Y₁ X₂ ((X₃ ⊗ Y₂) ⊗ Y₃)).hom) ≫
                (α_ X₁ Y₁ (X₂ ⊗ (X₃ ⊗ Y₂) ⊗ Y₃)).inv ≫
                  (𝟙 (X₁ ⊗ Y₁) ⊗ 𝟙 X₂ ⊗ (α_ X₃ Y₂ Y₃).hom) ≫
                    (𝟙 (X₁ ⊗ Y₁) ⊗ (α_ X₂ X₃ (Y₂ ⊗ Y₃)).inv) =
      (α_ X₁ ((Y₁ ⊗ X₂ ⊗ X₃) ⊗ Y₂) Y₃).hom ≫
        (𝟙 X₁ ⊗ (α_ (Y₁ ⊗ X₂ ⊗ X₃) Y₂ Y₃).hom) ≫
          (𝟙 X₁ ⊗ (α_ Y₁ (X₂ ⊗ X₃) (Y₂ ⊗ Y₃)).hom) ≫ (α_ X₁ Y₁ ((X₂ ⊗ X₃) ⊗ Y₂ ⊗ Y₃)).inv :=
    by pure_coherence
  slice_lhs 9 16 => rw [this]
  clear this
  slice_lhs 8 9 => rw [associator_naturality]
  slice_lhs 9 10 => rw [← tensor_comp, associator_naturality, tensor_comp]
  slice_lhs 10 12 => rw [tensor_id, ← tensor_μ_def₂]
  dsimp
  coherence
#align category_theory.associator_monoidal CategoryTheory.associator_monoidal

end Tensor

end CategoryTheory
