/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.CategoryTheory.CommSq

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

## References

* [Pavel Etingof, Shlomo Gelaki, Dmitri Nikshych, Victor Ostrik, *Tensor categories*][egno15]

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
  /-- The braiding natural isomorphism. -/
  braiding : ∀ X Y : C, X ⊗ Y ≅ Y ⊗ X
  braiding_naturality_right :
    ∀ (X : C) {Y Z : C} (f : Y ⟶ Z),
      X ◁ f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ f ▷ X := by
    aesop_cat
  braiding_naturality_left :
    ∀ {X Y : C} (f : X ⟶ Y) (Z : C),
      f ▷ Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f := by
    aesop_cat
  /-- The first hexagon identity. -/
  hexagon_forward :
    ∀ X Y Z : C,
      (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
        ((braiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (braiding X Z).hom) := by
    aesop_cat
  /-- The second hexagon identity. -/
  hexagon_reverse :
    ∀ X Y Z : C,
      (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
        (X ◁ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braiding X Z).hom ▷ Y) := by
    aesop_cat
#align category_theory.braided_category CategoryTheory.BraidedCategory

attribute [reassoc (attr := simp)]
  BraidedCategory.braiding_naturality_left
  BraidedCategory.braiding_naturality_right
attribute [reassoc] BraidedCategory.hexagon_forward BraidedCategory.hexagon_reverse

open Category

open MonoidalCategory

open BraidedCategory

@[inherit_doc]
notation "β_" => BraidedCategory.braiding

namespace BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory.{v} C]

@[simp, reassoc]
theorem braiding_tensor_left (X Y Z : C) :
    (β_ (X ⊗ Y) Z).hom  =
      (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).hom ≫ (α_ X Z Y).inv ≫
        (β_ X Z).hom ▷ Y ≫ (α_ Z X Y).hom := by
  apply (cancel_epi (α_ X Y Z).inv).1
  apply (cancel_mono (α_ Z X Y).inv).1
  simp [hexagon_reverse]

@[simp, reassoc]
theorem braiding_tensor_right (X Y Z : C) :
    (β_ X (Y ⊗ Z)).hom  =
      (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
        Y ◁ (β_ X Z).hom ≫ (α_ Y Z X).inv := by
  apply (cancel_epi (α_ X Y Z).hom).1
  apply (cancel_mono (α_ Y Z X).hom).1
  simp [hexagon_forward]

@[simp, reassoc]
theorem braiding_inv_tensor_left (X Y Z : C) :
    (β_ (X ⊗ Y) Z).inv  =
      (α_ Z X Y).inv ≫ (β_ X Z).inv ▷ Y ≫ (α_ X Z Y).hom ≫
        X ◁ (β_ Y Z).inv ≫ (α_ X Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[simp, reassoc]
theorem braiding_inv_tensor_right (X Y Z : C) :
    (β_ X (Y ⊗ Z)).inv  =
      (α_ Y Z X).hom ≫ Y ◁ (β_ X Z).inv ≫ (α_ Y X Z).inv ≫
        (β_ X Y).inv ▷ Z ≫ (α_ X Y Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem braiding_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ g) ≫ (braiding Y Y').hom = (braiding X X').hom ≫ (g ⊗ f) := by
  rw [tensorHom_def' f g, tensorHom_def g f]
  simp_rw [Category.assoc, braiding_naturality_left, braiding_naturality_right_assoc]

@[reassoc (attr := simp)]
theorem braiding_inv_naturality_right (X : C) {Y Z : C} (f : Y ⟶ Z) :
    X ◁ f ≫ (β_ Z X).inv = (β_ Y X).inv ≫ f ▷ X :=
  CommSq.w <| .vert_inv <| .mk <| braiding_naturality_left f X

@[reassoc (attr := simp)]
theorem braiding_inv_naturality_left {X Y : C} (f : X ⟶ Y) (Z : C) :
    f ▷ Z ≫ (β_ Z Y).inv = (β_ Z X).inv ≫ Z ◁ f :=
  CommSq.w <| .vert_inv <| .mk <| braiding_naturality_right Z f

@[reassoc (attr := simp)]
theorem braiding_inv_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ g) ≫ (β_ Y' Y).inv = (β_ X' X).inv ≫ (g ⊗ f) :=
  CommSq.w <| .vert_inv <| .mk <| braiding_naturality g f

@[reassoc]
theorem yang_baxter (X Y Z : C) :
    (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
    Y ◁ (β_ X Z).hom ≫ (α_ Y Z X).inv ≫ (β_ Y Z).hom ▷ X ≫ (α_ Z Y X).hom =
      X ◁ (β_ Y Z).hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫
      (α_ Z X Y).hom ≫ Z ◁ (β_ X Y).hom := by
  rw [← braiding_tensor_right_assoc X Y Z, ← cancel_mono (α_ Z Y X).inv]
  repeat rw [assoc]
  rw [Iso.hom_inv_id, comp_id, ← braiding_naturality_right, braiding_tensor_right]

theorem yang_baxter' (X Y Z : C) :
    (β_ X Y).hom ▷ Z ⊗≫ Y ◁ (β_ X Z).hom ⊗≫ (β_ Y Z).hom ▷ X =
      𝟙 _ ⊗≫ (X ◁ (β_ Y Z).hom ⊗≫ (β_ X Z).hom ▷ Y ⊗≫ Z ◁ (β_ X Y).hom) ⊗≫ 𝟙 _ := by
  rw [← cancel_epi (α_ X Y Z).inv, ← cancel_mono (α_ Z Y X).hom]
  convert yang_baxter X Y Z using 1
  all_goals coherence

theorem yang_baxter_iso (X Y Z : C) :
    (α_ X Y Z).symm ≪≫ whiskerRightIso (β_ X Y) Z ≪≫ α_ Y X Z ≪≫
    whiskerLeftIso Y (β_ X Z) ≪≫ (α_ Y Z X).symm ≪≫
    whiskerRightIso (β_ Y Z) X ≪≫ (α_ Z Y X) =
      whiskerLeftIso X (β_ Y Z) ≪≫ (α_ X Z Y).symm ≪≫
      whiskerRightIso (β_ X Z) Y ≪≫ α_ Z X Y ≪≫
      whiskerLeftIso Z (β_ X Y) := Iso.ext (yang_baxter X Y Z)

theorem hexagon_forward_iso (X Y Z : C) :
    α_ X Y Z ≪≫ β_ X (Y ⊗ Z) ≪≫ α_ Y Z X =
      whiskerRightIso (β_ X Y) Z ≪≫ α_ Y X Z ≪≫ whiskerLeftIso Y (β_ X Z) :=
  Iso.ext (hexagon_forward X Y Z)

theorem hexagon_reverse_iso (X Y Z : C) :
    (α_ X Y Z).symm ≪≫ β_ (X ⊗ Y) Z ≪≫ (α_ Z X Y).symm =
      whiskerLeftIso X (β_ Y Z) ≪≫ (α_ X Z Y).symm ≪≫ whiskerRightIso (β_ X Z) Y :=
  Iso.ext (hexagon_reverse X Y Z)

@[reassoc]
theorem hexagon_forward_inv (X Y Z : C) :
    (α_ Y Z X).inv ≫ (β_ X (Y ⊗ Z)).inv ≫ (α_ X Y Z).inv =
      Y ◁ (β_ X Z).inv ≫ (α_ Y X Z).inv ≫ (β_ X Y).inv ▷ Z := by
  simp

@[reassoc]
theorem hexagon_reverse_inv (X Y Z : C) :
    (α_ Z X Y).hom ≫ (β_ (X ⊗ Y) Z).inv ≫ (α_ X Y Z).hom =
      (β_ X Z).inv ▷ Y ≫ (α_ X Z Y).hom ≫ X ◁ (β_ Y Z).inv := by
  simp

end BraidedCategory

/--
Verifying the axioms for a braiding by checking that the candidate braiding is sent to a braiding
by a faithful monoidal functor.
-/
def braidedCategoryOfFaithful {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] (F : MonoidalFunctor C D) [F.Faithful] [BraidedCategory D]
    (β : ∀ X Y : C, X ⊗ Y ≅ Y ⊗ X)
    (w : ∀ X Y, F.μ _ _ ≫ F.map (β X Y).hom = (β_ _ _).hom ≫ F.μ _ _) : BraidedCategory C where
  braiding := β
  braiding_naturality_left := by
    intros
    apply F.map_injective
    refine (cancel_epi (F.μ ?_ ?_)).1 ?_
    rw [Functor.map_comp, ← LaxMonoidalFunctor.μ_natural_left_assoc, w, Functor.map_comp,
      reassoc_of% w, braiding_naturality_left_assoc, LaxMonoidalFunctor.μ_natural_right]
  braiding_naturality_right := by
    intros
    apply F.map_injective
    refine (cancel_epi (F.μ ?_ ?_)).1 ?_
    rw [Functor.map_comp, ← LaxMonoidalFunctor.μ_natural_right_assoc, w, Functor.map_comp,
      reassoc_of% w, braiding_naturality_right_assoc, LaxMonoidalFunctor.μ_natural_left]
  hexagon_forward := by
    intros
    apply F.map_injective
    refine (cancel_epi (F.μ _ _)).1 ?_
    refine (cancel_epi (F.μ _ _ ▷ _)).1 ?_
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, ←
      LaxMonoidalFunctor.μ_natural_left_assoc, ← comp_whiskerRight_assoc, w,
      comp_whiskerRight_assoc, LaxMonoidalFunctor.associativity_assoc,
      LaxMonoidalFunctor.associativity_assoc, ← LaxMonoidalFunctor.μ_natural_right, ←
      MonoidalCategory.whiskerLeft_comp_assoc, w, MonoidalCategory.whiskerLeft_comp_assoc,
      reassoc_of% w, braiding_naturality_right_assoc,
      LaxMonoidalFunctor.associativity, hexagon_forward_assoc]
  hexagon_reverse := by
    intros
    apply F.toFunctor.map_injective
    refine (cancel_epi (F.μ _ _)).1 ?_
    refine (cancel_epi (_ ◁ F.μ _ _)).1 ?_
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, ←
      LaxMonoidalFunctor.μ_natural_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, w,
      MonoidalCategory.whiskerLeft_comp_assoc, LaxMonoidalFunctor.associativity_inv_assoc,
      LaxMonoidalFunctor.associativity_inv_assoc, ← LaxMonoidalFunctor.μ_natural_left,
      ← comp_whiskerRight_assoc, w, comp_whiskerRight_assoc, reassoc_of% w,
      braiding_naturality_left_assoc, LaxMonoidalFunctor.associativity_inv, hexagon_reverse_assoc]
#align category_theory.braided_category_of_faithful CategoryTheory.braidedCategoryOfFaithful

/-- Pull back a braiding along a fully faithful monoidal functor. -/
noncomputable def braidedCategoryOfFullyFaithful {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : MonoidalFunctor C D) [F.Full]
    [F.Faithful] [BraidedCategory D] : BraidedCategory C :=
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
        (𝟙_ C ◁ (β_ X (𝟙_ C)).inv) ≫ (α_ _ X _).inv ≫ ((λ_ X).hom ▷ _) =
      ((λ_ _).hom ▷ X) ≫ (β_ X (𝟙_ C)).inv := by
  coherence
#align category_theory.braiding_left_unitor_aux₁ CategoryTheory.braiding_leftUnitor_aux₁

theorem braiding_leftUnitor_aux₂ (X : C) :
    ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ ((λ_ X).hom ▷ 𝟙_ C) = (ρ_ X).hom ▷ 𝟙_ C :=
  calc
    ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ ((λ_ X).hom ▷ 𝟙_ C) =
      ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫ ((λ_ X).hom ▷ 𝟙_ C) := by
      coherence
    _ = ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ (α_ _ _ _).hom ≫ (_ ◁ (β_ X _).hom) ≫
          (_ ◁ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫ ((λ_ X).hom ▷ 𝟙_ C) := by
      simp
    _ = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ (α_ _ _ _).hom ≫ (_ ◁ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫
          ((λ_ X).hom ▷ 𝟙_ C) := by
      (slice_lhs 1 3 => rw [← hexagon_forward]); simp only [assoc]
    _ = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ ((λ_ _).hom ▷ X) ≫ (β_ X _).inv := by
      rw [braiding_leftUnitor_aux₁]
    _ = (α_ _ _ _).hom ≫ (_ ◁ (λ_ _).hom) ≫ (β_ _ _).hom ≫ (β_ X _).inv := by
      (slice_lhs 2 3 => rw [← braiding_naturality_right]); simp only [assoc]
    _ = (α_ _ _ _).hom ≫ (_ ◁ (λ_ _).hom) := by rw [Iso.hom_inv_id, comp_id]
    _ = (ρ_ X).hom ▷ 𝟙_ C := by rw [triangle]
#align category_theory.braiding_left_unitor_aux₂ CategoryTheory.braiding_leftUnitor_aux₂

@[reassoc]
theorem braiding_leftUnitor (X : C) : (β_ X (𝟙_ C)).hom ≫ (λ_ X).hom = (ρ_ X).hom := by
  rw [← whiskerRight_iff, comp_whiskerRight, braiding_leftUnitor_aux₂]
#align category_theory.braiding_left_unitor CategoryTheory.braiding_leftUnitor

theorem braiding_rightUnitor_aux₁ (X : C) :
    (α_ X (𝟙_ C) (𝟙_ C)).inv ≫
        ((β_ (𝟙_ C) X).inv ▷ 𝟙_ C) ≫ (α_ _ X _).hom ≫ (_ ◁ (ρ_ X).hom) =
      (X ◁ (ρ_ _).hom) ≫ (β_ (𝟙_ C) X).inv := by
  coherence
#align category_theory.braiding_right_unitor_aux₁ CategoryTheory.braiding_rightUnitor_aux₁

theorem braiding_rightUnitor_aux₂ (X : C) :
    (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (𝟙_ C ◁ (ρ_ X).hom) = 𝟙_ C ◁ (λ_ X).hom :=
  calc
    (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (𝟙_ C ◁ (ρ_ X).hom) =
      (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).hom ≫ (𝟙_ C ◁ (ρ_ X).hom) := by
      coherence
    _ = (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ ((β_ _ X).hom ▷ _) ≫
          ((β_ _ X).inv ▷ _) ≫ (α_ _ _ _).hom ≫ (𝟙_ C ◁ (ρ_ X).hom) := by
      simp
    _ = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (α_ _ _ _).inv ≫ ((β_ _ X).inv ▷ _) ≫ (α_ _ _ _).hom ≫
          (𝟙_ C ◁ (ρ_ X).hom) := by
      (slice_lhs 1 3 => rw [← hexagon_reverse]); simp only [assoc]
    _ = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (X ◁ (ρ_ _).hom) ≫ (β_ _ X).inv := by
      rw [braiding_rightUnitor_aux₁]
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).hom ▷ _) ≫ (β_ _ X).hom ≫ (β_ _ _).inv := by
      (slice_lhs 2 3 => rw [← braiding_naturality_left]); simp only [assoc]
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).hom ▷ _) := by rw [Iso.hom_inv_id, comp_id]
    _ = 𝟙_ C ◁ (λ_ X).hom := by rw [triangle_assoc_comp_right]
#align category_theory.braiding_right_unitor_aux₂ CategoryTheory.braiding_rightUnitor_aux₂

@[reassoc]
theorem braiding_rightUnitor (X : C) : (β_ (𝟙_ C) X).hom ≫ (ρ_ X).hom = (λ_ X).hom := by
  rw [← whiskerLeft_iff, MonoidalCategory.whiskerLeft_comp, braiding_rightUnitor_aux₂]
#align category_theory.braiding_right_unitor CategoryTheory.braiding_rightUnitor

@[reassoc, simp]
theorem braiding_tensorUnit_left (X : C) : (β_ (𝟙_ C) X).hom = (λ_ X).hom ≫ (ρ_ X).inv := by
  simp [← braiding_rightUnitor]

@[reassoc, simp]
theorem braiding_inv_tensorUnit_left (X : C) : (β_ (𝟙_ C) X).inv = (ρ_ X).hom ≫ (λ_ X).inv := by
  rw [Iso.inv_ext]
  rw [braiding_tensorUnit_left]
  coherence

@[reassoc]
theorem leftUnitor_inv_braiding (X : C) : (λ_ X).inv ≫ (β_ (𝟙_ C) X).hom = (ρ_ X).inv := by
  simp
#align category_theory.left_unitor_inv_braiding CategoryTheory.leftUnitor_inv_braiding

@[reassoc]
theorem rightUnitor_inv_braiding (X : C) : (ρ_ X).inv ≫ (β_ X (𝟙_ C)).hom = (λ_ X).inv := by
  apply (cancel_mono (λ_ X).hom).1
  simp only [assoc, braiding_leftUnitor, Iso.inv_hom_id]
#align category_theory.right_unitor_inv_braiding CategoryTheory.rightUnitor_inv_braiding

@[reassoc, simp]
theorem braiding_tensorUnit_right (X : C) : (β_ X (𝟙_ C)).hom = (ρ_ X).hom ≫ (λ_ X).inv := by
  simp [← rightUnitor_inv_braiding]

@[reassoc, simp]
theorem braiding_inv_tensorUnit_right (X : C) : (β_ X (𝟙_ C)).inv = (λ_ X).hom ≫ (ρ_ X).inv := by
  rw [Iso.inv_ext]
  rw [braiding_tensorUnit_right]
  coherence

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

lemma SymmetricCategory.braiding_swap_eq_inv_braiding {C : Type u₁}
    [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C] (X Y : C) :
    (β_ Y X).hom = (β_ X Y).inv := Iso.inv_ext' (symmetry X Y)

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
lemma ext' {F G : LaxBraidedFunctor C D} {α β : F ⟶ G} (w : ∀ X : C, α.app X = β.app X) : α = β :=
  MonoidalNatTrans.ext _ _ (funext w)

@[simp]
theorem comp_toNatTrans {F G H : LaxBraidedFunctor C D} {α : F ⟶ G} {β : G ⟶ H} :
    (α ≫ β).toNatTrans = @CategoryStruct.comp (C ⥤ D) _ _ _ _ α.toNatTrans β.toNatTrans :=
  rfl
#align category_theory.lax_braided_functor.comp_to_nat_trans CategoryTheory.LaxBraidedFunctor.comp_toNatTrans

/-- Interpret a natural isomorphism of the underlying lax monoidal functors as an
isomorphism of the lax braided monoidal functors.
-/
@[simps]
def mkIso {F G : LaxBraidedFunctor C D} (i : F.toLaxMonoidalFunctor ≅ G.toLaxMonoidalFunctor) :
    F ≅ G :=
  { i with }
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
    [F.Faithful] : SymmetricCategory C where
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
lemma ext' {F G : BraidedFunctor C D} {α β : F ⟶ G} (w : ∀ X : C, α.app X = β.app X) : α = β :=
  MonoidalNatTrans.ext _ _ (funext w)

@[simp]
theorem comp_toNatTrans {F G H : BraidedFunctor C D} {α : F ⟶ G} {β : G ⟶ H} :
    (α ≫ β).toNatTrans = @CategoryStruct.comp (C ⥤ D) _ _ _ _ α.toNatTrans β.toNatTrans :=
  rfl
#align category_theory.braided_functor.comp_to_nat_trans CategoryTheory.BraidedFunctor.comp_toNatTrans

/-- Interpret a natural isomorphism of the underlying monoidal functors as an
isomorphism of the braided monoidal functors.
-/
@[simps]
def mkIso {F G : BraidedFunctor C D} (i : F.toMonoidalFunctor ≅ G.toMonoidalFunctor) : F ≅ G :=
  { i with }
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
def tensor_μ (X Y : C × C) : (X.1 ⊗ X.2) ⊗ Y.1 ⊗ Y.2 ⟶ (X.1 ⊗ Y.1) ⊗ X.2 ⊗ Y.2 :=
  (α_ X.1 X.2 (Y.1 ⊗ Y.2)).hom ≫
    (X.1 ◁ (α_ X.2 Y.1 Y.2).inv) ≫
      (X.1 ◁ (β_ X.2 Y.1).hom ▷ Y.2) ≫
        (X.1 ◁ (α_ Y.1 X.2 Y.2).hom) ≫ (α_ X.1 Y.1 (X.2 ⊗ Y.2)).inv
#align category_theory.tensor_μ CategoryTheory.tensor_μ

@[reassoc]
theorem tensor_μ_natural {X₁ X₂ Y₁ Y₂ U₁ U₂ V₁ V₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : U₁ ⟶ V₁)
    (g₂ : U₂ ⟶ V₂) :
    ((f₁ ⊗ f₂) ⊗ g₁ ⊗ g₂) ≫ tensor_μ C (Y₁, Y₂) (V₁, V₂) =
      tensor_μ C (X₁, X₂) (U₁, U₂) ≫ ((f₁ ⊗ g₁) ⊗ f₂ ⊗ g₂) := by
  dsimp only [tensor_μ]
  simp_rw [← id_tensorHom, ← tensorHom_id]
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

@[reassoc]
theorem tensor_μ_natural_left {X₁ X₂ Y₁ Y₂ : C} (f₁: X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (Z₁ Z₂ : C) :
    (f₁ ⊗ f₂) ▷ (Z₁ ⊗ Z₂) ≫ tensor_μ C (Y₁, Y₂) (Z₁, Z₂) =
      tensor_μ C (X₁, X₂) (Z₁, Z₂) ≫ (f₁ ▷ Z₁ ⊗ f₂ ▷ Z₂) := by
  convert tensor_μ_natural C f₁ f₂ (𝟙 Z₁) (𝟙 Z₂) using 1 <;> simp

@[reassoc]
theorem tensor_μ_natural_right (Z₁ Z₂ : C) {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    (Z₁ ⊗ Z₂) ◁ (f₁ ⊗ f₂) ≫ tensor_μ C (Z₁, Z₂) (Y₁, Y₂) =
      tensor_μ C (Z₁, Z₂) (X₁, X₂) ≫ (Z₁ ◁ f₁ ⊗ Z₂ ◁ f₂) := by
  convert tensor_μ_natural C (𝟙 Z₁) (𝟙 Z₂) f₁ f₂ using 1 <;> simp

@[reassoc]
theorem tensor_left_unitality (X₁ X₂ : C) :
    (λ_ (X₁ ⊗ X₂)).hom =
      ((λ_ (𝟙_ C)).inv ▷ (X₁ ⊗ X₂)) ≫
        tensor_μ C (𝟙_ C, 𝟙_ C) (X₁, X₂) ≫ ((λ_ X₁).hom ⊗ (λ_ X₂).hom) := by
  dsimp only [tensor_μ]
  have :
    ((λ_ (𝟙_ C)).inv ▷ (X₁ ⊗ X₂)) ≫
        (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫ (𝟙_ C ◁ (α_ (𝟙_ C) X₁ X₂).inv) =
      𝟙_ C ◁ (λ_ X₁).inv ▷ X₂ := by
    coherence
  slice_rhs 1 3 => rw [this]
  clear this
  slice_rhs 1 2 => rw [← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight,
    leftUnitor_inv_braiding]
  simp [tensorHom_id, id_tensorHom, tensorHom_def]
#align category_theory.tensor_left_unitality CategoryTheory.tensor_left_unitality

@[reassoc]
theorem tensor_right_unitality (X₁ X₂ : C) :
    (ρ_ (X₁ ⊗ X₂)).hom =
      ((X₁ ⊗ X₂) ◁ (λ_ (𝟙_ C)).inv) ≫
        tensor_μ C (X₁, X₂) (𝟙_ C, 𝟙_ C) ≫ ((ρ_ X₁).hom ⊗ (ρ_ X₂).hom) := by
  dsimp only [tensor_μ]
  have :
    ((X₁ ⊗ X₂) ◁ (λ_ (𝟙_ C)).inv) ≫
        (α_ X₁ X₂ (𝟙_ C ⊗ 𝟙_ C)).hom ≫ (X₁ ◁ (α_ X₂ (𝟙_ C) (𝟙_ C)).inv) =
      (α_ X₁ X₂ (𝟙_ C)).hom ≫ (X₁ ◁ (ρ_ X₂).inv ▷ 𝟙_ C) := by
    coherence
  slice_rhs 1 3 => rw [this]
  clear this
  slice_rhs 2 3 => rw [← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight,
    rightUnitor_inv_braiding]
  simp [tensorHom_id, id_tensorHom, tensorHom_def]
#align category_theory.tensor_right_unitality CategoryTheory.tensor_right_unitality

theorem tensor_associativity (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C) :
    (tensor_μ C (X₁, X₂) (Y₁, Y₂) ▷ (Z₁ ⊗ Z₂)) ≫
        tensor_μ C (X₁ ⊗ Y₁, X₂ ⊗ Y₂) (Z₁, Z₂) ≫ ((α_ X₁ Y₁ Z₁).hom ⊗ (α_ X₂ Y₂ Z₂).hom) =
      (α_ (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (Z₁ ⊗ Z₂)).hom ≫
        ((X₁ ⊗ X₂) ◁ tensor_μ C (Y₁, Y₂) (Z₁, Z₂)) ≫ tensor_μ C (X₁, X₂) (Y₁ ⊗ Z₁, Y₂ ⊗ Z₂) := by
  dsimp only [tensor_obj, prodMonoidal_tensorObj, tensor_μ]
  simp only [whiskerRight_tensor, comp_whiskerRight, whisker_assoc, assoc, Iso.inv_hom_id_assoc,
    tensor_whiskerLeft, braiding_tensor_left, MonoidalCategory.whiskerLeft_comp,
    braiding_tensor_right]
  calc
    _ = 𝟙 _ ⊗≫
      X₁ ◁ ((β_ X₂ Y₁).hom ▷ (Y₂ ⊗ Z₁) ≫ (Y₁ ⊗ X₂) ◁ (β_ Y₂ Z₁).hom) ▷ Z₂ ⊗≫
        X₁ ◁ Y₁ ◁ (β_ X₂ Z₁).hom ▷ Y₂ ▷ Z₂ ⊗≫ 𝟙 _ := by coherence
    _ = _ := by rw [← whisker_exchange]; coherence
#align category_theory.tensor_associativity CategoryTheory.tensor_associativity

-- We got a timeout if `reassoc` was at the declaration, so we put it here instead.
attribute [reassoc] tensor_associativity

/-- The tensor product functor from `C × C` to `C` as a monoidal functor. -/
@[simps!]
def tensorMonoidal : MonoidalFunctor (C × C) C :=
  { tensor C with
    ε := (λ_ (𝟙_ C)).inv
    μ := tensor_μ C
    μ_natural_left := fun f Z => by
      -- `simpa` will be not needed when we define `μ_natural_left` in terms of the whiskerings.
      simpa using tensor_μ_natural_left C f.1 f.2 Z.1 Z.2
    μ_natural_right := fun Z f => by
      simpa using tensor_μ_natural_right C Z.1 Z.2 f.1 f.2
    associativity := fun X Y Z => by
      simpa using tensor_associativity C X.1 X.2 Y.1 Y.2 Z.1 Z.2
    left_unitality := fun ⟨X₁, X₂⟩ => by
      simpa using tensor_left_unitality C X₁ X₂
    right_unitality := fun ⟨X₁, X₂⟩ => by
      simpa using tensor_right_unitality C X₁ X₂
    μ_isIso := by dsimp [tensor_μ]; infer_instance }

@[reassoc]
theorem leftUnitor_monoidal (X₁ X₂ : C) :
    (λ_ X₁).hom ⊗ (λ_ X₂).hom =
      tensor_μ C (𝟙_ C, X₁) (𝟙_ C, X₂) ≫ ((λ_ (𝟙_ C)).hom ▷ (X₁ ⊗ X₂)) ≫ (λ_ (X₁ ⊗ X₂)).hom := by
  dsimp only [tensor_μ]
  have :
    (λ_ X₁).hom ⊗ (λ_ X₂).hom =
      (α_ (𝟙_ C) X₁ (𝟙_ C ⊗ X₂)).hom ≫
        (𝟙_ C ◁ (α_ X₁ (𝟙_ C) X₂).inv) ≫ (λ_ ((X₁ ⊗ 𝟙_ C) ⊗ X₂)).hom ≫ ((ρ_ X₁).hom ▷ X₂) := by
    coherence
  rw [this]; clear this
  rw [← braiding_leftUnitor]
  dsimp only [tensor_obj, prodMonoidal_tensorObj]
  coherence
#align category_theory.left_unitor_monoidal CategoryTheory.leftUnitor_monoidal

@[reassoc]
theorem rightUnitor_monoidal (X₁ X₂ : C) :
    (ρ_ X₁).hom ⊗ (ρ_ X₂).hom =
      tensor_μ C (X₁, 𝟙_ C) (X₂, 𝟙_ C) ≫ ((X₁ ⊗ X₂) ◁ (λ_ (𝟙_ C)).hom) ≫ (ρ_ (X₁ ⊗ X₂)).hom := by
  dsimp only [tensor_μ]
  have :
    (ρ_ X₁).hom ⊗ (ρ_ X₂).hom =
      (α_ X₁ (𝟙_ C) (X₂ ⊗ 𝟙_ C)).hom ≫
        (X₁ ◁ (α_ (𝟙_ C) X₂ (𝟙_ C)).inv) ≫ (X₁ ◁ (ρ_ (𝟙_ C ⊗ X₂)).hom) ≫ (X₁ ◁ (λ_ X₂).hom) := by
    coherence
  rw [this]; clear this
  rw [← braiding_rightUnitor]
  dsimp only [tensor_obj, prodMonoidal_tensorObj]
  coherence
#align category_theory.right_unitor_monoidal CategoryTheory.rightUnitor_monoidal

theorem associator_monoidal (X₁ X₂ X₃ Y₁ Y₂ Y₃ : C) :
    tensor_μ C (X₁ ⊗ X₂, X₃) (Y₁ ⊗ Y₂, Y₃) ≫
        (tensor_μ C (X₁, X₂) (Y₁, Y₂) ▷ (X₃ ⊗ Y₃)) ≫ (α_ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) (X₃ ⊗ Y₃)).hom =
      ((α_ X₁ X₂ X₃).hom ⊗ (α_ Y₁ Y₂ Y₃).hom) ≫
        tensor_μ C (X₁, X₂ ⊗ X₃) (Y₁, Y₂ ⊗ Y₃) ≫ ((X₁ ⊗ Y₁) ◁ tensor_μ C (X₂, X₃) (Y₂, Y₃)) := by
  dsimp only [tensor_μ]
  calc
    _ = 𝟙 _ ⊗≫ X₁ ◁ X₂ ◁ (β_ X₃ Y₁).hom ▷ Y₂ ▷ Y₃ ⊗≫
      X₁ ◁ ((X₂ ⊗ Y₁) ◁ (β_ X₃ Y₂).hom ≫
        (β_ X₂ Y₁).hom ▷ (Y₂ ⊗ X₃)) ▷ Y₃ ⊗≫ 𝟙 _ := by simp; coherence
    _ = _ := by rw [whisker_exchange]; simp; coherence
#align category_theory.associator_monoidal CategoryTheory.associator_monoidal

-- We got a timeout if `reassoc` was at the declaration, so we put it here instead.
attribute [reassoc] associator_monoidal

end Tensor

instance : BraidedCategory Cᵒᵖ where
  braiding X Y := (β_ Y.unop X.unop).op
  braiding_naturality_right X {_ _} f := Quiver.Hom.unop_inj <| by simp
  braiding_naturality_left {_ _} f Z := Quiver.Hom.unop_inj <| by simp

section OppositeLemmas

open Opposite

@[simp] lemma op_braiding (X Y : C) : (β_ X Y).op = β_ (op Y) (op X) := rfl
@[simp] lemma unop_braiding (X Y : Cᵒᵖ) : (β_ X Y).unop = β_ (unop Y) (unop X) := rfl

@[simp] lemma op_hom_braiding (X Y : C) : (β_ X Y).hom.op = (β_ (op Y) (op X)).hom := rfl
@[simp] lemma unop_hom_braiding (X Y : Cᵒᵖ) : (β_ X Y).hom.unop = (β_ (unop Y) (unop X)).hom := rfl

@[simp] lemma op_inv_braiding (X Y : C) : (β_ X Y).inv.op = (β_ (op Y) (op X)).inv := rfl
@[simp] lemma unop_inv_braiding (X Y : Cᵒᵖ) : (β_ X Y).inv.unop = (β_ (unop Y) (unop X)).inv := rfl

end OppositeLemmas

namespace MonoidalOpposite

instance instBraiding : BraidedCategory Cᴹᵒᵖ where
  braiding X Y := (β_ Y.unmop X.unmop).mop
  braiding_naturality_right X {_ _} f := Quiver.Hom.unmop_inj <| by simp
  braiding_naturality_left {_ _} f Z := Quiver.Hom.unmop_inj <| by simp

section MonoidalOppositeLemmas

@[simp] lemma mop_braiding (X Y : C) : (β_ X Y).mop = β_ (mop Y) (mop X) := rfl
@[simp] lemma unmop_braiding (X Y : Cᴹᵒᵖ) : (β_ X Y).unmop = β_ (unmop Y) (unmop X) := rfl

@[simp] lemma mop_hom_braiding (X Y : C) : (β_ X Y).hom.mop = (β_ (mop Y) (mop X)).hom := rfl
@[simp]
lemma unmop_hom_braiding (X Y : Cᴹᵒᵖ) : (β_ X Y).hom.unmop = (β_ (unmop Y) (unmop X)).hom := rfl

@[simp] lemma mop_inv_braiding (X Y : C) : (β_ X Y).inv.mop = (β_ (mop Y) (mop X)).inv := rfl
@[simp]
lemma unmop_inv_braiding (X Y : Cᴹᵒᵖ) : (β_ X Y).inv.unmop = (β_ (unmop Y) (unmop X)).inv := rfl

end MonoidalOppositeLemmas

/-- The identity functor on `C`, viewed as a functor from `C` to its
monoidal opposite, upgraded to a braided functor. -/
@[simps!] def mopBraidedFunctor : BraidedFunctor C Cᴹᵒᵖ where
  μ X Y := (β_ (mop X) (mop Y)).hom
  ε := 𝟙 (𝟙_ Cᴹᵒᵖ)
  -- we could make this fully automated if we mark `← yang_baxter_assoc` as simp
  -- should it be marked as such?
  associativity X Y Z := by
    simp [← yang_baxter_assoc]
  __ := mopFunctor C

/-- The identity functor on `C`, viewed as a functor from the
monoidal opposite of `C` to `C`, upgraded to a braided functor. -/
@[simps!] def unmopBraidedFunctor : BraidedFunctor Cᴹᵒᵖ C where
  μ X Y := (β_ (unmop X) (unmop Y)).hom
  ε := 𝟙 (𝟙_ C)
  associativity X Y Z := by
    simp [← yang_baxter_assoc]
  __ := unmopFunctor C

end MonoidalOpposite

/-- The braided monoidal category obtained from `C` by replacing its braiding
`β_ X Y : X ⊗ Y ≅ Y ⊗ X` with the inverse `(β_ Y X)⁻¹ : X ⊗ Y ≅ Y ⊗ X`.
This corresponds to the automorphism of the braid group swapping
over-crossings and under-crossings. -/
abbrev reverseBraiding : BraidedCategory C where
  braiding X Y := (β_ Y X).symm
  braiding_naturality_right X {_ _} f := by simp
  braiding_naturality_left {_ _} f Z := by simp

lemma SymmetricCategory.reverseBraiding_eq (C : Type u₁) [Category.{v₁} C]
    [MonoidalCategory C] [i : SymmetricCategory C] :
    reverseBraiding C = i.toBraidedCategory := by
  dsimp only [reverseBraiding]
  congr
  funext X Y
  exact Iso.ext (braiding_swap_eq_inv_braiding Y X).symm

/-- The identity functor from `C` to `C`, where the codomain is given the
reversed braiding, upgraded to a braided functor. -/
def SymmetricCategory.equivReverseBraiding (C : Type u₁) [Category.{v₁} C]
    [MonoidalCategory C] [SymmetricCategory C] :=
  @BraidedFunctor.mk C _ _ _ C _ _ (reverseBraiding C) (.id C) <| by
    intros; simp [reverseBraiding, braiding_swap_eq_inv_braiding]

end CategoryTheory
