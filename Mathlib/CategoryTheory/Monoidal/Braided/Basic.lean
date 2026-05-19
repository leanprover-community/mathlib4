/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Discrete
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import Mathlib.CategoryTheory.CommSq

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

@[expose] public section



universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

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
    cat_disch
  braiding_naturality_left :
    ∀ {X Y : C} (f : X ⟶ Y) (Z : C),
      f ▷ Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f := by
    cat_disch
  /-- The first hexagon identity. -/
  hexagon_forward :
    ∀ X Y Z : C,
      (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
        ((braiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (braiding X Z).hom) := by
    cat_disch
  /-- The second hexagon identity. -/
  hexagon_reverse :
    ∀ X Y Z : C,
      (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
        (X ◁ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braiding X Z).hom ▷ Y) := by
    cat_disch

attribute [reassoc (attr := simp)]
  BraidedCategory.braiding_naturality_left
  BraidedCategory.braiding_naturality_right
attribute [reassoc] BraidedCategory.hexagon_forward BraidedCategory.hexagon_reverse

open BraidedCategory

@[inherit_doc]
notation "β_" => BraidedCategory.braiding

namespace BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory.{v} C]

@[simp, reassoc]
theorem braiding_tensor_left_hom (X Y Z : C) :
    (β_ (X ⊗ Y) Z).hom =
      (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).hom ≫ (α_ X Z Y).inv ≫
        (β_ X Z).hom ▷ Y ≫ (α_ Z X Y).hom := by
  apply (cancel_epi (α_ X Y Z).inv).1
  apply (cancel_mono (α_ Z X Y).inv).1
  simp [hexagon_reverse]

@[simp, reassoc]
theorem braiding_tensor_right_hom (X Y Z : C) :
    (β_ X (Y ⊗ Z)).hom =
      (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
        Y ◁ (β_ X Z).hom ≫ (α_ Y Z X).inv := by
  apply (cancel_epi (α_ X Y Z).hom).1
  apply (cancel_mono (α_ Y Z X).hom).1
  simp [hexagon_forward]

@[simp, reassoc]
theorem braiding_tensor_left_inv (X Y Z : C) :
    (β_ (X ⊗ Y) Z).inv =
      (α_ Z X Y).inv ≫ (β_ X Z).inv ▷ Y ≫ (α_ X Z Y).hom ≫
        X ◁ (β_ Y Z).inv ≫ (α_ X Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[simp, reassoc]
theorem braiding_tensor_right_inv (X Y Z : C) :
    (β_ X (Y ⊗ Z)).inv =
      (α_ Y Z X).hom ≫ Y ◁ (β_ X Z).inv ≫ (α_ Y X Z).inv ≫
        (β_ X Y).inv ▷ Z ≫ (α_ X Y Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
theorem braiding_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ₘ g) ≫ (braiding Y Y').hom = (braiding X X').hom ≫ (g ⊗ₘ f) := by
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
    (f ⊗ₘ g) ≫ (β_ Y' Y).inv = (β_ X' X).inv ≫ (g ⊗ₘ f) :=
  CommSq.w <| .vert_inv <| .mk <| braiding_naturality g f

set_option backward.defeqAttrib.useBackward true in
/-- In a braided monoidal category, the functors `tensorLeft X` and
`tensorRight X` are isomorphic. -/
@[simps]
def tensorLeftIsoTensorRight (X : C) :
    tensorLeft X ≅ tensorRight X where
  hom := { app Y := (β_ X Y).hom }
  inv := { app Y := (β_ X Y).inv }

set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-- The braiding isomorphism as a natural isomorphism of bifunctors `C ⥤ C ⥤ C`. -/
@[simps!]
def curriedBraidingNatIso : curriedTensor C ≅ (curriedTensor C).flip :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ β_ X Y))

@[reassoc]
theorem yang_baxter (X Y Z : C) :
    (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
    Y ◁ (β_ X Z).hom ≫ (α_ Y Z X).inv ≫ (β_ Y Z).hom ▷ X ≫ (α_ Z Y X).hom =
      X ◁ (β_ Y Z).hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫
      (α_ Z X Y).hom ≫ Z ◁ (β_ X Y).hom := by
  rw [← braiding_tensor_right_hom_assoc X Y Z, ← cancel_mono (α_ Z Y X).inv]
  repeat rw [assoc]
  rw [Iso.hom_inv_id, comp_id, ← braiding_naturality_right, braiding_tensor_right_hom]

theorem yang_baxter' (X Y Z : C) :
    (β_ X Y).hom ▷ Z ⊗≫ Y ◁ (β_ X Z).hom ⊗≫ (β_ Y Z).hom ▷ X =
      𝟙 _ ⊗≫ (X ◁ (β_ Y Z).hom ⊗≫ (β_ X Z).hom ▷ Y ⊗≫ Z ◁ (β_ X Y).hom) ⊗≫ 𝟙 _ := by
  rw [← cancel_epi (α_ X Y Z).inv, ← cancel_mono (α_ Z Y X).hom]
  convert yang_baxter X Y Z using 1
  all_goals monoidal

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

-- FIXME: `reassoc_of%` should unfold `autoParam`.
/--
Verifying the axioms for a braiding by checking that the candidate braiding is sent to a braiding
by a faithful monoidal functor.
-/
@[implicit_reducible]
def BraidedCategory.ofFaithful {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
    [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] [F.Faithful] [BraidedCategory D]
    (β : ∀ X Y : C, X ⊗ Y ≅ Y ⊗ X)
    (w : ∀ X Y, μ F _ _ ≫ F.map (β X Y).hom = (β_ _ _).hom ≫ μ F _ _ := by cat_disch) :
    BraidedCategory C where
  braiding := β
  braiding_naturality_left := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F ?_ ?_)).1 ?_
    rw [Functor.map_comp, ← μ_natural_left_assoc, w, Functor.map_comp,
      reassoc_of% w, braiding_naturality_left_assoc, μ_natural_right]
  braiding_naturality_right := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F ?_ ?_)).1 ?_
    rw [Functor.map_comp, ← μ_natural_right_assoc, w, Functor.map_comp,
      reassoc_of% w, braiding_naturality_right_assoc, μ_natural_left]
  hexagon_forward := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F _ _)).1 ?_
    refine (cancel_epi (μ F _ _ ▷ _)).1 ?_
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, ←
      μ_natural_left_assoc, ← comp_whiskerRight_assoc, w,
      comp_whiskerRight_assoc, Functor.LaxMonoidal.associativity_assoc,
      Functor.LaxMonoidal.associativity_assoc, ← μ_natural_right, ←
      whiskerLeft_comp_assoc, w, whiskerLeft_comp_assoc,
      reassoc_of% w, braiding_naturality_right_assoc,
      Functor.LaxMonoidal.associativity, hexagon_forward_assoc]
  hexagon_reverse := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F _ _)).1 ?_
    refine (cancel_epi (_ ◁ μ F _ _)).1 ?_
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, ←
      μ_natural_right_assoc, ← whiskerLeft_comp_assoc, w,
      whiskerLeft_comp_assoc, Functor.LaxMonoidal.associativity_inv_assoc,
      Functor.LaxMonoidal.associativity_inv_assoc, ← μ_natural_left,
      ← comp_whiskerRight_assoc, w, comp_whiskerRight_assoc, reassoc_of% w,
      braiding_naturality_left_assoc, Functor.LaxMonoidal.associativity_inv, hexagon_reverse_assoc]

/-- Pull back a braiding along a fully faithful monoidal functor. -/
@[implicit_reducible]
noncomputable def BraidedCategory.ofFullyFaithful {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] [F.Full]
    [F.Faithful] [BraidedCategory D] : BraidedCategory C :=
  .ofFaithful F fun X Y ↦ F.preimageIso ((μIso F _ _).symm ≪≫ β_ (F.obj X) (F.obj Y) ≪≫ μIso F _ _)

section

/-!
We now establish how the braiding interacts with the unitors.

I couldn't find a detailed proof in print, but this is discussed in:

* Proposition 1 of André Joyal and Ross Street,
  "Braided monoidal categories", Macquarie Math Reports 860081 (1986).
* Proposition 2.1 of André Joyal and Ross Street,
  "Braided tensor categories", Adv. Math. 102 (1993), 20–78.
* Exercise 8.1.6 of Etingof, Gelaki, Nikshych, Ostrik,
  "Tensor categories", vol 25, Mathematical Surveys and Monographs (2015), AMS.
-/

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]

theorem braiding_leftUnitor_aux₁ (X : C) :
    (α_ (𝟙_ C) (𝟙_ C) X).hom ≫
        (𝟙_ C ◁ (β_ X (𝟙_ C)).inv) ≫ (α_ _ X _).inv ≫ ((λ_ X).hom ▷ _) =
      ((λ_ _).hom ▷ X) ≫ (β_ X (𝟙_ C)).inv := by
  monoidal

theorem braiding_leftUnitor_aux₂ (X : C) :
    ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ ((λ_ X).hom ▷ 𝟙_ C) = (ρ_ X).hom ▷ 𝟙_ C :=
  calc
    ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ ((λ_ X).hom ▷ 𝟙_ C) =
      ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫ ((λ_ X).hom ▷ 𝟙_ C) := by
      simp
    _ = ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ (α_ _ _ _).hom ≫ (_ ◁ (β_ X _).hom) ≫
          (_ ◁ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫ ((λ_ X).hom ▷ 𝟙_ C) := by simp
    _ = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ (α_ _ _ _).hom ≫ (_ ◁ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫
          ((λ_ X).hom ▷ 𝟙_ C) := by simp
    _ = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ ((λ_ _).hom ▷ X) ≫ (β_ X _).inv := by
      rw [braiding_leftUnitor_aux₁]
    _ = (α_ _ _ _).hom ≫ (_ ◁ (λ_ _).hom) ≫ (β_ _ _).hom ≫ (β_ X _).inv := by
      (slice_lhs 2 3 => rw [← braiding_naturality_right]); simp only [assoc]
    _ = (α_ _ _ _).hom ≫ (_ ◁ (λ_ _).hom) := by rw [Iso.hom_inv_id, comp_id]
    _ = (ρ_ X).hom ▷ 𝟙_ C := by rw [triangle]

@[reassoc]
theorem braiding_leftUnitor (X : C) : (β_ X (𝟙_ C)).hom ≫ (λ_ X).hom = (ρ_ X).hom := by
  rw [← whiskerRight_iff, comp_whiskerRight, braiding_leftUnitor_aux₂]

theorem braiding_rightUnitor_aux₁ (X : C) :
    (α_ X (𝟙_ C) (𝟙_ C)).inv ≫
        ((β_ (𝟙_ C) X).inv ▷ 𝟙_ C) ≫ (α_ _ X _).hom ≫ (_ ◁ (ρ_ X).hom) =
      (X ◁ (ρ_ _).hom) ≫ (β_ (𝟙_ C) X).inv := by
  simp

theorem braiding_rightUnitor_aux₂ (X : C) :
    (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (𝟙_ C ◁ (ρ_ X).hom) = 𝟙_ C ◁ (λ_ X).hom :=
  calc
    (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (𝟙_ C ◁ (ρ_ X).hom) =
      (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).hom ≫ (𝟙_ C ◁ (ρ_ X).hom) := by
      simp
    _ = (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ ((β_ _ X).hom ▷ _) ≫
          ((β_ _ X).inv ▷ _) ≫ (α_ _ _ _).hom ≫ (𝟙_ C ◁ (ρ_ X).hom) := by
      simp
    _ = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (α_ _ _ _).inv ≫ ((β_ _ X).inv ▷ _) ≫ (α_ _ _ _).hom ≫
          (𝟙_ C ◁ (ρ_ X).hom) := by
      (slice_lhs 1 3 => rw [← hexagon_reverse]); simp only [assoc]
    _ = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (X ◁ (ρ_ _).hom) ≫ (β_ _ X).inv := by simp
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).hom ▷ _) ≫ (β_ _ X).hom ≫ (β_ _ _).inv := by
      (slice_lhs 2 3 => rw [← braiding_naturality_left]); simp only [assoc]
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).hom ▷ _) := by rw [Iso.hom_inv_id, comp_id]
    _ = 𝟙_ C ◁ (λ_ X).hom := by rw [triangle_assoc_comp_right]

@[reassoc]
theorem braiding_rightUnitor (X : C) : (β_ (𝟙_ C) X).hom ≫ (ρ_ X).hom = (λ_ X).hom := by
  rw [← whiskerLeft_iff, whiskerLeft_comp, braiding_rightUnitor_aux₂]

@[reassoc, simp]
theorem braiding_tensorUnit_left (X : C) : (β_ (𝟙_ C) X).hom = (λ_ X).hom ≫ (ρ_ X).inv := by
  simp [← braiding_rightUnitor]

@[reassoc, simp]
theorem braiding_inv_tensorUnit_left (X : C) : (β_ (𝟙_ C) X).inv = (ρ_ X).hom ≫ (λ_ X).inv := by
  rw [Iso.inv_ext]
  rw [braiding_tensorUnit_left]
  monoidal

@[reassoc]
theorem leftUnitor_inv_braiding (X : C) : (λ_ X).inv ≫ (β_ (𝟙_ C) X).hom = (ρ_ X).inv := by
  simp

@[reassoc]
theorem rightUnitor_inv_braiding (X : C) : (ρ_ X).inv ≫ (β_ X (𝟙_ C)).hom = (λ_ X).inv := by
  apply (cancel_mono (λ_ X).hom).1
  simp only [assoc, braiding_leftUnitor, Iso.inv_hom_id]

@[reassoc, simp]
theorem braiding_tensorUnit_right (X : C) : (β_ X (𝟙_ C)).hom = (ρ_ X).hom ≫ (λ_ X).inv := by
  simp [← rightUnitor_inv_braiding]

@[reassoc, simp]
theorem braiding_inv_tensorUnit_right (X : C) : (β_ X (𝟙_ C)).inv = (λ_ X).hom ≫ (ρ_ X).inv := by
  rw [Iso.inv_ext]
  rw [braiding_tensorUnit_right]
  monoidal

end

/--
A symmetric monoidal category is a braided monoidal category for which the braiding is symmetric. -/
@[stacks 0FFW]
class SymmetricCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] extends
    BraidedCategory.{v} C where
  -- braiding symmetric:
  symmetry : ∀ X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) := by cat_disch

attribute [reassoc (attr := simp)] SymmetricCategory.symmetry

lemma SymmetricCategory.braiding_swap_eq_inv_braiding {C : Type u₁}
    [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C] (X Y : C) :
    (β_ Y X).hom = (β_ X Y).inv := Iso.inv_ext' (symmetry X Y)

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]

/-- A lax braided functor between braided monoidal categories is a lax monoidal functor
which preserves the braiding.
-/
class Functor.LaxBraided (F : C ⥤ D) extends F.LaxMonoidal where
  braided : ∀ X Y : C, μ X Y ≫ F.map (β_ X Y).hom =
    (β_ (F.obj X) (F.obj Y)).hom ≫ μ Y X := by cat_disch

namespace Functor.LaxBraided

attribute [reassoc] braided

instance id : (𝟭 C).LaxBraided where

set_option backward.defeqAttrib.useBackward true in
instance (F : C ⥤ D) (G : D ⥤ E) [F.LaxBraided] [G.LaxBraided] :
    (F ⋙ G).LaxBraided where
  braided X Y := by
    dsimp
    slice_lhs 2 3 =>
      rw [← CategoryTheory.Functor.map_comp, braided, CategoryTheory.Functor.map_comp]
    slice_lhs 1 2 => rw [braided]
    simp only [Category.assoc]

/--
Given two lax monoidal, monoidally isomorphic functors, if one is lax braided, so is the other.
-/
@[implicit_reducible]
def ofNatIso {F G : C ⥤ D} (i : F ≅ G) [F.LaxBraided] [G.LaxMonoidal]
    [NatTrans.IsMonoidal i.hom] : G.LaxBraided where
  braided X Y := by
    have (X Y : C) : μ G X Y = (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app _ := by
      simp [NatTrans.IsMonoidal.tensor X Y, tensorHom_comp_tensorHom_assoc]
    rw [this X Y, this Y X, ← braiding_naturality_assoc, ← Functor.LaxBraided.braided_assoc]
    simp

end Functor.LaxBraided

section

variable (C D)

/-- Bundled version of lax braided functors. -/
structure LaxBraidedFunctor extends C ⥤ D where
  laxBraided : toFunctor.LaxBraided := by infer_instance

namespace LaxBraidedFunctor

variable {C D}

attribute [instance] laxBraided

/-- Constructor for `LaxBraidedFunctor C D`. -/
@[simps toFunctor]
def of (F : C ⥤ D) [F.LaxBraided] : LaxBraidedFunctor C D where
  toFunctor := F

/-- The lax monoidal functor induced by a lax braided functor. -/
@[simps toFunctor]
def toLaxMonoidalFunctor (F : LaxBraidedFunctor C D) : LaxMonoidalFunctor C D where
  toFunctor := F.toFunctor

instance : Category (LaxBraidedFunctor C D) :=
  inferInstanceAs (Category (InducedCategory _ toLaxMonoidalFunctor))

@[simp]
lemma id_hom (F : LaxBraidedFunctor C D) :
    LaxMonoidalFunctor.Hom.hom (InducedCategory.Hom.hom (𝟙 F)) = 𝟙 _ := rfl

@[reassoc, simp]
lemma comp_hom {F G H : LaxBraidedFunctor C D} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).hom = α.hom ≫ β.hom := rfl

@[ext]
lemma hom_ext {F G : LaxBraidedFunctor C D} {α β : F ⟶ G} (h : α.hom.hom = β.hom.hom) :
    α = β :=
  InducedCategory.hom_ext (LaxMonoidalFunctor.hom_ext h)

set_option backward.isDefEq.respectTransparency false in
/-- Constructor for morphisms in the category `LaxBraidedFunctor C D`. -/
@[simps]
def homMk {F G : LaxBraidedFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal f] :
    F ⟶ G := ⟨f, inferInstance⟩

/-- Constructor for isomorphisms in the category `LaxBraidedFunctor C D`. -/
@[simps]
def isoMk {F G : LaxBraidedFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] :
    F ≅ G where
  hom := homMk e.hom
  inv := homMk e.inv

/-- The forgetful functor from lax braided functors to lax monoidal functors. -/
@[simps! obj map]
def forget : LaxBraidedFunctor C D ⥤ LaxMonoidalFunctor C D :=
  inducedFunctor _

/-- The forgetful functor from lax braided functors to lax monoidal functors
is fully faithful. -/
def fullyFaithfulForget : (forget (C := C) (D := D)).FullyFaithful :=
  fullyFaithfulInducedFunctor _

section

variable {F G : LaxBraidedFunctor C D} (e : ∀ X, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f := by
      cat_disch)
    (unit : ε F.toFunctor ≫ (e (𝟙_ C)).hom = ε G.toFunctor := by cat_disch)
    (tensor : ∀ X Y, μ F.toFunctor X Y ≫ (e (X ⊗ Y)).hom =
      ((e X).hom ⊗ₘ (e Y).hom) ≫ μ G.toFunctor X Y := by cat_disch)

set_option backward.privateInPublic true in
/-- Constructor for isomorphisms between lax braided functors. -/
def isoOfComponents :
    F ≅ G :=
  fullyFaithfulForget.preimageIso
    (LaxMonoidalFunctor.isoOfComponents e naturality unit tensor)

set_option backward.privateInPublic true in
@[simp]
lemma isoOfComponents_hom_hom_hom_app (X : C) :
    (isoOfComponents e naturality unit tensor).hom.hom.hom.app X = (e X).hom := rfl

set_option backward.privateInPublic true in
@[simp]
lemma isoOfComponents_inv_hom_hom_app (X : C) :
    (isoOfComponents e naturality unit tensor).inv.hom.hom.app X = (e X).inv := rfl

@[deprecated (since := "2025-12-18")] alias isoOfComponents_hom_hom_app :=
  isoOfComponents_hom_hom_hom_app

@[deprecated (since := "2025-12-18")] alias isoOfComponents_inv_hom_app :=
  isoOfComponents_inv_hom_hom_app

end

end LaxBraidedFunctor

end

/-- A braided functor between braided monoidal categories is a monoidal functor
which preserves the braiding.
-/
@[ext]
class Functor.Braided (F : C ⥤ D) extends F.Monoidal, F.LaxBraided where

@[simp, reassoc]
lemma Functor.map_braiding (F : C ⥤ D) (X Y : C) [F.Braided] :
    F.map (β_ X Y).hom =
    δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X := by
  rw [← Functor.Braided.braided, δ_μ_assoc]

/--
A braided category with a faithful braided functor to a symmetric category is itself symmetric.
-/
@[implicit_reducible]
def SymmetricCategory.ofFaithful {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [SymmetricCategory D] (F : C ⥤ D) [F.Braided]
    [F.Faithful] : SymmetricCategory C where
  symmetry X Y := F.map_injective (by simp)

/-- Pull back a symmetric braiding along a fully faithful monoidal functor. -/
@[implicit_reducible]
noncomputable def SymmetricCategory.ofFullyFaithful {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] [F.Full]
    [F.Faithful] [SymmetricCategory D] : SymmetricCategory C :=
  let h : BraidedCategory C := BraidedCategory.ofFullyFaithful F
  let _ : F.Braided := {
    braided X Y := by
      simp +instances [h, BraidedCategory.ofFullyFaithful, BraidedCategory.ofFaithful] }
  .ofFaithful F

@[deprecated (since := "2025-10-17")]
alias symmetricCategoryOfFaithful := SymmetricCategory.ofFaithful

@[deprecated (since := "2025-10-17")]
alias symmetricCategoryOfFullyFaithful := SymmetricCategory.ofFullyFaithful

namespace Functor.Braided

instance : (𝟭 C).Braided where

instance (F : C ⥤ D) (G : D ⥤ E) [F.Braided] [G.Braided] : (F ⋙ G).Braided where

lemma toMonoidal_injective (F : C ⥤ D) : Function.Injective
    (@Braided.toMonoidal _ _ _ _ _ _ _ _ _ : F.Braided → F.Monoidal) := by rintro ⟨⟩ ⟨⟩ rfl; rfl

end Functor.Braided

section CommMonoid

variable (M : Type u) [CommMonoid M]

instance : BraidedCategory (Discrete M) where
  braiding X Y := Discrete.eqToIso (mul_comm X.as Y.as)

variable {M} {N : Type u} [CommMonoid N]

/-- A multiplicative morphism between commutative monoids gives a braided functor between
the corresponding discrete braided monoidal categories.
-/
instance Discrete.monoidalFunctorBraided (F : M →* N) :
    (Discrete.monoidalFunctor F).Braided where

end CommMonoid

namespace MonoidalCategory

section Tensor

/-- Swap the second and third objects in `(X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂)`. This is used to strength the
tensor product functor from `C × C` to `C` as a monoidal functor. -/
def tensorμ (X₁ X₂ Y₁ Y₂ : C) : (X₁ ⊗ X₂) ⊗ Y₁ ⊗ Y₂ ⟶ (X₁ ⊗ Y₁) ⊗ X₂ ⊗ Y₂ :=
  (α_ X₁ X₂ (Y₁ ⊗ Y₂)).hom ≫
    (X₁ ◁ (α_ X₂ Y₁ Y₂).inv) ≫
      (X₁ ◁ (β_ X₂ Y₁).hom ▷ Y₂) ≫
        (X₁ ◁ (α_ Y₁ X₂ Y₂).hom) ≫ (α_ X₁ Y₁ (X₂ ⊗ Y₂)).inv

/-- The inverse of `tensorμ`. -/
def tensorδ (X₁ X₂ Y₁ Y₂ : C) : (X₁ ⊗ Y₁) ⊗ X₂ ⊗ Y₂ ⟶ (X₁ ⊗ X₂) ⊗ Y₁ ⊗ Y₂ :=
  (α_ X₁ Y₁ (X₂ ⊗ Y₂)).hom ≫
    (X₁ ◁ (α_ Y₁ X₂ Y₂).inv) ≫
      (X₁ ◁ (β_ X₂ Y₁).inv ▷ Y₂) ≫
        (X₁ ◁ (α_ X₂ Y₁ Y₂).hom) ≫
          (α_ X₁ X₂ (Y₁ ⊗ Y₂)).inv

@[reassoc (attr := simp)]
lemma tensorμ_tensorδ (X₁ X₂ Y₁ Y₂ : C) :
    tensorμ X₁ X₂ Y₁ Y₂ ≫ tensorδ X₁ X₂ Y₁ Y₂ = 𝟙 _ := by
  simp only [tensorμ, ← whiskerLeft_comp_assoc, tensorδ, assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, hom_inv_whiskerRight_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp,
    Iso.hom_inv_id]

@[reassoc (attr := simp)]
lemma tensorδ_tensorμ (X₁ X₂ Y₁ Y₂ : C) :
    tensorδ X₁ X₂ Y₁ Y₂ ≫ tensorμ X₁ X₂ Y₁ Y₂ = 𝟙 _ := by
  simp only [tensorδ, ← whiskerLeft_comp_assoc, tensorμ, assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, inv_hom_whiskerRight_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp,
    Iso.hom_inv_id]

@[reassoc]
theorem tensorμ_natural {X₁ X₂ Y₁ Y₂ U₁ U₂ V₁ V₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : U₁ ⟶ V₁)
    (g₂ : U₂ ⟶ V₂) :
    ((f₁ ⊗ₘ f₂) ⊗ₘ g₁ ⊗ₘ g₂) ≫ tensorμ Y₁ Y₂ V₁ V₂ =
      tensorμ X₁ X₂ U₁ U₂ ≫ ((f₁ ⊗ₘ g₁) ⊗ₘ f₂ ⊗ₘ g₂) := by
  dsimp only [tensorμ]
  simp_rw [← id_tensorHom, ← tensorHom_id]
  slice_lhs 1 2 => rw [associator_naturality]
  slice_lhs 2 3 =>
    rw [tensorHom_comp_tensorHom, comp_id f₁, ← id_comp f₁, associator_inv_naturality,
      ← tensorHom_comp_tensorHom]
  slice_lhs 3 4 =>
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, comp_id f₁, ← id_comp f₁, comp_id g₂,
      ← id_comp g₂, braiding_naturality, ← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom]
  slice_lhs 4 5 =>
    rw [tensorHom_comp_tensorHom, comp_id f₁, ← id_comp f₁, associator_naturality,
      ← tensorHom_comp_tensorHom]
  slice_lhs 5 6 => rw [associator_inv_naturality]
  simp only [assoc]

@[reassoc]
theorem tensorμ_natural_left {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (Z₁ Z₂ : C) :
    (f₁ ⊗ₘ f₂) ▷ (Z₁ ⊗ Z₂) ≫ tensorμ Y₁ Y₂ Z₁ Z₂ =
      tensorμ X₁ X₂ Z₁ Z₂ ≫ (f₁ ▷ Z₁ ⊗ₘ f₂ ▷ Z₂) := by
  convert tensorμ_natural f₁ f₂ (𝟙 Z₁) (𝟙 Z₂) using 1 <;> simp

@[reassoc]
theorem tensorμ_natural_right (Z₁ Z₂ : C) {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    (Z₁ ⊗ Z₂) ◁ (f₁ ⊗ₘ f₂) ≫ tensorμ Z₁ Z₂ Y₁ Y₂ =
      tensorμ Z₁ Z₂ X₁ X₂ ≫ (Z₁ ◁ f₁ ⊗ₘ Z₂ ◁ f₂) := by
  convert tensorμ_natural (𝟙 Z₁) (𝟙 Z₂) f₁ f₂ using 1 <;> simp

@[reassoc]
theorem tensor_left_unitality (X₁ X₂ : C) :
    (λ_ (X₁ ⊗ X₂)).hom =
      ((λ_ (𝟙_ C)).inv ▷ (X₁ ⊗ X₂)) ≫
        tensorμ (𝟙_ C) (𝟙_ C) X₁ X₂ ≫ ((λ_ X₁).hom ⊗ₘ (λ_ X₂).hom) := by
  dsimp only [tensorμ]
  have :
    ((λ_ (𝟙_ C)).inv ▷ (X₁ ⊗ X₂)) ≫
        (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫ (𝟙_ C ◁ (α_ (𝟙_ C) X₁ X₂).inv) =
      𝟙_ C ◁ (λ_ X₁).inv ▷ X₂ := by
    simp
  slice_rhs 1 3 => rw [this]
  clear this
  slice_rhs 1 2 => rw [← whiskerLeft_comp, ← comp_whiskerRight,
    leftUnitor_inv_braiding]
  simp [tensorHom_def]

@[reassoc]
theorem tensor_right_unitality (X₁ X₂ : C) :
    (ρ_ (X₁ ⊗ X₂)).hom =
      ((X₁ ⊗ X₂) ◁ (λ_ (𝟙_ C)).inv) ≫
        tensorμ X₁ X₂ (𝟙_ C) (𝟙_ C) ≫ ((ρ_ X₁).hom ⊗ₘ (ρ_ X₂).hom) := by
  dsimp only [tensorμ]
  have :
    ((X₁ ⊗ X₂) ◁ (λ_ (𝟙_ C)).inv) ≫
        (α_ X₁ X₂ (𝟙_ C ⊗ 𝟙_ C)).hom ≫ (X₁ ◁ (α_ X₂ (𝟙_ C) (𝟙_ C)).inv) =
      (α_ X₁ X₂ (𝟙_ C)).hom ≫ (X₁ ◁ (ρ_ X₂).inv ▷ 𝟙_ C) := by
    monoidal
  slice_rhs 1 3 => rw [this]
  clear this
  slice_rhs 2 3 => rw [← whiskerLeft_comp, ← comp_whiskerRight,
    rightUnitor_inv_braiding]
  simp [tensorHom_def]

@[reassoc]
theorem tensor_associativity (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C) :
    (tensorμ X₁ X₂ Y₁ Y₂ ▷ (Z₁ ⊗ Z₂)) ≫
        tensorμ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) Z₁ Z₂ ≫ ((α_ X₁ Y₁ Z₁).hom ⊗ₘ (α_ X₂ Y₂ Z₂).hom) =
      (α_ (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (Z₁ ⊗ Z₂)).hom ≫
        ((X₁ ⊗ X₂) ◁ tensorμ Y₁ Y₂ Z₁ Z₂) ≫ tensorμ X₁ X₂ (Y₁ ⊗ Z₁) (Y₂ ⊗ Z₂) := by
  dsimp only [tensor_obj, prodMonoidal_tensorObj, tensorμ]
  simp only [braiding_tensor_left_hom, braiding_tensor_right_hom]
  calc
    _ = 𝟙 _ ⊗≫
      X₁ ◁ ((β_ X₂ Y₁).hom ▷ (Y₂ ⊗ Z₁) ≫ (Y₁ ⊗ X₂) ◁ (β_ Y₂ Z₁).hom) ▷ Z₂ ⊗≫
        X₁ ◁ Y₁ ◁ (β_ X₂ Z₁).hom ▷ Y₂ ▷ Z₂ ⊗≫ 𝟙 _ := by monoidal
    _ = _ := by rw [← whisker_exchange]; monoidal

set_option backward.defeqAttrib.useBackward true in
instance tensorMonoidal : (tensor C).Monoidal :=
    Functor.CoreMonoidal.toMonoidal
      { εIso := (λ_ (𝟙_ C)).symm
        μIso := fun X Y ↦
          { hom := tensorμ X.1 X.2 Y.1 Y.2
            inv := tensorδ X.1 X.2 Y.1 Y.2 }
        μIso_hom_natural_left := fun f Z ↦ tensorμ_natural_left f.1 f.2 Z.1 Z.2
        μIso_hom_natural_right := fun Z f ↦ tensorμ_natural_right Z.1 Z.2 f.1 f.2
        associativity := fun X Y Z ↦ tensor_associativity X.1 X.2 Y.1 Y.2 Z.1 Z.2
        left_unitality := fun ⟨X₁, X₂⟩ ↦ tensor_left_unitality X₁ X₂
        right_unitality := fun ⟨X₁, X₂⟩ ↦ tensor_right_unitality X₁ X₂ }

@[simp] lemma tensor_ε : ε (tensor C) = (λ_ (𝟙_ C)).inv := rfl
@[simp] lemma tensor_η : η (tensor C) = (λ_ (𝟙_ C)).hom := rfl
@[simp] lemma tensor_μ (X Y : C × C) : μ (tensor C) X Y = tensorμ X.1 X.2 Y.1 Y.2 := rfl
@[simp] lemma tensor_δ (X Y : C × C) : δ (tensor C) X Y = tensorδ X.1 X.2 Y.1 Y.2 := rfl

@[reassoc]
theorem leftUnitor_monoidal (X₁ X₂ : C) :
    (λ_ X₁).hom ⊗ₘ (λ_ X₂).hom =
      tensorμ (𝟙_ C) X₁ (𝟙_ C) X₂ ≫ ((λ_ (𝟙_ C)).hom ▷ (X₁ ⊗ X₂)) ≫ (λ_ (X₁ ⊗ X₂)).hom := by
  dsimp only [tensorμ]
  have :
    (λ_ X₁).hom ⊗ₘ (λ_ X₂).hom =
      (α_ (𝟙_ C) X₁ (𝟙_ C ⊗ X₂)).hom ≫
        (𝟙_ C ◁ (α_ X₁ (𝟙_ C) X₂).inv) ≫ (λ_ ((X₁ ⊗ 𝟙_ C) ⊗ X₂)).hom ≫ ((ρ_ X₁).hom ▷ X₂) := by
    monoidal
  simp [this]

@[reassoc]
theorem rightUnitor_monoidal (X₁ X₂ : C) :
    (ρ_ X₁).hom ⊗ₘ (ρ_ X₂).hom =
      tensorμ X₁ (𝟙_ C) X₂ (𝟙_ C) ≫ ((X₁ ⊗ X₂) ◁ (λ_ (𝟙_ C)).hom) ≫ (ρ_ (X₁ ⊗ X₂)).hom := by
  dsimp only [tensorμ]
  have :
    (ρ_ X₁).hom ⊗ₘ (ρ_ X₂).hom =
      (α_ X₁ (𝟙_ C) (X₂ ⊗ 𝟙_ C)).hom ≫
        (X₁ ◁ (α_ (𝟙_ C) X₂ (𝟙_ C)).inv) ≫ (X₁ ◁ (ρ_ (𝟙_ C ⊗ X₂)).hom) ≫ (X₁ ◁ (λ_ X₂).hom) := by
    monoidal
  rw [this]; clear this
  rw [← braiding_rightUnitor]
  monoidal

@[reassoc]
theorem associator_monoidal (X₁ X₂ X₃ Y₁ Y₂ Y₃ : C) :
    tensorμ (X₁ ⊗ X₂) X₃ (Y₁ ⊗ Y₂) Y₃ ≫
        (tensorμ X₁ X₂ Y₁ Y₂ ▷ (X₃ ⊗ Y₃)) ≫ (α_ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) (X₃ ⊗ Y₃)).hom =
      ((α_ X₁ X₂ X₃).hom ⊗ₘ (α_ Y₁ Y₂ Y₃).hom) ≫
        tensorμ X₁ (X₂ ⊗ X₃) Y₁ (Y₂ ⊗ Y₃) ≫ ((X₁ ⊗ Y₁) ◁ tensorμ X₂ X₃ Y₂ Y₃) := by
  dsimp only [tensorμ]
  calc
    _ = 𝟙 _ ⊗≫ X₁ ◁ X₂ ◁ (β_ X₃ Y₁).hom ▷ Y₂ ▷ Y₃ ⊗≫
      X₁ ◁ ((X₂ ⊗ Y₁) ◁ (β_ X₃ Y₂).hom ≫
        (β_ X₂ Y₁).hom ▷ (Y₂ ⊗ X₃)) ▷ Y₃ ⊗≫ 𝟙 _ := by
          rw [braiding_tensor_right_hom]; monoidal
    _ = _ := by rw [whisker_exchange, braiding_tensor_left_hom]; monoidal

@[reassoc]
lemma tensorμ_comp_μ_tensorHom_μ_comp_μ (F : C ⥤ D) [F.LaxBraided] (W X Y Z : C) :
    tensorμ (F.obj W) (F.obj X) (F.obj Y) (F.obj Z) ≫
      (μ F W Y ⊗ₘ μ F X Z) ≫ μ F (W ⊗ Y) (X ⊗ Z) =
      (μ F W X ⊗ₘ μ F Y Z) ≫ μ F (W ⊗ X) (Y ⊗ Z) ≫ F.map (tensorμ W X Y Z) := by
  rw [tensorHom_def]
  simp only [tensorμ, Category.assoc]
  rw [whiskerLeft_μ_comp_μ,
    associator_inv_naturality_left_assoc, ← pentagon_inv_assoc,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, Category.assoc, μ_whiskerRight_comp_μ,
    whiskerLeft_hom_inv_assoc, Iso.inv_hom_id_assoc, comp_whiskerRight_assoc,
    comp_whiskerRight_assoc, μ_natural_left_assoc, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, ← MonoidalCategory.whiskerLeft_comp,
    ← Functor.LaxBraided.braided,
    MonoidalCategory.whiskerLeft_comp_assoc, μ_natural_right, whiskerLeft_μ_comp_μ_assoc,
    comp_whiskerRight_assoc, comp_whiskerRight_assoc, comp_whiskerRight_assoc,
    comp_whiskerRight_assoc, pentagon_inv_assoc, μ_natural_left_assoc, μ_natural_left_assoc,
    Iso.hom_inv_id_assoc, ← associator_inv_naturality_left_assoc, μ_whiskerRight_comp_μ_assoc,
    Iso.inv_hom_id_assoc, ← tensorHom_def_assoc]
  simp only [← Functor.map_comp, whisker_assoc, Category.assoc, pentagon_inv_inv_hom_hom_inv,
    pentagon_inv_hom_hom_hom_inv_assoc]

end Tensor

end MonoidalCategory

@[reassoc]
theorem SymmetricCategory.tensorμ_braid_swap
    {C : Type*} [Category* C] [MonoidalCategory C] [SymmetricCategory C]
    (X Y : C) :
    tensorμ X X Y Y ≫ (β_ (X ⊗ Y) (X ⊗ Y)).hom =
      ((β_ X X).hom ⊗ₘ (β_ Y Y).hom) ≫ tensorμ X X Y Y := by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding Y X, tensorHom_def]

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

set_option backward.defeqAttrib.useBackward true in
instance : (mopFunctor C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun X Y ↦ β_ (mop X) (mop Y)
      associativity := fun X Y Z ↦ by simp [← yang_baxter_assoc] }

@[simp] lemma mopFunctor_ε : ε (mopFunctor C) = 𝟙 _ := rfl
@[simp] lemma mopFunctor_η : η (mopFunctor C) = 𝟙 _ := rfl
@[simp] lemma mopFunctor_μ (X Y : C) : μ (mopFunctor C) X Y = (β_ (mop X) (mop Y)).hom := rfl
@[simp] lemma mopFunctor_δ (X Y : C) : δ (mopFunctor C) X Y = (β_ (mop X) (mop Y)).inv := rfl

set_option backward.defeqAttrib.useBackward true in
instance : (unmopFunctor C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun X Y ↦ β_ (unmop X) (unmop Y)
      associativity := fun X Y Z ↦ by simp [← yang_baxter_assoc] }

@[simp] lemma unmopFunctor_ε : ε (unmopFunctor C) = 𝟙 _ := rfl
@[simp] lemma unmopFunctor_η : η (unmopFunctor C) = 𝟙 _ := rfl
@[simp] lemma unmopFunctor_μ (X Y : Cᴹᵒᵖ) :
    μ (unmopFunctor C) X Y = (β_ (unmop X) (unmop Y)).hom := rfl
@[simp] lemma unmopFunctor_δ (X Y : Cᴹᵒᵖ) :
    δ (unmopFunctor C) X Y = (β_ (unmop X) (unmop Y)).inv := rfl

/-- The identity functor on `C`, viewed as a functor from `C` to its
monoidal opposite, upgraded to a braided functor. -/
instance : (mopFunctor C).Braided where

/-- The identity functor on `C`, viewed as a functor from the
monoidal opposite of `C` to `C`, upgraded to a braided functor. -/
instance : (unmopFunctor C).Braided where

end MonoidalOpposite

variable (C)

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
@[implicit_reducible]
def SymmetricCategory.equivReverseBraiding (C : Type u₁) [Category.{v₁} C]
    [MonoidalCategory C] [SymmetricCategory C] :=
  @Functor.Braided.mk C _ _ _ C _ _ (reverseBraiding C) (𝟭 C) _ <| by
    simp +instances [reverseBraiding, braiding_swap_eq_inv_braiding]

end CategoryTheory
