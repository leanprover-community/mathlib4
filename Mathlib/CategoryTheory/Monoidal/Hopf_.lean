/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Bimon_
import Mathlib.CategoryTheory.Monoidal.Conv

/-!
# The category of Hopf monoids in a braided monoidal category.


## TODO

* Show that in a cartesian monoidal category Hopf monoids are exactly group objects.
* Show that `Hopf_ (ModuleCat R) ≌ HopfAlgebraCat R`.
-/

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

open scoped Mon_Class Comon_Class

/--
A Hopf monoid in a braided category `C` is a bimonoid object in `C` equipped with an antipode.
-/
class Hopf_Class (X : C) extends Bimon_Class X where
  /-- The antipode is an endomorphism of the underlying object of the Hopf monoid. -/
  antipode : X ⟶ X
  /- For the names of the conditions below, the unprimed names are reserved for the version where
  the argument `X` is explicit. -/
  antipode_left' : Δ ≫ antipode ▷ X ≫ μ = ε ≫ η := by aesop_cat
  antipode_right' : Δ ≫ X ◁ antipode ≫ μ = ε ≫ η := by aesop_cat

namespace Hopf_Class

@[inherit_doc] scoped notation "𝒮" => Hopf_Class.antipode
@[inherit_doc] scoped notation "𝒮["X"]" => Hopf_Class.antipode (X := X)

/- The simp attribute is reserved for the unprimed versions. -/
attribute [reassoc] antipode_left' antipode_right'

/-- The object is provided as an explicit argument. -/
@[reassoc (attr := simp)]
theorem antipode_left (X : C) [Hopf_Class X] : Δ ≫ 𝒮 ▷ X ≫ μ = ε ≫ η := antipode_left'

/-- The object is provided as an explicit argument. -/
@[reassoc (attr := simp)]
theorem antipode_right (X : C) [Hopf_Class X] : Δ ≫ X ◁ 𝒮 ≫ μ = ε ≫ η := antipode_right'

end Hopf_Class

variable (C)

/--
A Hopf monoid in a braided category `C` is a bimonoid object in `C` equipped with an antipode.
-/
structure Hopf_ where
  /-- The underlying bimonoid of a Hopf monoid. -/
  X : Bimon_ C
  /-- The antipode is an endomorphism of the underlying object of the Hopf monoid. -/
  antipode : X.X.X ⟶ X.X.X
  antipode_left : X.comul.hom ≫ (antipode ▷ X.X.X) ≫ X.X.mul = X.counit.hom ≫ X.X.one
  antipode_right : X.comul.hom ≫ (X.X.X ◁ antipode) ≫ X.X.mul = X.counit.hom ≫ X.X.one

attribute [reassoc (attr := simp)] Hopf_.antipode_left Hopf_.antipode_right

namespace Hopf_

/--
Morphisms of Hopf monoids are just morphisms of the underlying bimonoids.
In fact they automatically intertwine the antipodes, proved below.
-/
instance : Category (Hopf_ C) := inferInstanceAs <| Category (InducedCategory (Bimon_ C) Hopf_.X)

variable {C}

/-- Morphisms of Hopf monoids intertwine the antipodes. -/
theorem hom_antipode {A B : Hopf_ C} (f : A ⟶ B) :
    f.hom.hom ≫ B.antipode = A.antipode ≫ f.hom.hom := by
  -- We show these elements are equal by exhibiting an element in the convolution algebra
  -- between `A` (as a comonoid) and `B` (as a monoid),
  -- such that the LHS is a left inverse, and the RHS is a right inverse.
  apply left_inv_eq_right_inv
    (M := Conv ((Bimon_.toComon_ C).obj A.X) B.X.X)
    (a := f.hom.hom)
  · erw [Conv.mul_eq, Conv.one_eq]
    simp only [Bimon_.toComon__obj_X, Bimon_.toComon__obj_comul, comp_whiskerRight, Category.assoc,
      Bimon_.toComon__obj_counit]
    slice_lhs 3 4 =>
      rw [← whisker_exchange]
    slice_lhs 2 3 =>
      rw [← tensorHom_def]
    slice_lhs 1 2 =>
      rw [← Bimon_.hom_comul_hom f]
    slice_lhs 2 4 =>
      rw [B.antipode_left]
    slice_lhs 1 2 =>
      rw [Bimon_.hom_counit_hom f]
  · erw [Conv.mul_eq, Conv.one_eq]
    simp only [Bimon_.toComon__obj_X, Bimon_.toComon__obj_comul, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, Bimon_.toComon__obj_counit]
    slice_lhs 2 3 =>
      rw [← whisker_exchange]
    slice_lhs 3 4 =>
      rw [← tensorHom_def]
    slice_lhs 3 4 =>
      rw [← f.hom.mul_hom]
    slice_lhs 1 3 =>
      rw [A.antipode_right]
    slice_lhs 2 3 =>
      rw [f.hom.one_hom]

@[reassoc (attr := simp)]
theorem one_antipode (A : Hopf_ C) : A.X.X.one ≫ A.antipode = A.X.X.one := by
  have := (rfl : A.X.X.one ≫ A.X.comul.hom ≫ (A.antipode ▷ A.X.X.X) ≫ A.X.X.mul = _)
  conv at this =>
    rhs
    rw [A.antipode_left]
  rw [A.X.one_comul_assoc, tensorHom_def, Category.assoc, whisker_exchange_assoc] at this
  simpa [unitors_inv_equal]

@[reassoc (attr := simp)]
theorem antipode_counit (A : Hopf_ C) : A.antipode ≫ A.X.counit.hom = A.X.counit.hom := by
  have := (rfl : A.X.comul.hom ≫ (A.antipode ▷ A.X.X.X) ≫ A.X.X.mul ≫ A.X.counit.hom = _)
  conv at this =>
    rhs
    rw [A.antipode_left_assoc]
  rw [A.X.mul_counit, tensorHom_def', Category.assoc, ← whisker_exchange_assoc] at this
  simpa [unitors_equal]

/-!
## The antipode is an antihomomorphism with respect to both the monoid and comonoid structures.
-/

theorem antipode_comul₁ (A : Hopf_ C) :
    A.X.comul.hom ≫
      A.antipode ▷ A.X.X.X ≫
      A.X.comul.hom ▷ A.X.X.X ≫
      (α_ A.X.X.X A.X.X.X A.X.X.X).hom ≫
      A.X.X.X ◁ A.X.X.X ◁ A.X.comul.hom ≫
      A.X.X.X ◁ (α_ A.X.X.X A.X.X.X A.X.X.X).inv ≫
      A.X.X.X ◁ (β_ A.X.X.X A.X.X.X).hom ▷ A.X.X.X ≫
      A.X.X.X ◁ (α_ A.X.X.X A.X.X.X A.X.X.X).hom ≫
      (α_ A.X.X.X A.X.X.X (A.X.X.X ⊗ A.X.X.X)).inv ≫
      (A.X.X.mul ⊗ A.X.X.mul) =
    A.X.counit.hom ≫ (λ_ (𝟙_ C)).inv ≫ (A.X.X.one ⊗ A.X.X.one) := by
  dsimp
  slice_lhs 3 5 =>
    rw [← associator_naturality_right, ← Category.assoc, ← tensorHom_def]
  slice_lhs 3 9 =>
    erw [Bimon_.compatibility]
  slice_lhs 1 3 =>
    erw [A.antipode_left]
  simp

/--
Auxiliary calculation for `antipode_comul`.
This calculation calls for some ASCII art out of This Week's Finds.

   |   |
   n   n
  | \ / |
  |  /  |
  | / \ |
  | | S S
  | | \ /
  | |  /
  | | / \
  \ / \ /
   v   v
    \ /
     v
     |

We move the left antipode up through the crossing,
the right antipode down through the crossing,
the right multiplication down across the strand,
reassociate the comultiplications,
then use `antipode_right` then `antipode_left` to simplify.
-/
theorem antipode_comul₂ (A : Hopf_ C) :
    A.X.comul.hom ≫
      A.X.comul.hom ▷ A.X.X.X ≫
      (α_ A.X.X.X A.X.X.X A.X.X.X).hom ≫
      A.X.X.X ◁ A.X.X.X ◁ A.X.comul.hom ≫
      A.X.X.X ◁ A.X.X.X ◁ (β_ A.X.X.X A.X.X.X).hom ≫
      A.X.X.X ◁ A.X.X.X ◁ (A.antipode ⊗ A.antipode) ≫
      A.X.X.X ◁ (α_ A.X.X.X A.X.X.X A.X.X.X).inv ≫
      A.X.X.X ◁ (β_ A.X.X.X A.X.X.X).hom ▷ A.X.X.X ≫
      A.X.X.X ◁ (α_ A.X.X.X A.X.X.X A.X.X.X).hom ≫
      (α_ A.X.X.X A.X.X.X (A.X.X.X ⊗ A.X.X.X)).inv ≫
      (A.X.X.mul ⊗ A.X.X.mul) =
    A.X.counit.hom ≫ (λ_ (𝟙_ C)).inv ≫ (A.X.X.one ⊗ A.X.X.one) := by
  -- We should write a version of `slice_lhs` that zooms through whiskerings.
  slice_lhs 6 6 =>
    simp only [tensorHom_def', MonoidalCategory.whiskerLeft_comp]
  slice_lhs 7 8 =>
    rw [← MonoidalCategory.whiskerLeft_comp, associator_inv_naturality_middle,
      MonoidalCategory.whiskerLeft_comp]
  slice_lhs 8 9 =>
    rw [← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight,
      BraidedCategory.braiding_naturality_right,
      comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
  slice_lhs 9 10 =>
    rw [← MonoidalCategory.whiskerLeft_comp,
      associator_naturality_left,
      MonoidalCategory.whiskerLeft_comp]
  slice_lhs 5 6 =>
    rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp,
      ← BraidedCategory.braiding_naturality_left,
      MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp]
  slice_lhs 11 12 =>
    rw [tensorHom_def', ← Category.assoc, ← associator_inv_naturality_right]
  slice_lhs 10 11 =>
    rw [← MonoidalCategory.whiskerLeft_comp, ← whisker_exchange,
      MonoidalCategory.whiskerLeft_comp]
  slice_lhs 6 10 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [← BraidedCategory.hexagon_reverse_assoc, Iso.inv_hom_id_assoc,
      ← BraidedCategory.braiding_naturality_left]
    simp only [MonoidalCategory.whiskerLeft_comp]
  rw [Bimon_.comul_assoc_flip_hom_assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [Bimon_.comul_assoc_hom]
    simp only [MonoidalCategory.whiskerLeft_comp]
  slice_lhs 3 7 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [← associator_naturality_middle_assoc, Iso.hom_inv_id_assoc]
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
    simp only [MonoidalCategory.whiskerLeft_comp]
  slice_lhs 2 3 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [Bimon_.counit_comul_hom]
    simp only [MonoidalCategory.whiskerLeft_comp]
  slice_lhs 3 4 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [BraidedCategory.braiding_naturality_left]
    simp only [MonoidalCategory.whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [whisker_exchange]
    simp only [MonoidalCategory.whiskerLeft_comp]
  slice_lhs 5 7 =>
    rw [associator_inv_naturality_right_assoc, whisker_exchange]
  simp only [Mon_.monMonoidalStruct_tensorObj_X, Mon_.tensorUnit_X, braiding_tensorUnit_left,
    MonoidalCategory.whiskerLeft_comp, whiskerLeft_rightUnitor_inv,
    MonoidalCategory.whiskerRight_id, whiskerLeft_rightUnitor, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc, whiskerLeft_inv_hom_assoc, antipode_right_assoc]
  rw [rightUnitor_inv_naturality_assoc, tensorHom_def]
  monoidal

theorem antipode_comul (A : Hopf_ C) :
    A.antipode ≫ A.X.comul.hom = A.X.comul.hom ≫ (β_ _ _).hom ≫ (A.antipode ⊗ A.antipode) := by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv ((Bimon_.toComon_ C).obj A.X) (A.X.X ⊗ A.X.X))
    (a := A.X.comul.hom)
  · erw [Conv.mul_eq, Conv.one_eq]
    simp only [Bimon_.toComon__obj_X, Mon_.monMonoidalStruct_tensorObj_X, Bimon_.toComon__obj_comul,
      comp_whiskerRight, tensor_whiskerLeft, Mon_.tensorObj_mul, Category.assoc,
      Bimon_.toComon__obj_counit, Mon_.tensorObj_one]
    simp only [tensor_μ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact antipode_comul₁ A
  · erw [Conv.mul_eq, Conv.one_eq]
    simp only [Bimon_.toComon__obj_X, Mon_.monMonoidalStruct_tensorObj_X, Bimon_.toComon__obj_comul,
      MonoidalCategory.whiskerLeft_comp, tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc,
      Mon_.tensorObj_mul, Bimon_.toComon__obj_counit, Mon_.tensorObj_one]
    simp only [tensor_μ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact antipode_comul₂ A

theorem mul_antipode₁ (A : Hopf_ C) :
    (A.X.comul.hom ⊗ A.X.comul.hom) ≫
      (α_ A.X.X.X A.X.X.X (A.X.X.X ⊗ A.X.X.X)).hom ≫
      A.X.X.X ◁ (α_ A.X.X.X A.X.X.X A.X.X.X).inv ≫
      A.X.X.X ◁ (β_ A.X.X.X A.X.X.X).hom ▷ A.X.X.X ≫
      (α_ A.X.X.X (A.X.X.X ⊗ A.X.X.X) A.X.X.X).inv ≫
      (α_ A.X.X.X A.X.X.X A.X.X.X).inv ▷ A.X.X.X ≫
      A.X.X.mul ▷ A.X.X.X ▷ A.X.X.X ≫
      A.antipode ▷ A.X.X.X ▷ A.X.X.X ≫
      (α_ A.X.X.X A.X.X.X A.X.X.X).hom ≫
      A.X.X.X ◁ A.X.X.mul ≫
      A.X.X.mul =
    (A.X.counit.hom ⊗ A.X.counit.hom) ≫ (λ_ (𝟙_ C)).hom ≫ A.X.X.one := by
  slice_lhs 8 9 =>
    rw [associator_naturality_left]
  slice_lhs 9 10 =>
    rw [← whisker_exchange]
  slice_lhs 7 8 =>
    rw [associator_naturality_left]
  slice_lhs 8 9 =>
    rw [← tensorHom_def]
  simp only [Mon_.monMonoidalStruct_tensorObj_X, Category.assoc, pentagon_inv_inv_hom_hom_inv_assoc,
    Mon_.tensorUnit_X]
  slice_lhs 1 7 =>
    erw [Bimon_.compatibility]
  slice_lhs 2 4 =>
    rw [antipode_left]
  simp


/--
Auxiliary calculation for `mul_antipode`.

       |
       n
      /  \
     |   n
     |  / \
     |  S S
     |  \ /
     n   /
    / \ / \
    |  /  |
    \ / \ /
     v   v
     |   |

We move the leftmost multiplication up, so we can reassociate.
We then move the rightmost comultiplication under the strand,
and simplify using `antipode_right`.
-/
theorem mul_antipode₂ (A : Hopf_ C) :
    (A.X.comul.hom ⊗ A.X.comul.hom) ≫
      (α_ A.X.X.X A.X.X.X (A.X.X.X ⊗ A.X.X.X)).hom ≫
      A.X.X.X ◁ (α_ A.X.X.X A.X.X.X A.X.X.X).inv ≫
      A.X.X.X ◁ (β_ A.X.X.X A.X.X.X).hom ▷ A.X.X.X ≫
      (α_ A.X.X.X (A.X.X.X ⊗ A.X.X.X) A.X.X.X).inv ≫
      (α_ A.X.X.X A.X.X.X A.X.X.X).inv ▷ A.X.X.X ≫
      A.X.X.mul ▷ A.X.X.X ▷ A.X.X.X ≫
      (α_ A.X.X.X A.X.X.X A.X.X.X).hom ≫
      A.X.X.X ◁ (β_ A.X.X.X A.X.X.X).hom ≫
      A.X.X.X ◁ (A.antipode ⊗ A.antipode) ≫
      A.X.X.X ◁ A.X.X.mul ≫ A.X.X.mul =
    (A.X.counit.hom ⊗ A.X.counit.hom) ≫ (λ_ (𝟙_ C)).hom ≫ A.X.X.one := by
  slice_lhs 7 8 =>
    rw [associator_naturality_left]
  slice_lhs 8 9 =>
    rw [← whisker_exchange]
  slice_lhs 9 10 =>
    rw [← whisker_exchange]
  slice_lhs 11 12 =>
    rw [Mon_.mul_assoc_flip]
  slice_lhs 10 11 =>
    rw [associator_inv_naturality_left]
  slice_lhs 11 12 =>
    simp only [← comp_whiskerRight]
    rw [Mon_.mul_assoc]
    simp only [comp_whiskerRight]
  rw [tensorHom_def]
  rw [tensor_whiskerLeft]
  rw [pentagon_inv_inv_hom_hom_inv_assoc]
  slice_lhs 7 8 =>
    rw [Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 5 7 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [← BraidedCategory.hexagon_forward]
    simp only [MonoidalCategory.whiskerLeft_comp]
  simp only [Mon_.monMonoidalStruct_tensorObj_X, tensor_whiskerLeft,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    whiskerLeft_inv_hom, Category.comp_id, whiskerLeft_hom_inv_assoc, Iso.inv_hom_id_assoc,
    pentagon_inv_inv_hom_inv_inv, whisker_assoc, Mon_.mul_assoc, Mon_.tensorUnit_X]
  slice_lhs 4 5 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [Iso.inv_hom_id]
    simp only [MonoidalCategory.whiskerLeft_comp]
  rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  slice_lhs 3 4 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [BraidedCategory.braiding_naturality_right]
    simp only [MonoidalCategory.whiskerLeft_comp]
  rw [tensorHom_def']
  simp only [MonoidalCategory.whiskerLeft_comp]
  slice_lhs 5 6 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [← associator_naturality_right]
    simp only [MonoidalCategory.whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [← whisker_exchange]
    simp only [MonoidalCategory.whiskerLeft_comp]
  slice_lhs 5 9 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [associator_inv_naturality_middle_assoc, Iso.hom_inv_id_assoc]
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
    simp only [MonoidalCategory.whiskerLeft_comp]
  slice_lhs 6 7 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [A.X.X.one_mul]
    simp only [MonoidalCategory.whiskerLeft_comp]
  slice_lhs 3 4 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [← BraidedCategory.braiding_naturality_left]
    simp only [MonoidalCategory.whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [← BraidedCategory.braiding_naturality_right]
    simp only [MonoidalCategory.whiskerLeft_comp]
  rw [← associator_naturality_middle_assoc]
  simp only [Mon_.tensorUnit_X, braiding_tensorUnit_right, MonoidalCategory.whiskerLeft_comp]
  slice_lhs 6 7 =>
    simp only [← MonoidalCategory.whiskerLeft_comp]
    rw [Iso.inv_hom_id]
    simp only [MonoidalCategory.whiskerLeft_comp]
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  slice_lhs 5 6 =>
    rw [whiskerLeft_rightUnitor, Category.assoc, ← rightUnitor_naturality]
  rw [associator_inv_naturality_right_assoc, Iso.hom_inv_id_assoc]
  slice_lhs 3 4 =>
    rw [whisker_exchange]
  slice_lhs 1 3 =>
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
  slice_lhs 2 3 =>
    rw [← whisker_exchange]
  slice_lhs 1 2 =>
    dsimp
    rw [← tensorHom_def]
  slice_lhs 2 3 =>
    rw [rightUnitor_naturality]
  simp only [Mon_.tensorUnit_X]
  monoidal

theorem mul_antipode (A : Hopf_ C) :
    A.X.X.mul ≫ A.antipode = (A.antipode ⊗ A.antipode) ≫ (β_ _ _).hom ≫ A.X.X.mul := by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv (((Bimon_.toComon_ C).obj A.X) ⊗ ((Bimon_.toComon_ C).obj A.X)) A.X.X)
    (a := A.X.X.mul)
  · -- Unfold the algebra structure in the convolution monoid,
    -- then `simp?, simp only [tensor_μ], simp?`.
    erw [Conv.mul_eq, Conv.one_eq]
    simp only [Monoidal.transportStruct_tensorObj, Equivalence.symm_functor,
      Comon_.Comon_EquivMon_OpOp_inverse, Equivalence.symm_inverse,
      Comon_.Comon_EquivMon_OpOp_functor, Comon_.Comon_ToMon_OpOp_obj, Comon_.Mon_OpOpToComon__obj,
      unop_tensorObj, Comon_.Mon_OpOpToComon_obj'_X, Mon_.monMonoidalStruct_tensorObj_X,
      Comon_.Comon_ToMon_OpOp_obj'_X, Bimon_.toComon__obj_X, Comon_.Mon_OpOpToComon_obj'_comul,
      Mon_.tensorObj_mul, Comon_.Comon_ToMon_OpOp_obj'_mul, Bimon_.toComon__obj_comul, unop_comp,
      unop_tensorHom, Quiver.Hom.unop_op, whiskerRight_tensor, comp_whiskerRight, Category.assoc,
      Comon_.Mon_OpOpToComon_obj'_counit, Mon_.tensorObj_one, Comon_.Comon_ToMon_OpOp_obj'_one,
      Bimon_.toComon__obj_counit, unop_tensorUnit, unop_inv_leftUnitor]
    simp only [tensor_μ]
    simp only [unop_comp, unop_tensorObj, unop_inv_associator, unop_whiskerLeft,
      unop_hom_associator, unop_whiskerRight, unop_hom_braiding, Category.assoc,
      pentagon_hom_inv_inv_inv_inv_assoc]
    exact mul_antipode₁ A
  · erw [Conv.mul_eq, Conv.one_eq]
    simp only [Monoidal.transportStruct_tensorObj, Equivalence.symm_functor,
      Comon_.Comon_EquivMon_OpOp_inverse, Equivalence.symm_inverse,
      Comon_.Comon_EquivMon_OpOp_functor, Comon_.Comon_ToMon_OpOp_obj, Comon_.Mon_OpOpToComon__obj,
      unop_tensorObj, Comon_.Mon_OpOpToComon_obj'_X, Mon_.monMonoidalStruct_tensorObj_X,
      Comon_.Comon_ToMon_OpOp_obj'_X, Bimon_.toComon__obj_X, Comon_.Mon_OpOpToComon_obj'_comul,
      Mon_.tensorObj_mul, Comon_.Comon_ToMon_OpOp_obj'_mul, Bimon_.toComon__obj_comul, unop_comp,
      unop_tensorHom, Quiver.Hom.unop_op, whiskerRight_tensor,
      BraidedCategory.braiding_naturality_assoc, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Comon_.Mon_OpOpToComon_obj'_counit, Mon_.tensorObj_one, Comon_.Comon_ToMon_OpOp_obj'_one,
      Bimon_.toComon__obj_counit, unop_tensorUnit, unop_inv_leftUnitor]
    simp only [tensor_μ]
    simp only [unop_comp, unop_tensorObj, unop_inv_associator, unop_whiskerLeft,
      unop_hom_associator, unop_whiskerRight, unop_hom_braiding, Category.assoc,
      pentagon_hom_inv_inv_inv_inv_assoc]
    exact mul_antipode₂ A

/--
In a commutative Hopf algebra, the antipode squares to the identity.
-/
theorem antipode_antipode (A : Hopf_ C) (comm : (β_ _ _).hom ≫ A.X.X.mul = A.X.X.mul) :
    A.antipode ≫ A.antipode = 𝟙 A.X.X.X := by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv ((Bimon_.toComon_ C).obj A.X) A.X.X)
    (a := A.antipode)
  · -- Unfold the algebra structure in the convolution monoid,
    -- then `simp?`.
    erw [Conv.mul_eq, Conv.one_eq]
    simp only [Bimon_.toComon__obj_X, Bimon_.toComon__obj_comul, comp_whiskerRight, Category.assoc,
      Bimon_.toComon__obj_counit]
    rw [← comm, ← tensorHom_def_assoc, ← mul_antipode]
    simp
  · erw [Conv.mul_eq, Conv.one_eq]
    simp

end Hopf_

end
