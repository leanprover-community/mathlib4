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

* Show that in a Cartesian monoidal category Hopf monoids are exactly group objects.
* Show that `Hopf_ (ModuleCat R) ≌ HopfAlgCat R`.
-/

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

open scoped MonObj ComonObj

/--
A Hopf monoid in a braided category `C` is a bimonoid object in `C` equipped with an antipode.
-/
class HopfObj (X : C) extends BimonObj X where
  /-- The antipode is an endomorphism of the underlying object of the Hopf monoid. -/
  antipode : X ⟶ X
  antipode_left (X) : Δ ≫ antipode ▷ X ≫ μ = ε ≫ η := by cat_disch
  antipode_right (X) : Δ ≫ X ◁ antipode ≫ μ = ε ≫ η := by cat_disch

@[deprecated (since := "2025-09-14")] alias Hopf_Class := HopfObj

namespace HopfObj

@[inherit_doc] scoped notation "𝒮" => HopfObj.antipode
@[inherit_doc] scoped notation "𝒮["M"]" => HopfObj.antipode (X := M)

attribute [reassoc (attr := simp)] antipode_left antipode_right


end HopfObj

variable (C)

/--
A Hopf monoid in a braided category `C` is a bimonoid object in `C` equipped with an antipode.
-/
structure Hopf_ where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [hopf : HopfObj X]

attribute [instance] Hopf_.hopf

namespace Hopf_

variable {C}

/-- A Hopf monoid is a bimonoid. -/
def toBimon_ (A : Hopf_ C) : Bimon_ C := .mk' A.X

/--
Morphisms of Hopf monoids are just morphisms of the underlying bimonoids.
In fact they automatically intertwine the antipodes, proved below.
-/
instance : Category (Hopf_ C) :=
  inferInstanceAs <| Category (InducedCategory (Bimon_ C) Hopf_.toBimon_)

end Hopf_

namespace HopfObj

variable {C}

/-- Morphisms of Hopf monoids intertwine the antipodes. -/
theorem hom_antipode {A B : C} [HopfObj A] [HopfObj B] (f : A ⟶ B) [IsBimon_Hom f] :
    f ≫ 𝒮 = 𝒮 ≫ f := by
  -- We show these elements are equal by exhibiting an element in the convolution algebra
  -- between `A` (as a comonoid) and `B` (as a monoid),
  -- such that the LHS is a left inverse, and the RHS is a right inverse.
  apply left_inv_eq_right_inv
    (M := Conv A B)
    (a := f)
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [comp_whiskerRight, Category.assoc]
    slice_lhs 3 4 =>
      rw [← whisker_exchange]
    slice_lhs 2 3 =>
      rw [← tensorHom_def]
    slice_lhs 1 2 =>
      rw [← IsComon_Hom.hom_comul f]
    slice_lhs 2 4 =>
      rw [antipode_left]
    slice_lhs 1 2 =>
      rw [IsComon_Hom.hom_counit]
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [whiskerLeft_comp, Category.assoc]
    slice_lhs 2 3 =>
      rw [← whisker_exchange]
    slice_lhs 3 4 =>
      rw [← tensorHom_def]
    slice_lhs 3 4 =>
      rw [← IsMon_Hom.mul_hom]
    slice_lhs 1 3 =>
      rw [antipode_right]
    slice_lhs 2 3 =>
      rw [IsMon_Hom.one_hom]

@[reassoc (attr := simp)]
theorem one_antipode (A : C) [HopfObj A] : η[A] ≫ 𝒮[A] = η[A] := by
  have := (rfl : η[A] ≫ Δ[A] ≫ (𝒮[A] ▷ A) ≫ μ[A] = _)
  conv at this =>
    rhs
    rw [antipode_left]
  rw [Bimon_.one_comul_assoc, tensorHom_def_assoc, unitors_inv_equal,
    ← rightUnitor_inv_naturality_assoc, whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc,
    rightUnitor_inv_naturality_assoc] at this
  simpa

@[reassoc (attr := simp)]
theorem antipode_counit (A : C) [HopfObj A] : 𝒮[A] ≫ ε[A] = ε[A] := by
  have := (rfl : Δ[A] ≫ (𝒮[A] ▷ A) ≫ μ[A] ≫ ε[A] = _)
  conv at this =>
    rhs
    rw [antipode_left_assoc]
  rw [Bimon_.mul_counit, tensorHom_def', Category.assoc, ← whisker_exchange_assoc] at this
  simpa [unitors_equal]

/-!
## The antipode is an antihomomorphism with respect to both the monoid and comonoid structures.
-/

theorem antipode_comul₁ (A : C) [HopfObj A] :
    Δ[A] ≫
      𝒮[A] ▷ A ≫
      Δ[A] ▷ A ≫
      (α_ A A A).hom ≫
      A ◁ A ◁ Δ[A] ≫
      A ◁ (α_ A A A).inv ≫
      A ◁ (β_ A A).hom ▷ A ≫
      A ◁ (α_ A A A).hom ≫
      (α_ A A (A ⊗ A)).inv ≫
      (μ[A] ⊗ₘ μ[A]) =
    ε[A] ≫ (λ_ (𝟙_ C)).inv ≫ (η[A] ⊗ₘ η[A]) := by
  slice_lhs 3 5 =>
    rw [← associator_naturality_right, ← Category.assoc, ← tensorHom_def]
  slice_lhs 3 9 =>
    rw [Bimon_.compatibility]
  slice_lhs 1 3 =>
    rw [antipode_left]
  simp [MonObj.tensorObj.one_def]

/--
Auxiliary calculation for `antipode_comul`.
This calculation calls for some ASCII art out of This Week's Finds.

```
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
```

We move the left antipode up through the crossing,
the right antipode down through the crossing,
the right multiplication down across the strand,
reassociate the comultiplications,
then use `antipode_right` then `antipode_left` to simplify.
-/
theorem antipode_comul₂ (A : C) [HopfObj A] :
    Δ[A] ≫
      Δ[A] ▷ A ≫
      (α_ A A A).hom ≫
      A ◁ A ◁ Δ[A] ≫
      A ◁ A ◁ (β_ A A).hom ≫
      A ◁ A ◁ (𝒮[A] ⊗ₘ 𝒮[A]) ≫
      A ◁ (α_ A A A).inv ≫
      A ◁ (β_ A A).hom ▷ A ≫
      A ◁ (α_ A A A).hom ≫
      (α_ A A (A ⊗ A)).inv ≫
      (μ[A] ⊗ₘ μ[A]) =
    ε[A] ≫ (λ_ (𝟙_ C)).inv ≫ (η[A] ⊗ₘ η[A]) := by
  -- We should write a version of `slice_lhs` that zooms through whiskerings.
  slice_lhs 6 6 =>
    simp only [tensorHom_def', whiskerLeft_comp]
  slice_lhs 7 8 =>
    rw [← whiskerLeft_comp, associator_inv_naturality_middle, whiskerLeft_comp]
  slice_lhs 8 9 =>
    rw [← whiskerLeft_comp, ← comp_whiskerRight, BraidedCategory.braiding_naturality_right,
      comp_whiskerRight, whiskerLeft_comp]
  slice_lhs 9 10 =>
    rw [← whiskerLeft_comp, associator_naturality_left, whiskerLeft_comp]
  slice_lhs 5 6 =>
    rw [← whiskerLeft_comp, ← whiskerLeft_comp, ← BraidedCategory.braiding_naturality_left,
      whiskerLeft_comp, whiskerLeft_comp]
  slice_lhs 11 12 =>
    rw [tensorHom_def', ← Category.assoc, ← associator_inv_naturality_right]
  slice_lhs 10 11 =>
    rw [← whiskerLeft_comp, ← whisker_exchange, whiskerLeft_comp]
  slice_lhs 6 10 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.hexagon_reverse_assoc, Iso.inv_hom_id_assoc,
      ← BraidedCategory.braiding_naturality_left]
    simp only [whiskerLeft_comp]
  rw [ComonObj.comul_assoc_flip_assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 =>
    simp only [← whiskerLeft_comp]
    rw [ComonObj.comul_assoc]
    simp only [whiskerLeft_comp]
  slice_lhs 3 7 =>
    simp only [← whiskerLeft_comp]
    rw [← associator_naturality_middle_assoc, Iso.hom_inv_id_assoc]
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
    simp only [whiskerLeft_comp]
  slice_lhs 2 3 =>
    simp only [← whiskerLeft_comp]
    rw [ComonObj.counit_comul]
    simp only [whiskerLeft_comp]
  slice_lhs 3 4 =>
    simp only [← whiskerLeft_comp]
    rw [BraidedCategory.braiding_naturality_left]
    simp only [whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← whiskerLeft_comp]
    rw [whisker_exchange]
    simp only [whiskerLeft_comp]
  slice_lhs 5 7 =>
    rw [associator_inv_naturality_right_assoc, whisker_exchange]
  simp only [braiding_tensorUnit_left,
    whiskerLeft_comp, whiskerLeft_rightUnitor_inv,
    whiskerRight_id, whiskerLeft_rightUnitor, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc, whiskerLeft_inv_hom_assoc, antipode_right_assoc]
  rw [rightUnitor_inv_naturality_assoc, tensorHom_def]
  monoidal

theorem antipode_comul (A : C) [HopfObj A] :
    𝒮[A] ≫ Δ[A] = Δ[A] ≫ (β_ _ _).hom ≫ (𝒮[A] ⊗ₘ 𝒮[A]) := by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv A (A ⊗ A))
    (a := Δ[A])
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [comp_whiskerRight, tensor_whiskerLeft, MonObj.tensorObj.mul_def, Category.assoc,
      MonObj.tensorObj.one_def]
    simp only [tensorμ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact antipode_comul₁ A
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [whiskerLeft_comp, tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc,
      MonObj.tensorObj.mul_def, MonObj.tensorObj.one_def]
    simp only [tensorμ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact antipode_comul₂ A

theorem mul_antipode₁ (A : C) [HopfObj A] :
    (Δ[A] ⊗ₘ Δ[A]) ≫
      (α_ A A (A ⊗ A)).hom ≫
      A ◁ (α_ A A A).inv ≫
      A ◁ (β_ A A).hom ▷ A ≫
      (α_ A (A ⊗ A) A).inv ≫
      (α_ A A A).inv ▷ A ≫
      μ[A] ▷ A ▷ A ≫
      𝒮[A] ▷ A ▷ A ≫
      (α_ A A A).hom ≫
      A ◁ μ[A] ≫
      μ[A] =
    (ε[A] ⊗ₘ ε[A]) ≫ (λ_ (𝟙_ C)).hom ≫ η[A] := by
  slice_lhs 8 9 =>
    rw [associator_naturality_left]
  slice_lhs 9 10 =>
    rw [← whisker_exchange]
  slice_lhs 7 8 =>
    rw [associator_naturality_left]
  slice_lhs 8 9 =>
    rw [← tensorHom_def]
  simp


/--
Auxiliary calculation for `mul_antipode`.

```
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
```

We move the leftmost multiplication up, so we can reassociate.
We then move the rightmost comultiplication under the strand,
and simplify using `antipode_right`.
-/
theorem mul_antipode₂ (A : C) [HopfObj A] :
    (Δ[A] ⊗ₘ Δ[A]) ≫
      (α_ A A (A ⊗ A)).hom ≫
      A ◁ (α_ A A A).inv ≫
      A ◁ (β_ A A).hom ▷ A ≫
      (α_ A (A ⊗ A) A).inv ≫
      (α_ A A A).inv ▷ A ≫
      μ[A] ▷ A ▷ A ≫
      (α_ A A A).hom ≫
      A ◁ (β_ A A).hom ≫
      A ◁ (𝒮[A] ⊗ₘ 𝒮[A]) ≫
      A ◁ μ[A] ≫ μ[A] =
    (ε[A] ⊗ₘ ε[A]) ≫ (λ_ (𝟙_ C)).hom ≫ η[A] := by
  slice_lhs 7 8 =>
    rw [associator_naturality_left]
  slice_lhs 8 9 =>
    rw [← whisker_exchange]
  slice_lhs 9 10 =>
    rw [← whisker_exchange]
  slice_lhs 11 12 =>
    rw [MonObj.mul_assoc_flip]
  slice_lhs 10 11 =>
    rw [associator_inv_naturality_left]
  slice_lhs 11 12 =>
    simp only [← comp_whiskerRight]
    rw [MonObj.mul_assoc]
    simp only [comp_whiskerRight]
  rw [tensorHom_def]
  rw [tensor_whiskerLeft _ _ (β_ A A).hom]
  rw [pentagon_inv_inv_hom_hom_inv_assoc]
  slice_lhs 7 8 =>
    rw [Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 5 7 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.hexagon_forward]
    simp only [whiskerLeft_comp]
  simp only [tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc, pentagon_inv_inv_hom_inv_inv,
    whisker_assoc, MonObj.mul_assoc, whiskerLeft_inv_hom_assoc]
  slice_lhs 3 4 =>
    simp only [← whiskerLeft_comp]
    rw [BraidedCategory.braiding_naturality_right]
    simp only [whiskerLeft_comp]
  rw [tensorHom_def']
  simp only [whiskerLeft_comp]
  slice_lhs 5 6 =>
    simp only [← whiskerLeft_comp]
    rw [← associator_naturality_right]
    simp only [whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← whiskerLeft_comp]
    rw [← whisker_exchange]
    simp only [whiskerLeft_comp]
  slice_lhs 5 9 =>
    simp only [← whiskerLeft_comp]
    rw [associator_inv_naturality_middle_assoc, Iso.hom_inv_id_assoc]
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
    simp only [whiskerLeft_comp]
  slice_lhs 6 7 =>
    simp only [← whiskerLeft_comp]
    rw [MonObj.one_mul]
    simp only [whiskerLeft_comp]
  slice_lhs 3 4 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.braiding_naturality_left]
    simp only [whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.braiding_naturality_right]
    simp only [whiskerLeft_comp]
  rw [← associator_naturality_middle_assoc]
  simp only [braiding_tensorUnit_right, whiskerLeft_comp]
  slice_lhs 6 7 =>
    simp only [← whiskerLeft_comp]
    rw [Iso.inv_hom_id]
    simp only [whiskerLeft_comp]
  simp only [whiskerLeft_id, Category.id_comp]
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
  monoidal

theorem mul_antipode (A : C) [HopfObj A] :
    μ[A] ≫ 𝒮[A] = (𝒮[A] ⊗ₘ 𝒮[A]) ≫ (β_ _ _).hom ≫ μ[A] := by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv (A ⊗ A) A)
    (a := μ[A])
  · -- Unfold the algebra structure in the convolution monoid,
    -- then `simp?, simp only [tensor_μ], simp?`.
    rw [Conv.mul_eq, Conv.one_eq]
    simp only [Comon_.tensorObj_comul, whiskerRight_tensor, comp_whiskerRight, Category.assoc,
      Comon_.tensorObj_counit]
    simp only [tensorμ]
    simp only [Category.assoc, pentagon_hom_inv_inv_inv_inv_assoc]
    exact mul_antipode₁ A
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [Comon_.tensorObj_comul, whiskerRight_tensor,
      BraidedCategory.braiding_naturality_assoc, whiskerLeft_comp, Category.assoc,
      Comon_.tensorObj_counit]
    simp only [tensorμ]
    simp only [Category.assoc, pentagon_hom_inv_inv_inv_inv_assoc]
    exact mul_antipode₂ A

/--
In a commutative Hopf algebra, the antipode squares to the identity.
-/
theorem antipode_antipode (A : C) [HopfObj A] (comm : (β_ _ _).hom ≫ μ[A] = μ[A]) :
    𝒮[A] ≫ 𝒮[A] = 𝟙 A := by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv A A)
    (a := 𝒮[A])
  · -- Unfold the algebra structure in the convolution monoid,
    -- then `simp?`.
    rw [Conv.mul_eq, Conv.one_eq]
    simp only [comp_whiskerRight, Category.assoc]
    rw [← comm, ← tensorHom_def_assoc, ← mul_antipode]
    simp
  · rw [Conv.mul_eq, Conv.one_eq]
    simp

end HopfObj

end
