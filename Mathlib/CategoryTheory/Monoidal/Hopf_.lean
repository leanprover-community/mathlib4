/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Saul Glasman
-/
module

public import Mathlib.CategoryTheory.Monoidal.Bimon_
public import Mathlib.CategoryTheory.Monoidal.Conv
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.HopfAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Internal.Module

/-!
# The category of Hopf monoids in a braided monoidal category.


## TODO

* Show that in a Cartesian monoidal category Hopf monoids are exactly group objects.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

namespace CategoryTheory
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

namespace HopfObj

@[inherit_doc] scoped notation "𝒮" => HopfObj.antipode
@[inherit_doc] scoped notation "𝒮[" M "]" => HopfObj.antipode (X := M)

attribute [reassoc (attr := simp)] antipode_left antipode_right


end HopfObj

variable (C)

/--
A Hopf monoid in a braided category `C` is a bimonoid object in `C` equipped with an antipode.
-/
structure Hopf where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [hopf : HopfObj X]

attribute [instance] Hopf.hopf

namespace Hopf

variable {C}

/-- A Hopf monoid is a bimonoid. -/
def toBimon (A : Hopf C) : Bimon C := .mk' A.X

/--
Morphisms of Hopf monoids are just morphisms of the underlying bimonoids.
In fact they automatically intertwine the antipodes, proved below.
-/
instance : Category (Hopf C) :=
  inferInstanceAs <| Category (InducedCategory (Bimon C) Hopf.toBimon)

end Hopf

namespace HopfObj

variable {C}

/-- Morphisms of Hopf monoids intertwine the antipodes. -/
theorem hom_antipode {A B : C} [HopfObj A] [HopfObj B] (f : A ⟶ B) [IsBimonHom f] :
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
      rw [← IsComonHom.hom_comul f]
    slice_lhs 2 4 =>
      rw [antipode_left]
    slice_lhs 1 2 =>
      rw [IsComonHom.hom_counit]
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [whiskerLeft_comp, Category.assoc]
    slice_lhs 2 3 =>
      rw [← whisker_exchange]
    slice_lhs 3 4 =>
      rw [← tensorHom_def]
    slice_lhs 3 4 =>
      rw [← IsMonHom.mul_hom]
    slice_lhs 1 3 =>
      rw [antipode_right]
    slice_lhs 2 3 =>
      rw [IsMonHom.one_hom]

@[reassoc (attr := simp)]
theorem one_antipode (A : C) [HopfObj A] : η[A] ≫ 𝒮[A] = η[A] := by
  have := (rfl : η[A] ≫ Δ[A] ≫ (𝒮[A] ▷ A) ≫ μ[A] = _)
  conv at this =>
    rhs
    rw [antipode_left]
  rw [Bimon.one_comul_assoc, tensorHom_def_assoc, unitors_inv_equal,
    ← rightUnitor_inv_naturality_assoc, whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc,
    rightUnitor_inv_naturality_assoc] at this
  simpa

@[reassoc (attr := simp)]
theorem antipode_counit (A : C) [HopfObj A] : 𝒮[A] ≫ ε[A] = ε[A] := by
  have := (rfl : Δ[A] ≫ (𝒮[A] ▷ A) ≫ μ[A] ≫ ε[A] = _)
  conv at this =>
    rhs
    rw [antipode_left_assoc]
  rw [Bimon.mul_counit, tensorHom_def', Category.assoc, ← whisker_exchange_assoc] at this
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
    rw [Bimon.compatibility]
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
    simp only [Comon.tensorObj_comul, whiskerRight_tensor, comp_whiskerRight, Category.assoc,
      Comon.tensorObj_counit]
    simp only [tensorμ]
    simp only [Category.assoc, pentagon_hom_inv_inv_inv_inv_assoc]
    exact mul_antipode₁ A
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [Comon.tensorObj_comul, whiskerRight_tensor,
      BraidedCategory.braiding_naturality_assoc, whiskerLeft_comp, Category.assoc,
      Comon.tensorObj_counit]
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

variable (R : Type u₁) [CommRing R]

lemma mul_eq_tensorμ (M : ModuleCat R) [MonObj M] (a b : (M ⊗ M : ModuleCat R)) :
    @HMul.hMul _ _ _ (@instHMul _ Algebra.TensorProduct.instMul) a b =
      (μ[M] ⊗ₘ μ[M]) (tensorμ M M M M (a ⊗ₜ b)) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => induction b using TensorProduct.induction_on with
    | add w v hw hv => simp only [mul_add, hw, hv, TensorProduct.tmul_add, map_add]
    | zero => simp
    | tmul w v =>
      simp only [ModuleCat.MonoidalCategory.tensorμ_apply, Algebra.TensorProduct.tmul_mul_tmul]
      rw [ModuleCat.MonoidalCategory.tensorHom_tmul]
      rfl
  | add x y hx hy => induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul w v => simp only [add_mul, hx, hy, TensorProduct.add_tmul, map_add]
    | add w v _ _ => simp only [add_mul, hx, hy, TensorProduct.add_tmul, map_add]

instance coalgebraOfComonObj (M : ModuleCat R) [ComonObj M] : Coalgebra R M := {
  comul := Δ[M].hom
  counit := ε[M].hom
  coassoc := by
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_whiskerLeft, ModuleCat.hom_whiskerRight,
      ModuleCat.hom_hom_associator, eq_comm] using congr_arg ModuleCat.Hom.hom
      (ComonObj.comul_assoc M)
  rTensor_counit_comp_comul := congr_arg ModuleCat.Hom.hom (ComonObj.counit_comul M)
  lTensor_counit_comp_comul := congr_arg ModuleCat.Hom.hom (ComonObj.comul_counit M)
}

instance bialgebraOfBimonObj (M : ModuleCat R) [BimonObj M] : Bialgebra R M := by
  refine Bialgebra.mk' R M ?_ ?_ ?_ ?_
  · exact DFunLike.congr_fun (congr_arg ModuleCat.Hom.hom (BimonObj.one_counit M)) (1 : R)
  · intro a b
    exact DFunLike.congr_fun (congr_arg ModuleCat.Hom.hom (BimonObj.mul_counit M)) (a ⊗ₜ b)
  · exact DFunLike.congr_fun (congr_arg ModuleCat.Hom.hom (BimonObj.one_comul M)) 1
  · intro a b
    simpa only [mul_eq_tensorμ] using DFunLike.congr_fun (congr_arg ModuleCat.Hom.hom
      (BimonObj.mul_comul M)) (a ⊗ₜ b)

instance hopfAlgebraOfHopfObj (M : ModuleCat R) [HopfObj M] : HopfAlgebra R M := by
  have mul'_eq : LinearMap.mul' R M = μ[M].hom := by
    ext a b
    simp
    rfl
  exact {
    antipode := 𝒮[M].hom
    mul_antipode_rTensor_comul := by
      simp only [mul'_eq]
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_whiskerRight, LinearMap.comp_assoc] using
        congr_arg ModuleCat.Hom.hom (HopfObj.antipode_left M)
    mul_antipode_lTensor_comul := by
      simp only [mul'_eq]
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_whiskerLeft, LinearMap.comp_assoc] using
        congr_arg ModuleCat.Hom.hom (HopfObj.antipode_right M)
  }

instance monObjOfHopfAlgebra (A : HopfAlgCat R) : MonObj (ModuleCat.of R A) where
  one := ModuleCat.ofHom (Algebra.linearMap _ _)
  mul := ModuleCat.ofHom (LinearMap.mul' _ _)
  one_mul := by
    change ModuleCat.ofHom ((Algebra.linearMap R A).rTensor A) ≫
      ModuleCat.ofHom (LinearMap.mul' R A) =
      (λ_ (ModuleCat.of R A)).hom
    rw [← ModuleCat.ofHom_comp]
    ext m
    simp [ModuleCat.hom_hom_leftUnitor]
  mul_one := by
    change ModuleCat.ofHom ((Algebra.linearMap R A).lTensor A) ≫
      ModuleCat.ofHom (LinearMap.mul' R A) =
      (ρ_ (ModuleCat.of R A)).hom
    rw [← ModuleCat.ofHom_comp]
    ext m
    simp [ModuleCat.hom_hom_rightUnitor]
  mul_assoc := by
    change ModuleCat.ofHom ((LinearMap.mul' R ↑(ModuleCat.of R A)).rTensor A) ≫
      ModuleCat.ofHom (LinearMap.mul' R ↑(ModuleCat.of R A)) =
      (α_ (ModuleCat.of R A) (ModuleCat.of R A) (ModuleCat.of R A)).hom ≫
      ModuleCat.ofHom ((LinearMap.mul' R ↑(ModuleCat.of R A)).lTensor A) ≫
      ModuleCat.ofHom (LinearMap.mul' R ↑(ModuleCat.of R A))
    ext a b c
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
      TensorProduct.curry_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.rTensor_tmul, LinearMap.mul'_apply, ModuleCat.hom_hom_associator]
    erw [LinearEquiv.coe_coe]
    simp only [TensorProduct.assoc_tmul]
    erw [LinearMap.lTensor_tmul A (LinearMap.mul' R A) a (b ⊗ₜ[R] c)]
    simp only [LinearMap.mul'_apply, mul_assoc]

instance hopfObjOfHopfAlgebra (A : HopfAlgCat R) : HopfObj (ModuleCat.of R A) where
  counit := ModuleCat.ofHom Coalgebra.counit
  comul := ModuleCat.ofHom Coalgebra.comul
  counit_comul := congr_arg ModuleCat.ofHom (Coalgebra.rTensor_counit_comp_comul)
  comul_counit := congr_arg ModuleCat.ofHom (Coalgebra.lTensor_counit_comp_comul)
  comul_assoc := congr_arg ModuleCat.ofHom (Coalgebra.coassoc).symm
  mul_comul := by
    ext t
    induction t using TensorProduct.induction_on with
    | zero => simp only [ModuleCat.hom_comp, map_zero]
    | tmul a b =>
      change CoalgebraStruct.comul (a * b) =
        (TensorProduct.map (LinearMap.mul' R A) (LinearMap.mul' R A))
          ((ModuleCat.Hom.hom
              (tensorμ (ModuleCat.of R A) (ModuleCat.of R A) (ModuleCat.of R A)
                (ModuleCat.of R A)))
            (((CoalgebraStruct.comul a) ⊗ₜ[R] (CoalgebraStruct.comul b))))
      rw [@Bialgebra.comul_mul R A _ _ _ a b]
      exact mul_eq_tensorμ R (ModuleCat.of R A)
        (CoalgebraStruct.comul a) (CoalgebraStruct.comul b)
    | add x y hx hy =>
      simp only [map_add]
      exact congr_arg₂ (· + ·) hx hy
  one_comul := by
    ext
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    erw [map_one (algebraMap R A), Bialgebra.comul_one (R := R) (A := A)]
    simp only [MonObj.tensorObj.one_def, Algebra.TensorProduct.one_def, ModuleCat.hom_comp,
      LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_inv_leftUnitor,
      TensorProduct.toLinearMap_symm_lid, ModuleCat.hom_tensorHom]
    erw [TensorProduct.mk_apply, map_one (algebraMap R A)]
  mul_counit := by
    ext t
    induction t using TensorProduct.induction_on with
    | zero => simp only [ModuleCat.hom_comp, map_zero, Comon.tensorObj_counit]
    | tmul a b => exact @Bialgebra.counit_mul R A _ _ _ a b
    | add x y hx hy =>
      simp only [map_add]
      exact congr_arg₂ (· + ·) hx hy
  one_counit := by
    ext
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_id]
    erw [map_one (algebraMap R A)]
    exact Bialgebra.counit_one
  antipode := ModuleCat.ofHom (HopfAlgebra.antipode _)
  antipode_left := congr_arg ModuleCat.ofHom
    (@HopfAlgebra.mul_antipode_rTensor_comul R A _ _ _)
  antipode_right := congr_arg ModuleCat.ofHom
    (@HopfAlgebra.mul_antipode_lTensor_comul R A _ _ _)

/-- The functor from Hopf objects in `ModuleCat R` to the category of `R`-Hopf algebras. -/
def moduleCatToHopfAlgCat : Hopf (ModuleCat R) ⥤ HopfAlgCat R := {
  obj M := HopfAlgCat.of R M.X

  map {M N} f := HopfAlgCat.ofHom {
    toFun := f.hom.hom.hom
    map_add' := LinearMap.map_add (ModuleCat.Hom.hom f.hom.hom.hom)
    map_smul' := LinearMap.map_smul (ModuleCat.Hom.hom f.hom.hom.hom)
    counit_comp := congr_arg ModuleCat.Hom.hom (
      congr_arg CategoryTheory.Mon.Hom.hom (IsComonHom.hom_counit f.hom.hom))
    map_comp_comul := (congr_arg ModuleCat.Hom.hom (congr_arg CategoryTheory.Mon.Hom.hom
      (IsComonHom.hom_comul f.hom.hom))).symm
    map_one' := DFunLike.congr_fun (congr_arg ModuleCat.Hom.hom (IsMonHom.one_hom f.hom.hom.hom))
      1
    map_mul' := fun x y ↦
      DFunLike.congr_fun (congr_arg ModuleCat.Hom.hom (IsMonHom.mul_hom f.hom.hom.hom)) (x ⊗ₜ[R] y)
  }
}

/-- `moduleCatToHopfAlgCat R` is an equivalence of categories. -/
instance isEquivModuleCatToHopfAlgCat : Functor.IsEquivalence (moduleCatToHopfAlgCat R) := {
  faithful := ⟨by
    intro _ _ f g hfg
    simp only [moduleCatToHopfAlgCat] at hfg
    have h := congr_arg ConcreteCategory.hom hfg
    cases f
    cases g
    congr 1
    ext x
    exact DFunLike.congr_fun h x⟩
  full := ⟨by
    intro M N f
    use ⟨Comon.Hom.mk' (Mon.Hom.mk' (ModuleCat.ofHom f.toBialgHom'.toLinearMap)
      (by
        ext
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        convert (show f.toBialgHom'.toLinearMap 1 = 1 from f.toBialgHom.map_one)
      )
      (by
        ext t
        induction t using TensorProduct.induction_on with
        | zero => simp only [ModuleCat.hom_comp, map_zero]
        | tmul x y => exact f.toBialgHom.map_mul x y
        | add x y hx hy =>
            simp only [map_add]
            exact congr_arg₂ (· + ·) hx hy
      ))
      (by ext m; exact DFunLike.congr_fun f.toBialgHom.counit_comp m)
      (by ext m; exact DFunLike.congr_fun f.toBialgHom.map_comp_comul.symm m)
    ⟩
    rfl
  ⟩
  essSurj := ⟨fun M ↦
    ⟨⟨ModuleCat.of R M⟩, ⟨{
      hom := ⟨⟨CoalgHom.id R M.carrier, map_one (algebraMap R M.carrier), by intro x y; rfl⟩⟩,
      inv := ⟨⟨
        CoalgHom.id R M.carrier,
        (map_one (algebraMap R M.carrier)).symm,
        by intro x y; rfl
      ⟩⟩,
      hom_inv_id := rfl,
      inv_hom_id := rfl
    }⟩⟩
  ⟩
}

end HopfObj
end CategoryTheory
