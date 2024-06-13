/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.GroupTheory.Perm.Basic

#align_import algebra.hom.aut from "leanprover-community/mathlib"@"d4f69d96f3532729da8ebb763f4bc26fcf640f06"

/-!
# Multiplicative and additive group automorphisms

This file defines the automorphism group structure on `AddAut R := AddEquiv R R` and
`MulAut R := MulEquiv R R`.

## Implementation notes

The definition of multiplication in the automorphism groups agrees with function composition,
multiplication in `Equiv.Perm`, and multiplication in `CategoryTheory.End`, but not with
`CategoryTheory.comp`.

This file is kept separate from `Data/Equiv/MulAdd` so that `GroupTheory.Perm` is free to use
equivalences (and other files that use them) before the group structure is defined.

## Tags

MulAut, AddAut
-/

-- TODO after #13161
-- assert_not_exists MonoidWithZero
assert_not_exists Ring

variable {A : Type*} {M : Type*} {G : Type*}

/-- The group of multiplicative automorphisms. -/
@[reducible, to_additive "The group of additive automorphisms."]
def MulAut (M : Type*) [Mul M] :=
  M ≃* M
#align mul_aut MulAut
#align add_aut AddAut

-- Note that `(attr := reducible)` in `to_additive` currently doesn't work,
-- so we add the reducible attribute manually.
attribute [reducible] AddAut

namespace MulAut

variable (M) [Mul M]

/-- The group operation on multiplicative automorphisms is defined by `g h => MulEquiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance : Group (MulAut M) where
  mul g h := MulEquiv.trans h g
  one := MulEquiv.refl _
  inv := MulEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  mul_left_inv := MulEquiv.self_trans_symm

instance : Inhabited (MulAut M) :=
  ⟨1⟩

@[simp]
theorem coe_mul (e₁ e₂ : MulAut M) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl
#align mul_aut.coe_mul MulAut.coe_mul

@[simp]
theorem coe_one : ⇑(1 : MulAut M) = id :=
  rfl
#align mul_aut.coe_one MulAut.coe_one

theorem mul_def (e₁ e₂ : MulAut M) : e₁ * e₂ = e₂.trans e₁ :=
  rfl
#align mul_aut.mul_def MulAut.mul_def

theorem one_def : (1 : MulAut M) = MulEquiv.refl _ :=
  rfl
#align mul_aut.one_def MulAut.one_def

theorem inv_def (e₁ : MulAut M) : e₁⁻¹ = e₁.symm :=
  rfl
#align mul_aut.inv_def MulAut.inv_def

@[simp]
theorem mul_apply (e₁ e₂ : MulAut M) (m : M) : (e₁ * e₂) m = e₁ (e₂ m) :=
  rfl
#align mul_aut.mul_apply MulAut.mul_apply

@[simp]
theorem one_apply (m : M) : (1 : MulAut M) m = m :=
  rfl
#align mul_aut.one_apply MulAut.one_apply

@[simp]
theorem apply_inv_self (e : MulAut M) (m : M) : e (e⁻¹ m) = m :=
  MulEquiv.apply_symm_apply _ _
#align mul_aut.apply_inv_self MulAut.apply_inv_self

@[simp]
theorem inv_apply_self (e : MulAut M) (m : M) : e⁻¹ (e m) = m :=
  MulEquiv.apply_symm_apply _ _
#align mul_aut.inv_apply_self MulAut.inv_apply_self

/-- Monoid hom from the group of multiplicative automorphisms to the group of permutations. -/
def toPerm : MulAut M →* Equiv.Perm M where
  toFun := MulEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl
#align mul_aut.to_perm MulAut.toPerm

/-- The tautological action by `MulAut M` on `M`.

This generalizes `Function.End.applyMulAction`. -/
instance applyMulDistribMulAction {M} [Monoid M] : MulDistribMulAction (MulAut M) M where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one := MulEquiv.map_one
  smul_mul := MulEquiv.map_mul
#align mul_aut.apply_mul_distrib_mul_action MulAut.applyMulDistribMulAction

@[simp]
protected theorem smul_def {M} [Monoid M] (f : MulAut M) (a : M) : f • a = f a :=
  rfl
#align mul_aut.smul_def MulAut.smul_def

/-- `MulAut.applyDistribMulAction` is faithful. -/
instance apply_faithfulSMul {M} [Monoid M] : FaithfulSMul (MulAut M) M :=
  ⟨ fun h => MulEquiv.ext h ⟩
#align mul_aut.apply_has_faithful_smul MulAut.apply_faithfulSMul

/-- Group conjugation, `MulAut.conj g h = g * h * g⁻¹`, as a monoid homomorphism
mapping multiplication in `G` into multiplication in the automorphism group `MulAut G`.
See also the type `ConjAct G` for any group `G`, which has a `MulAction (ConjAct G) G` instance
where `conj G` acts on `G` by conjugation. -/
def conj [Group G] : G →* MulAut G where
  toFun g :=
    { toFun := fun h => g * h * g⁻¹
      invFun := fun h => g⁻¹ * h * g
      left_inv := fun _ => by simp only [mul_assoc, inv_mul_cancel_left, mul_left_inv, mul_one]
      right_inv := fun _ => by simp only [mul_assoc, mul_inv_cancel_left, mul_right_inv, mul_one]
      map_mul' := by simp only [mul_assoc, inv_mul_cancel_left, forall_const] }
  map_mul' g₁ g₂ := by
    ext h
    show g₁ * g₂ * h * (g₁ * g₂)⁻¹ = g₁ * (g₂ * h * g₂⁻¹) * g₁⁻¹
    simp only [mul_assoc, mul_inv_rev]
  map_one' := by ext; simp only [one_mul, inv_one, mul_one, one_apply]; rfl
#align mul_aut.conj MulAut.conj

@[simp]
theorem conj_apply [Group G] (g h : G) : conj g h = g * h * g⁻¹ :=
  rfl
#align mul_aut.conj_apply MulAut.conj_apply

@[simp]
theorem conj_symm_apply [Group G] (g h : G) : (conj g).symm h = g⁻¹ * h * g :=
  rfl
#align mul_aut.conj_symm_apply MulAut.conj_symm_apply

@[simp]
theorem conj_inv_apply [Group G] (g h : G) : (conj g)⁻¹ h = g⁻¹ * h * g :=
  rfl
#align mul_aut.conj_inv_apply MulAut.conj_inv_apply

end MulAut

namespace AddAut

variable (A) [Add A]

/-- The group operation on additive automorphisms is defined by `g h => AddEquiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance group : Group (AddAut A) where
  mul g h := AddEquiv.trans h g
  one := AddEquiv.refl _
  inv := AddEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  mul_left_inv := AddEquiv.self_trans_symm
#align add_aut.group AddAut.group

instance : Inhabited (AddAut A) :=
  ⟨1⟩

@[simp]
theorem coe_mul (e₁ e₂ : AddAut A) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl
#align add_aut.coe_mul AddAut.coe_mul

@[simp]
theorem coe_one : ⇑(1 : AddAut A) = id :=
  rfl
#align add_aut.coe_one AddAut.coe_one

theorem mul_def (e₁ e₂ : AddAut A) : e₁ * e₂ = e₂.trans e₁ :=
  rfl
#align add_aut.mul_def AddAut.mul_def

theorem one_def : (1 : AddAut A) = AddEquiv.refl _ :=
  rfl
#align add_aut.one_def AddAut.one_def

theorem inv_def (e₁ : AddAut A) : e₁⁻¹ = e₁.symm :=
  rfl
#align add_aut.inv_def AddAut.inv_def

@[simp]
theorem mul_apply (e₁ e₂ : AddAut A) (a : A) : (e₁ * e₂) a = e₁ (e₂ a) :=
  rfl
#align add_aut.mul_apply AddAut.mul_apply

@[simp]
theorem one_apply (a : A) : (1 : AddAut A) a = a :=
  rfl
#align add_aut.one_apply AddAut.one_apply

@[simp]
theorem apply_inv_self (e : AddAut A) (a : A) : e⁻¹ (e a) = a :=
  AddEquiv.apply_symm_apply _ _
#align add_aut.apply_inv_self AddAut.apply_inv_self

@[simp]
theorem inv_apply_self (e : AddAut A) (a : A) : e (e⁻¹ a) = a :=
  AddEquiv.apply_symm_apply _ _
#align add_aut.inv_apply_self AddAut.inv_apply_self

/-- Monoid hom from the group of multiplicative automorphisms to the group of permutations. -/
def toPerm : AddAut A →* Equiv.Perm A where
  toFun := AddEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl
#align add_aut.to_perm AddAut.toPerm

/-- The tautological action by `AddAut A` on `A`.

This generalizes `Function.End.applyMulAction`. -/
instance applyDistribMulAction {A} [AddMonoid A] : DistribMulAction (AddAut A) A where
  smul := (· <| ·)
  smul_zero := AddEquiv.map_zero
  smul_add := AddEquiv.map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align add_aut.apply_distrib_mul_action AddAut.applyDistribMulAction

@[simp]
protected theorem smul_def {A} [AddMonoid A] (f : AddAut A) (a : A) : f • a = f a :=
  rfl
#align add_aut.smul_def AddAut.smul_def

/-- `AddAut.applyDistribMulAction` is faithful. -/
instance apply_faithfulSMul {A} [AddMonoid A] : FaithfulSMul (AddAut A) A :=
  ⟨fun h => AddEquiv.ext h⟩
#align add_aut.apply_has_faithful_smul AddAut.apply_faithfulSMul

/-- Additive group conjugation, `AddAut.conj g h = g + h - g`, as an additive monoid
homomorphism mapping addition in `G` into multiplication in the automorphism group `AddAut G`
(written additively in order to define the map). -/
def conj [AddGroup G] : G →+ Additive (AddAut G) where
  toFun g :=
    @Additive.ofMul (AddAut G)
      { toFun := fun h => g + h + -g
        -- this definition is chosen to match `MulAut.conj`
        invFun := fun h => -g + h + g
        left_inv := fun _ => by simp only [add_assoc, neg_add_cancel_left, add_left_neg, add_zero]
        right_inv := fun _ => by simp only [add_assoc, add_neg_cancel_left, add_right_neg, add_zero]
        map_add' := by simp only [add_assoc, neg_add_cancel_left, forall_const] }
  map_add' g₁ g₂ := by
    apply Additive.toMul.injective; ext h
    show g₁ + g₂ + h + -(g₁ + g₂) = g₁ + (g₂ + h + -g₂) + -g₁
    simp only [add_assoc, neg_add_rev]
  map_zero' := by
    apply Additive.toMul.injective; ext
    simp only [zero_add, neg_zero, add_zero, toMul_ofMul, toMul_zero, one_apply]
    rfl
#align add_aut.conj AddAut.conj

@[simp]
theorem conj_apply [AddGroup G] (g h : G) : conj g h = g + h + -g :=
  rfl
#align add_aut.conj_apply AddAut.conj_apply

@[simp]
theorem conj_symm_apply [AddGroup G] (g h : G) : (conj g).symm h = -g + h + g :=
  rfl
#align add_aut.conj_symm_apply AddAut.conj_symm_apply

-- Porting note: the exact translation of this mathlib3 lemma would be`(-conj g) h = -g + h + g`,
-- but this no longer pass the simp_nf linter, as the LHS simplifies by `toMul_neg` to
-- `(Additive.toMul (conj g))⁻¹`.
@[simp]
theorem conj_inv_apply [AddGroup G] (g h : G) : (Additive.toMul (conj g))⁻¹ h = -g + h + g :=
  rfl
#align add_aut.conj_inv_apply AddAut.conj_inv_apply

end AddAut
