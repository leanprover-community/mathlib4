/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
import Mathlib.GroupTheory.Congruence
import Mathlib.Algebra.Module.Submodule.Bilinear

#align_import linear_algebra.tensor_product from "leanprover-community/mathlib"@"88fcdc3da43943f5b01925deddaa5bf0c0e85e4e"

/-!
# Tensor product of modules over commutative semirings.

This file constructs the tensor product of modules over commutative semirings. Given a semiring
`R` and modules over it `M` and `N`, the standard construction of the tensor product is
`TensorProduct R M N`. It is also a module over `R`.

It comes with a canonical bilinear map `M → N → TensorProduct R M N`.

Given any bilinear map `M → N → P`, there is a unique linear map `TensorProduct R M N → P` whose
composition with the canonical bilinear map `M → N → TensorProduct R M N` is the given bilinear
map `M → N → P`.

We start by proving basic lemmas about bilinear maps.

## Notations

This file uses the localized notation `M ⊗ N` and `M ⊗[R] N` for `TensorProduct R M N`, as well
as `m ⊗ₜ n` and `m ⊗ₜ[R] n` for `TensorProduct.tmul R m n`.

## Tags

bilinear, tensor, tensor product
-/


section Semiring

variable {R : Type*} [CommSemiring R]
variable {R' : Type*} [Monoid R']
variable {R'' : Type*} [Semiring R'']
variable {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid S]
variable [Module R M] [Module R N] [Module R P] [Module R Q] [Module R S]
variable [DistribMulAction R' M]
variable [Module R'' M]
variable (M N)

namespace TensorProduct

section

variable (R)

/-- The relation on `FreeAddMonoid (M × N)` that generates a congruence whose quotient is
the tensor product. -/
inductive Eqv : FreeAddMonoid (M × N) → FreeAddMonoid (M × N) → Prop
  | of_zero_left : ∀ n : N, Eqv (.of (0, n)) 0
  | of_zero_right : ∀ m : M, Eqv (.of (m, 0)) 0
  | of_add_left : ∀ (m₁ m₂ : M) (n : N), Eqv (.of (m₁, n) + .of (m₂, n)) (.of (m₁ + m₂, n))
  | of_add_right : ∀ (m : M) (n₁ n₂ : N), Eqv (.of (m, n₁) + .of (m, n₂)) (.of (m, n₁ + n₂))
  | of_smul : ∀ (r : R) (m : M) (n : N), Eqv (.of (r • m, n)) (.of (m, r • n))
  | add_comm : ∀ x y, Eqv (x + y) (y + x)
#align tensor_product.eqv TensorProduct.Eqv

end

end TensorProduct

variable (R)

/-- The tensor product of two modules `M` and `N` over the same commutative semiring `R`.
The localized notations are `M ⊗ N` and `M ⊗[R] N`, accessed by `open scoped TensorProduct`. -/
def TensorProduct : Type _ :=
  (addConGen (TensorProduct.Eqv R M N)).Quotient
#align tensor_product TensorProduct

variable {R}

set_option quotPrecheck false in
scoped[TensorProduct] infixl:100 " ⊗ " => TensorProduct _

scoped[TensorProduct] notation:100 M " ⊗[" R "] " N:100 => TensorProduct R M N

namespace TensorProduct

section Module

-- porting note: This is added as a local instance for `SMul.aux`.
-- For some reason type-class inference in Lean 3 unfolded this definition.
def addMonoid : AddMonoid (M ⊗[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with }

instance addZeroClass : AddZeroClass (M ⊗[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with }

instance addCommSemigroup : AddCommSemigroup (M ⊗[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with
    add_comm := fun x y =>
      AddCon.induction_on₂ x y fun _ _ =>
        Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.add_comm _ _ }

instance : Inhabited (M ⊗[R] N) :=
  ⟨0⟩

variable (R) {M N}

/-- The canonical function `M → N → M ⊗ N`. The localized notations are `m ⊗ₜ n` and `m ⊗ₜ[R] n`,
accessed by `open scoped TensorProduct`. -/
def tmul (m : M) (n : N) : M ⊗[R] N :=
  AddCon.mk' _ <| FreeAddMonoid.of (m, n)
#align tensor_product.tmul TensorProduct.tmul

variable {R}

infixl:100 " ⊗ₜ " => tmul _

notation:100 x " ⊗ₜ[" R "] " y:100 => tmul R x y

-- porting note: make the arguments of induction_on explicit
@[elab_as_elim]
protected theorem induction_on {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (zero : motive 0)
    (tmul : ∀ x y, motive <| x ⊗ₜ[R] y)
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  AddCon.induction_on z fun x =>
    FreeAddMonoid.recOn x zero fun ⟨m, n⟩ y ih => by
      rw [AddCon.coe_add]
      -- ⊢ motive (↑(FreeAddMonoid.of (m, n)) + ↑y)
      exact add _ _ (tmul ..) ih
      -- 🎉 no goals
#align tensor_product.induction_on TensorProduct.induction_on

variable (M)

@[simp]
theorem zero_tmul (n : N) : (0 : M) ⊗ₜ[R] n = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_left _
#align tensor_product.zero_tmul TensorProduct.zero_tmul

variable {M}

theorem add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) ⊗ₜ n = m₁ ⊗ₜ n + m₂ ⊗ₜ[R] n :=
  Eq.symm <| Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_add_left _ _ _
#align tensor_product.add_tmul TensorProduct.add_tmul

variable (N)

@[simp]
theorem tmul_zero (m : M) : m ⊗ₜ[R] (0 : N) = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_right _
#align tensor_product.tmul_zero TensorProduct.tmul_zero

variable {N}

theorem tmul_add (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ + n₂) = m ⊗ₜ n₁ + m ⊗ₜ[R] n₂ :=
  Eq.symm <| Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_add_right _ _ _
#align tensor_product.tmul_add TensorProduct.tmul_add

section

variable (R R' M N)

/-- A typeclass for `SMul` structures which can be moved across a tensor product.

This typeclass is generated automatically from an `IsScalarTower` instance, but exists so that
we can also add an instance for `AddCommGroup.intModule`, allowing `z •` to be moved even if
`R` does not support negation.

Note that `Module R' (M ⊗[R] N)` is available even without this typeclass on `R'`; it's only
needed if `TensorProduct.smul_tmul`, `TensorProduct.smul_tmul'`, or `TensorProduct.tmul_smul` is
used.
-/
class CompatibleSMul [DistribMulAction R' N] : Prop where
  smul_tmul : ∀ (r : R') (m : M) (n : N), (r • m) ⊗ₜ n = m ⊗ₜ[R] (r • n)
#align tensor_product.compatible_smul TensorProduct.CompatibleSMul

end

/-- Note that this provides the default `compatible_smul R R M N` instance through
`IsScalarTower.left`. -/
instance (priority := 100) CompatibleSMul.isScalarTower [SMul R' R] [IsScalarTower R' R M]
    [DistribMulAction R' N] [IsScalarTower R' R N] : CompatibleSMul R R' M N :=
  ⟨fun r m n => by
    conv_lhs => rw [← one_smul R m]
    -- ⊢ (r • 1 • m) ⊗ₜ[R] n = m ⊗ₜ[R] (r • n)
    conv_rhs => rw [← one_smul R n]
    -- ⊢ (r • 1 • m) ⊗ₜ[R] n = m ⊗ₜ[R] (r • 1 • n)
    rw [← smul_assoc, ← smul_assoc]
    -- ⊢ ((r • 1) • m) ⊗ₜ[R] n = m ⊗ₜ[R] ((r • 1) • n)
    exact Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_smul _ _ _⟩
    -- 🎉 no goals
#align tensor_product.compatible_smul.is_scalar_tower TensorProduct.CompatibleSMul.isScalarTower

/-- `smul` can be moved from one side of the product to the other .-/
theorem smul_tmul [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (m : M) (n : N) :
    (r • m) ⊗ₜ n = m ⊗ₜ[R] (r • n) :=
  CompatibleSMul.smul_tmul _ _ _
#align tensor_product.smul_tmul TensorProduct.smul_tmul

attribute [local instance] addMonoid
/-- Auxiliary function to defining scalar multiplication on tensor product. -/
def SMul.aux {R' : Type*} [SMul R' M] (r : R') : FreeAddMonoid (M × N) →+ M ⊗[R] N :=
  FreeAddMonoid.lift fun p : M × N => (r • p.1) ⊗ₜ p.2
#align tensor_product.smul.aux TensorProduct.SMul.aux
attribute [-instance] addMonoid

theorem SMul.aux_of {R' : Type*} [SMul R' M] (r : R') (m : M) (n : N) :
    SMul.aux r (.of (m, n)) = (r • m) ⊗ₜ[R] n :=
  rfl
#align tensor_product.smul.aux_of TensorProduct.SMul.aux_of

variable [SMulCommClass R R' M] [SMulCommClass R R'' M]

/-- Given two modules over a commutative semiring `R`, if one of the factors carries a
(distributive) action of a second type of scalars `R'`, which commutes with the action of `R`, then
the tensor product (over `R`) carries an action of `R'`.

This instance defines this `R'` action in the case that it is the left module which has the `R'`
action. Two natural ways in which this situation arises are:
 * Extension of scalars
 * A tensor product of a group representation with a module not carrying an action

Note that in the special case that `R = R'`, since `R` is commutative, we just get the usual scalar
action on a tensor product of two modules. This special case is important enough that, for
performance reasons, we define it explicitly below. -/
instance leftHasSMul : SMul R' (M ⊗[R] N) :=
  ⟨fun r =>
    (addConGen (TensorProduct.Eqv R M N)).lift (SMul.aux r : _ →+ M ⊗[R] N) <|
      AddCon.addConGen_le fun x y hxy =>
        match x, y, hxy with
        | _, _, .of_zero_left n =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_zero, SMul.aux_of, smul_zero, zero_tmul]
                                     -- 🎉 no goals
        | _, _, .of_zero_right m =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_zero, SMul.aux_of, tmul_zero]
                                     -- 🎉 no goals
        | _, _, .of_add_left m₁ m₂ n =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, SMul.aux_of, smul_add, add_tmul]
                                     -- 🎉 no goals
        | _, _, .of_add_right m n₁ n₂ =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, SMul.aux_of, tmul_add]
                                     -- 🎉 no goals
        | _, _, .of_smul s m n =>
          (AddCon.ker_rel _).2 <| by rw [SMul.aux_of, SMul.aux_of, ← smul_comm, smul_tmul]
                                     -- 🎉 no goals
        | _, _, .add_comm x y =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]⟩
                                     -- 🎉 no goals
#align tensor_product.left_has_smul TensorProduct.leftHasSMul

instance : SMul R (M ⊗[R] N) :=
  TensorProduct.leftHasSMul

protected theorem smul_zero (r : R') : r • (0 : M ⊗[R] N) = 0 :=
  AddMonoidHom.map_zero _
#align tensor_product.smul_zero TensorProduct.smul_zero

protected theorem smul_add (r : R') (x y : M ⊗[R] N) : r • (x + y) = r • x + r • y :=
  AddMonoidHom.map_add _ _ _
#align tensor_product.smul_add TensorProduct.smul_add

protected theorem zero_smul (x : M ⊗[R] N) : (0 : R'') • x = 0 :=
  have : ∀ (r : R'') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
                     -- 🎉 no goals
    (fun m n => by rw [this, zero_smul, zero_tmul]) fun x y ihx ihy => by
                   -- 🎉 no goals
    rw [TensorProduct.smul_add, ihx, ihy, add_zero]
    -- 🎉 no goals
#align tensor_product.zero_smul TensorProduct.zero_smul

protected theorem one_smul (x : M ⊗[R] N) : (1 : R') • x = x :=
  have : ∀ (r : R') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
                     -- 🎉 no goals
    (fun m n => by rw [this, one_smul])
                   -- 🎉 no goals
    fun x y ihx ihy => by rw [TensorProduct.smul_add, ihx, ihy]
                          -- 🎉 no goals
#align tensor_product.one_smul TensorProduct.one_smul

protected theorem add_smul (r s : R'') (x : M ⊗[R] N) : (r + s) • x = r • x + s • x :=
  have : ∀ (r : R'') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by simp_rw [TensorProduct.smul_zero, add_zero])
                     -- 🎉 no goals
    (fun m n => by simp_rw [this, add_smul, add_tmul]) fun x y ihx ihy => by
                   -- 🎉 no goals
    simp_rw [TensorProduct.smul_add]
    -- ⊢ (r + s) • x + (r + s) • y = r • x + r • y + (s • x + s • y)
    rw [ihx, ihy, add_add_add_comm]
    -- 🎉 no goals
#align tensor_product.add_smul TensorProduct.add_smul

instance addCommMonoid : AddCommMonoid (M ⊗[R] N) :=
  { TensorProduct.addCommSemigroup _ _,
    TensorProduct.addZeroClass _ _ with
    nsmul := fun n v => n • v
    nsmul_zero := by simp [TensorProduct.zero_smul]
                     -- 🎉 no goals
    nsmul_succ := by simp only [TensorProduct.one_smul, TensorProduct.add_smul, add_comm,
      forall_const] }

instance leftDistribMulAction : DistribMulAction R' (M ⊗[R] N) :=
  have : ∀ (r : R') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  { smul := (· • ·)
    smul_add := fun r x y => TensorProduct.smul_add r x y
    mul_smul := fun r s x =>
      x.induction_on (by simp_rw [TensorProduct.smul_zero])
                         -- 🎉 no goals
        (fun m n => by simp_rw [this, mul_smul]) fun x y ihx ihy => by
                       -- 🎉 no goals
        simp_rw [TensorProduct.smul_add]
        -- ⊢ (r * s) • x + (r * s) • y = r • s • x + r • s • y
        rw [ihx, ihy]
        -- 🎉 no goals
    one_smul := TensorProduct.one_smul
    smul_zero := TensorProduct.smul_zero }
#align tensor_product.left_distrib_mul_action TensorProduct.leftDistribMulAction

instance : DistribMulAction R (M ⊗[R] N) :=
  TensorProduct.leftDistribMulAction

theorem smul_tmul' (r : R') (m : M) (n : N) : r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n :=
  rfl
#align tensor_product.smul_tmul' TensorProduct.smul_tmul'

@[simp]
theorem tmul_smul [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (x : M) (y : N) :
    x ⊗ₜ (r • y) = r • x ⊗ₜ[R] y :=
  (smul_tmul _ _ _).symm
#align tensor_product.tmul_smul TensorProduct.tmul_smul

theorem smul_tmul_smul (r s : R) (m : M) (n : N) : (r • m) ⊗ₜ[R] (s • n) = (r * s) • m ⊗ₜ[R] n := by
  simp_rw [smul_tmul, tmul_smul, mul_smul]
  -- 🎉 no goals
#align tensor_product.smul_tmul_smul TensorProduct.smul_tmul_smul

instance leftModule : Module R'' (M ⊗[R] N) :=
  { TensorProduct.leftDistribMulAction with
    smul := (· • ·)
    add_smul := TensorProduct.add_smul
    zero_smul := TensorProduct.zero_smul }
#align tensor_product.left_module TensorProduct.leftModule

instance : Module R (M ⊗[R] N) :=
  TensorProduct.leftModule

instance [Module R''ᵐᵒᵖ M] [IsCentralScalar R'' M] : IsCentralScalar R'' (M ⊗[R] N) where
  op_smul_eq_smul r x :=
    x.induction_on (by rw [smul_zero, smul_zero])
                       -- 🎉 no goals
      (fun x y => by rw [smul_tmul', smul_tmul', op_smul_eq_smul]) fun x y hx hy => by
                     -- 🎉 no goals
      rw [smul_add, smul_add, hx, hy]
      -- 🎉 no goals

section

-- Like `R'`, `R'₂` provides a `DistribMulAction R'₂ (M ⊗[R] N)`
variable {R'₂ : Type*} [Monoid R'₂] [DistribMulAction R'₂ M]
variable [SMulCommClass R R'₂ M]

/-- `SMulCommClass R' R'₂ M` implies `SMulCommClass R' R'₂ (M ⊗[R] N)` -/
instance smulCommClass_left [SMulCommClass R' R'₂ M] : SMulCommClass R' R'₂ (M ⊗[R] N) where
  smul_comm r' r'₂ x :=
    TensorProduct.induction_on x (by simp_rw [TensorProduct.smul_zero])
                                     -- 🎉 no goals
      (fun m n => by simp_rw [smul_tmul', smul_comm]) fun x y ihx ihy => by
                     -- 🎉 no goals
      simp_rw [TensorProduct.smul_add]; rw [ihx, ihy]
      -- ⊢ r' • r'₂ • x + r' • r'₂ • y = r'₂ • r' • x + r'₂ • r' • y
                                        -- 🎉 no goals
#align tensor_product.smul_comm_class_left TensorProduct.smulCommClass_left

variable [SMul R'₂ R']

/-- `IsScalarTower R'₂ R' M` implies `IsScalarTower R'₂ R' (M ⊗[R] N)` -/
instance isScalarTower_left [IsScalarTower R'₂ R' M] : IsScalarTower R'₂ R' (M ⊗[R] N) :=
  ⟨fun s r x =>
    x.induction_on (by simp)
                       -- 🎉 no goals
      (fun m n => by rw [smul_tmul', smul_tmul', smul_tmul', smul_assoc]) fun x y ihx ihy => by
                     -- 🎉 no goals
      rw [smul_add, smul_add, smul_add, ihx, ihy]⟩
      -- 🎉 no goals
#align tensor_product.is_scalar_tower_left TensorProduct.isScalarTower_left

variable [DistribMulAction R'₂ N] [DistribMulAction R' N]
variable [CompatibleSMul R R'₂ M N] [CompatibleSMul R R' M N]

/-- `IsScalarTower R'₂ R' N` implies `IsScalarTower R'₂ R' (M ⊗[R] N)` -/
instance isScalarTower_right [IsScalarTower R'₂ R' N] : IsScalarTower R'₂ R' (M ⊗[R] N) :=
  ⟨fun s r x =>
    x.induction_on (by simp)
                       -- 🎉 no goals
      (fun m n => by rw [← tmul_smul, ← tmul_smul, ← tmul_smul, smul_assoc]) fun x y ihx ihy => by
                     -- 🎉 no goals
      rw [smul_add, smul_add, smul_add, ihx, ihy]⟩
      -- 🎉 no goals
#align tensor_product.is_scalar_tower_right TensorProduct.isScalarTower_right

end

/-- A short-cut instance for the common case, where the requirements for the `compatible_smul`
instances are sufficient. -/
instance isScalarTower [SMul R' R] [IsScalarTower R' R M] : IsScalarTower R' R (M ⊗[R] N) :=
  TensorProduct.isScalarTower_left
#align tensor_product.is_scalar_tower TensorProduct.isScalarTower

-- or right
variable (R M N)

/-- The canonical bilinear map `M → N → M ⊗[R] N`. -/
def mk : M →ₗ[R] N →ₗ[R] M ⊗[R] N :=
  LinearMap.mk₂ R (· ⊗ₜ ·) add_tmul (fun c m n => by simp_rw [smul_tmul, tmul_smul])
                                                     -- 🎉 no goals
    tmul_add tmul_smul
#align tensor_product.mk TensorProduct.mk

variable {R M N}

@[simp]
theorem mk_apply (m : M) (n : N) : mk R M N m n = m ⊗ₜ n :=
  rfl
#align tensor_product.mk_apply TensorProduct.mk_apply

theorem ite_tmul (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (if P then x₁ else 0) ⊗ₜ[R] x₂ = if P then x₁ ⊗ₜ x₂ else 0 := by split_ifs <;> simp
                                                                     -- ⊢ x₁ ⊗ₜ[R] x₂ = x₁ ⊗ₜ[R] x₂
                                                                                   -- 🎉 no goals
                                                                                   -- 🎉 no goals
#align tensor_product.ite_tmul TensorProduct.ite_tmul

theorem tmul_ite (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (x₁ ⊗ₜ[R] if P then x₂ else 0) = if P then x₁ ⊗ₜ x₂ else 0 := by split_ifs <;> simp
                                                                     -- ⊢ x₁ ⊗ₜ[R] x₂ = x₁ ⊗ₜ[R] x₂
                                                                                   -- 🎉 no goals
                                                                                   -- 🎉 no goals
#align tensor_product.tmul_ite TensorProduct.tmul_ite

section

open BigOperators

theorem sum_tmul {α : Type*} (s : Finset α) (m : α → M) (n : N) :
    (∑ a in s, m a) ⊗ₜ[R] n = ∑ a in s, m a ⊗ₜ[R] n := by
  classical
    induction' s using Finset.induction with a s has ih h
    · simp
    · simp [Finset.sum_insert has, add_tmul, ih]
#align tensor_product.sum_tmul TensorProduct.sum_tmul

theorem tmul_sum (m : M) {α : Type*} (s : Finset α) (n : α → N) :
    (m ⊗ₜ[R] ∑ a in s, n a) = ∑ a in s, m ⊗ₜ[R] n a := by
  classical
    induction' s using Finset.induction with a s has ih h
    · simp
    · simp [Finset.sum_insert has, tmul_add, ih]
#align tensor_product.tmul_sum TensorProduct.tmul_sum

end

variable (R M N)

/-- The simple (aka pure) elements span the tensor product. -/
theorem span_tmul_eq_top : Submodule.span R { t : M ⊗[R] N | ∃ m n, m ⊗ₜ n = t } = ⊤ := by
  ext t; simp only [Submodule.mem_top, iff_true_iff]
  -- ⊢ t ∈ Submodule.span R {t | ∃ m n, m ⊗ₜ[R] n = t} ↔ t ∈ ⊤
         -- ⊢ t ∈ Submodule.span R {t | ∃ m n, m ⊗ₜ[R] n = t}
  refine t.induction_on ?_ ?_ ?_
  · exact Submodule.zero_mem _
    -- 🎉 no goals
  · intro m n
    -- ⊢ m ⊗ₜ[R] n ∈ Submodule.span R {t | ∃ m n, m ⊗ₜ[R] n = t}
    apply Submodule.subset_span
    -- ⊢ m ⊗ₜ[R] n ∈ {t | ∃ m n, m ⊗ₜ[R] n = t}
    use m, n
    -- 🎉 no goals
  · intro t₁ t₂ ht₁ ht₂
    -- ⊢ t₁ + t₂ ∈ Submodule.span R {t | ∃ m n, m ⊗ₜ[R] n = t}
    exact Submodule.add_mem _ ht₁ ht₂
    -- 🎉 no goals
#align tensor_product.span_tmul_eq_top TensorProduct.span_tmul_eq_top

@[simp]
theorem map₂_mk_top_top_eq_top : Submodule.map₂ (mk R M N) ⊤ ⊤ = ⊤ := by
  rw [← top_le_iff, ← span_tmul_eq_top, Submodule.map₂_eq_span_image2]
  -- ⊢ Submodule.span R {t | ∃ m n, m ⊗ₜ[R] n = t} ≤ Submodule.span R (Set.image2 ( …
  exact Submodule.span_mono fun _ ⟨m, n, h⟩ => ⟨m, n, trivial, trivial, h⟩
  -- 🎉 no goals
#align tensor_product.map₂_mk_top_top_eq_top TensorProduct.map₂_mk_top_top_eq_top

theorem exists_eq_tmul_of_forall (x : TensorProduct R M N)
    (h : ∀ (m₁ m₂ : M) (n₁ n₂ : N), ∃ m n, m₁ ⊗ₜ n₁ + m₂ ⊗ₜ n₂ = m ⊗ₜ[R] n) :
    ∃ m n, x = m ⊗ₜ n := by
  induction x using TensorProduct.induction_on with
  | zero =>
    use 0, 0
    rw [TensorProduct.zero_tmul]
  | tmul m n => use m, n
  | add x y h₁ h₂ =>
    obtain ⟨m₁, n₁, rfl⟩ := h₁
    obtain ⟨m₂, n₂, rfl⟩ := h₂
    apply h

end Module

section UMP

variable {M N}
variable (f : M →ₗ[R] N →ₗ[R] P)

/-- Auxiliary function to constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def liftAux : M ⊗[R] N →+ P :=
  (addConGen (TensorProduct.Eqv R M N)).lift (FreeAddMonoid.lift fun p : M × N => f p.1 p.2) <|
    AddCon.addConGen_le fun x y hxy =>
      match x, y, hxy with
      | _, _, Eqv.of_zero_left n =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, f.map_zero₂]
                                   -- 🎉 no goals
      | _, _, Eqv.of_zero_right m =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, (f m).map_zero]
                                   -- 🎉 no goals
      | _, _, Eqv.of_add_left m₁ m₂ n =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, FreeAddMonoid.lift_eval_of, f.map_add₂]
                                   -- 🎉 no goals
      | _, _, Eqv.of_add_right m n₁ n₂ =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, FreeAddMonoid.lift_eval_of, (f m).map_add]
                                   -- 🎉 no goals
      | _, _, Eqv.of_smul r m n =>
        (AddCon.ker_rel _).2 <| by simp_rw [FreeAddMonoid.lift_eval_of, f.map_smul₂, (f m).map_smul]
                                   -- 🎉 no goals
      | _, _, Eqv.add_comm x y =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]
                                   -- 🎉 no goals
#align tensor_product.lift_aux TensorProduct.liftAux

theorem liftAux_tmul (m n) : liftAux f (m ⊗ₜ n) = f m n :=
  rfl
#align tensor_product.lift_aux_tmul TensorProduct.liftAux_tmul

variable {f}

@[simp]
theorem liftAux.smul (r : R) (x) : liftAux f (r • x) = r • liftAux f x :=
  TensorProduct.induction_on x (smul_zero _).symm
    (fun p q => by simp_rw [← tmul_smul, liftAux_tmul, (f p).map_smul])
                   -- 🎉 no goals
    fun p q ih1 ih2 => by simp_rw [smul_add, (liftAux f).map_add, ih1, ih2, smul_add]
                          -- 🎉 no goals
#align tensor_product.lift_aux.smul TensorProduct.liftAux.smul

variable (f)

/-- Constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P` with the property that
its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def lift : M ⊗[R] N →ₗ[R] P :=
  { liftAux f with map_smul' := liftAux.smul }
#align tensor_product.lift TensorProduct.lift

variable {f}

@[simp]
theorem lift.tmul (x y) : lift f (x ⊗ₜ y) = f x y :=
  rfl
#align tensor_product.lift.tmul TensorProduct.lift.tmul

@[simp]
theorem lift.tmul' (x y) : (lift f).1 (x ⊗ₜ y) = f x y :=
  rfl
#align tensor_product.lift.tmul' TensorProduct.lift.tmul'

theorem ext' {g h : M ⊗[R] N →ₗ[R] P} (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
  LinearMap.ext fun z =>
    TensorProduct.induction_on z (by simp_rw [LinearMap.map_zero]) H fun x y ihx ihy => by
                                     -- 🎉 no goals
      rw [g.map_add, h.map_add, ihx, ihy]
      -- 🎉 no goals
#align tensor_product.ext' TensorProduct.ext'

theorem lift.unique {g : M ⊗[R] N →ₗ[R] P} (H : ∀ x y, g (x ⊗ₜ y) = f x y) : g = lift f :=
  ext' fun m n => by rw [H, lift.tmul]
                     -- 🎉 no goals
#align tensor_product.lift.unique TensorProduct.lift.unique

theorem lift_mk : lift (mk R M N) = LinearMap.id :=
  Eq.symm <| lift.unique fun _ _ => rfl
#align tensor_product.lift_mk TensorProduct.lift_mk

theorem lift_compr₂ (g : P →ₗ[R] Q) : lift (f.compr₂ g) = g.comp (lift f) :=
  Eq.symm <| lift.unique fun _ _ => by simp
                                       -- 🎉 no goals
#align tensor_product.lift_compr₂ TensorProduct.lift_compr₂

theorem lift_mk_compr₂ (f : M ⊗ N →ₗ[R] P) : lift ((mk R M N).compr₂ f) = f := by
  rw [lift_compr₂ f, lift_mk, LinearMap.comp_id]
  -- 🎉 no goals
#align tensor_product.lift_mk_compr₂ TensorProduct.lift_mk_compr₂

/-- This used to be an `@[ext]` lemma, but it fails very slowly when the `ext` tactic tries to apply
it in some cases, notably when one wants to show equality of two linear maps. The `@[ext]`
attribute is now added locally where it is needed. Using this as the `@[ext]` lemma instead of
`TensorProduct.ext'` allows `ext` to apply lemmas specific to `M →ₗ _` and `N →ₗ _`.

See note [partially-applied ext lemmas]. -/
theorem ext {g h : M ⊗ N →ₗ[R] P} (H : (mk R M N).compr₂ g = (mk R M N).compr₂ h) : g = h := by
  rw [← lift_mk_compr₂ g, H, lift_mk_compr₂]
  -- 🎉 no goals
#align tensor_product.ext TensorProduct.ext

attribute [local ext high] ext

example : M → N → (M → N → P) → P := fun m => flip fun f => f m

variable (R M N P)

/-- Linearly constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def uncurry : (M →ₗ[R] N →ₗ[R] P) →ₗ[R] M ⊗[R] N →ₗ[R] P :=
  LinearMap.flip <| lift <| LinearMap.lflip.comp (LinearMap.flip LinearMap.id)
#align tensor_product.uncurry TensorProduct.uncurry

variable {R M N P}

@[simp]
theorem uncurry_apply (f : M →ₗ[R] N →ₗ[R] P) (m : M) (n : N) :
    uncurry R M N P f (m ⊗ₜ n) = f m n := by rw [uncurry, LinearMap.flip_apply, lift.tmul]; rfl
                                             -- ⊢ ↑(↑(↑(LinearMap.comp LinearMap.lflip (LinearMap.flip LinearMap.id)) m) n) f  …
                                                                                            -- 🎉 no goals
#align tensor_product.uncurry_apply TensorProduct.uncurry_apply

variable (R M N P)

/-- A linear equivalence constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def lift.equiv : (M →ₗ[R] N →ₗ[R] P) ≃ₗ[R] M ⊗[R] N →ₗ[R] P :=
  { uncurry R M N P with
    invFun := fun f => (mk R M N).compr₂ f
    left_inv := fun _ => LinearMap.ext₂ fun _ _ => lift.tmul _ _
    right_inv := fun _ => ext' fun _ _ => lift.tmul _ _ }
#align tensor_product.lift.equiv TensorProduct.lift.equiv

@[simp]
theorem lift.equiv_apply (f : M →ₗ[R] N →ₗ[R] P) (m : M) (n : N) :
    lift.equiv R M N P f (m ⊗ₜ n) = f m n :=
  uncurry_apply f m n
#align tensor_product.lift.equiv_apply TensorProduct.lift.equiv_apply

@[simp]
theorem lift.equiv_symm_apply (f : M ⊗[R] N →ₗ[R] P) (m : M) (n : N) :
    (lift.equiv R M N P).symm f m n = f (m ⊗ₜ n) :=
  rfl
#align tensor_product.lift.equiv_symm_apply TensorProduct.lift.equiv_symm_apply

/-- Given a linear map `M ⊗ N → P`, compose it with the canonical bilinear map `M → N → M ⊗ N` to
form a bilinear map `M → N → P`. -/
def lcurry : (M ⊗[R] N →ₗ[R] P) →ₗ[R] M →ₗ[R] N →ₗ[R] P :=
  (lift.equiv R M N P).symm
#align tensor_product.lcurry TensorProduct.lcurry

variable {R M N P}

@[simp]
theorem lcurry_apply (f : M ⊗[R] N →ₗ[R] P) (m : M) (n : N) : lcurry R M N P f m n = f (m ⊗ₜ n) :=
  rfl
#align tensor_product.lcurry_apply TensorProduct.lcurry_apply

/-- Given a linear map `M ⊗ N → P`, compose it with the canonical bilinear map `M → N → M ⊗ N` to
form a bilinear map `M → N → P`. -/
def curry (f : M ⊗[R] N →ₗ[R] P) : M →ₗ[R] N →ₗ[R] P :=
  lcurry R M N P f
#align tensor_product.curry TensorProduct.curry

@[simp]
theorem curry_apply (f : M ⊗ N →ₗ[R] P) (m : M) (n : N) : curry f m n = f (m ⊗ₜ n) :=
  rfl
#align tensor_product.curry_apply TensorProduct.curry_apply

theorem curry_injective : Function.Injective (curry : (M ⊗[R] N →ₗ[R] P) → M →ₗ[R] N →ₗ[R] P) :=
  fun _ _ H => ext H
#align tensor_product.curry_injective TensorProduct.curry_injective

theorem ext_threefold {g h : (M ⊗[R] N) ⊗[R] P →ₗ[R] Q}
    (H : ∀ x y z, g (x ⊗ₜ y ⊗ₜ z) = h (x ⊗ₜ y ⊗ₜ z)) : g = h := by
  ext x y z
  -- ⊢ ↑(↑(↑(LinearMap.compr₂ (mk R M N) (LinearMap.compr₂ (mk R (M ⊗[R] N) P) g))  …
  exact H x y z
  -- 🎉 no goals
#align tensor_product.ext_threefold TensorProduct.ext_threefold

-- We'll need this one for checking the pentagon identity!
theorem ext_fourfold {g h : ((M ⊗[R] N) ⊗[R] P) ⊗[R] Q →ₗ[R] S}
    (H : ∀ w x y z, g (w ⊗ₜ x ⊗ₜ y ⊗ₜ z) = h (w ⊗ₜ x ⊗ₜ y ⊗ₜ z)) : g = h := by
  ext w x y z
  -- ⊢ ↑(↑(↑(↑(LinearMap.compr₂ (mk R M N) (LinearMap.compr₂ (mk R (M ⊗[R] N) P) (L …
  exact H w x y z
  -- 🎉 no goals
#align tensor_product.ext_fourfold TensorProduct.ext_fourfold

/-- Two linear maps (M ⊗ N) ⊗ (P ⊗ Q) → S which agree on all elements of the
form (m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q) are equal. -/
theorem ext_fourfold' {φ ψ : (M ⊗[R] N) ⊗[R] P ⊗[R] Q →ₗ[R] S}
    (H : ∀ w x y z, φ (w ⊗ₜ x ⊗ₜ (y ⊗ₜ z)) = ψ (w ⊗ₜ x ⊗ₜ (y ⊗ₜ z))) : φ = ψ := by
  ext m n p q
  -- ⊢ ↑(↑(LinearMap.compr₂ (mk R P Q) (↑(↑(LinearMap.compr₂ (mk R M N) (LinearMap. …
  exact H m n p q
  -- 🎉 no goals
#align tensor_product.ext_fourfold' TensorProduct.ext_fourfold'

end UMP

variable {M N}

section

variable (R M)

/-- The base ring is a left identity for the tensor product of modules, up to linear equivalence.
-/
protected def lid : R ⊗[R] M ≃ₗ[R] M :=
  LinearEquiv.ofLinear (lift <| LinearMap.lsmul R M) (mk R R M 1) (LinearMap.ext fun _ => by simp)
                                                                                             -- 🎉 no goals
    (ext' fun r m => by simp; rw [← tmul_smul, ← smul_tmul, smul_eq_mul, mul_one])
                        -- ⊢ r • 1 ⊗ₜ[R] m = r ⊗ₜ[R] m
                              -- 🎉 no goals
#align tensor_product.lid TensorProduct.lid

end

@[simp]
theorem lid_tmul (m : M) (r : R) : (TensorProduct.lid R M : R ⊗ M → M) (r ⊗ₜ m) = r • m :=
  rfl
#align tensor_product.lid_tmul TensorProduct.lid_tmul

@[simp]
theorem lid_symm_apply (m : M) : (TensorProduct.lid R M).symm m = 1 ⊗ₜ m :=
  rfl
#align tensor_product.lid_symm_apply TensorProduct.lid_symm_apply

section

variable (R M N)

/-- The tensor product of modules is commutative, up to linear equivalence.
-/
protected def comm : M ⊗[R] N ≃ₗ[R] N ⊗[R] M :=
  LinearEquiv.ofLinear (lift (mk R N M).flip) (lift (mk R M N).flip) (ext' fun _ _ => rfl)
    (ext' fun _ _ => rfl)
#align tensor_product.comm TensorProduct.comm

@[simp]
theorem comm_tmul (m : M) (n : N) : (TensorProduct.comm R M N) (m ⊗ₜ n) = n ⊗ₜ m :=
  rfl
#align tensor_product.comm_tmul TensorProduct.comm_tmul

@[simp]
theorem comm_symm_tmul (m : M) (n : N) : (TensorProduct.comm R M N).symm (n ⊗ₜ m) = m ⊗ₜ n :=
  rfl
#align tensor_product.comm_symm_tmul TensorProduct.comm_symm_tmul

end

section

variable (R M)

/-- The base ring is a right identity for the tensor product of modules, up to linear equivalence.
-/
protected def rid : M ⊗[R] R ≃ₗ[R] M :=
  LinearEquiv.trans (TensorProduct.comm R M R) (TensorProduct.lid R M)
#align tensor_product.rid TensorProduct.rid

end

@[simp]
theorem rid_tmul (m : M) (r : R) : (TensorProduct.rid R M) (m ⊗ₜ r) = r • m :=
  rfl
#align tensor_product.rid_tmul TensorProduct.rid_tmul

@[simp]
theorem rid_symm_apply (m : M) : (TensorProduct.rid R M).symm m = m ⊗ₜ 1 :=
  rfl
#align tensor_product.rid_symm_apply TensorProduct.rid_symm_apply

open LinearMap

section

variable (R M N P)

/-- The associator for tensor product of R-modules, as a linear equivalence. -/
protected def assoc : (M ⊗[R] N) ⊗[R] P ≃ₗ[R] M ⊗[R] N ⊗[R] P := by
  refine
      LinearEquiv.ofLinear (lift <| lift <| comp (lcurry R _ _ _) <| mk _ _ _)
        (lift <| comp (uncurry R _ _ _) <| curry <| mk _ _ _)
        (ext <| LinearMap.ext fun m => ext' fun n p => ?_)
        (ext <| flip_inj <| LinearMap.ext fun p => ext' fun m n => ?_) <;>
    repeat'
      first
        |rw [lift.tmul]|rw [compr₂_apply]|rw [comp_apply]|rw [mk_apply]|rw [flip_apply]
        |rw [lcurry_apply]|rw [uncurry_apply]|rw [curry_apply]|rw [id_apply]
#align tensor_product.assoc TensorProduct.assoc

end

@[simp]
theorem assoc_tmul (m : M) (n : N) (p : P) :
    (TensorProduct.assoc R M N P) (m ⊗ₜ n ⊗ₜ p) = m ⊗ₜ (n ⊗ₜ p) :=
  rfl
#align tensor_product.assoc_tmul TensorProduct.assoc_tmul

@[simp]
theorem assoc_symm_tmul (m : M) (n : N) (p : P) :
    (TensorProduct.assoc R M N P).symm (m ⊗ₜ (n ⊗ₜ p)) = m ⊗ₜ n ⊗ₜ p :=
  rfl
#align tensor_product.assoc_symm_tmul TensorProduct.assoc_symm_tmul

/-- The tensor product of a pair of linear maps between modules. -/
def map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) : M ⊗[R] N →ₗ[R] P ⊗[R] Q :=
  lift <| comp (compl₂ (mk _ _ _) g) f
#align tensor_product.map TensorProduct.map

@[simp]
theorem map_tmul (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (m : M) (n : N) : map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl
#align tensor_product.map_tmul TensorProduct.map_tmul

theorem map_range_eq_span_tmul (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    range (map f g) = Submodule.span R { t | ∃ m n, f m ⊗ₜ g n = t } := by
  simp only [← Submodule.map_top, ← span_tmul_eq_top, Submodule.map_span, Set.mem_image,
    Set.mem_setOf_eq]
  congr; ext t
  -- ⊢ (fun a => ↑(map f g) a) '' {t | ∃ m n, m ⊗ₜ[R] n = t} = {t | ∃ m n, ↑f m ⊗ₜ[ …
         -- ⊢ t ∈ (fun a => ↑(map f g) a) '' {t | ∃ m n, m ⊗ₜ[R] n = t} ↔ t ∈ {t | ∃ m n,  …
  constructor
  -- ⊢ t ∈ (fun a => ↑(map f g) a) '' {t | ∃ m n, m ⊗ₜ[R] n = t} → t ∈ {t | ∃ m n,  …
  · rintro ⟨_, ⟨⟨m, n, rfl⟩, rfl⟩⟩
    -- ⊢ (fun a => ↑(map f g) a) (m ⊗ₜ[R] n) ∈ {t | ∃ m n, ↑f m ⊗ₜ[R] ↑g n = t}
    use m, n
    -- ⊢ ↑f m ⊗ₜ[R] ↑g n = (fun a => ↑(map f g) a) (m ⊗ₜ[R] n)
    simp only [map_tmul]
    -- 🎉 no goals
  · rintro ⟨m, n, rfl⟩
    -- ⊢ ↑f m ⊗ₜ[R] ↑g n ∈ (fun a => ↑(map f g) a) '' {t | ∃ m n, m ⊗ₜ[R] n = t}
    refine ⟨_, ⟨⟨m, n, rfl⟩, ?_⟩⟩
    -- ⊢ (fun a => ↑(map f g) a) (m ⊗ₜ[R] n) = ↑f m ⊗ₜ[R] ↑g n
    simp only [map_tmul]
    -- 🎉 no goals
#align tensor_product.map_range_eq_span_tmul TensorProduct.map_range_eq_span_tmul

/-- Given submodules `p ⊆ P` and `q ⊆ Q`, this is the natural map: `p ⊗ q → P ⊗ Q`. -/
@[simp]
def mapIncl (p : Submodule R P) (q : Submodule R Q) : p ⊗[R] q →ₗ[R] P ⊗[R] Q :=
  map p.subtype q.subtype
#align tensor_product.map_incl TensorProduct.mapIncl

section

variable {P' Q' : Type*}
variable [AddCommMonoid P'] [Module R P']
variable [AddCommMonoid Q'] [Module R Q']

theorem map_comp (f₂ : P →ₗ[R] P') (f₁ : M →ₗ[R] P) (g₂ : Q →ₗ[R] Q') (g₁ : N →ₗ[R] Q) :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
  ext' fun _ _ => rfl
#align tensor_product.map_comp TensorProduct.map_comp

theorem lift_comp_map (i : P →ₗ[R] Q →ₗ[R] Q') (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (lift i).comp (map f g) = lift ((i.comp f).compl₂ g) :=
  ext' fun _ _ => rfl
#align tensor_product.lift_comp_map TensorProduct.lift_comp_map

attribute [local ext high] ext

@[simp]
theorem map_id : map (id : M →ₗ[R] M) (id : N →ₗ[R] N) = .id := by
  ext
  -- ⊢ ↑(↑(compr₂ (mk R M N) (map LinearMap.id LinearMap.id)) x✝¹) x✝ = ↑(↑(compr₂  …
  simp only [mk_apply, id_coe, compr₂_apply, id.def, map_tmul]
  -- 🎉 no goals
#align tensor_product.map_id TensorProduct.map_id

@[simp]
theorem map_one : map (1 : M →ₗ[R] M) (1 : N →ₗ[R] N) = 1 :=
  map_id
#align tensor_product.map_one TensorProduct.map_one

theorem map_mul (f₁ f₂ : M →ₗ[R] M) (g₁ g₂ : N →ₗ[R] N) :
    map (f₁ * f₂) (g₁ * g₂) = map f₁ g₁ * map f₂ g₂ :=
  map_comp f₁ f₂ g₁ g₂
#align tensor_product.map_mul TensorProduct.map_mul

@[simp]
protected theorem map_pow (f : M →ₗ[R] M) (g : N →ₗ[R] N) (n : ℕ) :
    map f g ^ n = map (f ^ n) (g ^ n) := by
  induction' n with n ih
  -- ⊢ map f g ^ Nat.zero = map (f ^ Nat.zero) (g ^ Nat.zero)
  · simp only [Nat.zero_eq, pow_zero, map_one]
    -- 🎉 no goals
  · simp only [pow_succ', ih, map_mul]
    -- 🎉 no goals
#align tensor_product.map_pow TensorProduct.map_pow

theorem map_add_left (f₁ f₂ : M →ₗ[R] P) (g : N →ₗ[R] Q) :
  map (f₁ + f₂) g = map f₁ g + map f₂ g := by
  ext
  -- ⊢ ↑(↑(compr₂ (mk R M N) (map (f₁ + f₂) g)) x✝¹) x✝ = ↑(↑(compr₂ (mk R M N) (ma …
  simp only [add_tmul, compr₂_apply, mk_apply, map_tmul, add_apply]
  -- 🎉 no goals
#align tensor_product.map_add_left TensorProduct.map_add_left

theorem map_add_right (f : M →ₗ[R] P) (g₁ g₂ : N →ₗ[R] Q) :
  map f (g₁ + g₂) = map f g₁ + map f g₂ := by
  ext
  -- ⊢ ↑(↑(compr₂ (mk R M N) (map f (g₁ + g₂))) x✝¹) x✝ = ↑(↑(compr₂ (mk R M N) (ma …
  simp only [tmul_add, compr₂_apply, mk_apply, map_tmul, add_apply]
  -- 🎉 no goals
#align tensor_product.map_add_right TensorProduct.map_add_right

theorem map_smul_left (r : R) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) : map (r • f) g = r • map f g := by
  ext
  -- ⊢ ↑(↑(compr₂ (mk R M N) (map (r • f) g)) x✝¹) x✝ = ↑(↑(compr₂ (mk R M N) (r •  …
  simp only [smul_tmul, compr₂_apply, mk_apply, map_tmul, smul_apply, tmul_smul]
  -- 🎉 no goals
#align tensor_product.map_smul_left TensorProduct.map_smul_left

theorem map_smul_right (r : R) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) : map f (r • g) = r • map f g := by
  ext
  -- ⊢ ↑(↑(compr₂ (mk R M N) (map f (r • g))) x✝¹) x✝ = ↑(↑(compr₂ (mk R M N) (r •  …
  simp only [smul_tmul, compr₂_apply, mk_apply, map_tmul, smul_apply, tmul_smul]
  -- 🎉 no goals
#align tensor_product.map_smul_right TensorProduct.map_smul_right

variable (R M N P Q)

/-- The tensor product of a pair of linear maps between modules, bilinear in both maps. -/
def mapBilinear : (M →ₗ[R] P) →ₗ[R] (N →ₗ[R] Q) →ₗ[R] M ⊗[R] N →ₗ[R] P ⊗[R] Q :=
  LinearMap.mk₂ R map map_add_left map_smul_left map_add_right map_smul_right
#align tensor_product.map_bilinear TensorProduct.mapBilinear

/-- The canonical linear map from `P ⊗[R] (M →ₗ[R] Q)` to `(M →ₗ[R] P ⊗[R] Q)` -/
def lTensorHomToHomLTensor : P ⊗[R] (M →ₗ[R] Q) →ₗ[R] M →ₗ[R] P ⊗[R] Q :=
  TensorProduct.lift (llcomp R M Q _ ∘ₗ mk R P Q)
#align tensor_product.ltensor_hom_to_hom_ltensor TensorProduct.lTensorHomToHomLTensor

/-- The canonical linear map from `(M →ₗ[R] P) ⊗[R] Q` to `(M →ₗ[R] P ⊗[R] Q)` -/
def rTensorHomToHomRTensor : (M →ₗ[R] P) ⊗[R] Q →ₗ[R] M →ₗ[R] P ⊗[R] Q :=
  TensorProduct.lift (llcomp R M P _ ∘ₗ (mk R P Q).flip).flip
#align tensor_product.rtensor_hom_to_hom_rtensor TensorProduct.rTensorHomToHomRTensor

/-- The linear map from `(M →ₗ P) ⊗ (N →ₗ Q)` to `(M ⊗ N →ₗ P ⊗ Q)` sending `f ⊗ₜ g` to
the `TensorProduct.map f g`, the tensor product of the two maps. -/
def homTensorHomMap : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) →ₗ[R] M ⊗[R] N →ₗ[R] P ⊗[R] Q :=
  lift (mapBilinear R M N P Q)
#align tensor_product.hom_tensor_hom_map TensorProduct.homTensorHomMap

variable {R M N P Q}

@[simp]
theorem mapBilinear_apply (f : M →ₗ[R] P) (g : N →ₗ[R] Q) : mapBilinear R M N P Q f g = map f g :=
  rfl
#align tensor_product.map_bilinear_apply TensorProduct.mapBilinear_apply

@[simp]
theorem lTensorHomToHomLTensor_apply (p : P) (f : M →ₗ[R] Q) (m : M) :
    lTensorHomToHomLTensor R M P Q (p ⊗ₜ f) m = p ⊗ₜ f m :=
  rfl
#align tensor_product.ltensor_hom_to_hom_ltensor_apply TensorProduct.lTensorHomToHomLTensor_apply

@[simp]
theorem rTensorHomToHomRTensor_apply (f : M →ₗ[R] P) (q : Q) (m : M) :
    rTensorHomToHomRTensor R M P Q (f ⊗ₜ q) m = f m ⊗ₜ q :=
  rfl
#align tensor_product.rtensor_hom_to_hom_rtensor_apply TensorProduct.rTensorHomToHomRTensor_apply

@[simp]
theorem homTensorHomMap_apply (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    homTensorHomMap R M N P Q (f ⊗ₜ g) = map f g :=
  rfl
#align tensor_product.hom_tensor_hom_map_apply TensorProduct.homTensorHomMap_apply

end

/-- If `M` and `P` are linearly equivalent and `N` and `Q` are linearly equivalent
then `M ⊗ N` and `P ⊗ Q` are linearly equivalent. -/
def congr (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) : M ⊗[R] N ≃ₗ[R] P ⊗[R] Q :=
  LinearEquiv.ofLinear (map f g) (map f.symm g.symm)
    (ext' fun m n => by simp)
                        -- 🎉 no goals
    (ext' fun m n => by simp)
                        -- 🎉 no goals
#align tensor_product.congr TensorProduct.congr

@[simp]
theorem congr_tmul (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (m : M) (n : N) :
    congr f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl
#align tensor_product.congr_tmul TensorProduct.congr_tmul

@[simp]
theorem congr_symm_tmul (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (p : P) (q : Q) :
    (congr f g).symm (p ⊗ₜ q) = f.symm p ⊗ₜ g.symm q :=
  rfl
#align tensor_product.congr_symm_tmul TensorProduct.congr_symm_tmul

variable (R M N P Q)

/-- A tensor product analogue of `mul_left_comm`. -/
def leftComm : M ⊗[R] N ⊗[R] P ≃ₗ[R] N ⊗[R] M ⊗[R] P :=
  let e₁ := (TensorProduct.assoc R M N P).symm
  let e₂ := congr (TensorProduct.comm R M N) (1 : P ≃ₗ[R] P)
  let e₃ := TensorProduct.assoc R N M P
  e₁ ≪≫ₗ (e₂ ≪≫ₗ e₃)
#align tensor_product.left_comm TensorProduct.leftComm

variable {M N P Q}

@[simp]
theorem leftComm_tmul (m : M) (n : N) (p : P) : leftComm R M N P (m ⊗ₜ (n ⊗ₜ p)) = n ⊗ₜ (m ⊗ₜ p) :=
  rfl
#align tensor_product.left_comm_tmul TensorProduct.leftComm_tmul

@[simp]
theorem leftComm_symm_tmul (m : M) (n : N) (p : P) :
    (leftComm R M N P).symm (n ⊗ₜ (m ⊗ₜ p)) = m ⊗ₜ (n ⊗ₜ p) :=
  rfl
#align tensor_product.left_comm_symm_tmul TensorProduct.leftComm_symm_tmul

variable (M N P Q)

/-- This special case is worth defining explicitly since it is useful for defining multiplication
on tensor products of modules carrying multiplications (e.g., associative rings, Lie rings, ...).

E.g., suppose `M = P` and `N = Q` and that `M` and `N` carry bilinear multiplications:
`M ⊗ M → M` and `N ⊗ N → N`. Using `map`, we can define `(M ⊗ M) ⊗ (N ⊗ N) → M ⊗ N` which, when
combined with this definition, yields a bilinear multiplication on `M ⊗ N`:
`(M ⊗ N) ⊗ (M ⊗ N) → M ⊗ N`. In particular we could use this to define the multiplication in
the `TensorProduct.semiring` instance (currently defined "by hand" using `TensorProduct.mul`).

See also `mul_mul_mul_comm`. -/
def tensorTensorTensorComm : (M ⊗[R] N) ⊗[R] P ⊗[R] Q ≃ₗ[R] (M ⊗[R] P) ⊗[R] N ⊗[R] Q :=
  let e₁ := TensorProduct.assoc R M N (P ⊗[R] Q)
  let e₂ := congr (1 : M ≃ₗ[R] M) (leftComm R N P Q)
  let e₃ := (TensorProduct.assoc R M P (N ⊗[R] Q)).symm
  e₁ ≪≫ₗ (e₂ ≪≫ₗ e₃)
#align tensor_product.tensor_tensor_tensor_comm TensorProduct.tensorTensorTensorComm

variable {M N P Q}

@[simp]
theorem tensorTensorTensorComm_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorComm R M N P Q (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ p ⊗ₜ (n ⊗ₜ q) :=
  rfl
#align tensor_product.tensor_tensor_tensor_comm_tmul TensorProduct.tensorTensorTensorComm_tmul

-- porting note: the proof here was `rfl` but that caused a timeout.
@[simp]
theorem tensorTensorTensorComm_symm :
    (tensorTensorTensorComm R M N P Q).symm = tensorTensorTensorComm R M P N Q :=
  by ext; rfl
     -- ⊢ ↑(LinearEquiv.symm (tensorTensorTensorComm R M N P Q)) x✝ = ↑(tensorTensorTe …
          -- 🎉 no goals
#align tensor_product.tensor_tensor_tensor_comm_symm TensorProduct.tensorTensorTensorComm_symm

variable (M N P Q)

/-- This special case is useful for describing the interplay between `dualTensorHomEquiv` and
composition of linear maps.

E.g., composition of linear maps gives a map `(M → N) ⊗ (N → P) → (M → P)`, and applying
`dual_tensor_hom_equiv.symm` to the three hom-modules gives a map
`(M.dual ⊗ N) ⊗ (N.dual ⊗ P) → (M.dual ⊗ P)`, which agrees with the application of `contractRight`
on `N ⊗ N.dual` after the suitable rebracketting.
-/
def tensorTensorTensorAssoc : (M ⊗[R] N) ⊗[R] P ⊗[R] Q ≃ₗ[R] (M ⊗[R] N ⊗[R] P) ⊗[R] Q :=
  (TensorProduct.assoc R (M ⊗[R] N) P Q).symm ≪≫ₗ
    congr (TensorProduct.assoc R M N P) (1 : Q ≃ₗ[R] Q)
#align tensor_product.tensor_tensor_tensor_assoc TensorProduct.tensorTensorTensorAssoc

variable {M N P Q}

@[simp]
theorem tensorTensorTensorAssoc_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorAssoc R M N P Q (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ (n ⊗ₜ p) ⊗ₜ q :=
  rfl
#align tensor_product.tensor_tensor_tensor_assoc_tmul TensorProduct.tensorTensorTensorAssoc_tmul

@[simp]
theorem tensorTensorTensorAssoc_symm_tmul (m : M) (n : N) (p : P) (q : Q) :
    (tensorTensorTensorAssoc R M N P Q).symm (m ⊗ₜ (n ⊗ₜ p) ⊗ₜ q) = m ⊗ₜ n ⊗ₜ (p ⊗ₜ q) :=
  rfl
#align tensor_product.tensor_tensor_tensor_assoc_symm_tmul TensorProduct.tensorTensorTensorAssoc_symm_tmul

end TensorProduct

open scoped TensorProduct
namespace LinearMap

variable {N}

/-- `lTensor M f : M ⊗ N →ₗ M ⊗ P` is the natural linear map induced by `f : N →ₗ P`. -/
def lTensor (f : N →ₗ[R] P) : M ⊗[R] N →ₗ[R] M ⊗[R] P :=
  TensorProduct.map id f
#align linear_map.ltensor LinearMap.lTensor

/-- `rTensor f M : N₁ ⊗ M →ₗ N₂ ⊗ M` is the natural linear map induced by `f : N₁ →ₗ N₂`. -/
def rTensor (f : N →ₗ[R] P) : N ⊗[R] M →ₗ[R] P ⊗[R] M :=
  TensorProduct.map f id
#align linear_map.rtensor LinearMap.rTensor

variable (g : P →ₗ[R] Q) (f : N →ₗ[R] P)

@[simp]
theorem lTensor_tmul (m : M) (n : N) : f.lTensor M (m ⊗ₜ n) = m ⊗ₜ f n :=
  rfl
#align linear_map.ltensor_tmul LinearMap.lTensor_tmul

@[simp]
theorem rTensor_tmul (m : M) (n : N) : f.rTensor M (n ⊗ₜ m) = f n ⊗ₜ m :=
  rfl
#align linear_map.rtensor_tmul LinearMap.rTensor_tmul

open TensorProduct

attribute [local ext high] TensorProduct.ext

/-- `lTensorHom M` is the natural linear map that sends a linear map `f : N →ₗ P` to `M ⊗ f`. -/
def lTensorHom : (N →ₗ[R] P) →ₗ[R] M ⊗[R] N →ₗ[R] M ⊗[R] P where
  toFun := lTensor M
  map_add' f g := by
    ext x y
    -- ⊢ ↑(↑(compr₂ (TensorProduct.mk R M N) (lTensor M (f + g))) x) y = ↑(↑(compr₂ ( …
    simp only [compr₂_apply, mk_apply, add_apply, lTensor_tmul, tmul_add]
    -- 🎉 no goals
  map_smul' r f := by
    dsimp
    -- ⊢ lTensor M (r • f) = r • lTensor M f
    ext x y
    -- ⊢ ↑(↑(compr₂ (TensorProduct.mk R M N) (lTensor M (r • f))) x) y = ↑(↑(compr₂ ( …
    simp only [compr₂_apply, mk_apply, tmul_smul, smul_apply, lTensor_tmul]
    -- 🎉 no goals
#align linear_map.ltensor_hom LinearMap.lTensorHom

/-- `rTensorHom M` is the natural linear map that sends a linear map `f : N →ₗ P` to `M ⊗ f`. -/
def rTensorHom : (N →ₗ[R] P) →ₗ[R] N ⊗[R] M →ₗ[R] P ⊗[R] M where
  toFun f := f.rTensor M
  map_add' f g := by
    ext x y
    -- ⊢ ↑(↑(compr₂ (TensorProduct.mk R N M) ((fun f => rTensor M f) (f + g))) x) y = …
    simp only [compr₂_apply, mk_apply, add_apply, rTensor_tmul, add_tmul]
    -- 🎉 no goals
  map_smul' r f := by
    dsimp
    -- ⊢ rTensor M (r • f) = r • rTensor M f
    ext x y
    -- ⊢ ↑(↑(compr₂ (TensorProduct.mk R N M) (rTensor M (r • f))) x) y = ↑(↑(compr₂ ( …
    simp only [compr₂_apply, mk_apply, smul_tmul, tmul_smul, smul_apply, rTensor_tmul]
    -- 🎉 no goals
#align linear_map.rtensor_hom LinearMap.rTensorHom

@[simp]
theorem coe_lTensorHom : (lTensorHom M : (N →ₗ[R] P) → M ⊗[R] N →ₗ[R] M ⊗[R] P) = lTensor M :=
  rfl
#align linear_map.coe_ltensor_hom LinearMap.coe_lTensorHom

@[simp]
theorem coe_rTensorHom : (rTensorHom M : (N →ₗ[R] P) → N ⊗[R] M →ₗ[R] P ⊗[R] M) = rTensor M :=
  rfl
#align linear_map.coe_rtensor_hom LinearMap.coe_rTensorHom

@[simp]
theorem lTensor_add (f g : N →ₗ[R] P) : (f + g).lTensor M = f.lTensor M + g.lTensor M :=
  (lTensorHom M).map_add f g
#align linear_map.ltensor_add LinearMap.lTensor_add

@[simp]
theorem rTensor_add (f g : N →ₗ[R] P) : (f + g).rTensor M = f.rTensor M + g.rTensor M :=
  (rTensorHom M).map_add f g
#align linear_map.rtensor_add LinearMap.rTensor_add

@[simp]
theorem lTensor_zero : lTensor M (0 : N →ₗ[R] P) = 0 :=
  (lTensorHom M).map_zero
#align linear_map.ltensor_zero LinearMap.lTensor_zero

@[simp]
theorem rTensor_zero : rTensor M (0 : N →ₗ[R] P) = 0 :=
  (rTensorHom M).map_zero
#align linear_map.rtensor_zero LinearMap.rTensor_zero

@[simp]
theorem lTensor_smul (r : R) (f : N →ₗ[R] P) : (r • f).lTensor M = r • f.lTensor M :=
  (lTensorHom M).map_smul r f
#align linear_map.ltensor_smul LinearMap.lTensor_smul

@[simp]
theorem rTensor_smul (r : R) (f : N →ₗ[R] P) : (r • f).rTensor M = r • f.rTensor M :=
  (rTensorHom M).map_smul r f
#align linear_map.rtensor_smul LinearMap.rTensor_smul

theorem lTensor_comp : (g.comp f).lTensor M = (g.lTensor M).comp (f.lTensor M) := by
  ext m n
  -- ⊢ ↑(↑(compr₂ (TensorProduct.mk R M N) (lTensor M (comp g f))) m) n = ↑(↑(compr …
  simp only [compr₂_apply, mk_apply, comp_apply, lTensor_tmul]
  -- 🎉 no goals
#align linear_map.ltensor_comp LinearMap.lTensor_comp

theorem lTensor_comp_apply (x : M ⊗[R] N) :
    (g.comp f).lTensor M x = (g.lTensor M) ((f.lTensor M) x) := by rw [lTensor_comp, coe_comp]; rfl
                                                                   -- ⊢ (↑(lTensor M g) ∘ ↑(lTensor M f)) x = ↑(lTensor M g) (↑(lTensor M f) x)
                                                                                                -- 🎉 no goals
#align linear_map.ltensor_comp_apply LinearMap.lTensor_comp_apply

theorem rTensor_comp : (g.comp f).rTensor M = (g.rTensor M).comp (f.rTensor M) := by
  ext m n
  -- ⊢ ↑(↑(compr₂ (TensorProduct.mk R N M) (rTensor M (comp g f))) m) n = ↑(↑(compr …
  simp only [compr₂_apply, mk_apply, comp_apply, rTensor_tmul]
  -- 🎉 no goals
#align linear_map.rtensor_comp LinearMap.rTensor_comp

theorem rTensor_comp_apply (x : N ⊗[R] M) :
    (g.comp f).rTensor M x = (g.rTensor M) ((f.rTensor M) x) := by rw [rTensor_comp, coe_comp]; rfl
                                                                   -- ⊢ (↑(rTensor M g) ∘ ↑(rTensor M f)) x = ↑(rTensor M g) (↑(rTensor M f) x)
                                                                                                -- 🎉 no goals
#align linear_map.rtensor_comp_apply LinearMap.rTensor_comp_apply

theorem lTensor_mul (f g : Module.End R N) : (f * g).lTensor M = f.lTensor M * g.lTensor M :=
  lTensor_comp M f g
#align linear_map.ltensor_mul LinearMap.lTensor_mul

theorem rTensor_mul (f g : Module.End R N) : (f * g).rTensor M = f.rTensor M * g.rTensor M :=
  rTensor_comp M f g
#align linear_map.rtensor_mul LinearMap.rTensor_mul

variable (N)

@[simp]
theorem lTensor_id : (id : N →ₗ[R] N).lTensor M = id :=
  map_id
#align linear_map.ltensor_id LinearMap.lTensor_id

-- `simp` can prove this.
theorem lTensor_id_apply (x : M ⊗[R] N) : (LinearMap.id : N →ₗ[R] N).lTensor M x = x := by
  rw [lTensor_id, id_coe, id.def]
  -- 🎉 no goals
#align linear_map.ltensor_id_apply LinearMap.lTensor_id_apply

@[simp]
theorem rTensor_id : (id : N →ₗ[R] N).rTensor M = id :=
  map_id
#align linear_map.rtensor_id LinearMap.rTensor_id

-- `simp` can prove this.
theorem rTensor_id_apply (x : N ⊗[R] M) : (LinearMap.id : N →ₗ[R] N).rTensor M x = x := by
  rw [rTensor_id, id_coe, id.def]
  -- 🎉 no goals
#align linear_map.rtensor_id_apply LinearMap.rTensor_id_apply

variable {N}

@[simp]
theorem lTensor_comp_rTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (g.lTensor P).comp (f.rTensor N) = map f g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]
  -- 🎉 no goals
#align linear_map.ltensor_comp_rtensor LinearMap.lTensor_comp_rTensor

@[simp]
theorem rTensor_comp_lTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (f.rTensor Q).comp (g.lTensor M) = map f g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]
  -- 🎉 no goals
#align linear_map.rtensor_comp_ltensor LinearMap.rTensor_comp_lTensor

@[simp]
theorem map_comp_rTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (f' : S →ₗ[R] M) :
    (map f g).comp (f'.rTensor _) = map (f.comp f') g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]
  -- 🎉 no goals
#align linear_map.map_comp_rtensor LinearMap.map_comp_rTensor

@[simp]
theorem map_comp_lTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (g' : S →ₗ[R] N) :
    (map f g).comp (g'.lTensor _) = map f (g.comp g') := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]
  -- 🎉 no goals
#align linear_map.map_comp_ltensor LinearMap.map_comp_lTensor

@[simp]
theorem rTensor_comp_map (f' : P →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (f'.rTensor _).comp (map f g) = map (f'.comp f) g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]
  -- 🎉 no goals
#align linear_map.rtensor_comp_map LinearMap.rTensor_comp_map

@[simp]
theorem lTensor_comp_map (g' : Q →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (g'.lTensor _).comp (map f g) = map f (g'.comp g) := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]
  -- 🎉 no goals
#align linear_map.ltensor_comp_map LinearMap.lTensor_comp_map

variable {M}

@[simp]
theorem rTensor_pow (f : M →ₗ[R] M) (n : ℕ) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  have h := TensorProduct.map_pow f (id : N →ₗ[R] N) n
  -- ⊢ rTensor N f ^ n = rTensor N (f ^ n)
  rwa [id_pow] at h
  -- 🎉 no goals
#align linear_map.rtensor_pow LinearMap.rTensor_pow

@[simp]
theorem lTensor_pow (f : N →ₗ[R] N) (n : ℕ) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  have h := TensorProduct.map_pow (id : M →ₗ[R] M) f n
  -- ⊢ lTensor M f ^ n = lTensor M (f ^ n)
  rwa [id_pow] at h
  -- 🎉 no goals
#align linear_map.ltensor_pow LinearMap.lTensor_pow

end LinearMap

end Semiring

section Ring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q] [AddCommGroup S]
variable [Module R M] [Module R N] [Module R P] [Module R Q] [Module R S]

namespace TensorProduct

open TensorProduct

open LinearMap

variable (R)

/-- Auxiliary function to defining negation multiplication on tensor product. -/
def Neg.aux : FreeAddMonoid (M × N) →+ M ⊗[R] N :=
  FreeAddMonoid.lift fun p : M × N => (-p.1) ⊗ₜ p.2
#align tensor_product.neg.aux TensorProduct.Neg.aux

variable {R}

theorem Neg.aux_of (m : M) (n : N) : Neg.aux R (FreeAddMonoid.of (m, n)) = (-m) ⊗ₜ[R] n :=
  rfl
#align tensor_product.neg.aux_of TensorProduct.Neg.aux_of

instance neg : Neg (M ⊗[R] N) where
  neg :=
    (addConGen (TensorProduct.Eqv R M N)).lift (Neg.aux R) <|
      AddCon.addConGen_le fun x y hxy =>
        match x, y, hxy with
        | _, _, Eqv.of_zero_left n =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_zero, Neg.aux_of, neg_zero, zero_tmul]
                                     -- 🎉 no goals
        | _, _, Eqv.of_zero_right m =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_zero, Neg.aux_of, tmul_zero]
                                     -- 🎉 no goals
        | _, _, Eqv.of_add_left m₁ m₂ n =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, Neg.aux_of, neg_add, add_tmul]
                                     -- 🎉 no goals
        | _, _, Eqv.of_add_right m n₁ n₂ =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, Neg.aux_of, tmul_add]
                                     -- 🎉 no goals
        | _, _, Eqv.of_smul s m n =>
          (AddCon.ker_rel _).2 <| by simp_rw [Neg.aux_of, ← smul_neg, ← smul_tmul]
                                     -- 🎉 no goals
        | _, _, Eqv.add_comm x y =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]
                                     -- 🎉 no goals

protected theorem add_left_neg (x : M ⊗[R] N) : -x + x = 0 :=
  x.induction_on
    (by rw [add_zero]; apply (Neg.aux R).map_zero)
        -- ⊢ -0 = 0
                       -- 🎉 no goals
    (fun x y => by convert (add_tmul (R := R) (-x) x y).symm; rw [add_left_neg, zero_tmul])
                   -- ⊢ 0 = (-x + x) ⊗ₜ[R] y
                                                              -- 🎉 no goals
    fun x y hx hy => by
    suffices : -x + x + (-y + y) = 0
    -- ⊢ -(x + y) + (x + y) = 0
    · rw [← this]
      -- ⊢ -(x + y) + (x + y) = -x + x + (-y + y)
      unfold Neg.neg neg
      -- ⊢ { neg := ↑(AddCon.lift (addConGen (Eqv R M N)) (Neg.aux R) (_ : addConGen (E …
      simp only
      -- ⊢ ↑(AddCon.lift (addConGen (Eqv R M N)) (Neg.aux R) (_ : addConGen (Eqv R M N) …
      rw [AddMonoidHom.map_add]
      -- ⊢ ↑(AddCon.lift (addConGen (Eqv R M N)) (Neg.aux R) (_ : addConGen (Eqv R M N) …
      abel
      -- 🎉 no goals
      -- 🎉 no goals
    rw [hx, hy, add_zero]
    -- 🎉 no goals
#align tensor_product.add_left_neg TensorProduct.add_left_neg

instance addCommGroup : AddCommGroup (M ⊗[R] N) :=
  { TensorProduct.addCommMonoid with
    neg := Neg.neg
    sub := _
    sub_eq_add_neg := fun _ _ => rfl
    add_left_neg := fun x => TensorProduct.add_left_neg x
    zsmul := fun n v => n • v
    zsmul_zero' := by simp [TensorProduct.zero_smul]
                      -- 🎉 no goals
    zsmul_succ' := by simp [Nat.succ_eq_one_add, TensorProduct.one_smul, TensorProduct.add_smul]
                      -- 🎉 no goals
    zsmul_neg' := fun n x => by
      change (-n.succ : ℤ) • x = -(((n : ℤ) + 1) • x)
      -- ⊢ -↑(Nat.succ n) • x = -((↑n + 1) • x)
      rw [← zero_add (_ • x), ← TensorProduct.add_left_neg ((n.succ : ℤ) • x), add_assoc,
        ← add_smul, ← sub_eq_add_neg, sub_self, zero_smul, add_zero]
      rfl }
      -- 🎉 no goals

theorem neg_tmul (m : M) (n : N) : (-m) ⊗ₜ n = -m ⊗ₜ[R] n :=
  rfl
#align tensor_product.neg_tmul TensorProduct.neg_tmul

theorem tmul_neg (m : M) (n : N) : m ⊗ₜ (-n) = -m ⊗ₜ[R] n :=
  (mk R M N _).map_neg _
#align tensor_product.tmul_neg TensorProduct.tmul_neg

theorem tmul_sub (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ - n₂) = m ⊗ₜ[R] n₁ - m ⊗ₜ[R] n₂ :=
  (mk R M N _).map_sub _ _
#align tensor_product.tmul_sub TensorProduct.tmul_sub

theorem sub_tmul (m₁ m₂ : M) (n : N) : (m₁ - m₂) ⊗ₜ n = m₁ ⊗ₜ[R] n - m₂ ⊗ₜ[R] n :=
  (mk R M N).map_sub₂ _ _ _
#align tensor_product.sub_tmul TensorProduct.sub_tmul

/-- While the tensor product will automatically inherit a ℤ-module structure from
`AddCommGroup.intModule`, that structure won't be compatible with lemmas like `tmul_smul` unless
we use a `ℤ-Module` instance provided by `TensorProduct.left_module`.

When `R` is a `Ring` we get the required `TensorProduct.compatible_smul` instance through
`IsScalarTower`, but when it is only a `Semiring` we need to build it from scratch.
The instance diamond in `compatible_smul` doesn't matter because it's in `Prop`.
-/
instance CompatibleSMul.int : CompatibleSMul R ℤ M N :=
  ⟨fun r m n =>
    Int.induction_on r (by simp) (fun r ih => by simpa [add_smul, tmul_add, add_tmul] using ih)
                           -- 🎉 no goals
                                                 -- 🎉 no goals
      fun r ih => by simpa [sub_smul, tmul_sub, sub_tmul] using ih⟩
                     -- 🎉 no goals
#align tensor_product.compatible_smul.int TensorProduct.CompatibleSMul.int

instance CompatibleSMul.unit {S} [Monoid S] [DistribMulAction S M] [DistribMulAction S N]
    [CompatibleSMul R S M N] : CompatibleSMul R Sˣ M N :=
  ⟨fun s m n => (CompatibleSMul.smul_tmul (s : S) m n : _)⟩
#align tensor_product.compatible_smul.unit TensorProduct.CompatibleSMul.unit

end TensorProduct

namespace LinearMap

@[simp]
theorem lTensor_sub (f g : N →ₗ[R] P) : (f - g).lTensor M = f.lTensor M - g.lTensor M := by
  simp_rw [← coe_lTensorHom]
  -- ⊢ ↑(lTensorHom M) (f - g) = ↑(lTensorHom M) f - ↑(lTensorHom M) g
  exact (lTensorHom (R:=R) (N:=N) (P:=P) M).map_sub f g
  -- 🎉 no goals
#align linear_map.ltensor_sub LinearMap.lTensor_sub

@[simp]
theorem rTensor_sub (f g : N →ₗ[R] P) : (f - g).rTensor M = f.rTensor M - g.rTensor M := by
  simp only [← coe_rTensorHom]
  -- ⊢ ↑(rTensorHom M) (f - g) = ↑(rTensorHom M) f - ↑(rTensorHom M) g
  exact (rTensorHom (R:=R) (N:=N) (P:=P) M).map_sub f g
  -- 🎉 no goals
#align linear_map.rtensor_sub LinearMap.rTensor_sub

@[simp]
theorem lTensor_neg (f : N →ₗ[R] P) : (-f).lTensor M = -f.lTensor M := by
  simp only [← coe_lTensorHom]
  -- ⊢ ↑(lTensorHom M) (-f) = -↑(lTensorHom M) f
  exact (lTensorHom (R:=R) (N:=N) (P:=P) M).map_neg f
  -- 🎉 no goals
#align linear_map.ltensor_neg LinearMap.lTensor_neg

@[simp]
theorem rTensor_neg (f : N →ₗ[R] P) : (-f).rTensor M = -f.rTensor M := by
  simp only [← coe_rTensorHom]
  -- ⊢ ↑(rTensorHom M) (-f) = -↑(rTensorHom M) f
  exact (rTensorHom (R:=R) (N:=N) (P:=P) M).map_neg f
  -- 🎉 no goals
#align linear_map.rtensor_neg LinearMap.rTensor_neg

end LinearMap

end Ring
