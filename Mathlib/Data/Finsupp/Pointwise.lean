/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.Finsupp.Defs
import Mathlib.Algebra.Ring.Pi

#align_import data.finsupp.pointwise from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# The pointwise product on `Finsupp`.

For the convolution product on `Finsupp` when the domain has a binary operation,
see the type synonyms `AddMonoidAlgebra`
(which is in turn used to define `Polynomial` and `MvPolynomial`)
and `MonoidAlgebra`.
-/


noncomputable section

open Finset

universe u₁ u₂ u₃ u₄ u₅

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄} {ι : Type u₅}

namespace Finsupp

/-! ### Declarations about the pointwise product on `Finsupp`s -/


section

variable [MulZeroClass β]

/-- The product of `f g : α →₀ β` is the finitely supported function
  whose value at `a` is `f a * g a`. -/
instance : Mul (α →₀ β) :=
  ⟨zipWith (· * ·) (mul_zero 0)⟩

theorem coe_mul (g₁ g₂ : α →₀ β) : ⇑(g₁ * g₂) = g₁ * g₂ :=
  rfl
#align finsupp.coe_mul Finsupp.coe_mul

@[simp]
theorem mul_apply {g₁ g₂ : α →₀ β} {a : α} : (g₁ * g₂) a = g₁ a * g₂ a :=
  rfl
#align finsupp.mul_apply Finsupp.mul_apply

theorem support_mul [DecidableEq α] {g₁ g₂ : α →₀ β} :
    (g₁ * g₂).support ⊆ g₁.support ∩ g₂.support := by
  intro a h
  -- ⊢ a ∈ g₁.support ∩ g₂.support
  simp only [mul_apply, mem_support_iff] at h
  -- ⊢ a ∈ g₁.support ∩ g₂.support
  simp only [mem_support_iff, mem_inter, Ne.def]
  -- ⊢ ¬↑g₁ a = 0 ∧ ¬↑g₂ a = 0
  rw [← not_or]
  -- ⊢ ¬(↑g₁ a = 0 ∨ ↑g₂ a = 0)
  intro w
  -- ⊢ False
  apply h
  -- ⊢ ↑g₁ a * ↑g₂ a = 0
  cases' w with w w <;> (rw [w]; simp)
  -- ⊢ ↑g₁ a * ↑g₂ a = 0
                         -- ⊢ 0 * ↑g₂ a = 0
                                 -- 🎉 no goals
                         -- ⊢ ↑g₁ a * 0 = 0
                                 -- 🎉 no goals
#align finsupp.support_mul Finsupp.support_mul

instance : MulZeroClass (α →₀ β) :=
  FunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

end

instance [SemigroupWithZero β] : SemigroupWithZero (α →₀ β) :=
  FunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

instance [NonUnitalNonAssocSemiring β] : NonUnitalNonAssocSemiring (α →₀ β) :=
  FunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ ↦ rfl

instance [NonUnitalSemiring β] : NonUnitalSemiring (α →₀ β) :=
  FunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ ↦ rfl

instance [NonUnitalCommSemiring β] : NonUnitalCommSemiring (α →₀ β) :=
  FunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ ↦ rfl

instance [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing (α →₀ β) :=
  FunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance [NonUnitalRing β] : NonUnitalRing (α →₀ β) :=
  FunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ ↦ rfl)
    fun _ _ ↦ rfl

instance [NonUnitalCommRing β] : NonUnitalCommRing (α →₀ β) :=
  FunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl

-- TODO can this be generalized in the direction of `Pi.smul'`
-- (i.e. dependent functions and finsupps)
-- TODO in theory this could be generalised, we only really need `smul_zero` for the definition
instance pointwiseScalar [Semiring β] : SMul (α → β) (α →₀ β) where
  smul f g :=
    Finsupp.ofSupportFinite (fun a ↦ f a • g a) (by
      apply Set.Finite.subset g.finite_support
      -- ⊢ (Function.support fun a => f a • ↑g a) ⊆ Function.support ↑g
      simp only [Function.support_subset_iff, Finsupp.mem_support_iff, Ne.def,
        Finsupp.fun_support_eq, Finset.mem_coe]
      intro x hx h
      -- ⊢ False
      apply hx
      -- ⊢ f x • ↑g x = 0
      rw [h, smul_zero])
      -- 🎉 no goals
#align finsupp.pointwise_scalar Finsupp.pointwiseScalar

@[simp]
theorem coe_pointwise_smul [Semiring β] (f : α → β) (g : α →₀ β) : FunLike.coe (f • g) = f • g :=
  rfl
#align finsupp.coe_pointwise_smul Finsupp.coe_pointwise_smul

/-- The pointwise multiplicative action of functions on finitely supported functions -/
instance pointwiseModule [Semiring β] : Module (α → β) (α →₀ β) :=
  Function.Injective.module _ coeFnAddHom FunLike.coe_injective coe_pointwise_smul
#align finsupp.pointwise_module Finsupp.pointwiseModule

end Finsupp
