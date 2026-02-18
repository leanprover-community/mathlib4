/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.GroupTheory.GroupAction.Ring

/-!
# The pointwise product on `Finsupp`.

For the convolution product on `Finsupp` when the domain has a binary operation,
see the type synonyms `AddMonoidAlgebra`
(which is in turn used to define `Polynomial` and `MvPolynomial`)
and `MonoidAlgebra`.
-/

@[expose] public section


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

@[simp]
theorem mul_apply {g₁ g₂ : α →₀ β} {a : α} : (g₁ * g₂) a = g₁ a * g₂ a :=
  rfl

@[simp]
theorem single_mul (a : α) (b₁ b₂ : β) : single a (b₁ * b₂) = single a b₁ * single a b₂ :=
  (zipWith_single_single _ _ _ _ _).symm

lemma support_mul_subset_left {g₁ g₂ : α →₀ β} :
    (g₁ * g₂).support ⊆ g₁.support := fun x hx => by
  aesop

lemma support_mul_subset_right {g₁ g₂ : α →₀ β} :
    (g₁ * g₂).support ⊆ g₂.support := fun x hx => by
  aesop

theorem support_mul [DecidableEq α] {g₁ g₂ : α →₀ β} :
    (g₁ * g₂).support ⊆ g₁.support ∩ g₂.support :=
  subset_inter support_mul_subset_left support_mul_subset_right

instance : MulZeroClass (α →₀ β) :=
  DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

end

instance [SemigroupWithZero β] : SemigroupWithZero (α →₀ β) :=
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

instance [NonUnitalNonAssocSemiring β] : NonUnitalNonAssocSemiring (α →₀ β) :=
  DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ ↦ rfl

instance [NonUnitalSemiring β] : NonUnitalSemiring (α →₀ β) :=
  DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ ↦ rfl

instance [NonUnitalCommSemiring β] : NonUnitalCommSemiring (α →₀ β) :=
  DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ ↦ rfl

instance [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing (α →₀ β) :=
  DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance [NonUnitalRing β] : NonUnitalRing (α →₀ β) :=
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ ↦ rfl)
    fun _ _ ↦ rfl

instance [NonUnitalCommRing β] : NonUnitalCommRing (α →₀ β) :=
  DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl

section pointwiseModule

lemma pointwise_smul_support_finite {ι R M : Type*} [Zero M] [SMulZeroClass R M] (f : ι → R)
    (g : ι →₀ M) : (fun x ↦ f x • g x).support.Finite :=
  Set.Finite.subset g.finite_support (by intro; simp; grind [smul_zero])

-- TODO(Paul-Lez): add a `DFinsupp` version of this.
-- Note: this creates an instance diamond with `SMul (α → β) (α →₀ (α → β))`, so this is an
-- def rather than an instance.
/-- Pointwise scalar multiplication given by `(f • g) x = f x • g x`. -/
-- see Note [reducible non-instances]
abbrev pointwiseScalar {ι R M : Type*} [Zero M] [SMulZeroClass R M] : SMul (ι → R) (ι →₀ M) where
  smul f g := Finsupp.ofSupportFinite (fun a ↦ f a • g a) (pointwise_smul_support_finite ..)

instance pointwiseScalarModule {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] :
    SMul (ι → R) (ι →₀ M) := pointwiseScalar

@[simp]
theorem coe_pointwise_smul {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (f : ι → R) (g : ι →₀ M) : ⇑(f • g) = f • ⇑g := by rfl

/-- The pointwise multiplicative action of functions on finitely supported functions -/
instance pointwiseModule {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] :
    Module (ι → R) (ι →₀ M) :=
  Function.Injective.module _ coeFnAddHom DFunLike.coe_injective (by intros; rfl)

instance {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] :
    IsScalarTower R (ι → R) (ι →₀ M) where
  smul_assoc r f m := by ext; simp [smul_smul]

end pointwiseModule

end Finsupp
