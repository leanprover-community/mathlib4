/-
Copyright (c) 2024 Raghuram Sundararajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raghuram Sundararajan
-/
module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Ext

/-!
# Extensionality lemmas for rings and similar structures

In this file we prove extensionality lemmas for the ring-like structures defined in
`Mathlib/Algebra/Ring/Defs.lean`, ranging from `NonUnitalNonAssocSemiring` to `Ring`. These
extensionality lemmas take the form of asserting that two algebraic structures on a type are equal
whenever the addition and multiplication defined by them are both the same.

## Implementation details

We follow `Mathlib/Algebra/Group/Ext.lean` in using the term `(letI := i; HMul.hMul : R → R → R)` to
refer to the multiplication specified by a typeclass instance `i` on a type `R` (and similarly for
addition). We abbreviate these using some local notations.

Since `Mathlib/Algebra/Group/Ext.lean` proved several injectivity lemmas, we do so as well — even if
sometimes we don't need them to prove extensionality.

## Tags
semiring, ring, extensionality
-/

public section

local macro:max "local_hAdd[" type:term ", " inst:term "]" : term =>
  `(term| (letI := $inst; HAdd.hAdd : $type → $type → $type))
local macro:max "local_hMul[" type:term ", " inst:term "]" : term =>
  `(term| (letI := $inst; HMul.hMul : $type → $type → $type))

universe u

variable {R : Type u}

/-! ### Distrib -/
namespace Distrib

@[ext] theorem ext ⦃inst₁ inst₂ : Distrib R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Split into `add` and `mul` functions and properties.
  rcases inst₁ with @⟨⟨⟩, ⟨⟩⟩
  rcases inst₂ with @⟨⟨⟩, ⟨⟩⟩
  -- Prove equality of parts using function extensionality.
  congr

end Distrib

/-! ### NonUnitalNonAssocSemiring -/
namespace NonUnitalNonAssocSemiring

@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Split into `AddMonoid` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, _, ⟨⟩⟩
  rcases inst₂ with @⟨_, _, ⟨⟩⟩
  -- Prove equality of parts using already-proved extensionality lemmas.
  congr; ext : 1; assumption

theorem toDistrib_injective : Function.Injective (@toDistrib R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end NonUnitalNonAssocSemiring

/-! ### NonUnitalSemiring -/
namespace NonUnitalSemiring

theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
  toNonUnitalNonAssocSemiring_injective <|
    NonUnitalNonAssocSemiring.ext h_add h_mul

end NonUnitalSemiring

/-! ### NonAssocSemiring and its ancestors

This section also includes results for `AddMonoidWithOne` etc.
as these are considered implementation detail of the ring classes.
TODO consider relocating these lemmas.
-/
@[ext] theorem AddMonoidWithOne.ext ⦃inst₁ inst₂ : AddMonoidWithOne R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_one : (letI := inst₁; One.one : R) = (letI := inst₂; One.one : R)) :
    inst₁ = inst₂ := by
  have h_monoid : inst₁.toAddMonoid = inst₂.toAddMonoid := by ext : 1; exact h_add
  have h_zero' : inst₁.toZero = inst₂.toZero := congrArg (·.toZero) h_monoid
  have h_one' : inst₁.toOne = inst₂.toOne :=
    congrArg One.mk h_one
  have h_natCast : inst₁.toNatCast.natCast = inst₂.toNatCast.natCast := by
    funext n; induction n with
    | zero => rewrite [inst₁.natCast_zero, inst₂.natCast_zero]
              exact congrArg (@Zero.zero R) h_zero'
    | succ n h => rw [inst₁.natCast_succ, inst₂.natCast_succ, h_add]
                  exact congrArg₂ _ h h_one
  rcases inst₁ with @⟨⟨⟩⟩; rcases inst₂ with @⟨⟨⟩⟩
  congr

namespace NonAssocSemiring

/-! The best place to prove that the `NatCast` is determined by the other operations is probably in
an extensionality lemma for `AddMonoidWithOne`, in which case we may as well do the typeclasses
defined in `Mathlib/Algebra/GroupWithZero/Defs.lean` as well. -/
@[ext] theorem ext ⦃inst₁ inst₂ : NonAssocSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  have h : inst₁.toNonUnitalNonAssocSemiring = inst₂.toNonUnitalNonAssocSemiring := by
    ext : 1 <;> assumption
  have h_zero : (inst₁.toMulZeroClass).toZero.zero = (inst₂.toMulZeroClass).toZero.zero :=
    congrArg (fun inst => (inst.toMulZeroClass).toZero.zero) h
  have h_one' : (inst₁.toMulZeroOneClass).toMulOneClass.toOne
                = (inst₂.toMulZeroOneClass).toMulOneClass.toOne := by
    congr 1; ext : 1; exact h_mul
  have h_one : (inst₁.toMulZeroOneClass).toMulOneClass.toOne.one
               = (inst₂.toMulZeroOneClass).toMulOneClass.toOne.one :=
    congrArg (@One.one R) h_one'
  have : inst₁.toAddMonoidWithOne = inst₂.toAddMonoidWithOne := by
    ext : 1 <;> assumption
  have : inst₁.toNatCast = inst₂.toNatCast :=
    congrArg (·.toNatCast) this
  -- Split into `NonUnitalNonAssocSemiring`, `One` and `natCast` instances.
  cases inst₁; cases inst₂
  congr

theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  intro _ _ _
  ext <;> congr

end NonAssocSemiring

/-! ### NonUnitalNonAssocRing -/
namespace NonUnitalNonAssocRing

@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Split into `AddGroup` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, _, ⟨⟩⟩; rcases inst₂ with @⟨_, _, ⟨⟩⟩
  congr; (ext : 1; assumption)

theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  intro _ _ h
  -- Use above extensionality lemma to prove injectivity by showing that `h_add` and `h_mul` hold.
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end NonUnitalNonAssocRing

/-! ### NonUnitalRing -/
namespace NonUnitalRing

@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  have : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext : 1 <;> assumption
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr

theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

theorem toNonUnitalNonAssocRing_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

@[deprecated (since := "2026-09-17")]
alias toNonUnitalNonAssocring_injective := toNonUnitalNonAssocRing_injective

end NonUnitalRing

/-! ### NonAssocRing and its ancestors

This section also includes results for `AddGroupWithOne` etc.
as these are considered implementation detail of the ring classes.
TODO consider relocating these lemmas. -/
@[ext] theorem AddGroupWithOne.ext ⦃inst₁ inst₂ : AddGroupWithOne R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_one : (letI := inst₁; One.one : R) = (letI := inst₂; One.one)) :
    inst₁ = inst₂ := by
  have : inst₁.toAddMonoidWithOne = inst₂.toAddMonoidWithOne :=
    AddMonoidWithOne.ext h_add h_one
  have : inst₁.toNatCast = inst₂.toNatCast := congrArg (·.toNatCast) this
  have h_group : inst₁.toAddGroup = inst₂.toAddGroup := by ext : 1; exact h_add
  -- Extract equality of necessary substructures from h_group
  injection h_group with h_group; injection h_group
  have : inst₁.toIntCast.intCast = inst₂.toIntCast.intCast := by
    funext n; cases n with
    | ofNat n => rewrite [Int.ofNat_eq_natCast, inst₁.intCast_ofNat, inst₂.intCast_ofNat]; congr
    | negSucc n => rewrite [inst₁.intCast_negSucc, inst₂.intCast_negSucc]; congr
  rcases inst₁ with @⟨⟨⟩⟩; rcases inst₂ with @⟨⟨⟩⟩
  congr

namespace NonAssocRing

@[ext] theorem ext ⦃inst₁ inst₂ : NonAssocRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  have h₁ : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemiring := by
    ext : 1 <;> assumption
  -- Mathematically non-trivial fact: `intCast` is determined by the rest.
  have h₃ : inst₁.toAddGroupWithOne = inst₂.toAddGroupWithOne :=
    AddGroupWithOne.ext h_add (congrArg (·.toOne.one) h₂)
  cases inst₁; cases inst₂
  congr <;> solve | injection h₁ | injection h₂ | injection h₃

theorem toNonAssocSemiring_injective :
    Function.Injective (@toNonAssocSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

theorem toNonUnitalNonAssocRing_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

@[deprecated (since := "2026-09-17")]
alias toNonUnitalNonAssocring_injective := toNonUnitalNonAssocRing_injective

end NonAssocRing

/-! ### Semiring -/
namespace Semiring

@[ext] theorem ext ⦃inst₁ inst₂ : Semiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Show that enough substructures are equal.
  have h₀ : inst₁.toAddMonoid = inst₂.toAddMonoid := by
    ext : 1 <;> assumption
  have h₁ : inst₁.toNonUnitalSemiring = inst₂.toNonUnitalSemiring := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemiring := by
    ext : 1 <;> assumption
  have h₃ : (inst₁.toMonoidWithZero).toMonoid = (inst₂.toMonoidWithZero).toMonoid := by
    ext : 1; exact h_mul
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr <;> solve | injection h₁ | injection h₂

theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

theorem toNonAssocSemiring_injective :
    Function.Injective (@toNonAssocSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end Semiring

/-! ### Ring -/
namespace Ring

@[ext] theorem ext ⦃inst₁ inst₂ : Ring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Show that enough substructures are equal.
  have h₁ : inst₁.toSemiring = inst₂.toSemiring := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocRing = inst₂.toNonAssocRing := by
    ext : 1 <;> assumption
  /- We prove that the `SubNegMonoid`s are equal because they are one
  field away from `Sub` and `Neg`, enabling use of `injection`. -/
  have h₃ : inst₁.toAddGroup.toSubNegMonoid
            = inst₂.toAddGroup.toSubNegMonoid :=
    congrArg (@AddGroup.toSubNegMonoid R) <| by ext : 1; exact h_add
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr <;> solve | injection h₂ | injection h₃

theorem toNonUnitalRing_injective :
    Function.Injective (@toNonUnitalRing R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

theorem toNonAssocRing_injective :
    Function.Injective (@toNonAssocRing R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

theorem toSemiring_injective :
    Function.Injective (@toSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end Ring
