/-
Copyright (c) 2024 Raghuram Sundararajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raghuram Sundararajan
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Ext
-- import Mathlib

/-!
# Extensionality lemmas for rings and similar structures

In this file we prove extensionality lemmas for the ring-like structures defined in
`Algebra/Ring/Defs`, ranging from `NonUnitalNonAssocSemiring` to `CommRing`. These extensionality
lemmas take the form of asserting that two algebraic structures on a type are equal whenever the
addition and multiplication defined by them are both the same.

## Implementation details

We follow `Algebra/Group/Ext` in using the term `(letI := i; HMul.hMul : R → R → R)` to refer to the
multiplication specified by a typeclass instance `i` on a type `R` (and similarly for addition). We
abbreviate these using some local notations.

Since `Algebra/Group/Ext` proved several injectivity lemmas, we do so as well — even if sometimes we
don't need them to prove extensionality.

## Tags
semiring, ring, extensionality
-/

local macro:65 lhs:term:65 "+[" type:term ", " inst:term "]" rhs:term:66 : term =>
  `(term| (letI := $inst; ($lhs : $type) + ($rhs : $type) : $type))
local macro:70 lhs:term:70 "*[" type:term ", " inst:term "]" rhs:term:71 : term =>
  `(term| (letI := $inst; ($lhs : $type) * ($rhs : $type) : $type))

universe u

variable {R : Type u}

/-! ### Distrib -/
namespace Distrib

@[ext] theorem ext ⦃inst₁ inst₂ : Distrib R⦄
    (h_add : ∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
    (h_mul : ∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :
    inst₁ = inst₂ := by
  -- Split into `add` and `mul` functions and properties.
  rcases inst₁ with @⟨⟨⟩, ⟨⟩⟩
  rcases inst₂ with @⟨⟨⟩, ⟨⟩⟩
  -- Prove equality of parts using function extensionality.
  congr <;> (apply funext₂; assumption)

theorem ext_iff (inst₁ inst₂ : Distrib R) :
    inst₁ = inst₂ ↔
      (∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
      ∧ (∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (ext · ·)⟩

end Distrib

/-! ### NonUnitalNonAssocSemiring -/
namespace NonUnitalNonAssocSemiring

@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocSemiring R⦄
    (h_add : ∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
    (h_mul : ∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :
    inst₁ = inst₂ := by
  -- Split into `AddMonoid` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩
  rcases inst₂ with @⟨_, ⟨⟩⟩
  -- Prove equality of parts using already-proved extensionality lemmas.
  congr <;> (ext; apply_assumption)

theorem toDistrib_injective : Function.Injective (@toDistrib R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

theorem ext_iff (inst₁ inst₂ : NonUnitalNonAssocSemiring R) :
    inst₁ = inst₂ ↔
      (∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
      ∧ (∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (ext · ·)⟩

end NonUnitalNonAssocSemiring

/-! ### NonUnitalSemiring -/
namespace NonUnitalSemiring

theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalSemiring R⦄
    (h_add : ∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
    (h_mul : ∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :
    inst₁ = inst₂ :=
  toNonUnitalNonAssocSemiring_injective <|
    NonUnitalNonAssocSemiring.ext h_add h_mul

theorem ext_iff (inst₁ inst₂ : NonUnitalSemiring R) :
    inst₁ = inst₂ ↔
      (∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
      ∧ (∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (ext · ·)⟩

end NonUnitalSemiring

/-! ### NonAssocSemiring -/
namespace NonAssocSemiring

/- The best place to prove that the `NatCast` is determined by the other operations is probably in
an extensionality lemma for `AddMonoidWithOne`, in which case we may as well do the typeclasses
defined in `Algebra/GroupWithZero/Defs` as well. -/
@[ext] theorem ext ⦃inst₁ inst₂ : NonAssocSemiring R⦄
    (h_add : ∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
    (h_mul : ∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :
    inst₁ = inst₂ := by
  have h : inst₁.toNonUnitalNonAssocSemiring = inst₂.toNonUnitalNonAssocSemiring := by
    ext <;> apply_assumption
  have h_zero : (inst₁.toMulZeroClass).toZero.zero = (inst₂.toMulZeroClass).toZero.zero :=
    congrArg (fun inst => (inst.toMulZeroClass).toZero.zero) h
  have h_one' : (inst₁.toMulZeroOneClass).toMulOneClass.toOne
                = (inst₂.toMulZeroOneClass).toMulOneClass.toOne :=
    congrArg (@MulOneClass.toOne R) <| by
      ext; apply h_mul
  have h_one : (inst₁.toMulZeroOneClass).toMulOneClass.toOne.one
               = (inst₂.toMulZeroOneClass).toMulOneClass.toOne.one :=
    congrArg (@One.one R) h_one'
  -- Mathematically non-trivial fact: `natCast` is determined by `0`, `1` and `+`.
  have h_natCast : inst₁.toNatCast.natCast = inst₂.toNatCast.natCast := by
    funext n; induction n with
    | zero     => rewrite [inst₁.natCast_zero, inst₂.natCast_zero]; exact h_zero
    | succ n h => rw [inst₁.natCast_succ, inst₂.natCast_succ, h_add]
                  exact congrArg₂ _ h h_one
  -- Split into `NonUnitalNonAssocSemiring`, `One` instances, `natCast` function and properties.
  rcases inst₁ with @⟨_, _, _, _, ⟨⟩⟩; rcases inst₂ with @⟨_, _, _, _, ⟨⟩⟩
  -- Prove equality of parts using the above lemmas.
  congr

theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  intro _ _ _
  ext <;> congr

theorem ext_iff (inst₁ inst₂ : NonAssocSemiring R) :
    inst₁ = inst₂ ↔
      (∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
      ∧ (∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (ext · ·)⟩

end NonAssocSemiring

/-! ### NonUnitalNonAssocRing -/
namespace NonUnitalNonAssocRing

@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocRing R⦄
    (h_add : ∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
    (h_mul : ∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :
    inst₁ = inst₂ := by
  -- Split into `AddCommGroup` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩; rcases inst₂ with @⟨_, ⟨⟩⟩
  congr <;> (ext; apply_assumption)

theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  intro _ _ h
  -- Use above extensionality lemma to prove injectivity by showing that `h_add` and `h_mul` hold.
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

theorem ext_iff (inst₁ inst₂ : NonUnitalNonAssocRing R) :
    inst₁ = inst₂ ↔
      (∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
      ∧ (∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (ext · ·)⟩

end NonUnitalNonAssocRing

/-! ### NonUnitalRing -/
namespace NonUnitalRing

@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalRing R⦄
    (h_add : ∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
    (h_mul : ∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :
    inst₁ = inst₂ := by
  have : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext <;> apply_assumption
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr

theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

theorem toNonUnitalNonAssocring_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

theorem ext_iff (inst₁ inst₂ : NonUnitalRing R) :
    inst₁ = inst₂ ↔
      (∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
      ∧ (∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (ext · ·)⟩

end NonUnitalRing

/-! ### NonAssocRing -/
namespace NonAssocRing

@[ext] theorem ext ⦃inst₁ inst₂ : NonAssocRing R⦄
    (h_add : ∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
    (h_mul : ∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :
    inst₁ = inst₂ := by
  have h₁ : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext <;> apply_assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemiring := by
    ext <;> apply_assumption
  -- Mathematically non-trivial fact: `intCast` is determined by the rest.
  have h_intCast : inst₁.toIntCast.intCast = inst₂.toIntCast.intCast := by
    have : inst₁.toNatCast = inst₂.toNatCast := by injection h₂
    funext n; cases n with
    | ofNat n   => rewrite [← Int.coe_nat_eq, inst₁.intCast_ofNat, inst₂.intCast_ofNat]; congr
    | negSucc n => rewrite [inst₁.intCast_negSucc, inst₂.intCast_negSucc]; congr
  -- Split into fields (extracting `intCast` function) and prove they are equal using the above.
  rcases inst₁ with @⟨_, _, _, _, _, _, _, ⟨⟩⟩
  rcases inst₂ with @⟨_, _, _, _, _, _, _, ⟨⟩⟩
  congr <;> try solve| injection h₁ | injection h₂

theorem toNonAssocSemiring_injective :
    Function.Injective (@toNonAssocSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

theorem toNonUnitalNonAssocring_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

theorem ext_iff (inst₁ inst₂ : NonAssocRing R) :
    inst₁ = inst₂ ↔
      (∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
      ∧ (∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (ext · ·)⟩

end NonAssocRing

/-! ### Semiring -/
namespace Semiring

@[ext] theorem ext ⦃inst₁ inst₂ : Semiring R⦄
    (h_add : ∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
    (h_mul : ∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :
    inst₁ = inst₂ := by
  -- Show that enough substructures are equal.
  have h₁ : inst₁.toNonUnitalSemiring = inst₂.toNonUnitalSemiring := by
    ext <;> apply_assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemiring := by
    ext <;> apply_assumption
  have h₃ : (inst₁.toMonoidWithZero).toMonoid = (inst₂.toMonoidWithZero).toMonoid := by
    ext; apply h_mul
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr <;> solve| injection h₁ | injection h₂ | injection h₃

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

theorem ext_iff (inst₁ inst₂ : Semiring R) :
    inst₁ = inst₂ ↔
      (∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
      ∧ (∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (ext · ·)⟩

end Semiring

/-! ### Ring -/
namespace Ring

@[ext] theorem ext ⦃inst₁ inst₂ : Ring R⦄
    (h_add : ∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
    (h_mul : ∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :
    inst₁ = inst₂ := by
  -- Show that enough substructures are equal.
  have h₁ : inst₁.toSemiring = inst₂.toSemiring := by
    ext <;> apply_assumption
  have h₂ : inst₁.toNonAssocRing = inst₂.toNonAssocRing := by
    ext <;> apply_assumption
  /- We prove that the `SubNegMonoid`s are equal because they are one
  field away from `Sub` and `Neg`, enabling use of `injection`. -/
  have h₃ : (inst₁.toAddCommGroup).toAddGroup.toSubNegMonoid
            = (inst₂.toAddCommGroup).toAddGroup.toSubNegMonoid :=
    congrArg (@AddGroup.toSubNegMonoid R) <| by ext; apply h_add
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
  intro _ _ _
  ext <;> congr

theorem toSemiring_injective :
    Function.Injective (@toSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

theorem ext_iff (inst₁ inst₂ : Ring R) :
    inst₁ = inst₂ ↔
      (∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
      ∧ (∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (ext ·)⟩

end Ring

/-! ### NonUnitalNonAssocCommSemiring -/
namespace NonUnitalNonAssocCommSemiring

theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocCommSemiring R⦄
    (h_add : ∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
    (h_mul : ∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :
    inst₁ = inst₂ :=
  toNonUnitalNonAssocSemiring_injective <|
    NonUnitalNonAssocSemiring.ext h_add h_mul

theorem ext_iff (inst₁ inst₂ : NonUnitalNonAssocCommSemiring R) :
    inst₁ = inst₂ ↔
      (∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
      ∧ (∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (ext · ·)⟩

end NonUnitalNonAssocCommSemiring

/-! ### NonUnitalCommSemiring -/
namespace NonUnitalCommSemiring

theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalCommSemiring R⦄
    (h_add : ∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
    (h_mul : ∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :
    inst₁ = inst₂ :=
  toNonUnitalSemiring_injective <|
    NonUnitalSemiring.ext h_add h_mul

theorem ext_iff (inst₁ inst₂ : NonUnitalCommSemiring R) :
    inst₁ = inst₂ ↔
      (∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
      ∧ (∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (ext · ·)⟩

end NonUnitalCommSemiring

-- At present, there is no `NonAssocCommSemiring` in Mathlib.

/-! ### NonUnitalNonAssocCommRing -/
namespace NonUnitalNonAssocCommRing

theorem toNonUnitalNonAssocRing_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocCommRing R⦄
    (h_add : ∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
    (h_mul : ∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :
    inst₁ = inst₂ :=
  toNonUnitalNonAssocRing_injective <|
    NonUnitalNonAssocRing.ext h_add h_mul

theorem ext_iff (inst₁ inst₂ : NonUnitalNonAssocCommRing R) :
    inst₁ = inst₂ ↔
      (∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
      ∧ (∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (ext · ·)⟩

end NonUnitalNonAssocCommRing

/-! ### NonUnitalCommRing -/
namespace NonUnitalCommRing

theorem toNonUnitalRing_injective :
    Function.Injective (@toNonUnitalRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalCommRing R⦄
    (h_add : ∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
    (h_mul : ∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :
    inst₁ = inst₂ :=
  toNonUnitalRing_injective <|
    NonUnitalRing.ext h_add h_mul

theorem ext_iff (inst₁ inst₂ : NonUnitalCommRing R) :
    inst₁ = inst₂ ↔
      (∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
      ∧ (∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (ext · ·)⟩

end NonUnitalCommRing

-- At present, there is no `NonAssocCommRing` in Mathlib.

/-! ### CommSemiring -/
namespace CommSemiring

theorem toSemiring_injective :
    Function.Injective (@toSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

@[ext] theorem ext ⦃inst₁ inst₂ : CommSemiring R⦄
    (h_add : ∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
    (h_mul : ∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :
    inst₁ = inst₂ :=
  toSemiring_injective <|
    Semiring.ext h_add h_mul

theorem ext_iff (inst₁ inst₂ : CommSemiring R) :
    inst₁ = inst₂ ↔
      (∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
      ∧ (∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (ext · ·)⟩

end CommSemiring

/-! ### CommRing -/
namespace CommRing

theorem toRing_injective : Function.Injective (@toRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

@[ext] theorem ext ⦃inst₁ inst₂ : CommRing R⦄
    (h_add : ∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
    (h_mul : ∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :
    inst₁ = inst₂ :=
  toRing_injective <| Ring.ext h_add h_mul

theorem ext_iff (inst₁ inst₂ : CommRing R) :
    inst₁ = inst₂ ↔
      (∀ x y, x +[R, inst₁] y = x +[R, inst₂] y)
      ∧ (∀ x y, x *[R, inst₁] y = x *[R, inst₂] y) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (ext ·)⟩

end CommRing
