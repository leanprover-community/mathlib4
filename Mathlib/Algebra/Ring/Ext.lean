/-
Copyright (c) 2023 Raghuram Sundararajan. All rights reserved.
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
multiplcation specified by a typeclass instance `i` on a type `R` (and similarly for addition). We
abbreviate these using some local notations.

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

@[ext] theorem Distrib.ext ⦃inst₁ inst₂ : Distrib R⦄
    (h_add : ∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
    (h_mul : ∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :
    inst₁ = inst₂ := by
  -- Split into `add` and `mul` functions and properties.
  rcases inst₁ with @⟨⟨⟩, ⟨⟩⟩
  rcases inst₂ with @⟨⟨⟩, ⟨⟩⟩
  -- Prove equality of parts using function extensionality.
  congr <;> (apply funext₂; assumption)

theorem Distrib.ext_iff (inst₁ inst₂ : Distrib R) :
    inst₁ = inst₂ ↔
      (∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
      ∧ (∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (Distrib.ext · ·)⟩

/-! ### NonUnitalNonAssocSemiring -/

@[ext] theorem NonUnitalNonAssocSemiring.ext ⦃inst₁ inst₂ : NonUnitalNonAssocSemiring R⦄
    (h_add : ∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
    (h_mul : ∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :
    inst₁ = inst₂ := by
  -- Split into `AddMonoid` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩
  rcases inst₂ with @⟨_, ⟨⟩⟩
  -- Prove equality of parts using already-proved extensionality lemmas.
  congr <;> (ext; apply_assumption)

theorem NonUnitalNonAssocSemiring.toDistrib_injective :
    Function.Injective (@NonUnitalNonAssocSemiring.toDistrib R) := by
  intro _ _ h
  ext a b
  · exact congrArg (·.toAdd.add a b) h
  · exact congrArg (·.toMul.mul a b) h

theorem NonUnitalNonAssocSemiring.ext_iff (inst₁ inst₂ : NonUnitalNonAssocSemiring R) :
    inst₁ = inst₂ ↔
      (∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
      ∧ (∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (NonUnitalNonAssocSemiring.ext · ·)⟩

/-! ### NonUnitalSemiring -/

theorem NonUnitalSemiring.toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@NonUnitalSemiring.toNonUnitalNonAssocSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

@[ext] theorem NonUnitalSemiring.ext ⦃inst₁ inst₂ : NonUnitalSemiring R⦄
    (h_add : ∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
    (h_mul : ∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :
    inst₁ = inst₂ :=
  NonUnitalSemiring.toNonUnitalNonAssocSemiring_injective <|
    NonUnitalNonAssocSemiring.ext h_add h_mul

theorem NonUnitalSemiring.ext_iff (inst₁ inst₂ : NonUnitalSemiring R) :
    inst₁ = inst₂ ↔
      (∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
      ∧ (∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (NonUnitalSemiring.ext · ·)⟩

/-! ### NonAssocSemiring -/

/- The best place to prove that the `NatCast` is determined by the other operations is probably in
an extensionality lemma for `AddMonoidWithOne`, in which case we may as well do the typeclasses
defined in `Algebra/GroupWithZero/Defs` as well. -/
@[ext] theorem NonAssocSemiring.ext ⦃inst₁ inst₂ : NonAssocSemiring R⦄
    (h_add : ∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
    (h_mul : ∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :
    inst₁ = inst₂ := by
  have h : inst₁.toNonUnitalNonAssocSemiring = inst₂.toNonUnitalNonAssocSemiring := by
    ext <;> apply_assumption
  have h_zero : (inst₁.toMulZeroClass).toZero.zero = (inst₂.toMulZeroClass).toZero.zero :=
    congrArg (fun inst' => (inst'.toMulZeroClass).toZero.zero) h
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

theorem NonAssocSemiring.toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@NonAssocSemiring.toNonUnitalNonAssocSemiring R) := by
  intro _ _ _
  ext <;> congr

theorem NonAssocSemiring.ext_iff (inst₁ inst₂ : NonAssocSemiring R) :
    inst₁ = inst₂ ↔
      (∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
      ∧ (∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (NonAssocSemiring.ext · ·)⟩

/-! ### NonUnitalNonAssocRing -/

@[ext] theorem NonUnitalNonAssocRing.ext ⦃inst₁ inst₂ : NonUnitalNonAssocRing R⦄
    (h_add : ∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
    (h_mul : ∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :
    inst₁ = inst₂ := by
  -- Split into `AddCommGroup` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩; rcases inst₂ with @⟨_, ⟨⟩⟩
  congr <;> (ext; apply_assumption)

theorem NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring R) := by
  intro _ _ h
  -- Use above extensionality lemma to prove injectivity by showing that `h_add` and `h_mul` hold.
  ext a b
  · exact congrArg (·.toAdd.add a b) h
  · exact congrArg (·.toMul.mul a b) h

theorem NonUnitalNonAssocRing.ext_iff (inst₁ inst₂ : NonUnitalNonAssocRing R) :
    inst₁ = inst₂ ↔
      (∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
      ∧ (∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (NonUnitalNonAssocRing.ext · ·)⟩

/-! ### NonUnitalRing -/

@[ext] theorem NonUnitalRing.ext ⦃inst₁ inst₂ : NonUnitalRing R⦄
    (h_add : ∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
    (h_mul : ∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :
    inst₁ = inst₂ := by
  have : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext <;> apply_assumption
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr

theorem NonUnitalRing.toNonUnitalSemiring_injective :
    Function.Injective (@NonUnitalRing.toNonUnitalSemiring R) := by
  intro _ _ h
  ext a b
  · exact congrArg (·.toAdd.add a b) h
  · exact congrArg (·.toMul.mul a b) h

theorem NonUnitalRing.toNonUnitalNonAssocring_injective :
    Function.Injective (@NonUnitalRing.toNonUnitalNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

theorem NonUnitalRing.ext_iff (inst₁ inst₂ : NonUnitalRing R) :
    inst₁ = inst₂ ↔
      (∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
      ∧ (∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (NonUnitalRing.ext · ·)⟩

/-! ### NonAssocRing -/

@[ext] theorem NonAssocRing.ext ⦃inst₁ inst₂ : NonAssocRing R⦄
    (h_add : ∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
    (h_mul : ∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :
    inst₁ = inst₂ := by
  have h₁ : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext <;> apply_assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemiring := by
    ext <;> apply_assumption
  -- Mathematically non-trivial fact: `intCast` is determined by the rest.
  have h_intCast : inst₁.toIntCast.intCast = inst₂.toIntCast.intCast := by
    have : inst₁.toNatCast = inst₂.toNatCast := by injection h₂
    funext n; cases n with
    | ofNat n   => rewrite [←Int.coe_nat_eq, inst₁.intCast_ofNat, inst₂.intCast_ofNat]; congr
    | negSucc n => rewrite [inst₁.intCast_negSucc, inst₂.intCast_negSucc]; congr
  -- Split into fields (extracting `intCast` function) and prove they are equal using the above.
  rcases inst₁ with @⟨_, _, _, _, _, _, _, ⟨⟩⟩
  rcases inst₂ with @⟨_, _, _, _, _, _, _, ⟨⟩⟩
  congr <;> try solve| injection h₁ | injection h₂

theorem NonAssocRing.toNonAssocSemiring_injective :
    Function.Injective (@NonAssocRing.toNonAssocSemiring R) := by
  intro _ _ h
  ext a b
  · exact congrArg (·.toAdd.add a b) h
  · exact congrArg (·.toMul.mul a b) h

theorem NonAssocRing.toNonUnitalNonAssocring_injective :
    Function.Injective (@NonAssocRing.toNonUnitalNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

theorem NonAssocRing.ext_iff (inst₁ inst₂ : NonAssocRing R) :
    inst₁ = inst₂ ↔
      (∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
      ∧ (∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (NonAssocRing.ext · ·)⟩

/-! ### Semiring -/

@[ext] theorem Semiring.ext ⦃inst₁ inst₂ : Semiring R⦄
    (h_add : ∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
    (h_mul : ∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :
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

theorem Semiring.toNonUnitalSemiring_injective :
    Function.Injective (@Semiring.toNonUnitalSemiring R) := by
  intro _ _ h
  ext a b
  · exact congrArg (·.toAdd.add a b) h
  · exact congrArg (·.toMul.mul a b) h

theorem Semiring.toNonAssocSemiring_injective :
    Function.Injective (@Semiring.toNonAssocSemiring R) := by
  intro _ _ h
  ext a b
  · exact congrArg (·.toAdd.add a b) h
  · exact congrArg (·.toMul.mul a b) h

theorem Semiring.ext_iff (inst₁ inst₂ : Semiring R) :
    inst₁ = inst₂ ↔
      (∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
      ∧ (∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (Semiring.ext · ·)⟩

/-! ### Ring -/

@[ext] theorem Ring.ext ⦃inst₁ inst₂ : Ring R⦄
    (h_add : ∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
    (h_mul : ∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :
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

theorem Ring.ext_iff (inst₁ inst₂ : Ring R) :
    inst₁ = inst₂ ↔
      (∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
      ∧ (∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (Ring.ext ·)⟩
