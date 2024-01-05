/-
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

@[ext] theorem Distrib.ext ⦃inst₁ inst₂ : Distrib R⦄
    (h_add : ∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
    (h_mul : ∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :
    inst₁ = inst₂ := by
  -- Extract `add` and `mul` functions
  rcases inst₁ with @⟨⟨⟩, ⟨⟩⟩
  rcases inst₂ with @⟨⟨⟩, ⟨⟩⟩
  congr <;> (ext; apply_assumption)

theorem Distrib.ext_iff (inst₁ inst₂ : Distrib R) :
    inst₁ = inst₂ ↔
      (∀ a b, a +[R, inst₁] b = a +[R, inst₂] b) ∧
      (∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :=
  ⟨fun h ↦ by constructor <;> (intro _ _; congr), And.elim (Distrib.ext · ·)⟩

@[ext] theorem NonUnitalNonAssocSemiring.ext ⦃inst₁ inst₂ : NonUnitalNonAssocSemiring R⦄
    (h_add : ∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
    (h_mul : ∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :
    inst₁ = inst₂ := by
  -- Extract `AddMonoid` instance and `mul` function
  rcases inst₁ with @⟨_, ⟨⟩⟩
  rcases inst₂ with @⟨_, ⟨⟩⟩
  congr <;> (ext; apply_assumption)

theorem NonUnitalNonAssocSemiring.ext_iff (inst₁ inst₂ : NonUnitalNonAssocSemiring R) :
    inst₁ = inst₂ ↔
      (∀ a b, a +[R, inst₁] b = a +[R, inst₂] b) ∧
      (∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (NonUnitalNonAssocSemiring.ext · ·)⟩

theorem NonUnitalSemiring.toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@NonUnitalSemiring.toNonUnitalNonAssocSemiring R) := by
  rintro ⟨⟩ ⟨⟩ h; congr

@[ext] theorem NonUnitalSemiring.ext ⦃inst₁ inst₂ : NonUnitalSemiring R⦄
    (h_add : ∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
    (h_mul : ∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :
    inst₁ = inst₂ :=
  NonUnitalSemiring.toNonUnitalNonAssocSemiring_injective <|
    NonUnitalNonAssocSemiring.ext h_add h_mul

theorem NonUnitalSemiring.ext_iff (inst₁ inst₂ : NonUnitalSemiring R) :
    inst₁ = inst₂ ↔
      (∀ a b, a +[R, inst₁] b = a +[R, inst₂] b) ∧
      (∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (NonUnitalSemiring.ext · ·)⟩

/- The best place to prove that the `NatCast` is determined by the other operations is probably in
an extensionality lemma for `AddMonoidWithOne`, in which case we may as well do the typeclasses
defined in `Algebra/GroupWithZero/Defs` as well. -/
@[ext] theorem NonAssocSemiring.ext ⦃inst₁ inst₂ : NonAssocSemiring R⦄
    (h_add : ∀ a b, a +[R, inst₁] b = a +[R, inst₂] b)
    (h_mul : ∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :
    inst₁ = inst₂ := by
  have h_one: (inst₁.toMulZeroOneClass).toMulOneClass = (letI := inst₂; inferInstance) :=
    by ext; apply h_mul
  -- Extract `NonUnitalNonAssocSemiring`, `One` instances and `natCast` function
  rcases inst₁ with @⟨inst'₁, one₁, _, _, ⟨natCast₁⟩⟩
  rcases inst₂ with @⟨inst'₂, one₂, _, _, ⟨natCast₂⟩⟩
  congr
  show inst'₁ = inst'₂
  · ext <;> apply_assumption
  show one₁ = one₂
  · injection h_one
  show natCast₁ = natCast₂
  · funext n; induction n with
    | zero => sorry
    | succ n => sorry

theorem NonAssocSemiring.ext_iff (inst₁ inst₂ : NonAssocSemiring R) :
    inst₁ = inst₂ ↔
      (∀ a b, a +[R, inst₁] b = a +[R, inst₂] b) ∧
      (∀ a b, a *[R, inst₁] b = a *[R, inst₂] b) :=
  ⟨fun h ↦ by constructor <;> (intros; congr), And.elim (NonAssocSemiring.ext · ·)⟩

