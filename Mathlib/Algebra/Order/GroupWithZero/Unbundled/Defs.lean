/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Tactic.MkIffOfInductiveProp
import Mathlib.Util.Notation3

/-!
# (Strict) monotonicity of multiplication by nonnegative (positive) elements

This file defines eight typeclasses expressing monotonicity (strict monotonicity)
of multiplication on the left or right by nonnegative (positive) elements in a preorder.

For left multiplication (`a ↦ b * a`) we define the following typeclasses:
* `PosMulMono`: If `b ≥ 0`, then `a₁ ≤ a₂ → b * a₁ ≤ b * a₂`.
* `PosMulStrictMono`: If `b > 0`, then `a₁ < a₂ → b * a₁ < b * a₂`.
* `PosMulReflectLT`: If `b ≥ 0`, then `b * a₁ < b * a₂ → a₁ < a₂`.
* `PosMulReflectLE`: If `b > 0`, then `b * a₁ ≤ b * a₂ → a₁ ≤ a₂`.

For right multiplication (`a ↦ a * b`) we define the following typeclasses:
* `MulPosMono`: If `b ≥ 0`, then `a₁ ≤ a₂ → a₁ * b ≤ a₂ * b`.
* `MulPosStrictMono`: If `b > 0`, then `a₁ < a₂ → a₁ * b < a₂ * b`.
* `MulPosReflectLT`: If `b ≥ 0`, then `a₁ * b < a₂ * b → a₁ < a₂`.
* `MulPosReflectLE`: If `b > 0`, then `a₁ * b ≤ a₂ * b → a₁ ≤ a₂`.

We then provide statements and instances about these typeclasses not requiring `MulZeroClass`
or higher on the underlying type – those that do can be found in
`Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean`.

Less granular typeclasses like `OrderedAddCommMonoid` and `LinearOrderedField` should be enough for
most purposes, and the system is set up so that they imply the correct granular typeclasses here.

## Implications

As the underlying type `α` gets more structured, some of the above typeclasses become equivalent.
The commonly used implications are:
* When `α` is a partial order (in `Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean`):
  * `PosMulStrictMono.toPosMulMono`
  * `MulPosStrictMono.toMulPosMono`
  * `PosMulReflectLE.toPosMulReflectLT`
  * `MulPosReflectLE.toMulPosReflectLT`
* When `α` is a linear order:
  * `PosMulStrictMono.toPosMulReflectLE`
  * `MulPosStrictMono.toMulPosReflectLE`
* When multiplication on `α` is commutative:
  * `posMulMono_iff_mulPosMono`
  * `posMulStrictMono_iff_mulPosStrictMono`
  * `posMulReflectLE_iff_mulPosReflectLE`
  * `posMulReflectLT_iff_mulPosReflectLT`

Furthermore, the bundled non-granular typeclasses imply the granular ones like so:
* `OrderedSemiring → PosMulMono`
* `OrderedSemiring → MulPosMono`
* `StrictOrderedSemiring → PosMulStrictMono`
* `StrictOrderedSemiring → MulPosStrictMono`

All these are registered as instances, which means that in practice you should not worry about these
implications. However, if you encounter a case where you think a statement is true but not covered
by the current implications, please bring it up on Zulip!

## Notation

The following is local notation in this file:
* `α≥0`: `{x : α // 0 ≤ x}`
* `α>0`: `{x : α // 0 < x}`

See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/notation.20for.20positive.20elements
for a discussion about this notation, and whether to enable it globally (note that the notation is
currently global but broken, hence actually only works locally).
-/

assert_not_exists MulZeroClass

open Function

variable (α : Type*)

/-- Local notation for the nonnegative elements of a type `α`. -/
local notation3 "α≥0" => { x : α // 0 ≤ x }

/-- Local notation for the positive elements of a type `α`. -/
local notation3 "α>0" => { x : α // 0 < x }

section Abbreviations

variable [Mul α] [Zero α] [Preorder α]

/-- Typeclass for monotonicity of multiplication by nonnegative elements on the left,
namely `a₁ ≤ a₂ → b * a₁ ≤ b * a₂` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSemiring`. -/
@[mk_iff] class PosMulMono : Prop extends CovariantClass α≥0 α (fun x y => x * y) (· ≤ ·)

/-- Typeclass for strict monotonicity of multiplication by positive elements on the left,
namely `a₁ < a₂ → b * a₁ < b * a₂` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`StrictOrderedSemiring`. -/
@[mk_iff] class PosMulStrictMono : Prop extends CovariantClass α>0 α (fun x y => x * y) (· < ·)

/-- Typeclass for strict reverse monotonicity of multiplication by nonnegative elements on
the left, namely `b * a₁ < b * a₂ → a₁ < a₂` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
@[mk_iff] class PosMulReflectLT : Prop extends ContravariantClass α≥0 α (fun x y => x * y) (· < ·)

/-- Typeclass for reverse monotonicity of multiplication by positive elements on the left,
namely `b * a₁ ≤ b * a₂ → a₁ ≤ a₂` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
@[mk_iff] class PosMulReflectLE : Prop extends ContravariantClass α>0 α (fun x y => x * y) (· ≤ ·)

/-- Typeclass for monotonicity of multiplication by nonnegative elements on the right,
namely `a₁ ≤ a₂ → a₁ * b ≤ a₂ * b` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSemiring`. -/
@[mk_iff] class MulPosMono : Prop extends CovariantClass α≥0 α (fun x y => y * x) (· ≤ ·)

/-- Typeclass for strict monotonicity of multiplication by positive elements on the right,
namely `a₁ < a₂ → a₁ * b < a₂ * b` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`StrictOrderedSemiring`. -/
@[mk_iff] class MulPosStrictMono : Prop extends CovariantClass α>0 α (fun x y => y * x) (· < ·)

/-- Typeclass for strict reverse monotonicity of multiplication by nonnegative elements on
the right, namely `a₁ * b < a₂ * b → a₁ < a₂` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
@[mk_iff] class MulPosReflectLT : Prop extends ContravariantClass α≥0 α (fun x y => y * x) (· < ·)

/-- Typeclass for reverse monotonicity of multiplication by positive elements on the right,
namely `a₁ * b ≤ a₂ * b → a₁ ≤ a₂` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
@[mk_iff] class MulPosReflectLE : Prop extends ContravariantClass α>0 α (fun x y => y * x) (· ≤ ·)

end Abbreviations

variable {α}
variable [Mul α] [Zero α]

section Preorder

variable [Preorder α] {a b c d : α}

instance PosMulMono.to_covariantClass_pos_mul_le [PosMulMono α] :
    CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) :=
  ⟨fun a _ _ bc => @CovariantClass.elim α≥0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, a.2.le⟩ _ _ bc⟩

instance MulPosMono.to_covariantClass_pos_mul_le [MulPosMono α] :
    CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) :=
  ⟨fun a _ _ bc => @CovariantClass.elim α≥0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, a.2.le⟩ _ _ bc⟩

instance PosMulReflectLT.to_contravariantClass_pos_mul_lt [PosMulReflectLT α] :
    ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨fun a _ _ bc => @ContravariantClass.elim α≥0 α (fun x y => x * y) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩

instance MulPosReflectLT.to_contravariantClass_pos_mul_lt [MulPosReflectLT α] :
    ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨fun a _ _ bc => @ContravariantClass.elim α≥0 α (fun x y => y * x) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩

instance (priority := 100) MulLeftMono.toPosMulMono [MulLeftMono α] :
    PosMulMono α where elim _ _ := ‹MulLeftMono α›.elim _

instance (priority := 100) MulRightMono.toMulPosMono [MulRightMono α] :
    MulPosMono α where elim _ _ := ‹MulRightMono α›.elim _

instance (priority := 100) MulLeftStrictMono.toPosMulStrictMono [MulLeftStrictMono α] :
    PosMulStrictMono α where elim _ _ := ‹MulLeftStrictMono α›.elim _

instance (priority := 100) MulRightStrictMono.toMulPosStrictMono [MulRightStrictMono α] :
    MulPosStrictMono α where elim _ _ := ‹MulRightStrictMono α›.elim _

instance (priority := 100) MulLeftMono.toPosMulReflectLT [MulLeftReflectLT α] :
   PosMulReflectLT α where elim _ _ := ‹MulLeftReflectLT α›.elim _

instance (priority := 100) MulRightMono.toMulPosReflectLT [MulRightReflectLT α] :
   MulPosReflectLT α where elim _ _ := ‹MulRightReflectLT α›.elim _

instance (priority := 100) MulLeftStrictMono.toPosMulReflectLE [MulLeftReflectLE α] :
   PosMulReflectLE α where elim _ _ := ‹MulLeftReflectLE α›.elim _

instance (priority := 100) MulRightStrictMono.toMulPosReflectLE [MulRightReflectLE α] :
   MulPosReflectLE α where elim _ _ := ‹MulRightReflectLE α›.elim _

@[gcongr]
theorem mul_le_mul_of_nonneg_left [PosMulMono α] (h : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c :=
  @CovariantClass.elim α≥0 α (fun x y => x * y) (· ≤ ·) _ ⟨a, a0⟩ _ _ h

@[gcongr]
theorem mul_le_mul_of_nonneg_right [MulPosMono α] (h : b ≤ c) (a0 : 0 ≤ a) : b * a ≤ c * a :=
  @CovariantClass.elim α≥0 α (fun x y => y * x) (· ≤ ·) _ ⟨a, a0⟩ _ _ h

@[gcongr]
theorem mul_lt_mul_of_pos_left [PosMulStrictMono α] (bc : b < c) (a0 : 0 < a) : a * b < a * c :=
  @CovariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ bc

@[gcongr]
theorem mul_lt_mul_of_pos_right [MulPosStrictMono α] (bc : b < c) (a0 : 0 < a) : b * a < c * a :=
  @CovariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ bc

theorem lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a * b < a * c) (a0 : 0 ≤ a) : b < c :=
  @ContravariantClass.elim α≥0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ h

theorem lt_of_mul_lt_mul_right [MulPosReflectLT α] (h : b * a < c * a) (a0 : 0 ≤ a) : b < c :=
  @ContravariantClass.elim α≥0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ h

theorem le_of_mul_le_mul_left [PosMulReflectLE α] (bc : a * b ≤ a * c) (a0 : 0 < a) : b ≤ c :=
  @ContravariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc

theorem le_of_mul_le_mul_right [MulPosReflectLE α] (bc : b * a ≤ c * a) (a0 : 0 < a) : b ≤ c :=
  @ContravariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc

alias lt_of_mul_lt_mul_of_nonneg_left := lt_of_mul_lt_mul_left
alias lt_of_mul_lt_mul_of_nonneg_right := lt_of_mul_lt_mul_right
alias le_of_mul_le_mul_of_pos_left := le_of_mul_le_mul_left
alias le_of_mul_le_mul_of_pos_right := le_of_mul_le_mul_right

@[simp]
theorem mul_lt_mul_left [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a * c ↔ b < c :=
  @rel_iff_cov α>0 α (fun x y => x * y) (· < ·) _ _ ⟨a, a0⟩ _ _

@[simp]
theorem mul_lt_mul_right [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    b * a < c * a ↔ b < c :=
  @rel_iff_cov α>0 α (fun x y => y * x) (· < ·) _ _ ⟨a, a0⟩ _ _

@[simp]
theorem mul_le_mul_left [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c :=
  @rel_iff_cov α>0 α (fun x y => x * y) (· ≤ ·) _ _ ⟨a, a0⟩ _ _

@[simp]
theorem mul_le_mul_right [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) : b * a ≤ c * a ↔ b ≤ c :=
  @rel_iff_cov α>0 α (fun x y => y * x) (· ≤ ·) _ _ ⟨a, a0⟩ _ _

alias mul_le_mul_iff_of_pos_left := mul_le_mul_left
alias mul_le_mul_iff_of_pos_right := mul_le_mul_right
alias mul_lt_mul_iff_of_pos_left := mul_lt_mul_left
alias mul_lt_mul_iff_of_pos_right := mul_lt_mul_right

theorem mul_le_mul_of_nonneg [PosMulMono α] [MulPosMono α]
    (h₁ : a ≤ b) (h₂ : c ≤ d) (a0 : 0 ≤ a) (d0 : 0 ≤ d) : a * c ≤ b * d :=
  (mul_le_mul_of_nonneg_left h₂ a0).trans (mul_le_mul_of_nonneg_right h₁ d0)

theorem mul_le_mul_of_nonneg' [PosMulMono α] [MulPosMono α]
    (h₁ : a ≤ b) (h₂ : c ≤ d) (c0 : 0 ≤ c) (b0 : 0 ≤ b) : a * c ≤ b * d :=
  (mul_le_mul_of_nonneg_right h₁ c0).trans (mul_le_mul_of_nonneg_left h₂ b0)

theorem mul_lt_mul_of_le_of_lt_of_pos_of_nonneg [PosMulStrictMono α] [MulPosMono α]
    (h₁ : a ≤ b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 ≤ d) : a * c < b * d :=
  (mul_lt_mul_of_pos_left h₂ a0).trans_le (mul_le_mul_of_nonneg_right h₁ d0)

alias mul_lt_mul_of_pos_of_nonneg := mul_lt_mul_of_le_of_lt_of_pos_of_nonneg

theorem mul_lt_mul_of_le_of_lt_of_nonneg_of_pos [PosMulStrictMono α] [MulPosMono α]
    (h₁ : a ≤ b) (h₂ : c < d) (c0 : 0 ≤ c) (b0 : 0 < b) : a * c < b * d :=
  (mul_le_mul_of_nonneg_right h₁ c0).trans_lt (mul_lt_mul_of_pos_left h₂ b0)

alias mul_lt_mul_of_nonneg_of_pos' := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos

theorem mul_lt_mul_of_lt_of_le_of_nonneg_of_pos [PosMulMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c ≤ d) (a0 : 0 ≤ a) (d0 : 0 < d) : a * c < b * d :=
  (mul_le_mul_of_nonneg_left h₂ a0).trans_lt (mul_lt_mul_of_pos_right h₁ d0)

alias mul_lt_mul_of_nonneg_of_pos := mul_lt_mul_of_lt_of_le_of_nonneg_of_pos

theorem mul_lt_mul_of_lt_of_le_of_pos_of_nonneg [PosMulMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c ≤ d) (c0 : 0 < c) (b0 : 0 ≤ b) : a * c < b * d :=
  (mul_lt_mul_of_pos_right h₁ c0).trans_le (mul_le_mul_of_nonneg_left h₂ b0)

alias mul_lt_mul_of_pos_of_nonneg' := mul_lt_mul_of_lt_of_le_of_pos_of_nonneg

theorem mul_lt_mul_of_pos [PosMulStrictMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 < d) : a * c < b * d :=
  (mul_lt_mul_of_pos_left h₂ a0).trans (mul_lt_mul_of_pos_right h₁ d0)

theorem mul_lt_mul_of_pos' [PosMulStrictMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c < d) (c0 : 0 < c) (b0 : 0 < b) : a * c < b * d :=
  (mul_lt_mul_of_pos_right h₁ c0).trans (mul_lt_mul_of_pos_left h₂ b0)

alias mul_le_mul := mul_le_mul_of_nonneg'
attribute [gcongr] mul_le_mul

alias mul_lt_mul := mul_lt_mul_of_pos_of_nonneg'

alias mul_lt_mul' := mul_lt_mul_of_nonneg_of_pos'

theorem mul_le_of_mul_le_of_nonneg_left [PosMulMono α] (h : a * b ≤ c) (hle : d ≤ b) (a0 : 0 ≤ a) :
    a * d ≤ c :=
  (mul_le_mul_of_nonneg_left hle a0).trans h

theorem mul_lt_of_mul_lt_of_nonneg_left [PosMulMono α] (h : a * b < c) (hle : d ≤ b) (a0 : 0 ≤ a) :
    a * d < c :=
  (mul_le_mul_of_nonneg_left hle a0).trans_lt h

theorem le_mul_of_le_mul_of_nonneg_left [PosMulMono α] (h : a ≤ b * c) (hle : c ≤ d) (b0 : 0 ≤ b) :
    a ≤ b * d :=
  h.trans (mul_le_mul_of_nonneg_left hle b0)

theorem lt_mul_of_lt_mul_of_nonneg_left [PosMulMono α] (h : a < b * c) (hle : c ≤ d) (b0 : 0 ≤ b) :
    a < b * d :=
  h.trans_le (mul_le_mul_of_nonneg_left hle b0)

theorem mul_le_of_mul_le_of_nonneg_right [MulPosMono α] (h : a * b ≤ c) (hle : d ≤ a) (b0 : 0 ≤ b) :
    d * b ≤ c :=
  (mul_le_mul_of_nonneg_right hle b0).trans h

theorem mul_lt_of_mul_lt_of_nonneg_right [MulPosMono α] (h : a * b < c) (hle : d ≤ a) (b0 : 0 ≤ b) :
    d * b < c :=
  (mul_le_mul_of_nonneg_right hle b0).trans_lt h

theorem le_mul_of_le_mul_of_nonneg_right [MulPosMono α] (h : a ≤ b * c) (hle : b ≤ d) (c0 : 0 ≤ c) :
    a ≤ d * c :=
  h.trans (mul_le_mul_of_nonneg_right hle c0)

theorem lt_mul_of_lt_mul_of_nonneg_right [MulPosMono α] (h : a < b * c) (hle : b ≤ d) (c0 : 0 ≤ c) :
    a < d * c :=
  h.trans_le (mul_le_mul_of_nonneg_right hle c0)

variable [@Std.Commutative α (· * ·)]

theorem posMulMono_iff_mulPosMono : PosMulMono α ↔ MulPosMono α := by
  simp only [posMulMono_iff, mulPosMono_iff, Std.Commutative.comm]

theorem PosMulMono.toMulPosMono [PosMulMono α] : MulPosMono α := posMulMono_iff_mulPosMono.mp ‹_›

theorem posMulStrictMono_iff_mulPosStrictMono : PosMulStrictMono α ↔ MulPosStrictMono α := by
  simp only [posMulStrictMono_iff, mulPosStrictMono_iff, Std.Commutative.comm]

theorem PosMulStrictMono.toMulPosStrictMono [PosMulStrictMono α] : MulPosStrictMono α :=
  posMulStrictMono_iff_mulPosStrictMono.mp ‹_›

theorem posMulReflectLE_iff_mulPosReflectLE : PosMulReflectLE α ↔ MulPosReflectLE α := by
  simp only [posMulReflectLE_iff, mulPosReflectLE_iff, Std.Commutative.comm]

theorem PosMulReflectLE.toMulPosReflectLE [PosMulReflectLE α] : MulPosReflectLE α :=
  posMulReflectLE_iff_mulPosReflectLE.mp ‹_›

theorem posMulReflectLT_iff_mulPosReflectLT : PosMulReflectLT α ↔ MulPosReflectLT α := by
  simp only [posMulReflectLT_iff, mulPosReflectLT_iff, Std.Commutative.comm]

theorem PosMulReflectLT.toMulPosReflectLT [PosMulReflectLT α] : MulPosReflectLT α :=
  posMulReflectLT_iff_mulPosReflectLT.mp ‹_›

end Preorder

section LinearOrder

variable [LinearOrder α]

-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosMulReflectLE [PosMulStrictMono α] :
    PosMulReflectLE α where
  elim := (covariant_lt_iff_contravariant_le _ _ _).1 CovariantClass.elim

-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toMulPosReflectLE [MulPosStrictMono α] :
    MulPosReflectLE α where
  elim := (covariant_lt_iff_contravariant_le _ _ _).1 CovariantClass.elim

theorem PosMulReflectLE.toPosMulStrictMono [PosMulReflectLE α] : PosMulStrictMono α where
  elim := (covariant_lt_iff_contravariant_le _ _ _).2 ContravariantClass.elim

theorem MulPosReflectLE.toMulPosStrictMono [MulPosReflectLE α] : MulPosStrictMono α where
  elim := (covariant_lt_iff_contravariant_le _ _ _).2 ContravariantClass.elim

theorem posMulStrictMono_iff_posMulReflectLE : PosMulStrictMono α ↔ PosMulReflectLE α :=
  ⟨@PosMulStrictMono.toPosMulReflectLE _ _ _ _, @PosMulReflectLE.toPosMulStrictMono _ _ _ _⟩

theorem mulPosStrictMono_iff_mulPosReflectLE : MulPosStrictMono α ↔ MulPosReflectLE α :=
  ⟨@MulPosStrictMono.toMulPosReflectLE _ _ _ _, @MulPosReflectLE.toMulPosStrictMono _ _ _ _⟩

theorem PosMulReflectLT.toPosMulMono [PosMulReflectLT α] : PosMulMono α where
  elim := (covariant_le_iff_contravariant_lt _ _ _).2 ContravariantClass.elim

theorem MulPosReflectLT.toMulPosMono [MulPosReflectLT α] : MulPosMono α where
  elim := (covariant_le_iff_contravariant_lt _ _ _).2 ContravariantClass.elim

theorem PosMulMono.toPosMulReflectLT [PosMulMono α] : PosMulReflectLT α where
  elim := (covariant_le_iff_contravariant_lt _ _ _).1 CovariantClass.elim

theorem MulPosMono.toMulPosReflectLT [MulPosMono α] : MulPosReflectLT α where
  elim := (covariant_le_iff_contravariant_lt _ _ _).1 CovariantClass.elim

/- TODO: Currently, only one in four of the above are made instances; we could consider making
  both directions of `covariant_le_iff_contravariant_lt` and `covariant_lt_iff_contravariant_le`
  instances, then all of the above become redundant instances, but there are performance issues. -/

theorem posMulMono_iff_posMulReflectLT : PosMulMono α ↔ PosMulReflectLT α :=
  ⟨@PosMulMono.toPosMulReflectLT _ _ _ _, @PosMulReflectLT.toPosMulMono _ _ _ _⟩

theorem mulPosMono_iff_mulPosReflectLT : MulPosMono α ↔ MulPosReflectLT α :=
  ⟨@MulPosMono.toMulPosReflectLT _ _ _ _, @MulPosReflectLT.toMulPosMono _ _ _ _⟩

end LinearOrder
