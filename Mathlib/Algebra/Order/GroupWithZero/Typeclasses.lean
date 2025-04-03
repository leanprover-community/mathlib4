/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Notation.Pi
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Tactic.MkIffOfInductiveProp
import Mathlib.Util.Notation3

/-!
# Monotonicity of multiplication by positive elements

This file defines typeclasses to reason about monotonicity of the operations
* `b ↦ a * b`, "left multiplication"
* `a ↦ a * b`, "right multiplication"

We use eight typeclasses to encode the various properties we care about for those two operations.
These typeclasses are meant to be mostly internal to this file, to set up each lemma in the
appropriate generality.

Less granular typeclasses like `OrderedAddCommMonoid`, `LinearOrderedField` should be enough for
most purposes, and the system is set up so that they imply the correct granular typeclasses here.
If those are enough for you, you may stop reading here! Else, beware that what follows is a bit
technical.

## Definitions

In all that follows, `α` is an orders which has a `0` and a multiplication. Note however that we do
not use lawfulness of this action in most of the file. Hence `*` should be considered here as a
mostly arbitrary function `α → α → α`.

We use the following four typeclasses to reason about left multiplication (`b ↦ a * b`):
* `PosMulMono`: If `a ≥ 0`, then `b₁ ≤ b₂ → a * b₁ ≤ a * b₂`.
* `PosMulStrictMono`: If `a > 0`, then `b₁ < b₂ → a * b₁ < a * b₂`.
* `PosMulReflectLT`: If `a ≥ 0`, then `a * b₁ < a * b₂ → b₁ < b₂`.
* `PosMulReflectLE`: If `a > 0`, then `a * b₁ ≤ a * b₂ → b₁ ≤ b₂`.

We use the following four typeclasses to reason about right multiplication (`a ↦ a * b`):
* `MulPosMono`: If `b ≥ 0`, then `a₁ ≤ a₂ → a₁ * b ≤ a₂ * b`.
* `MulPosStrictMono`: If `b > 0`, then `a₁ < a₂ → a₁ * b < a₂ * b`.
* `MulPosReflectLT`: If `b ≥ 0`, then `a₁ * b < a₂ * b → a₁ < a₂`.
* `MulPosReflectLE`: If `b > 0`, then `a₁ * b ≤ a₂ * b → a₁ ≤ a₂`.

## Implications

As `α` gets more and more structure, those typeclasses end up being equivalent. The commonly used
implications are:
*  When `α` is a partial order:
  * `PosMulStrictMono → PosMulMono`
  * `MulPosStrictMono → MulPosMono`
  * `PosMulReflectLE → PosMulReflectLT`
  * `MulPosReflectLE → MulPosReflectLT`
* When `α` is a linear order:
  * `PosMulStrictMono → PosMulReflectLE`
  * `MulPosStrictMono → MulPosReflectLE` .
* When the multiplication of `α` is commutative:
  * `PosMulMono → MulPosMono`
  * `PosMulStrictMono → MulPosStrictMono`
  * `PosMulReflectLE → MulPosReflectLE`
  * `PosMulReflectLT → MulPosReflectLT`

Further, the bundled non-granular typeclasses imply the granular ones like so:
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

open Function

variable (α : Type*)

/-- Local notation for the nonnegative elements of a type `α`. -/
local notation3 "α≥0" => { x : α // 0 ≤ x }

/-- Local notation for the positive elements of a type `α`. -/
local notation3 "α>0" => { x : α // 0 < x }

section Abbreviations

variable [Mul α] [Zero α] [Preorder α]

/-- Typeclass for monotonicity of multiplication by nonnegative elements on the left,
namely `b₁ ≤ b₂ → a * b₁ ≤ a * b₂` if `0 ≤ a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSemiring`. -/
@[mk_iff] class PosMulMono : Prop extends CovariantClass α≥0 α (fun x y => x * y) (· ≤ ·)

/-- Typeclass for monotonicity of multiplication by nonnegative elements on the right,
namely `a₁ ≤ a₂ → a₁ * b ≤ a₂ * b` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSemiring`. -/
@[mk_iff] class MulPosMono : Prop extends CovariantClass α≥0 α (fun x y => y * x) (· ≤ ·)

/-- Typeclass for strict monotonicity of multiplication by positive elements on the left,
namely `b₁ < b₂ → a * b₁ < a * b₂` if `0 < a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`StrictOrderedSemiring`. -/
@[mk_iff] class PosMulStrictMono : Prop extends CovariantClass α>0 α (fun x y => x * y) (· < ·)

/-- Typeclass for strict monotonicity of multiplication by positive elements on the right,
namely `a₁ < a₂ → a₁ * b < a₂ * b` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`StrictOrderedSemiring`. -/
@[mk_iff] class MulPosStrictMono : Prop extends CovariantClass α>0 α (fun x y => y * x) (· < ·)

/-- Typeclass for strict reverse monotonicity of multiplication by nonnegative elements on
the left, namely `a * b₁ < a * b₂ → b₁ < b₂` if `0 ≤ a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
@[mk_iff] class PosMulReflectLT : Prop extends ContravariantClass α≥0 α (fun x y => x * y) (· < ·)

/-- Typeclass for strict reverse monotonicity of multiplication by nonnegative elements on
the right, namely `a₁ * b < a₂ * b → a₁ < a₂` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
@[mk_iff] class MulPosReflectLT : Prop extends ContravariantClass α≥0 α (fun x y => y * x) (· < ·)

/-- Typeclass for reverse monotonicity of multiplication by positive elements on the left,
namely `a * b₁ ≤ a * b₂ → b₁ ≤ b₂` if `0 < a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
@[mk_iff] class PosMulReflectLE : Prop extends ContravariantClass α>0 α (fun x y => x * y) (· ≤ ·)

/-- Typeclass for reverse monotonicity of multiplication by positive elements on the right,
namely `a₁ * b ≤ a₂ * b → a₁ ≤ a₂` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
@[mk_iff] class MulPosReflectLE : Prop extends ContravariantClass α>0 α (fun x y => y * x) (· ≤ ·)

end Abbreviations

variable {α} {a b c d : α}

section MulZero

variable [Mul α] [Zero α]

section Preorder

variable [Preorder α]

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

end MulZero

section MulZeroClass

variable [MulZeroClass α]

section Preorder

variable [Preorder α]

/-- Assumes left covariance. -/
theorem Left.mul_pos [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

alias mul_pos := Left.mul_pos

theorem mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

@[simp]
theorem mul_pos_iff_of_pos_left [PosMulStrictMono α] [PosMulReflectLT α] (h : 0 < a) :
    0 < a * b ↔ 0 < b := by simpa using mul_lt_mul_left (b := 0) h

/-- Assumes right covariance. -/
theorem Right.mul_pos [MulPosStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

theorem mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

@[simp]
theorem mul_pos_iff_of_pos_right [MulPosStrictMono α] [MulPosReflectLT α] (h : 0 < b) :
    0 < a * b ↔ 0 < a := by simpa using mul_lt_mul_right (b := 0) h

/-- Assumes left covariance. -/
theorem Left.mul_nonneg [PosMulMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

alias mul_nonneg := Left.mul_nonneg

theorem mul_nonpos_of_nonneg_of_nonpos [PosMulMono α] (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

/-- Assumes right covariance. -/
theorem Right.mul_nonneg [MulPosMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

theorem mul_nonpos_of_nonpos_of_nonneg [MulPosMono α] (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

theorem pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b :=
  lt_of_mul_lt_mul_left ((mul_zero a).symm ▸ h : a * 0 < a * b) ha

theorem pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a :=
  lt_of_mul_lt_mul_right ((zero_mul b).symm ▸ h : 0 * b < a * b) hb

theorem pos_iff_pos_of_mul_pos [PosMulReflectLT α] [MulPosReflectLT α] (hab : 0 < a * b) :
    0 < a ↔ 0 < b :=
  ⟨pos_of_mul_pos_right hab ∘ le_of_lt, pos_of_mul_pos_left hab ∘ le_of_lt⟩

/-- Assumes left strict covariance. -/
theorem Left.mul_lt_mul_of_nonneg [PosMulStrictMono α] [MulPosMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : a * c < b * d :=
  mul_lt_mul_of_le_of_lt_of_nonneg_of_pos h₁.le h₂ c0 (a0.trans_lt h₁)

/-- Assumes right strict covariance. -/
theorem Right.mul_lt_mul_of_nonneg [PosMulMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : a * c < b * d :=
  mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h₁ h₂.le a0 (c0.trans_lt h₂)

alias mul_lt_mul_of_nonneg := Left.mul_lt_mul_of_nonneg

alias mul_lt_mul'' := Left.mul_lt_mul_of_nonneg
attribute [gcongr] mul_lt_mul''

theorem mul_self_le_mul_self [PosMulMono α] [MulPosMono α] (ha : 0 ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b :=
  mul_le_mul hab hab ha <| ha.trans hab

end Preorder

section PartialOrder

variable [PartialOrder α]

theorem posMulMono_iff_covariant_pos :
    PosMulMono α ↔ CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) :=
  ⟨@PosMulMono.to_covariantClass_pos_mul_le _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, ha⟩ _ _ h }⟩

theorem mulPosMono_iff_covariant_pos :
    MulPosMono α ↔ CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) :=
  ⟨@MulPosMono.to_covariantClass_pos_mul_le _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, ha⟩ _ _ h }⟩

theorem posMulReflectLT_iff_contravariant_pos :
    PosMulReflectLT α ↔ ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨@PosMulReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩

theorem mulPosReflectLT_iff_contravariant_pos :
    MulPosReflectLT α ↔ ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨@MulPosReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩

-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosMulMono [PosMulStrictMono α] : PosMulMono α :=
  posMulMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)

-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toMulPosMono [MulPosStrictMono α] : MulPosMono α :=
  mulPosMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)

-- see Note [lower instance priority]
instance (priority := 100) PosMulReflectLE.toPosMulReflectLT [PosMulReflectLE α] :
    PosMulReflectLT α :=
  posMulReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_left h.le a.2).lt_of_ne <| by
        rintro rfl
        simp at h⟩

-- see Note [lower instance priority]
instance (priority := 100) MulPosReflectLE.toMulPosReflectLT [MulPosReflectLE α] :
    MulPosReflectLT α :=
  mulPosReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_right h.le a.2).lt_of_ne <| by
        rintro rfl
        simp at h⟩

theorem mul_left_cancel_iff_of_pos [PosMulReflectLE α] (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_left h.le a0).antisymm <|
    le_of_mul_le_mul_of_pos_left h.ge a0, congr_arg _⟩

theorem mul_right_cancel_iff_of_pos [MulPosReflectLE α] (b0 : 0 < b) : a * b = c * b ↔ a = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_right h.le b0).antisymm <|
    le_of_mul_le_mul_of_pos_right h.ge b0, congr_arg (· * b)⟩

theorem mul_eq_mul_iff_eq_and_eq_of_pos [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a ≤ b) (hcd : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab ↦ h.not_lt ?_, fun hcd ↦ h.not_lt ?_⟩
  · exact (mul_le_mul_of_nonneg_left hcd a0.le).trans_lt (mul_lt_mul_of_pos_right hab d0)
  · exact (mul_lt_mul_of_pos_left hcd a0).trans_le (mul_le_mul_of_nonneg_right hab d0.le)

theorem mul_eq_mul_iff_eq_and_eq_of_pos' [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a ≤ b) (hcd : c ≤ d) (b0 : 0 < b) (c0 : 0 < c) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab ↦ h.not_lt ?_, fun hcd ↦ h.not_lt ?_⟩
  · exact (mul_lt_mul_of_pos_right hab c0).trans_le (mul_le_mul_of_nonneg_left hcd b0.le)
  · exact (mul_le_mul_of_nonneg_right hab c0.le).trans_lt (mul_lt_mul_of_pos_left hcd b0)

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem pos_and_pos_or_neg_and_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) :
    0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rcases lt_trichotomy a 0 with (ha | rfl | ha)
  · refine Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_mul] at hab
    exact hab.false.elim
  · refine Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hb

theorem neg_of_mul_pos_right [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.1.not_le ha).2

theorem neg_of_mul_pos_left [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b ≤ 0) : a < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.2.not_le ha).1

theorem neg_iff_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : a < 0 ↔ b < 0 :=
  ⟨neg_of_mul_pos_right hab ∘ le_of_lt, neg_of_mul_pos_left hab ∘ le_of_lt⟩

theorem Left.neg_of_mul_neg_right [PosMulMono α] (h : a * b < 0) (a0 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun b0 : b ≥ 0 => (Left.mul_nonneg a0 b0).not_lt h

alias neg_of_mul_neg_right := Left.neg_of_mul_neg_right

theorem Right.neg_of_mul_neg_right [MulPosMono α] (h : a * b < 0) (a0 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun b0 : b ≥ 0 => (Right.mul_nonneg a0 b0).not_lt h

theorem Left.neg_of_mul_neg_left [PosMulMono α] (h : a * b < 0) (b0 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun a0 : a ≥ 0 => (Left.mul_nonneg a0 b0).not_lt h

alias neg_of_mul_neg_left := Left.neg_of_mul_neg_left

theorem Right.neg_of_mul_neg_left [MulPosMono α] (h : a * b < 0) (b0 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun a0 : a ≥ 0 => (Right.mul_nonneg a0 b0).not_lt h

end LinearOrder

end MulZeroClass

section MulOneClass

variable [MulOneClass α] [Zero α]

section Preorder

variable [Preorder α]

/-! Lemmas of the form `a ≤ a * b ↔ 1 ≤ b` and `a * b ≤ a ↔ b ≤ 1`,
which assume left covariance. -/

lemma one_lt_of_lt_mul_left₀ [PosMulReflectLT α] (ha : 0 ≤ a) (h : a < a * b) : 1 < b :=
  lt_of_mul_lt_mul_left (by simpa) ha

lemma one_lt_of_lt_mul_right₀ [MulPosReflectLT α] (hb : 0 ≤ b) (h : b < a * b) : 1 < a :=
  lt_of_mul_lt_mul_right (by simpa) hb

lemma one_le_of_le_mul_left₀ [PosMulReflectLE α] (ha : 0 < a) (h : a ≤ a * b) : 1 ≤ b :=
  le_of_mul_le_mul_left (by simpa) ha

lemma one_le_of_le_mul_right₀ [MulPosReflectLE α] (hb : 0 < b) (h : b ≤ a * b) : 1 ≤ a :=
  le_of_mul_le_mul_right (by simpa) hb

@[simp]
lemma le_mul_iff_one_le_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_left a0)

@[simp]
theorem lt_mul_iff_one_lt_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_left a0)

@[simp]
lemma mul_le_iff_le_one_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_left a0)

@[simp]
theorem mul_lt_iff_lt_one_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_left a0)

/-! Lemmas of the form `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`,
which assume right covariance. -/


@[simp]
lemma le_mul_iff_one_le_left [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) : a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_right a0)

@[simp]
theorem lt_mul_iff_one_lt_left [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_right a0)

@[simp]
lemma mul_le_iff_le_one_left [MulPosMono α] [MulPosReflectLE α] (b0 : 0 < b) : a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_right b0)

@[simp]
theorem mul_lt_iff_lt_one_left [MulPosStrictMono α] [MulPosReflectLT α] (b0 : 0 < b) :
    a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_right b0)

/-! Lemmas of the form `1 ≤ b → a ≤ a * b`.

Variants with `< 0` and `≤ 0` instead of `0 <` and `0 ≤` appear in `Mathlib/Algebra/Order/Ring/Defs`
(which imports this file) as they need additional results which are not yet available here. -/


theorem mul_le_of_le_one_left [MulPosMono α] (hb : 0 ≤ b) (h : a ≤ 1) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

theorem le_mul_of_one_le_left [MulPosMono α] (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

theorem mul_le_of_le_one_right [PosMulMono α] (ha : 0 ≤ a) (h : b ≤ 1) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

theorem le_mul_of_one_le_right [PosMulMono α] (ha : 0 ≤ a) (h : 1 ≤ b) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

theorem mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 0 < b) (h : a < 1) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

theorem lt_mul_of_one_lt_left [MulPosStrictMono α] (hb : 0 < b) (h : 1 < a) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

theorem mul_lt_of_lt_one_right [PosMulStrictMono α] (ha : 0 < a) (h : b < 1) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

theorem lt_mul_of_one_lt_right [PosMulStrictMono α] (ha : 0 < a) (h : 1 < b) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

end Preorder

end MulOneClass

section MulZero

variable {M₀ : Type*} [Mul M₀] [Zero M₀] [Preorder M₀] [Preorder α] {f g : α → M₀}

lemma Monotone.mul [PosMulMono M₀] [MulPosMono M₀] (hf : Monotone f) (hg : Monotone g)
    (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) : Monotone (f * g) :=
  fun _ _ h ↦ mul_le_mul (hf h) (hg h) (hg₀ _) (hf₀ _)

lemma MonotoneOn.mul [PosMulMono M₀] [MulPosMono M₀] {s : Set α} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) (hf₀ : ∀ x ∈ s, 0 ≤ f x) (hg₀ : ∀ x ∈ s, 0 ≤ g x) :
    MonotoneOn (f * g) s :=
  fun _ ha _ hb h ↦ mul_le_mul (hf ha hb h) (hg ha hb h) (hg₀ _ ha) (hf₀ _ hb)

end MulZero
