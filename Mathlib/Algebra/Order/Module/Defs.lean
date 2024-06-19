/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Algebra.Order.Module.Synonym
import Mathlib.GroupTheory.GroupAction.Group
import Mathlib.Tactic.Positivity.Core

/-!
# Monotonicity of scalar multiplication by positive elements

This file defines typeclasses to reason about monotonicity of the operations
* `b ↦ a • b`, "left scalar multiplication"
* `a ↦ a • b`, "right scalar multiplication"

We use eight typeclasses to encode the various properties we care about for those two operations.
These typeclasses are meant to be mostly internal to this file, to set up each lemma in the
appropriate generality.

Less granular typeclasses like `OrderedAddCommMonoid`, `LinearOrderedField`, `OrderedSMul` should be
enough for most purposes, and the system is set up so that they imply the correct granular
typeclasses here. If those are enough for you, you may stop reading here! Else, beware that what
follows is a bit technical.

## Definitions

In all that follows, `α` and `β` are orders which have a `0` and such that `α` acts on `β` by scalar
multiplication. Note however that we do not use lawfulness of this action in most of the file. Hence
`•` should be considered here as a mostly arbitrary function `α → β → β`.

We use the following four typeclasses to reason about left scalar multiplication (`b ↦ a • b`):
* `PosSMulMono`: If `a ≥ 0`, then `b₁ ≤ b₂` implies `a • b₁ ≤ a • b₂`.
* `PosSMulStrictMono`: If `a > 0`, then `b₁ < b₂` implies `a • b₁ < a • b₂`.
* `PosSMulReflectLT`: If `a ≥ 0`, then `a • b₁ < a • b₂` implies `b₁ < b₂`.
* `PosSMulReflectLE`: If `a > 0`, then `a • b₁ ≤ a • b₂` implies `b₁ ≤ b₂`.

We use the following four typeclasses to reason about right scalar multiplication (`a ↦ a • b`):
* `SMulPosMono`: If `b ≥ 0`, then `a₁ ≤ a₂` implies `a₁ • b ≤ a₂ • b`.
* `SMulPosStrictMono`: If `b > 0`, then `a₁ < a₂` implies `a₁ • b < a₂ • b`.
* `SMulPosReflectLT`: If `b ≥ 0`, then `a₁ • b < a₂ • b` implies `a₁ < a₂`.
* `SMulPosReflectLE`: If `b > 0`, then `a₁ • b ≤ a₂ • b` implies `a₁ ≤ a₂`.

## Constructors

The four typeclasses about nonnegativity can usually be checked only on positive inputs due to their
condition becoming trivial when `a = 0` or `b = 0`. We therefore make the following constructors
available: `PosSMulMono.of_pos`, `PosSMulReflectLT.of_pos`, `SMulPosMono.of_pos`,
`SMulPosReflectLT.of_pos`

## Implications

As `α` and `β` get more and more structure, those typeclasses end up being equivalent. The commonly
used implications are:
* When `α`, `β` are partial orders:
  * `PosSMulStrictMono → PosSMulMono`
  * `SMulPosStrictMono → SMulPosMono`
  * `PosSMulReflectLE → PosSMulReflectLT`
  * `SMulPosReflectLE → SMulPosReflectLT`
* When `β` is a linear order: `PosSMulStrictMono → PosSMulReflectLE`
* When `α` is a linear order: `SMulPosStrictMono → SMulPosReflectLE`
* When `α` is an ordered ring, `β` an ordered group and also an `α`-module:
  * `PosSMulMono → SMulPosMono`
  * `PosSMulStrictMono → SMulPosStrictMono`
* When `α` is an ordered semifield, `β` is an `α`-module:
  * `PosSMulStrictMono → PosSMulReflectLT`
  * `PosSMulMono → PosSMulReflectLE`

Further, the bundled non-granular typeclasses imply the granular ones like so:
* `OrderedSMul → PosSMulStrictMono`
* `OrderedSMul → PosSMulReflectLT`

All these are registered as instances, which means that in practice you should not worry about these
implications. However, if you encounter a case where you think a statement is true but not covered
by the current implications, please bring it up on Zulip!

## Implementation notes

This file uses custom typeclasses instead of abbreviations of `CovariantClass`/`ContravariantClass`
because:
* They get displayed as classes in the docs. In particular, one can see their list of instances,
  instead of their instances being invariably dumped to the `CovariantClass`/`ContravariantClass`
  list.
* They don't pollute other typeclass searches. Having many abbreviations of the same typeclass for
  different purposes always felt like a performance issue (more instances with the same key, for no
  added benefit), and indeed making the classes here abbreviation previous creates timeouts due to
  the higher number of `CovariantClass`/`ContravariantClass` instances.
* `SMulPosReflectLT`/`SMulPosReflectLE` do not fit in the framework since they relate `≤` on two
  different types. So we would have to generalise `CovariantClass`/`ContravariantClass` to three
  types and two relations.
* Very minor, but the constructors let you work with `a : α`, `h : 0 ≤ a` instead of
  `a : {a : α // 0 ≤ a}`. This actually makes some instances surprisingly cleaner to prove.
* The `CovariantClass`/`ContravariantClass` framework is only useful to automate very simple logic
  anyway. It is easily copied over.

In the future, it would be good to make the corresponding typeclasses in
`Mathlib.Algebra.Order.GroupWithZero.Unbundled` custom typeclasses too.

## TODO

This file acts as a substitute for `Mathlib.Algebra.Order.SMul`. We now need to
* finish the transition by deleting the duplicate lemmas
* rearrange the non-duplicate lemmas into new files
* generalise (most of) the lemmas from `Mathlib.Algebra.Order.Module` to here
* rethink `OrderedSMul`
-/

open OrderDual

variable (α β : Type*)

section Defs
variable [SMul α β] [Preorder α] [Preorder β]

section Left
variable [Zero α]

/-- Typeclass for monotonicity of scalar multiplication by nonnegative elements on the left,
namely `b₁ ≤ b₂ → a • b₁ ≤ a • b₂` if `0 ≤ a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSMul`. -/
class PosSMulMono : Prop where
  /-- Do not use this. Use `smul_le_smul_of_nonneg_left` instead. -/
  protected elim ⦃a : α⦄ (ha : 0 ≤ a) ⦃b₁ b₂ : β⦄ (hb : b₁ ≤ b₂) : a • b₁ ≤ a • b₂

/-- Typeclass for strict monotonicity of scalar multiplication by positive elements on the left,
namely `b₁ < b₂ → a • b₁ < a • b₂` if `0 < a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSMul`. -/
class PosSMulStrictMono : Prop where
  /-- Do not use this. Use `smul_lt_smul_of_pos_left` instead. -/
  protected elim ⦃a : α⦄ (ha : 0 < a) ⦃b₁ b₂ : β⦄ (hb : b₁ < b₂) : a • b₁ < a • b₂

/-- Typeclass for strict reverse monotonicity of scalar multiplication by nonnegative elements on
the left, namely `a • b₁ < a • b₂ → b₁ < b₂` if `0 ≤ a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSMul`. -/
class PosSMulReflectLT : Prop where
  /-- Do not use this. Use `lt_of_smul_lt_smul_left` instead. -/
  protected elim ⦃a : α⦄ (ha : 0 ≤ a) ⦃b₁ b₂ : β⦄ (hb : a • b₁ < a • b₂) : b₁ < b₂

/-- Typeclass for reverse monotonicity of scalar multiplication by positive elements on the left,
namely `a • b₁ ≤ a • b₂ → b₁ ≤ b₂` if `0 < a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSMul`. -/
class PosSMulReflectLE : Prop where
  /-- Do not use this. Use `le_of_smul_lt_smul_left` instead. -/
  protected elim ⦃a : α⦄ (ha : 0 < a) ⦃b₁ b₂ : β⦄ (hb : a • b₁ ≤ a • b₂) : b₁ ≤ b₂

end Left

section Right
variable [Zero β]

/-- Typeclass for monotonicity of scalar multiplication by nonnegative elements on the left,
namely `a₁ ≤ a₂ → a₁ • b ≤ a₂ • b` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSMul`. -/
class SMulPosMono : Prop where
  /-- Do not use this. Use `smul_le_smul_of_nonneg_right` instead. -/
  protected elim ⦃b : β⦄ (hb : 0 ≤ b) ⦃a₁ a₂ : α⦄ (ha : a₁ ≤ a₂) : a₁ • b ≤ a₂ • b

/-- Typeclass for strict monotonicity of scalar multiplication by positive elements on the left,
namely `a₁ < a₂ → a₁ • b < a₂ • b` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSMul`. -/
class SMulPosStrictMono : Prop where
  /-- Do not use this. Use `smul_lt_smul_of_pos_right` instead. -/
  protected elim ⦃b : β⦄ (hb : 0 < b) ⦃a₁ a₂ : α⦄ (ha : a₁ < a₂) : a₁ • b < a₂ • b

/-- Typeclass for strict reverse monotonicity of scalar multiplication by nonnegative elements on
the left, namely `a₁ • b < a₂ • b → a₁ < a₂` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSMul`. -/
class SMulPosReflectLT : Prop where
  /-- Do not use this. Use `lt_of_smul_lt_smul_right` instead. -/
  protected elim ⦃b : β⦄ (hb : 0 ≤ b) ⦃a₁ a₂ : α⦄ (hb : a₁ • b < a₂ • b) : a₁ < a₂

/-- Typeclass for reverse monotonicity of scalar multiplication by positive elements on the left,
namely `a₁ • b ≤ a₂ • b → a₁ ≤ a₂` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSMul`. -/
class SMulPosReflectLE : Prop where
  /-- Do not use this. Use `le_of_smul_lt_smul_right` instead. -/
  protected elim ⦃b : β⦄ (hb : 0 < b) ⦃a₁ a₂ : α⦄ (hb : a₁ • b ≤ a₂ • b) : a₁ ≤ a₂

end Right
end Defs

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

section Mul
variable [Zero α] [Mul α] [Preorder α]

-- See note [lower instance priority]
instance (priority := 100) PosMulMono.toPosSMulMono [PosMulMono α] : PosSMulMono α α where
  elim _a ha _b₁ _b₂ hb := mul_le_mul_of_nonneg_left hb ha

-- See note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosSMulStrictMono [PosMulStrictMono α] :
    PosSMulStrictMono α α where
  elim _a ha _b₁ _b₂ hb := mul_lt_mul_of_pos_left hb ha

-- See note [lower instance priority]
instance (priority := 100) PosMulReflectLT.toPosSMulReflectLT [PosMulReflectLT α] :
    PosSMulReflectLT α α where
  elim _a ha _b₁ _b₂ h := lt_of_mul_lt_mul_left h ha

-- See note [lower instance priority]
instance (priority := 100) PosMulReflectLE.toPosSMulReflectLE [PosMulReflectLE α] :
    PosSMulReflectLE α α where
  elim _a ha _b₁ _b₂ h := le_of_mul_le_mul_left h ha

-- See note [lower instance priority]
instance (priority := 100) MulPosMono.toSMulPosMono [MulPosMono α] : SMulPosMono α α where
  elim _b hb _a₁ _a₂ ha := mul_le_mul_of_nonneg_right ha hb

-- See note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toSMulPosStrictMono [MulPosStrictMono α] :
    SMulPosStrictMono α α where
  elim _b hb _a₁ _a₂ ha := mul_lt_mul_of_pos_right ha hb

-- See note [lower instance priority]
instance (priority := 100) MulPosReflectLT.toSMulPosReflectLT [MulPosReflectLT α] :
    SMulPosReflectLT α α where
  elim _b hb _a₁ _a₂ h := lt_of_mul_lt_mul_right h hb

-- See note [lower instance priority]
instance (priority := 100) MulPosReflectLE.toSMulPosReflectLE [MulPosReflectLE α] :
    SMulPosReflectLE α α where
  elim _b hb _a₁ _a₂ h := le_of_mul_le_mul_right h hb

end Mul

section SMul
variable [SMul α β]

section Preorder
variable [Preorder α] [Preorder β]

section Left
variable [Zero α]

lemma monotone_smul_left_of_nonneg [PosSMulMono α β] (ha : 0 ≤ a) : Monotone ((a • ·) : β → β) :=
  PosSMulMono.elim ha
#align monotone_smul_left monotone_smul_left_of_nonneg

lemma strictMono_smul_left_of_pos [PosSMulStrictMono α β] (ha : 0 < a) :
    StrictMono ((a • ·) : β → β) := PosSMulStrictMono.elim ha
#align strict_mono_smul_left strictMono_smul_left_of_pos

@[gcongr] lemma smul_le_smul_of_nonneg_left [PosSMulMono α β] (hb : b₁ ≤ b₂) (ha : 0 ≤ a) :
    a • b₁ ≤ a • b₂ := monotone_smul_left_of_nonneg ha hb
#align smul_le_smul_of_nonneg smul_le_smul_of_nonneg_left

@[gcongr] lemma smul_lt_smul_of_pos_left [PosSMulStrictMono α β] (hb : b₁ < b₂) (ha : 0 < a) :
    a • b₁ < a • b₂ := strictMono_smul_left_of_pos ha hb
#align smul_lt_smul_of_pos smul_lt_smul_of_pos_left

lemma lt_of_smul_lt_smul_left [PosSMulReflectLT α β] (h : a • b₁ < a • b₂) (ha : 0 ≤ a) : b₁ < b₂ :=
  PosSMulReflectLT.elim ha h

lemma le_of_smul_le_smul_left [PosSMulReflectLE α β] (h : a • b₁ ≤ a • b₂) (ha : 0 < a) : b₁ ≤ b₂ :=
  PosSMulReflectLE.elim ha h

alias lt_of_smul_lt_smul_of_nonneg_left := lt_of_smul_lt_smul_left
alias le_of_smul_le_smul_of_pos_left := le_of_smul_le_smul_left
#align lt_of_smul_lt_smul_of_nonneg lt_of_smul_lt_smul_of_nonneg_left

@[simp]
lemma smul_le_smul_iff_of_pos_left [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) :
    a • b₁ ≤ a • b₂ ↔ b₁ ≤ b₂ :=
  ⟨fun h ↦ le_of_smul_le_smul_left h ha, fun h ↦ smul_le_smul_of_nonneg_left h ha.le⟩
#align smul_le_smul_iff_of_pos smul_le_smul_iff_of_pos_left

@[simp]
lemma smul_lt_smul_iff_of_pos_left [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    a • b₁ < a • b₂ ↔ b₁ < b₂ :=
  ⟨fun h ↦ lt_of_smul_lt_smul_left h ha.le, fun hb ↦ smul_lt_smul_of_pos_left hb ha⟩
#align smul_lt_smul_iff_of_pos smul_lt_smul_iff_of_pos_left

end Left

section Right
variable [Zero β]

lemma monotone_smul_right_of_nonneg [SMulPosMono α β] (hb : 0 ≤ b) : Monotone ((· • b) : α → β) :=
  SMulPosMono.elim hb

lemma strictMono_smul_right_of_pos [SMulPosStrictMono α β] (hb : 0 < b) :
    StrictMono ((· • b) : α → β) := SMulPosStrictMono.elim hb

@[gcongr] lemma smul_le_smul_of_nonneg_right [SMulPosMono α β] (ha : a₁ ≤ a₂) (hb : 0 ≤ b) :
    a₁ • b ≤ a₂ • b := monotone_smul_right_of_nonneg hb ha

@[gcongr] lemma smul_lt_smul_of_pos_right [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : 0 < b) :
    a₁ • b < a₂ • b := strictMono_smul_right_of_pos hb ha

lemma lt_of_smul_lt_smul_right [SMulPosReflectLT α β] (h : a₁ • b < a₂ • b) (hb : 0 ≤ b) :
    a₁ < a₂ := SMulPosReflectLT.elim hb h

lemma le_of_smul_le_smul_right [SMulPosReflectLE α β] (h : a₁ • b ≤ a₂ • b) (hb : 0 < b) :
    a₁ ≤ a₂ := SMulPosReflectLE.elim hb h

alias lt_of_smul_lt_smul_of_nonneg_right := lt_of_smul_lt_smul_right
alias le_of_smul_le_smul_of_pos_right := le_of_smul_le_smul_right

@[simp]
lemma smul_le_smul_iff_of_pos_right [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b) :
    a₁ • b ≤ a₂ • b ↔ a₁ ≤ a₂ :=
  ⟨fun h ↦ le_of_smul_le_smul_right h hb, fun ha ↦ smul_le_smul_of_nonneg_right ha hb.le⟩

@[simp]
lemma smul_lt_smul_iff_of_pos_right [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) :
    a₁ • b < a₂ • b ↔ a₁ < a₂ :=
  ⟨fun h ↦ lt_of_smul_lt_smul_right h hb.le, fun ha ↦ smul_lt_smul_of_pos_right ha hb⟩

end Right

section LeftRight
variable [Zero α] [Zero β]

lemma smul_lt_smul_of_le_of_lt [PosSMulStrictMono α β] [SMulPosMono α β] (ha : a₁ ≤ a₂)
    (hb : b₁ < b₂) (h₁ : 0 < a₁) (h₂ : 0 ≤ b₂) : a₁ • b₁ < a₂ • b₂ :=
  (smul_lt_smul_of_pos_left hb h₁).trans_le (smul_le_smul_of_nonneg_right ha h₂)

lemma smul_lt_smul_of_le_of_lt' [PosSMulStrictMono α β] [SMulPosMono α β] (ha : a₁ ≤ a₂)
    (hb : b₁ < b₂) (h₂ : 0 < a₂) (h₁ : 0 ≤ b₁) : a₁ • b₁ < a₂ • b₂ :=
  (smul_le_smul_of_nonneg_right ha h₁).trans_lt (smul_lt_smul_of_pos_left hb h₂)

lemma smul_lt_smul_of_lt_of_le [PosSMulMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂)
    (hb : b₁ ≤ b₂) (h₁ : 0 ≤ a₁) (h₂ : 0 < b₂) : a₁ • b₁ < a₂ • b₂ :=
  (smul_le_smul_of_nonneg_left hb h₁).trans_lt (smul_lt_smul_of_pos_right ha h₂)

lemma smul_lt_smul_of_lt_of_le' [PosSMulMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂)
    (hb : b₁ ≤ b₂) (h₂ : 0 ≤ a₂) (h₁ : 0 < b₁) : a₁ • b₁ < a₂ • b₂ :=
  (smul_lt_smul_of_pos_right ha h₁).trans_le (smul_le_smul_of_nonneg_left hb h₂)

lemma smul_lt_smul [PosSMulStrictMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : b₁ < b₂)
    (h₁ : 0 < a₁) (h₂ : 0 < b₂) : a₁ • b₁ < a₂ • b₂ :=
  (smul_lt_smul_of_pos_left hb h₁).trans (smul_lt_smul_of_pos_right ha h₂)

lemma smul_lt_smul' [PosSMulStrictMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : b₁ < b₂)
    (h₂ : 0 < a₂) (h₁ : 0 < b₁) : a₁ • b₁ < a₂ • b₂ :=
  (smul_lt_smul_of_pos_right ha h₁).trans (smul_lt_smul_of_pos_left hb h₂)

lemma smul_le_smul [PosSMulMono α β] [SMulPosMono α β] (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ b₂) : a₁ • b₁ ≤ a₂ • b₂ :=
  (smul_le_smul_of_nonneg_left hb h₁).trans (smul_le_smul_of_nonneg_right ha h₂)

lemma smul_le_smul' [PosSMulMono α β] [SMulPosMono α β] (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (h₂ : 0 ≤ a₂)
    (h₁ : 0 ≤ b₁) : a₁ • b₁ ≤ a₂ • b₂ :=
  (smul_le_smul_of_nonneg_right ha h₁).trans (smul_le_smul_of_nonneg_left hb h₂)

end LeftRight
end Preorder

section LinearOrder
variable [Preorder α] [LinearOrder β]

section Left
variable [Zero α]

-- See note [lower instance priority]
instance (priority := 100) PosSMulStrictMono.toPosSMulReflectLE [PosSMulStrictMono α β] :
    PosSMulReflectLE α β where
  elim _a ha _b₁ _b₂ := (strictMono_smul_left_of_pos ha).le_iff_le.1

lemma PosSMulReflectLE.toPosSMulStrictMono [PosSMulReflectLE α β] : PosSMulStrictMono α β where
  elim _a ha _b₁ _b₂ hb := not_le.1 fun h ↦ hb.not_le <| le_of_smul_le_smul_left h ha

lemma posSMulStrictMono_iff_PosSMulReflectLE : PosSMulStrictMono α β ↔ PosSMulReflectLE α β :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ PosSMulReflectLE.toPosSMulStrictMono⟩

instance PosSMulMono.toPosSMulReflectLT [PosSMulMono α β] : PosSMulReflectLT α β where
  elim _a ha _b₁ _b₂ := (monotone_smul_left_of_nonneg ha).reflect_lt

lemma PosSMulReflectLT.toPosSMulMono [PosSMulReflectLT α β] : PosSMulMono α β where
  elim _a ha _b₁ _b₂ hb := not_lt.1 fun h ↦ hb.not_lt <| lt_of_smul_lt_smul_left h ha

lemma posSMulMono_iff_posSMulReflectLT : PosSMulMono α β ↔ PosSMulReflectLT α β :=
  ⟨fun _ ↦ PosSMulMono.toPosSMulReflectLT, fun _ ↦ PosSMulReflectLT.toPosSMulMono⟩

lemma smul_max_of_nonneg [PosSMulMono α β] (ha : 0 ≤ a) (b₁ b₂ : β) :
    a • max b₁ b₂ = max (a • b₁) (a • b₂) := (monotone_smul_left_of_nonneg ha).map_max
#align smul_max smul_max_of_nonneg

lemma smul_min_of_nonneg [PosSMulMono α β] (ha : 0 ≤ a) (b₁ b₂ : β) :
    a • min b₁ b₂ = min (a • b₁) (a • b₂) := (monotone_smul_left_of_nonneg ha).map_min
#align smul_min smul_min_of_nonneg

end Left

section Right
variable [Zero β]

lemma SMulPosReflectLE.toSMulPosStrictMono [SMulPosReflectLE α β] : SMulPosStrictMono α β where
  elim _b hb _a₁ _a₂ ha := not_le.1 fun h ↦ ha.not_le <| le_of_smul_le_smul_of_pos_right h hb

lemma SMulPosReflectLT.toSMulPosMono [SMulPosReflectLT α β] : SMulPosMono α β where
  elim _b hb _a₁ _a₂ ha := not_lt.1 fun h ↦ ha.not_lt <| lt_of_smul_lt_smul_right h hb

end Right
end LinearOrder

section LinearOrder
variable [LinearOrder α] [Preorder β]

section Right
variable [Zero β]

-- See note [lower instance priority]
instance (priority := 100) SMulPosStrictMono.toSMulPosReflectLE [SMulPosStrictMono α β] :
    SMulPosReflectLE α β where
  elim _b hb _a₁ _a₂ h := not_lt.1 fun ha ↦ h.not_lt <| smul_lt_smul_of_pos_right ha hb

lemma SMulPosMono.toSMulPosReflectLT [SMulPosMono α β] : SMulPosReflectLT α β where
  elim _b hb _a₁ _a₂ h := not_le.1 fun ha ↦ h.not_le <| smul_le_smul_of_nonneg_right ha hb

end Right
end LinearOrder

section LinearOrder
variable [LinearOrder α] [LinearOrder β]

section Right
variable [Zero β]

lemma smulPosStrictMono_iff_SMulPosReflectLE : SMulPosStrictMono α β ↔ SMulPosReflectLE α β :=
  ⟨fun _ ↦ SMulPosStrictMono.toSMulPosReflectLE, fun _ ↦ SMulPosReflectLE.toSMulPosStrictMono⟩

lemma smulPosMono_iff_smulPosReflectLT : SMulPosMono α β ↔ SMulPosReflectLT α β :=
  ⟨fun _ ↦ SMulPosMono.toSMulPosReflectLT, fun _ ↦ SMulPosReflectLT.toSMulPosMono⟩

end Right
end LinearOrder
end SMul

section SMulZeroClass
variable [Zero α] [Zero β] [SMulZeroClass α β]

section Preorder
variable [Preorder α] [Preorder β]

lemma smul_pos [PosSMulStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0 < a • b := by
  simpa only [smul_zero] using smul_lt_smul_of_pos_left hb ha
#align smul_pos smul_pos

lemma smul_neg_of_pos_of_neg [PosSMulStrictMono α β] (ha : 0 < a) (hb : b < 0) : a • b < 0 := by
  simpa only [smul_zero] using smul_lt_smul_of_pos_left hb ha
#align smul_neg_of_pos_of_neg smul_neg_of_pos_of_neg

@[simp]
lemma smul_pos_iff_of_pos_left [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    0 < a • b ↔ 0 < b := by
  simpa only [smul_zero] using smul_lt_smul_iff_of_pos_left ha (b₁ := 0) (b₂ := b)
#align smul_pos_iff_of_pos smul_pos_iff_of_pos_left

lemma smul_neg_iff_of_pos_left [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    a • b < 0 ↔ b < 0 := by
  simpa only [smul_zero]  using smul_lt_smul_iff_of_pos_left ha (b₂ := (0 : β))
#align smul_neg_iff_of_pos smul_neg_iff_of_pos_left

lemma smul_nonneg [PosSMulMono α β] (ha : 0 ≤ a) (hb : 0 ≤ b₁) : 0 ≤ a • b₁ := by
  simpa only [smul_zero] using smul_le_smul_of_nonneg_left hb ha
#align smul_nonneg smul_nonneg

lemma smul_nonpos_of_nonneg_of_nonpos [PosSMulMono α β] (ha : 0 ≤ a) (hb : b ≤ 0) : a • b ≤ 0 := by
  simpa only [smul_zero] using smul_le_smul_of_nonneg_left hb ha
#align smul_nonpos_of_nonneg_of_nonpos smul_nonpos_of_nonneg_of_nonpos

lemma pos_of_smul_pos_left [PosSMulReflectLT α β] (h : 0 < a • b) (ha : 0 ≤ a) : 0 < b :=
  lt_of_smul_lt_smul_left (by rwa [smul_zero]) ha

lemma neg_of_smul_neg_left [PosSMulReflectLT α β] (h : a • b < 0) (ha : 0 ≤ a) : b < 0 :=
  lt_of_smul_lt_smul_left (by rwa [smul_zero]) ha

end Preorder
end SMulZeroClass

section SMulWithZero
variable [Zero α] [Zero β] [SMulWithZero α β]

section Preorder
variable [Preorder α] [Preorder β]

lemma smul_pos' [SMulPosStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0 < a • b := by
  simpa only [zero_smul] using smul_lt_smul_of_pos_right ha hb

lemma smul_neg_of_neg_of_pos [SMulPosStrictMono α β] (ha : a < 0) (hb : 0 < b) : a • b < 0 := by
  simpa only [zero_smul] using smul_lt_smul_of_pos_right ha hb
#align smul_neg_of_neg_of_pos smul_neg_of_neg_of_pos

@[simp]
lemma smul_pos_iff_of_pos_right [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) :
    0 < a • b ↔ 0 < a := by
  simpa only [zero_smul] using smul_lt_smul_iff_of_pos_right hb (a₁ := 0) (a₂ := a)

lemma smul_nonneg' [SMulPosMono α β] (ha : 0 ≤ a) (hb : 0 ≤ b₁) : 0 ≤ a • b₁ := by
  simpa only [zero_smul] using smul_le_smul_of_nonneg_right ha hb

lemma smul_nonpos_of_nonpos_of_nonneg [SMulPosMono α β] (ha : a ≤ 0) (hb : 0 ≤ b) : a • b ≤ 0 := by
  simpa only [zero_smul] using smul_le_smul_of_nonneg_right ha hb
#align smul_nonpos_of_nonpos_of_nonneg smul_nonpos_of_nonpos_of_nonneg

lemma pos_of_smul_pos_right [SMulPosReflectLT α β] (h : 0 < a • b) (hb : 0 ≤ b) : 0 < a :=
  lt_of_smul_lt_smul_right (by rwa [zero_smul]) hb

lemma neg_of_smul_neg_right [SMulPosReflectLT α β] (h : a • b < 0) (hb : 0 ≤ b) : a < 0 :=
  lt_of_smul_lt_smul_right (by rwa [zero_smul]) hb

lemma pos_iff_pos_of_smul_pos [PosSMulReflectLT α β] [SMulPosReflectLT α β] (hab : 0 < a • b) :
    0 < a ↔ 0 < b :=
  ⟨pos_of_smul_pos_left hab ∘ le_of_lt, pos_of_smul_pos_right hab ∘ le_of_lt⟩

end Preorder

section PartialOrder
variable [PartialOrder α] [Preorder β]

/-- A constructor for `PosSMulMono` requiring you to prove `b₁ ≤ b₂ → a • b₁ ≤ a • b₂` only when
`0 < a`-/
lemma PosSMulMono.of_pos (h₀ : ∀ a : α, 0 < a → ∀ b₁ b₂ : β, b₁ ≤ b₂ → a • b₁ ≤ a • b₂) :
    PosSMulMono α β where
  elim a ha b₁ b₂ h := by
    obtain ha | ha := ha.eq_or_lt
    · simp [← ha]
    · exact h₀ _ ha _ _ h

/-- A constructor for `PosSMulReflectLT` requiring you to prove `a • b₁ < a • b₂ → b₁ < b₂` only
when `0 < a`-/
lemma PosSMulReflectLT.of_pos (h₀ : ∀ a : α, 0 < a → ∀ b₁ b₂ : β, a • b₁ < a • b₂ → b₁ < b₂) :
    PosSMulReflectLT α β where
  elim a ha b₁ b₂ h := by
    obtain ha | ha := ha.eq_or_lt
    · simp [← ha] at h
    · exact h₀ _ ha _ _ h

end PartialOrder

section PartialOrder
variable [Preorder α] [PartialOrder β]

/-- A constructor for `SMulPosMono` requiring you to prove `a₁ ≤ a₂ → a₁ • b ≤ a₂ • b` only when
`0 < b`-/
lemma SMulPosMono.of_pos (h₀ : ∀ b : β, 0 < b → ∀ a₁ a₂ : α, a₁ ≤ a₂ → a₁ • b ≤ a₂ • b) :
    SMulPosMono α β where
  elim b hb a₁ a₂ h := by
    obtain hb | hb := hb.eq_or_lt
    · simp [← hb]
    · exact h₀ _ hb _ _ h

/-- A constructor for `SMulPosReflectLT` requiring you to prove `a₁ • b < a₂ • b → a₁ < a₂` only
when `0 < b`-/
lemma SMulPosReflectLT.of_pos (h₀ : ∀ b : β, 0 < b → ∀ a₁ a₂ : α, a₁ • b < a₂ • b → a₁ < a₂) :
    SMulPosReflectLT α β where
  elim b hb a₁ a₂ h := by
    obtain hb | hb := hb.eq_or_lt
    · simp [← hb] at h
    · exact h₀ _ hb _ _ h

end PartialOrder

section PartialOrder
variable [PartialOrder α] [PartialOrder β]

-- See note [lower instance priority]
instance (priority := 100) PosSMulStrictMono.toPosSMulMono [PosSMulStrictMono α β] :
    PosSMulMono α β :=
  PosSMulMono.of_pos fun _a ha ↦ (strictMono_smul_left_of_pos ha).monotone

-- See note [lower instance priority]
instance (priority := 100) SMulPosStrictMono.toSMulPosMono [SMulPosStrictMono α β] :
    SMulPosMono α β :=
  SMulPosMono.of_pos fun _b hb ↦ (strictMono_smul_right_of_pos hb).monotone

-- See note [lower instance priority]
instance (priority := 100) PosSMulReflectLE.toPosSMulReflectLT [PosSMulReflectLE α β] :
    PosSMulReflectLT α β :=
  PosSMulReflectLT.of_pos fun a ha b₁ b₂ h ↦
    (le_of_smul_le_smul_of_pos_left h.le ha).lt_of_ne <| by rintro rfl; simp at h

-- See note [lower instance priority]
instance (priority := 100) SMulPosReflectLE.toSMulPosReflectLT [SMulPosReflectLE α β] :
    SMulPosReflectLT α β :=
  SMulPosReflectLT.of_pos fun b hb a₁ a₂ h ↦
    (le_of_smul_le_smul_of_pos_right h.le hb).lt_of_ne <| by rintro rfl; simp at h

lemma smul_eq_smul_iff_eq_and_eq_of_pos [PosSMulStrictMono α β] [SMulPosStrictMono α β]
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (h₁ : 0 < a₁) (h₂ : 0 < b₂) :
    a₁ • b₁ = a₂ • b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha ↦ h.not_lt ?_, fun hb ↦ h.not_lt ?_⟩
  · exact (smul_le_smul_of_nonneg_left hb h₁.le).trans_lt (smul_lt_smul_of_pos_right ha h₂)
  · exact (smul_lt_smul_of_pos_left hb h₁).trans_le (smul_le_smul_of_nonneg_right ha h₂.le)

lemma smul_eq_smul_iff_eq_and_eq_of_pos' [PosSMulStrictMono α β] [SMulPosStrictMono α β]
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (h₂ : 0 < a₂) (h₁ : 0 < b₁) :
    a₁ • b₁ = a₂ • b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha ↦ h.not_lt ?_, fun hb ↦ h.not_lt ?_⟩
  · exact (smul_lt_smul_of_pos_right ha h₁).trans_le (smul_le_smul_of_nonneg_left hb h₂.le)
  · exact (smul_le_smul_of_nonneg_right ha h₁.le).trans_lt (smul_lt_smul_of_pos_left hb h₂)

end PartialOrder

section LinearOrder
variable [LinearOrder α] [LinearOrder β]

lemma pos_and_pos_or_neg_and_neg_of_smul_pos [PosSMulMono α β] [SMulPosMono α β] (hab : 0 < a • b) :
    0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  obtain ha | rfl | ha := lt_trichotomy a 0
  · refine Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb ↦ ?_) hab⟩
    exact smul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_smul] at hab
    exact hab.false.elim
  · refine Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb ↦ ?_) hab⟩
    exact smul_nonpos_of_nonneg_of_nonpos ha.le hb

lemma neg_of_smul_pos_right [PosSMulMono α β] [SMulPosMono α β] (h : 0 < a • b) (ha : a ≤ 0) :
    b < 0 := ((pos_and_pos_or_neg_and_neg_of_smul_pos h).resolve_left fun h ↦ h.1.not_le ha).2

lemma neg_of_smul_pos_left [PosSMulMono α β] [SMulPosMono α β] (h : 0 < a • b) (ha : b ≤ 0) :
    a < 0 := ((pos_and_pos_or_neg_and_neg_of_smul_pos h).resolve_left fun h ↦ h.2.not_le ha).1

lemma neg_iff_neg_of_smul_pos [PosSMulMono α β] [SMulPosMono α β] (hab : 0 < a • b) :
    a < 0 ↔ b < 0 :=
  ⟨neg_of_smul_pos_right hab ∘ le_of_lt, neg_of_smul_pos_left hab ∘ le_of_lt⟩

lemma neg_of_smul_neg_left' [SMulPosMono α β] (h : a • b < 0) (ha : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun hb ↦ (smul_nonneg' ha hb).not_lt h

lemma neg_of_smul_neg_right' [PosSMulMono α β] (h : a • b < 0) (hb : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun ha ↦ (smul_nonneg ha hb).not_lt h

end LinearOrder
end SMulWithZero

section MulAction
variable [Monoid α] [Zero α] [Zero β] [MulAction α β]

section Preorder
variable [Preorder α] [Preorder β]

@[simp]
lemma le_smul_iff_one_le_left [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b) :
    b ≤ a • b ↔ 1 ≤ a := Iff.trans (by rw [one_smul]) (smul_le_smul_iff_of_pos_right hb)

@[simp]
lemma lt_smul_iff_one_lt_left [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) :
    b < a • b ↔ 1 < a := Iff.trans (by rw [one_smul]) (smul_lt_smul_iff_of_pos_right hb)

@[simp]
lemma smul_le_iff_le_one_left [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b) :
    a • b ≤ b ↔ a ≤ 1 := Iff.trans (by rw [one_smul]) (smul_le_smul_iff_of_pos_right hb)

@[simp]
lemma smul_lt_iff_lt_one_left [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) :
    a • b < b ↔ a < 1 := Iff.trans (by rw [one_smul]) (smul_lt_smul_iff_of_pos_right hb)

lemma smul_le_of_le_one_left [SMulPosMono α β] (hb : 0 ≤ b) (h : a ≤ 1) : a • b ≤ b := by
  simpa only [one_smul] using smul_le_smul_of_nonneg_right h hb

lemma le_smul_of_one_le_left [SMulPosMono α β] (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a • b := by
  simpa only [one_smul] using smul_le_smul_of_nonneg_right h hb

lemma smul_lt_of_lt_one_left [SMulPosStrictMono α β] (hb : 0 < b) (h : a < 1) : a • b < b := by
  simpa only [one_smul] using smul_lt_smul_of_pos_right h hb

lemma lt_smul_of_one_lt_left [SMulPosStrictMono α β] (hb : 0 < b) (h : 1 < a) : b < a • b := by
  simpa only [one_smul] using smul_lt_smul_of_pos_right h hb

end Preorder
end MulAction

section Semiring
variable [Semiring α] [AddCommGroup β] [Module α β] [NoZeroSMulDivisors α β]

section PartialOrder
variable [Preorder α] [PartialOrder β]

lemma PosSMulMono.toPosSMulStrictMono [PosSMulMono α β] : PosSMulStrictMono α β :=
  ⟨fun _a ha _b₁ _b₂ hb ↦ (smul_le_smul_of_nonneg_left hb.le ha.le).lt_of_ne <|
    (smul_right_injective _ ha.ne').ne hb.ne⟩

instance PosSMulReflectLT.toPosSMulReflectLE [PosSMulReflectLT α β] : PosSMulReflectLE α β :=
  ⟨fun _a ha _b₁ _b₂ h ↦ h.eq_or_lt.elim (fun h ↦ (smul_right_injective _ ha.ne' h).le) fun h' ↦
    (lt_of_smul_lt_smul_left h' ha.le).le⟩

end PartialOrder

section PartialOrder
variable [PartialOrder α] [PartialOrder β]

lemma posSMulMono_iff_posSMulStrictMono : PosSMulMono α β ↔ PosSMulStrictMono α β :=
  ⟨fun _ ↦ PosSMulMono.toPosSMulStrictMono, fun _ ↦ inferInstance⟩

lemma PosSMulReflectLE_iff_posSMulReflectLT : PosSMulReflectLE α β ↔ PosSMulReflectLT α β :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ PosSMulReflectLT.toPosSMulReflectLE⟩

end PartialOrder
end Semiring

section Ring
variable [Ring α] [AddCommGroup β] [Module α β] [NoZeroSMulDivisors α β]

section PartialOrder
variable [PartialOrder α] [PartialOrder β]

lemma SMulPosMono.toSMulPosStrictMono [SMulPosMono α β] : SMulPosStrictMono α β :=
  ⟨fun _b hb _a₁ _a₂ ha ↦ (smul_le_smul_of_nonneg_right ha.le hb.le).lt_of_ne <|
    (smul_left_injective _ hb.ne').ne ha.ne⟩

lemma smulPosMono_iff_smulPosStrictMono : SMulPosMono α β ↔ SMulPosStrictMono α β :=
  ⟨fun _ ↦ SMulPosMono.toSMulPosStrictMono, fun _ ↦ inferInstance⟩

lemma SMulPosReflectLT.toSMulPosReflectLE [SMulPosReflectLT α β] : SMulPosReflectLE α β :=
  ⟨fun _b hb _a₁ _a₂ h ↦ h.eq_or_lt.elim (fun h ↦ (smul_left_injective _ hb.ne' h).le) fun h' ↦
    (lt_of_smul_lt_smul_right h' hb.le).le⟩

lemma SMulPosReflectLE_iff_smulPosReflectLT : SMulPosReflectLE α β ↔ SMulPosReflectLT α β :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ SMulPosReflectLT.toSMulPosReflectLE⟩

end PartialOrder
end Ring

section GroupWithZero
variable [GroupWithZero α] [Preorder α] [Preorder β] [MulAction α β]

lemma inv_smul_le_iff_of_pos [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) :
    a⁻¹ • b₁ ≤ b₂ ↔ b₁ ≤ a • b₂ := by rw [← smul_le_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']
#align inv_smul_le_iff inv_smul_le_iff_of_pos

lemma le_inv_smul_iff_of_pos [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) :
    b₁ ≤ a⁻¹ • b₂ ↔ a • b₁ ≤ b₂ := by rw [← smul_le_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']
#align le_inv_smul_iff le_inv_smul_iff_of_pos

lemma inv_smul_lt_iff_of_pos [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    a⁻¹ • b₁ < b₂ ↔ b₁ < a • b₂ := by rw [← smul_lt_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']
#align inv_smul_lt_iff inv_smul_lt_iff_of_pos

lemma lt_inv_smul_iff_of_pos [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    b₁ < a⁻¹ • b₂ ↔ a • b₁ < b₂ := by rw [← smul_lt_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']
#align lt_inv_smul_iff lt_inv_smul_iff_of_pos

/-- Right scalar multiplication as an order isomorphism. -/
@[simps!]
def OrderIso.smulRight [PosSMulMono α β] [PosSMulReflectLE α β] {a : α} (ha : 0 < a) : β ≃o β where
  toEquiv := Equiv.smulRight ha.ne'
  map_rel_iff' := smul_le_smul_iff_of_pos_left ha
#align order_iso.smul_left OrderIso.smulRight
#align order_iso.smul_left_symm_apply OrderIso.smulRight_symm_apply
#align order_iso.smul_left_apply OrderIso.smulRight_apply

end GroupWithZero

namespace OrderDual

section Left
variable [Preorder α] [Preorder β] [SMul α β] [Zero α]

instance instPosSMulMono [PosSMulMono α β] : PosSMulMono α βᵒᵈ where
  elim _a ha _b₁ _b₂ hb := smul_le_smul_of_nonneg_left (β := β) hb ha
instance instPosSMulStrictMono [PosSMulStrictMono α β] : PosSMulStrictMono α βᵒᵈ where
  elim _a ha _b₁ _b₂ hb := smul_lt_smul_of_pos_left (β := β) hb ha
instance instPosSMulReflectLT [PosSMulReflectLT α β] : PosSMulReflectLT α βᵒᵈ where
  elim _a ha _b₁ _b₂ h := lt_of_smul_lt_smul_of_nonneg_left (β := β) h ha
instance instPosSMulReflectLE [PosSMulReflectLE α β] : PosSMulReflectLE α βᵒᵈ where
  elim _a ha _b₁ _b₂ h := le_of_smul_le_smul_of_pos_left (β := β) h ha

end Left

section Right
variable [Preorder α] [Ring α] [OrderedAddCommGroup β] [Module α β]

instance instSMulPosMono [SMulPosMono α β] : SMulPosMono α βᵒᵈ where
  elim _b hb a₁ a₂ ha := by
    rw [← neg_le_neg_iff, ← smul_neg, ← smul_neg]
    exact smul_le_smul_of_nonneg_right (β := β) ha <| neg_nonneg.2 hb

instance instSMulPosStrictMono [SMulPosStrictMono α β] : SMulPosStrictMono α βᵒᵈ where
  elim _b hb a₁ a₂ ha := by
    rw [← neg_lt_neg_iff, ← smul_neg, ← smul_neg]
    exact smul_lt_smul_of_pos_right (β := β) ha <| neg_pos.2 hb

instance instSMulPosReflectLT [SMulPosReflectLT α β] : SMulPosReflectLT α βᵒᵈ where
  elim _b hb a₁ a₂ h := by
    rw [← neg_lt_neg_iff, ← smul_neg, ← smul_neg] at h
    exact lt_of_smul_lt_smul_right (β := β) h <| neg_nonneg.2 hb

instance instSMulPosReflectLE [SMulPosReflectLE α β] : SMulPosReflectLE α βᵒᵈ where
  elim _b hb a₁ a₂ h := by
    rw [← neg_le_neg_iff, ← smul_neg, ← smul_neg] at h
    exact le_of_smul_le_smul_right (β := β) h <| neg_pos.2 hb

end Right
end OrderDual

section OrderedRing
variable [OrderedRing α]

section OrderedAddCommGroup
variable [OrderedAddCommGroup β] [Module α β]

#noalign eq_of_smul_eq_smul_of_neg_of_le

section PosSMulMono
variable [PosSMulMono α β]

lemma smul_le_smul_of_nonpos_left (h : b₁ ≤ b₂) (ha : a ≤ 0) : a • b₂ ≤ a • b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_le_neg_iff]
  exact smul_le_smul_of_nonneg_left h (neg_nonneg_of_nonpos ha)
#align smul_le_smul_of_nonpos smul_le_smul_of_nonpos_left

lemma antitone_smul_left (ha : a ≤ 0) : Antitone ((a • ·) : β → β) :=
  fun _ _ h ↦ smul_le_smul_of_nonpos_left h ha
#align antitone_smul_left antitone_smul_left

instance PosSMulMono.toSMulPosMono : SMulPosMono α β where
  elim _b hb a₁ a₂ ha := by rw [← sub_nonneg, ← sub_smul]; exact smul_nonneg (sub_nonneg.2 ha) hb

end PosSMulMono

section PosSMulStrictMono
variable [PosSMulStrictMono α β]

lemma smul_lt_smul_of_neg_left (hb : b₁ < b₂) (ha : a < 0) : a • b₂ < a • b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_lt_neg_iff]
  exact smul_lt_smul_of_pos_left hb (neg_pos_of_neg ha)
#align smul_lt_smul_of_neg smul_lt_smul_of_neg_left

lemma strictAnti_smul_left (ha : a < 0) : StrictAnti ((a • ·) : β → β) :=
  fun _ _ h ↦ smul_lt_smul_of_neg_left h ha
#align strict_anti_smul_left strictAnti_smul_left

instance PosSMulStrictMono.toSMulPosStrictMono : SMulPosStrictMono α β where
  elim _b hb a₁ a₂ ha := by rw [← sub_pos, ← sub_smul]; exact smul_pos (sub_pos.2 ha) hb

end PosSMulStrictMono

lemma le_of_smul_le_smul_of_neg [PosSMulReflectLE α β] (h : a • b₁ ≤ a • b₂) (ha : a < 0) :
    b₂ ≤ b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_le_neg_iff] at h
  exact le_of_smul_le_smul_of_pos_left h <| neg_pos.2 ha

lemma lt_of_smul_lt_smul_of_nonpos [PosSMulReflectLT α β] (h : a • b₁ < a • b₂) (ha : a ≤ 0) :
    b₂ < b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_lt_neg_iff] at h
  exact lt_of_smul_lt_smul_of_nonneg_left h (neg_nonneg_of_nonpos ha)
#align lt_of_smul_lt_smul_of_nonpos lt_of_smul_lt_smul_of_nonpos

lemma smul_nonneg_of_nonpos_of_nonpos [SMulPosMono α β] (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a • b :=
  smul_nonpos_of_nonpos_of_nonneg (β := βᵒᵈ) ha hb
#align smul_nonneg_of_nonpos_of_nonpos smul_nonneg_of_nonpos_of_nonpos

lemma smul_le_smul_iff_of_neg_left [PosSMulMono α β] [PosSMulReflectLE α β] (ha : a < 0) :
    a • b₁ ≤ a • b₂ ↔ b₂ ≤ b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_le_neg_iff]
  exact smul_le_smul_iff_of_pos_left (neg_pos_of_neg ha)
#align smul_le_smul_iff_of_neg smul_le_smul_iff_of_neg_left

section PosSMulStrictMono
variable [PosSMulStrictMono α β] [PosSMulReflectLT α β]

lemma smul_lt_smul_iff_of_neg_left (ha : a < 0) : a • b₁ < a • b₂ ↔ b₂ < b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_lt_neg_iff]
  exact smul_lt_smul_iff_of_pos_left (neg_pos_of_neg ha)
#align smul_lt_smul_iff_of_neg smul_lt_smul_iff_of_neg_left

lemma smul_pos_iff_of_neg_left (ha : a < 0) : 0 < a • b ↔ b < 0 := by
  simpa only [smul_zero] using smul_lt_smul_iff_of_neg_left ha (b₁ := (0 : β))
#align smul_pos_iff_of_neg smul_pos_iff_of_neg_left

alias ⟨_, smul_pos_of_neg_of_neg⟩ := smul_pos_iff_of_neg_left
#align smul_pos_of_neg_of_neg smul_pos_of_neg_of_neg

lemma smul_neg_iff_of_neg_left (ha : a < 0) : a • b < 0 ↔ 0 < b := by
  simpa only [smul_zero] using smul_lt_smul_iff_of_neg_left ha (b₂ := (0 : β))
#align smul_neg_iff_of_neg smul_neg_iff_of_neg_left

end PosSMulStrictMono

/-- Binary **rearrangement inequality**. -/
lemma smul_add_smul_le_smul_add_smul [PosSMulMono α β] [ContravariantClass β β (· + ·) (· ≤ ·)]
    {b₁ b₂ : α} {a d : β} (hab : b₁ ≤ b₂) (hcd : a ≤ d) : b₁ • d + b₂ • a ≤ b₁ • a + b₂ • d := by
  obtain ⟨b₂, rfl⟩ := exists_add_of_le hab
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd
  rw [smul_add, add_right_comm, smul_add, ← add_assoc, add_smul _ _ d]
  rw [le_add_iff_nonneg_right] at hab hcd
  exact add_le_add_left (le_add_of_nonneg_right <| smul_nonneg hab hcd) _
#align smul_add_smul_le_smul_add_smul smul_add_smul_le_smul_add_smul

/-- Binary **rearrangement inequality**. -/
lemma smul_add_smul_le_smul_add_smul' [PosSMulMono α β] [ContravariantClass β β (· + ·) (· ≤ ·)]
    {b₁ b₂ : α} {a d : β} (hba : b₂ ≤ b₁) (hdc : d ≤ a) : b₁ • d + b₂ • a ≤ b₁ • a + b₂ • d := by
  rw [add_comm (b₁ • d), add_comm (b₁ • a)]
  exact smul_add_smul_le_smul_add_smul hba hdc
#align smul_add_smul_le_smul_add_smul' smul_add_smul_le_smul_add_smul'

/-- Binary strict **rearrangement inequality**. -/
lemma smul_add_smul_lt_smul_add_smul [PosSMulStrictMono α β] [CovariantClass β β (· + ·) (· < ·)]
    [ContravariantClass β β (· + ·) (· < ·)] {b₁ b₂ : α} {a d : β} (hab : b₁ < b₂) (hcd : a < d) :
    b₁ • d + b₂ • a < b₁ • a + b₂ • d := by
  obtain ⟨b₂, rfl⟩ := exists_add_of_le hab.le
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd.le
  rw [smul_add, add_right_comm, smul_add, ← add_assoc, add_smul _ _ d]
  rw [lt_add_iff_pos_right] at hab hcd
  exact add_lt_add_left (lt_add_of_pos_right _ <| smul_pos hab hcd) _
#align smul_add_smul_lt_smul_add_smul smul_add_smul_lt_smul_add_smul

/-- Binary strict **rearrangement inequality**. -/
lemma smul_add_smul_lt_smul_add_smul' [PosSMulStrictMono α β] [CovariantClass β β (· + ·) (· < ·)]
    [ContravariantClass β β (· + ·) (· < ·)] {b₁ b₂ : α} {a d : β} (hba : b₂ < b₁) (hdc : d < a) :
    b₁ • d + b₂ • a < b₁ • a + b₂ • d := by
  rw [add_comm (b₁ • d), add_comm (b₁ • a)]
  exact smul_add_smul_lt_smul_add_smul hba hdc
#align smul_add_smul_lt_smul_add_smul' smul_add_smul_lt_smul_add_smul'

end OrderedAddCommGroup

section LinearOrderedAddCommGroup
variable [LinearOrderedAddCommGroup β] [Module α β] [PosSMulMono α β] {a : α} {b b₁ b₂ : β}

lemma smul_max_of_nonpos (ha : a ≤ 0) (b₁ b₂ : β) : a • max b₁ b₂ = min (a • b₁) (a • b₂) :=
  (antitone_smul_left ha : Antitone (_ : β → β)).map_max
#align smul_max_of_nonpos smul_max_of_nonpos

lemma smul_min_of_nonpos (ha : a ≤ 0) (b₁ b₂ : β) : a • min b₁ b₂ = max (a • b₁) (a • b₂) :=
  (antitone_smul_left ha : Antitone (_ : β → β)).map_min
#align smul_min_of_nonpos smul_min_of_nonpos

end LinearOrderedAddCommGroup
end OrderedRing

section LinearOrderedRing
variable [LinearOrderedRing α] [LinearOrderedAddCommGroup β] [Module α β] [PosSMulStrictMono α β]
  {a : α} {b : β}

lemma nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg (hab : 0 ≤ a • b) :
    0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  simp only [Decidable.or_iff_not_and_not, not_and, not_le]
  refine fun ab nab ↦ hab.not_lt ?_
  obtain ha | rfl | ha := lt_trichotomy 0 a
  exacts [smul_neg_of_pos_of_neg ha (ab ha.le), ((ab le_rfl).asymm (nab le_rfl)).elim,
    smul_neg_of_neg_of_pos ha (nab ha.le)]

lemma smul_nonneg_iff : 0 ≤ a • b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
  ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg,
    fun h ↦ h.elim (and_imp.2 smul_nonneg) (and_imp.2 smul_nonneg_of_nonpos_of_nonpos)⟩

lemma smul_nonpos_iff : a • b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  rw [← neg_nonneg, ← smul_neg, smul_nonneg_iff, neg_nonneg, neg_nonpos]

lemma smul_nonneg_iff_pos_imp_nonneg : 0 ≤ a • b ↔ (0 < a → 0 ≤ b) ∧ (0 < b → 0 ≤ a) :=
  smul_nonneg_iff.trans <| by
    simp_rw [← not_le, ← or_iff_not_imp_left]; have := le_total a 0; have := le_total b 0; tauto

lemma smul_nonneg_iff_neg_imp_nonpos : 0 ≤ a • b ↔ (a < 0 → b ≤ 0) ∧ (b < 0 → a ≤ 0) := by
  rw [← neg_smul_neg, smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

lemma smul_nonpos_iff_pos_imp_nonpos : a • b ≤ 0 ↔ (0 < a → b ≤ 0) ∧ (b < 0 → 0 ≤ a) := by
  rw [← neg_nonneg, ← smul_neg, smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

lemma smul_nonpos_iff_neg_imp_nonneg : a • b ≤ 0 ↔ (a < 0 → 0 ≤ b) ∧ (0 < b → a ≤ 0) := by
  rw [← neg_nonneg, ← neg_smul, smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

end LinearOrderedRing

section LinearOrderedSemifield
variable [LinearOrderedSemifield α] [AddCommGroup β] [PartialOrder β]

-- See note [lower instance priority]
instance (priority := 100) PosSMulMono.toPosSMulReflectLE [MulAction α β] [PosSMulMono α β] :
    PosSMulReflectLE α β where
  elim _a ha b₁ b₂ h := by simpa [ha.ne'] using smul_le_smul_of_nonneg_left h <| inv_nonneg.2 ha.le

-- See note [lower instance priority]
instance (priority := 100) PosSMulStrictMono.toPosSMulReflectLT [MulActionWithZero α β]
    [PosSMulStrictMono α β] : PosSMulReflectLT α β :=
  PosSMulReflectLT.of_pos fun a ha b₁ b₂ h ↦ by
    simpa [ha.ne'] using smul_lt_smul_of_pos_left h <| inv_pos.2 ha

end LinearOrderedSemifield

section Field
variable [LinearOrderedField α] [OrderedAddCommGroup β] [Module α β] {a : α} {b₁ b₂ : β}

section PosSMulMono
variable [PosSMulMono α β]

lemma inv_smul_le_iff_of_neg (h : a < 0) : a⁻¹ • b₁ ≤ b₂ ↔ a • b₂ ≤ b₁ := by
  rw [← smul_le_smul_iff_of_neg_left h, smul_inv_smul₀ h.ne]
#align inv_smul_le_iff_of_neg inv_smul_le_iff_of_neg

lemma smul_inv_le_iff_of_neg (h : a < 0) : b₁ ≤ a⁻¹ • b₂ ↔ b₂ ≤ a • b₁ := by
  rw [← smul_le_smul_iff_of_neg_left h, smul_inv_smul₀ h.ne]
#align smul_inv_le_iff_of_neg smul_inv_le_iff_of_neg

variable (β)

/-- Left scalar multiplication as an order isomorphism. -/
@[simps!]
def OrderIso.smulRightDual (ha : a < 0) : β ≃o βᵒᵈ where
  toEquiv := (Equiv.smulRight ha.ne).trans toDual
  map_rel_iff' := (@OrderDual.toDual_le_toDual β).trans <| smul_le_smul_iff_of_neg_left ha
#align order_iso.smul_left_dual OrderIso.smulRightDual

end PosSMulMono

variable [PosSMulStrictMono α β]

lemma inv_smul_lt_iff_of_neg (h : a < 0) : a⁻¹ • b₁ < b₂ ↔ a • b₂ < b₁ := by
  rw [← smul_lt_smul_iff_of_neg_left h, smul_inv_smul₀ h.ne]
#align inv_smul_lt_iff_of_neg inv_smul_lt_iff_of_neg

lemma smul_inv_lt_iff_of_neg (h : a < 0) : b₁ < a⁻¹ • b₂ ↔ b₂ < a • b₁ := by
  rw [← smul_lt_smul_iff_of_neg_left h, smul_inv_smul₀ h.ne]
#align smul_inv_lt_iff_of_neg smul_inv_lt_iff_of_neg

end Field

namespace Prod

end Prod

namespace Pi
variable {ι : Type*} {β : ι → Type*} [Zero α] [∀ i, Zero (β i)]

section SMulZeroClass
variable [Preorder α] [∀ i, Preorder (β i)] [∀ i, SMulZeroClass α (β i)]

instance instPosSMulMono [∀ i, PosSMulMono α (β i)] : PosSMulMono α (∀ i, β i) where
  elim _a ha _b₁ _b₂ hb i := smul_le_smul_of_nonneg_left (hb i) ha

instance instSMulPosMono [∀ i, SMulPosMono α (β i)] : SMulPosMono α (∀ i, β i) where
  elim _b hb _a₁ _a₂ ha i := smul_le_smul_of_nonneg_right ha (hb i)

instance instPosSMulReflectLE [∀ i, PosSMulReflectLE α (β i)] : PosSMulReflectLE α (∀ i, β i) where
  elim _a ha _b₁ _b₂ h i := le_of_smul_le_smul_left (h i) ha

instance instSMulPosReflectLE [∀ i, SMulPosReflectLE α (β i)] : SMulPosReflectLE α (∀ i, β i) where
  elim _b hb _a₁ _a₂ h := by
    obtain ⟨-, i, hi⟩ := lt_def.1 hb; exact le_of_smul_le_smul_right (h _) hi

end SMulZeroClass

section SMulWithZero
variable [PartialOrder α] [∀ i, PartialOrder (β i)] [∀ i, SMulWithZero α (β i)]

instance instPosSMulStrictMono [∀ i, PosSMulStrictMono α (β i)] :
    PosSMulStrictMono α (∀ i, β i) where
  elim := by
    simp_rw [lt_def]
    rintro _a ha _b₁ _b₂ ⟨hb, i, hi⟩
    exact ⟨smul_le_smul_of_nonneg_left hb ha.le, i, smul_lt_smul_of_pos_left hi ha⟩

instance instSMulPosStrictMono [∀ i, SMulPosStrictMono α (β i)] :
    SMulPosStrictMono α (∀ i, β i) where
  elim := by
    simp_rw [lt_def]
    rintro a ⟨ha, i, hi⟩ _b₁ _b₂ hb
    exact ⟨smul_le_smul_of_nonneg_right hb.le ha, i, smul_lt_smul_of_pos_right hb hi⟩

-- Note: There is no interesting instance for `PosSMulReflectLT α (∀ i, β i)` that's not already
-- implied by the other instances

instance instSMulPosReflectLT [∀ i, SMulPosReflectLT α (β i)] : SMulPosReflectLT α (∀ i, β i) where
  elim := by
    simp_rw [lt_def]
    rintro b hb _a₁ _a₂ ⟨-, i, hi⟩
    exact lt_of_smul_lt_smul_right hi <| hb _

end SMulWithZero
end Pi

section Lift
variable {γ : Type*} [Zero α] [Preorder α] [Zero β] [Preorder β] [Zero γ] [Preorder γ]
  [SMul α β] [SMul α γ] (f : β → γ) (hf : ∀ {b₁ b₂}, f b₁ ≤ f b₂ ↔ b₁ ≤ b₂)
  (smul : ∀ (a : α) b, f (a • b) = a • f b) (zero : f 0 = 0)

lemma PosSMulMono.lift [PosSMulMono α γ] : PosSMulMono α β where
  elim a ha b₁ b₂ hb := by simp only [← hf, smul] at *; exact smul_le_smul_of_nonneg_left hb ha

lemma PosSMulStrictMono.lift [PosSMulStrictMono α γ] : PosSMulStrictMono α β where
  elim a ha b₁ b₂ hb := by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, smul] at *; exact smul_lt_smul_of_pos_left hb ha

lemma PosSMulReflectLE.lift [PosSMulReflectLE α γ] : PosSMulReflectLE α β where
  elim a ha b₁ b₂ h := hf.1 <| le_of_smul_le_smul_left (by simpa only [smul] using hf.2 h) ha

lemma PosSMulReflectLT.lift [PosSMulReflectLT α γ] : PosSMulReflectLT α β where
  elim a ha b₁ b₂ h := by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, smul] at *; exact lt_of_smul_lt_smul_left h ha

lemma SMulPosMono.lift [SMulPosMono α γ] : SMulPosMono α β where
  elim b hb a₁ a₂ ha := by
    simp only [← hf, zero, smul] at *; exact smul_le_smul_of_nonneg_right ha hb

lemma SMulPosStrictMono.lift [SMulPosStrictMono α γ] : SMulPosStrictMono α β where
  elim b hb a₁ a₂ ha := by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact smul_lt_smul_of_pos_right ha hb

lemma SMulPosReflectLE.lift [SMulPosReflectLE α γ] : SMulPosReflectLE α β where
  elim b hb a₁ a₂ h := by
    simp only [← hf, ← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact le_of_smul_le_smul_right h hb

lemma SMulPosReflectLT.lift [SMulPosReflectLT α γ] : SMulPosReflectLT α β where
  elim b hb a₁ a₂ h := by
    simp only [← hf, ← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact lt_of_smul_lt_smul_right h hb

end Lift

section Nat

instance OrderedSemiring.toPosSMulMonoNat [OrderedSemiring α] : PosSMulMono ℕ α where
  elim _n _ _a _b hab := nsmul_le_nsmul_right hab _

instance OrderedSemiring.toSMulPosMonoNat [OrderedSemiring α] : SMulPosMono ℕ α where
  elim _a ha _m _n hmn := nsmul_le_nsmul_left ha hmn

instance StrictOrderedSemiring.toPosSMulStrictMonoNat [StrictOrderedSemiring α] :
    PosSMulStrictMono ℕ α where
  elim _n hn _a _b hab := nsmul_right_strictMono hn.ne' hab

instance StrictOrderedSemiring.toSMulPosStrictMonoNat [StrictOrderedSemiring α] :
    SMulPosStrictMono ℕ α where
  elim _a ha _m _n hmn := nsmul_lt_nsmul_left ha hmn

end Nat

-- TODO: Instances for `Int` and `Rat`

namespace Mathlib.Meta.Positivity
section OrderedSMul
variable [Zero α] [Zero β] [SMulZeroClass α β] [Preorder α] [Preorder β] [PosSMulMono α β] {a : α}
  {b : β}

private theorem smul_nonneg_of_pos_of_nonneg (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a • b :=
  smul_nonneg ha.le hb

private theorem smul_nonneg_of_nonneg_of_pos (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a • b :=
  smul_nonneg ha hb.le

end OrderedSMul

section NoZeroSMulDivisors
variable [Zero α] [Zero β] [SMul α β] [NoZeroSMulDivisors α β] {a : α} {b : β}

private theorem smul_ne_zero_of_pos_of_ne_zero [Preorder α] (ha : 0 < a) (hb : b ≠ 0) : a • b ≠ 0 :=
  smul_ne_zero ha.ne' hb

private theorem smul_ne_zero_of_ne_zero_of_pos [Preorder β] (ha : a ≠ 0) (hb : 0 < b) : a • b ≠ 0 :=
  smul_ne_zero ha hb.ne'

end NoZeroSMulDivisors

open Lean.Meta Qq

/-- Positivity extension for HSMul, i.e. (_ • _).  -/
@[positivity HSMul.hSMul _ _]
def evalHSMul : PositivityExt where eval {_u α} zα pα (e : Q($α)) := do
  let .app (.app (.app (.app (.app (.app
        (.const ``HSMul.hSMul [u1, _, _]) (β : Q(Type u1))) _) _) _)
          (a : Q($β))) (b : Q($α)) ← whnfR e | throwError "failed to match hSMul"
  let zM : Q(Zero $β) ← synthInstanceQ q(Zero $β)
  let pM : Q(PartialOrder $β) ← synthInstanceQ q(PartialOrder $β)
  -- Using `q()` here would be impractical, as we would have to manually `synthInstanceQ` all the
  -- required typeclasses. Ideally we could tell `q()` to do this automatically.
  match ← core zM pM a, ← core zα pα b with
  | .positive pa, .positive pb =>
      pure (.positive (← mkAppM ``smul_pos #[pa, pb]))
  | .positive pa, .nonnegative pb =>
      pure (.nonnegative (← mkAppM ``smul_nonneg_of_pos_of_nonneg #[pa, pb]))
  | .nonnegative pa, .positive pb =>
      pure (.nonnegative (← mkAppM ``smul_nonneg_of_nonneg_of_pos #[pa, pb]))
  | .nonnegative pa, .nonnegative pb =>
      pure (.nonnegative (← mkAppM ``smul_nonneg #[pa, pb]))
  | .positive pa, .nonzero pb =>
      pure (.nonzero (← mkAppM ``smul_ne_zero_of_pos_of_ne_zero #[pa, pb]))
  | .nonzero pa, .positive pb =>
      pure (.nonzero (← mkAppM ``smul_ne_zero_of_ne_zero_of_pos #[pa, pb]))
  | .nonzero pa, .nonzero pb =>
      pure (.nonzero (← mkAppM ``smul_ne_zero #[pa, pb]))
  | _, _ => pure .none

end Mathlib.Meta.Positivity

/-!
### Deprecated lemmas

Those lemmas have been deprecated on 2023-12-23.
-/

@[deprecated] alias monotone_smul_left := monotone_smul_left_of_nonneg
@[deprecated] alias strict_mono_smul_left := strictMono_smul_left_of_pos
@[deprecated] alias smul_le_smul_of_nonneg := smul_le_smul_of_nonneg_left
@[deprecated] alias smul_lt_smul_of_pos := smul_lt_smul_of_pos_left
@[deprecated] alias lt_of_smul_lt_smul_of_nonneg := lt_of_smul_lt_smul_of_nonneg_left
@[deprecated] alias smul_le_smul_iff_of_pos := smul_le_smul_iff_of_pos_left
@[deprecated] alias smul_lt_smul_iff_of_pos := smul_lt_smul_iff_of_pos_left
@[deprecated] alias smul_max := smul_max_of_nonneg
@[deprecated] alias smul_min := smul_min_of_nonneg
@[deprecated] alias smul_pos_iff_of_pos := smul_pos_iff_of_pos_left
@[deprecated] alias inv_smul_le_iff := inv_smul_le_iff_of_pos
@[deprecated] alias le_inv_smul_iff := le_inv_smul_iff_of_pos
@[deprecated] alias inv_smul_lt_iff := inv_smul_lt_iff_of_pos
@[deprecated] alias lt_inv_smul_iff := lt_inv_smul_iff_of_pos
@[deprecated] alias OrderIso.smulLeft := OrderIso.smulRight
@[deprecated] alias OrderIso.smulLeft_symm_apply := OrderIso.smulRight_symm_apply
@[deprecated] alias OrderIso.smulLeft_apply := OrderIso.smulRight_apply
@[deprecated] alias smul_neg_iff_of_pos := smul_neg_iff_of_pos_left

/-!
Those lemmas have been deprecated on 2023-12-27.
-/

@[deprecated] alias strict_anti_smul_left := strictAnti_smul_left
@[deprecated] alias smul_le_smul_of_nonpos := smul_le_smul_of_nonpos_left
@[deprecated] alias smul_lt_smul_of_neg := smul_lt_smul_of_neg_left
@[deprecated] alias smul_pos_iff_of_neg := smul_pos_iff_of_neg_left
@[deprecated] alias smul_neg_iff_of_neg := smul_neg_iff_of_neg_left
@[deprecated] alias smul_le_smul_iff_of_neg := smul_le_smul_iff_of_neg_left
@[deprecated] alias smul_lt_smul_iff_of_neg := smul_lt_smul_iff_of_neg_left
