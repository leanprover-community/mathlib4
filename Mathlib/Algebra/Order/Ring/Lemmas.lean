/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
import Mathlib.Tactic.Rewrites
import Mathlib.Algebra.CovariantAndContravariant
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Order.Monoid.NatCast


#align_import algebra.order.ring.lemmas from "leanprover-community/mathlib"@"44e29dbcff83ba7114a464d592b8c3743987c1e5"

/-!
# Monotonicity of multiplication by positive elements

This file defines typeclasses to reason about monotonicity of the operations
* `b ↦ a * b`, "left multiplication"
* `a ↦ a * b`, "right multiplication"

We use eight typeclasses to encode the various properties we care about for those two operations.
These typeclasses are meant to be mostly internal to this file, to set up each lemma in the
appropriate generality.

Less granular typeclasses like `OrderedAddCommMonoid`, `LinearOrderedField`` should be enough for
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


variable (α : Type*)

set_option quotPrecheck false in
/-- Local notation for the nonnegative elements of a type `α`. TODO: actually make local. -/
notation "α≥0" => { x : α // 0 ≤ x }

set_option quotPrecheck false in
/-- Local notation for the positive elements of a type `α`. TODO: actually make local. -/
notation "α>0" => { x : α // 0 < x }

section Abbreviations

variable [Mul α] [Zero α] [Preorder α]

/-- Typeclass for monotonicity of multiplication by nonnegative elements on the left,
namely `b₁ ≤ b₂ → a * b₁ ≤ a * b₂` if `0 ≤ a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSemiring`. -/
abbrev PosMulMono : Prop :=
  CovariantClass α≥0 α (fun x y => x * y) (· ≤ ·)
#align pos_mul_mono PosMulMono

/-- Typeclass for monotonicity of multiplication by nonnegative elements on the right,
namely `a₁ ≤ a₂ → a₁ * b ≤ a₂ * b` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedSemiring`. -/
abbrev MulPosMono : Prop :=
  CovariantClass α≥0 α (fun x y => y * x) (· ≤ ·)
#align mul_pos_mono MulPosMono

/-- Typeclass for strict monotonicity of multiplication by positive elements on the left,
namely `b₁ < b₂ → a * b₁ < a * b₂` if `0 < a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`StrictOrderedSemiring`. -/
abbrev PosMulStrictMono : Prop :=
  CovariantClass α>0 α (fun x y => x * y) (· < ·)
#align pos_mul_strict_mono PosMulStrictMono

/-- Typeclass for strict monotonicity of multiplication by positive elements on the right,
namely `a₁ < a₂ → a₁ * b < a₂ * b` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`StrictOrderedSemiring`. -/
abbrev MulPosStrictMono : Prop :=
  CovariantClass α>0 α (fun x y => y * x) (· < ·)
#align mul_pos_strict_mono MulPosStrictMono

/-- Typeclass for strict reverse monotonicity of multiplication by nonnegative elements on
the left, namely `a * b₁ < a * b₂ → b₁ < b₂` if `0 ≤ a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
abbrev PosMulReflectLT : Prop :=
  ContravariantClass α≥0 α (fun x y => x * y) (· < ·)
#align pos_mul_reflect_lt PosMulReflectLT

/-- Typeclass for strict reverse monotonicity of multiplication by nonnegative elements on
the right, namely `a₁ * b < a₂ * b → a₁ < a₂` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
abbrev MulPosReflectLT : Prop :=
  ContravariantClass α≥0 α (fun x y => y * x) (· < ·)
#align mul_pos_reflect_lt MulPosReflectLT

/-- Typeclass for reverse monotonicity of multiplication by positive elements on the left,
namely `a * b₁ ≤ a * b₂ → b₁ ≤ b₂` if `0 < a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
abbrev PosMulReflectLE : Prop :=
  ContravariantClass α>0 α (fun x y => x * y) (· ≤ ·)
#align pos_mul_mono_rev PosMulReflectLE

/-- Typeclass for reverse monotonicity of multiplication by positive elements on the right,
namely `a₁ * b ≤ a₂ * b → a₁ ≤ a₂` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`LinearOrderedSemiring`. -/
abbrev MulPosReflectLE : Prop :=
  ContravariantClass α>0 α (fun x y => y * x) (· ≤ ·)
#align mul_pos_mono_rev MulPosReflectLE

end Abbreviations

variable {α} {a b c d : α}

section MulZero

variable [Mul α] [Zero α]

section Preorder

variable [Preorder α]

instance PosMulMono.to_covariantClass_pos_mul_le [PosMulMono α] :
    CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) :=
  ⟨fun a _ _ bc => @CovariantClass.elim α≥0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, a.2.le⟩ _ _ bc⟩
#align pos_mul_mono.to_covariant_class_pos_mul_le PosMulMono.to_covariantClass_pos_mul_le

instance MulPosMono.to_covariantClass_pos_mul_le [MulPosMono α] :
    CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) :=
  ⟨fun a _ _ bc => @CovariantClass.elim α≥0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, a.2.le⟩ _ _ bc⟩
#align mul_pos_mono.to_covariant_class_pos_mul_le MulPosMono.to_covariantClass_pos_mul_le

instance PosMulReflectLT.to_contravariantClass_pos_mul_lt [PosMulReflectLT α] :
    ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨fun a _ _ bc => @ContravariantClass.elim α≥0 α (fun x y => x * y) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩
#align pos_mul_reflect_lt.to_contravariant_class_pos_mul_lt PosMulReflectLT.to_contravariantClass_pos_mul_lt

instance MulPosReflectLT.to_contravariantClass_pos_mul_lt [MulPosReflectLT α] :
    ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨fun a _ _ bc => @ContravariantClass.elim α≥0 α (fun x y => y * x) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩
#align mul_pos_reflect_lt.to_contravariant_class_pos_mul_lt MulPosReflectLT.to_contravariantClass_pos_mul_lt

theorem mul_le_mul_of_nonneg_left [PosMulMono α] (h : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c :=
  @CovariantClass.elim α≥0 α (fun x y => x * y) (· ≤ ·) _ ⟨a, a0⟩ _ _ h
#align mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_left

theorem mul_le_mul_of_nonneg_right [MulPosMono α] (h : b ≤ c) (a0 : 0 ≤ a) : b * a ≤ c * a :=
  @CovariantClass.elim α≥0 α (fun x y => y * x) (· ≤ ·) _ ⟨a, a0⟩ _ _ h
#align mul_le_mul_of_nonneg_right mul_le_mul_of_nonneg_right

theorem mul_lt_mul_of_pos_left [PosMulStrictMono α] (bc : b < c) (a0 : 0 < a) : a * b < a * c :=
  @CovariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ bc
#align mul_lt_mul_of_pos_left mul_lt_mul_of_pos_left

theorem mul_lt_mul_of_pos_right [MulPosStrictMono α] (bc : b < c) (a0 : 0 < a) : b * a < c * a :=
  @CovariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ bc
#align mul_lt_mul_of_pos_right mul_lt_mul_of_pos_right

theorem lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a * b < a * c) (a0 : 0 ≤ a) : b < c :=
  @ContravariantClass.elim α≥0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ h
#align lt_of_mul_lt_mul_left lt_of_mul_lt_mul_left

theorem lt_of_mul_lt_mul_right [MulPosReflectLT α] (h : b * a < c * a) (a0 : 0 ≤ a) : b < c :=
  @ContravariantClass.elim α≥0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ h
#align lt_of_mul_lt_mul_right lt_of_mul_lt_mul_right

theorem le_of_mul_le_mul_left [PosMulReflectLE α] (bc : a * b ≤ a * c) (a0 : 0 < a) : b ≤ c :=
  @ContravariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc
#align le_of_mul_le_mul_left le_of_mul_le_mul_left

theorem le_of_mul_le_mul_right [MulPosReflectLE α] (bc : b * a ≤ c * a) (a0 : 0 < a) : b ≤ c :=
  @ContravariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc
#align le_of_mul_le_mul_right le_of_mul_le_mul_right

alias lt_of_mul_lt_mul_of_nonneg_left := lt_of_mul_lt_mul_left
#align lt_of_mul_lt_mul_of_nonneg_left lt_of_mul_lt_mul_of_nonneg_left

alias lt_of_mul_lt_mul_of_nonneg_right := lt_of_mul_lt_mul_right
#align lt_of_mul_lt_mul_of_nonneg_right lt_of_mul_lt_mul_of_nonneg_right

alias le_of_mul_le_mul_of_pos_left := le_of_mul_le_mul_left
#align le_of_mul_le_mul_of_pos_left le_of_mul_le_mul_of_pos_left

alias le_of_mul_le_mul_of_pos_right := le_of_mul_le_mul_right
#align le_of_mul_le_mul_of_pos_right le_of_mul_le_mul_of_pos_right

@[simp]
theorem mul_lt_mul_left [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a * c ↔ b < c :=
  @rel_iff_cov α>0 α (fun x y => x * y) (· < ·) _ _ ⟨a, a0⟩ _ _
#align mul_lt_mul_left mul_lt_mul_left

@[simp]
theorem mul_lt_mul_right [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    b * a < c * a ↔ b < c :=
  @rel_iff_cov α>0 α (fun x y => y * x) (· < ·) _ _ ⟨a, a0⟩ _ _
#align mul_lt_mul_right mul_lt_mul_right

@[simp]
theorem mul_le_mul_left [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c :=
  @rel_iff_cov α>0 α (fun x y => x * y) (· ≤ ·) _ _ ⟨a, a0⟩ _ _
#align mul_le_mul_left mul_le_mul_left

@[simp]
theorem mul_le_mul_right [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) : b * a ≤ c * a ↔ b ≤ c :=
  @rel_iff_cov α>0 α (fun x y => y * x) (· ≤ ·) _ _ ⟨a, a0⟩ _ _
#align mul_le_mul_right mul_le_mul_right

theorem mul_lt_mul_of_pos_of_nonneg [PosMulStrictMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c < d)
    (a0 : 0 < a) (d0 : 0 ≤ d) : a * c < b * d :=
  (mul_lt_mul_of_pos_left h₂ a0).trans_le (mul_le_mul_of_nonneg_right h₁ d0)
#align mul_lt_mul_of_pos_of_nonneg mul_lt_mul_of_pos_of_nonneg

theorem mul_lt_mul_of_le_of_le' [PosMulStrictMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c < d)
    (b0 : 0 < b) (c0 : 0 ≤ c) : a * c < b * d :=
  (mul_le_mul_of_nonneg_right h₁ c0).trans_lt (mul_lt_mul_of_pos_left h₂ b0)
#align mul_lt_mul_of_le_of_le' mul_lt_mul_of_le_of_le'

theorem mul_lt_mul_of_nonneg_of_pos [PosMulMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c ≤ d)
    (a0 : 0 ≤ a) (d0 : 0 < d) : a * c < b * d :=
  (mul_le_mul_of_nonneg_left h₂ a0).trans_lt (mul_lt_mul_of_pos_right h₁ d0)
#align mul_lt_mul_of_nonneg_of_pos mul_lt_mul_of_nonneg_of_pos

theorem mul_lt_mul_of_le_of_lt' [PosMulMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c ≤ d)
    (b0 : 0 ≤ b) (c0 : 0 < c) : a * c < b * d :=
  (mul_lt_mul_of_pos_right h₁ c0).trans_le (mul_le_mul_of_nonneg_left h₂ b0)
#align mul_lt_mul_of_le_of_lt' mul_lt_mul_of_le_of_lt'

theorem mul_lt_mul_of_pos_of_pos [PosMulStrictMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c < d)
    (a0 : 0 < a) (d0 : 0 < d) : a * c < b * d :=
  (mul_lt_mul_of_pos_left h₂ a0).trans (mul_lt_mul_of_pos_right h₁ d0)
#align mul_lt_mul_of_pos_of_pos mul_lt_mul_of_pos_of_pos

theorem mul_lt_mul_of_lt_of_lt' [PosMulStrictMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c < d)
    (b0 : 0 < b) (c0 : 0 < c) : a * c < b * d :=
  (mul_lt_mul_of_pos_right h₁ c0).trans (mul_lt_mul_of_pos_left h₂ b0)
#align mul_lt_mul_of_lt_of_lt' mul_lt_mul_of_lt_of_lt'

theorem mul_lt_of_mul_lt_of_nonneg_left [PosMulMono α] (h : a * b < c) (hdb : d ≤ b) (ha : 0 ≤ a) :
    a * d < c :=
  (mul_le_mul_of_nonneg_left hdb ha).trans_lt h
#align mul_lt_of_mul_lt_of_nonneg_left mul_lt_of_mul_lt_of_nonneg_left

theorem lt_mul_of_lt_mul_of_nonneg_left [PosMulMono α] (h : a < b * c) (hcd : c ≤ d) (hb : 0 ≤ b) :
    a < b * d :=
  h.trans_le <| mul_le_mul_of_nonneg_left hcd hb
#align lt_mul_of_lt_mul_of_nonneg_left lt_mul_of_lt_mul_of_nonneg_left

theorem mul_lt_of_mul_lt_of_nonneg_right [MulPosMono α] (h : a * b < c) (hda : d ≤ a) (hb : 0 ≤ b) :
    d * b < c :=
  (mul_le_mul_of_nonneg_right hda hb).trans_lt h
#align mul_lt_of_mul_lt_of_nonneg_right mul_lt_of_mul_lt_of_nonneg_right

theorem lt_mul_of_lt_mul_of_nonneg_right [MulPosMono α] (h : a < b * c) (hbd : b ≤ d) (hc : 0 ≤ c) :
    a < d * c :=
  h.trans_le <| mul_le_mul_of_nonneg_right hbd hc
#align lt_mul_of_lt_mul_of_nonneg_right lt_mul_of_lt_mul_of_nonneg_right

end Preorder

section LinearOrder

variable [LinearOrder α]

-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosMulReflectLE [PosMulStrictMono α] :
    PosMulReflectLE α :=
  ⟨(covariant_lt_iff_contravariant_le _ _ _).1 CovariantClass.elim⟩

-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toMulPosReflectLE [MulPosStrictMono α] :
    MulPosReflectLE α :=
  ⟨(covariant_lt_iff_contravariant_le _ _ _).1 CovariantClass.elim⟩

theorem PosMulReflectLE.toPosMulStrictMono [PosMulReflectLE α] : PosMulStrictMono α :=
  ⟨(covariant_lt_iff_contravariant_le _ _ _).2 ContravariantClass.elim⟩
#align pos_mul_mono_rev.to_pos_mul_strict_mono PosMulReflectLE.toPosMulStrictMono

theorem MulPosReflectLE.toMulPosStrictMono [MulPosReflectLE α] : MulPosStrictMono α :=
  ⟨(covariant_lt_iff_contravariant_le _ _ _).2 ContravariantClass.elim⟩
#align mul_pos_mono_rev.to_mul_pos_strict_mono MulPosReflectLE.toMulPosStrictMono

theorem posMulStrictMono_iff_posMulReflectLE : PosMulStrictMono α ↔ PosMulReflectLE α :=
  ⟨@PosMulStrictMono.toPosMulReflectLE _ _ _ _, @PosMulReflectLE.toPosMulStrictMono _ _ _ _⟩
#align pos_mul_strict_mono_iff_pos_mul_mono_rev posMulStrictMono_iff_posMulReflectLE

theorem mulPosStrictMono_iff_mulPosReflectLE : MulPosStrictMono α ↔ MulPosReflectLE α :=
  ⟨@MulPosStrictMono.toMulPosReflectLE _ _ _ _, @MulPosReflectLE.toMulPosStrictMono _ _ _ _⟩
#align mul_pos_strict_mono_iff_mul_pos_mono_rev mulPosStrictMono_iff_mulPosReflectLE

theorem PosMulReflectLT.toPosMulMono [PosMulReflectLT α] : PosMulMono α :=
  ⟨(covariant_le_iff_contravariant_lt _ _ _).2 ContravariantClass.elim⟩
#align pos_mul_reflect_lt.to_pos_mul_mono PosMulReflectLT.toPosMulMono

theorem MulPosReflectLT.toMulPosMono [MulPosReflectLT α] : MulPosMono α :=
  ⟨(covariant_le_iff_contravariant_lt _ _ _).2 ContravariantClass.elim⟩
#align mul_pos_reflect_lt.to_mul_pos_mono MulPosReflectLT.toMulPosMono

theorem PosMulMono.toPosMulReflectLT [PosMulMono α] : PosMulReflectLT α :=
  ⟨(covariant_le_iff_contravariant_lt _ _ _).1 CovariantClass.elim⟩
#align pos_mul_mono.to_pos_mul_reflect_lt PosMulMono.toPosMulReflectLT

theorem MulPosMono.toMulPosReflectLT [MulPosMono α] : MulPosReflectLT α :=
  ⟨(covariant_le_iff_contravariant_lt _ _ _).1 CovariantClass.elim⟩
#align mul_pos_mono.to_mul_pos_reflect_lt MulPosMono.toMulPosReflectLT

/- TODO: Currently, only one in four of the above are made instances; we could consider making
  both directions of `covariant_le_iff_contravariant_lt` and `covariant_lt_iff_contravariant_le`
  instances, then all of the above become redundant instances, but there are performance issues. -/

theorem posMulMono_iff_posMulReflectLT : PosMulMono α ↔ PosMulReflectLT α :=
  ⟨@PosMulMono.toPosMulReflectLT _ _ _ _, @PosMulReflectLT.toPosMulMono _ _ _ _⟩
#align pos_mul_mono_iff_pos_mul_reflect_lt posMulMono_iff_posMulReflectLT

theorem mulPosMono_iff_mulPosReflectLT : MulPosMono α ↔ MulPosReflectLT α :=
  ⟨@MulPosMono.toMulPosReflectLT _ _ _ _, @MulPosReflectLT.toMulPosMono _ _ _ _⟩
#align mul_pos_mono_iff_mul_pos_reflect_lt mulPosMono_iff_mulPosReflectLT

end LinearOrder

end MulZero

section MulZeroClass

variable [MulZeroClass α]

section Preorder

variable [Preorder α]

/-- Assumes left covariance. -/
theorem Left.mul_pos [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha
#align left.mul_pos Left.mul_pos

alias mul_pos := Left.mul_pos
#align mul_pos mul_pos

theorem mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha
#align mul_neg_of_pos_of_neg mul_neg_of_pos_of_neg

@[simp]
theorem zero_lt_mul_left [PosMulStrictMono α] [PosMulReflectLT α] (h : 0 < c) :
    0 < c * b ↔ 0 < b := by
  rw [← mul_zero c, mul_lt_mul_left h]
  simp
#align zero_lt_mul_left zero_lt_mul_left

/-- Assumes right covariance. -/
theorem Right.mul_pos [MulPosStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb
#align right.mul_pos Right.mul_pos

theorem mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb
#align mul_neg_of_neg_of_pos mul_neg_of_neg_of_pos

@[simp]
theorem zero_lt_mul_right [MulPosStrictMono α] [MulPosReflectLT α] (h : 0 < c) :
    0 < b * c ↔ 0 < b := by
  rw [← zero_mul c, mul_lt_mul_right h]
  simp
#align zero_lt_mul_right zero_lt_mul_right

/-- Assumes left covariance. -/
theorem Left.mul_nonneg [PosMulMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha
#align left.mul_nonneg Left.mul_nonneg

alias mul_nonneg := Left.mul_nonneg
#align mul_nonneg mul_nonneg

theorem mul_nonpos_of_nonneg_of_nonpos [PosMulMono α] (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha
#align mul_nonpos_of_nonneg_of_nonpos mul_nonpos_of_nonneg_of_nonpos

/-- Assumes right covariance. -/
theorem Right.mul_nonneg [MulPosMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb
#align right.mul_nonneg Right.mul_nonneg

theorem mul_nonpos_of_nonpos_of_nonneg [MulPosMono α] (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb
#align mul_nonpos_of_nonpos_of_nonneg mul_nonpos_of_nonpos_of_nonneg

theorem pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b :=
  lt_of_mul_lt_mul_left ((mul_zero a).symm ▸ h : a * 0 < a * b) ha
#align pos_of_mul_pos_right pos_of_mul_pos_right

theorem pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a :=
  lt_of_mul_lt_mul_right ((zero_mul b).symm ▸ h : 0 * b < a * b) hb
#align pos_of_mul_pos_left pos_of_mul_pos_left

theorem pos_iff_pos_of_mul_pos [PosMulReflectLT α] [MulPosReflectLT α] (hab : 0 < a * b) :
    0 < a ↔ 0 < b :=
  ⟨pos_of_mul_pos_right hab ∘ le_of_lt, pos_of_mul_pos_left hab ∘ le_of_lt⟩
#align pos_iff_pos_of_mul_pos pos_iff_pos_of_mul_pos

theorem mul_le_mul_of_le_of_le [PosMulMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (a0 : 0 ≤ a)
    (d0 : 0 ≤ d) : a * c ≤ b * d :=
  (mul_le_mul_of_nonneg_left h₂ a0).trans <| mul_le_mul_of_nonneg_right h₁ d0
#align mul_le_mul_of_le_of_le mul_le_mul_of_le_of_le

theorem mul_le_mul [PosMulMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (c0 : 0 ≤ c)
    (b0 : 0 ≤ b) : a * c ≤ b * d :=
  (mul_le_mul_of_nonneg_right h₁ c0).trans <| mul_le_mul_of_nonneg_left h₂ b0
#align mul_le_mul mul_le_mul

theorem mul_self_le_mul_self [PosMulMono α] [MulPosMono α] (ha : 0 ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b :=
  mul_le_mul hab hab ha <| ha.trans hab
#align mul_self_le_mul_self mul_self_le_mul_self

theorem mul_le_of_mul_le_of_nonneg_left [PosMulMono α] (h : a * b ≤ c) (hle : d ≤ b)
    (a0 : 0 ≤ a) : a * d ≤ c :=
  (mul_le_mul_of_nonneg_left hle a0).trans h
#align mul_le_of_mul_le_of_nonneg_left mul_le_of_mul_le_of_nonneg_left

theorem le_mul_of_le_mul_of_nonneg_left [PosMulMono α] (h : a ≤ b * c) (hle : c ≤ d)
    (b0 : 0 ≤ b) : a ≤ b * d :=
  h.trans (mul_le_mul_of_nonneg_left hle b0)
#align le_mul_of_le_mul_of_nonneg_left le_mul_of_le_mul_of_nonneg_left

theorem mul_le_of_mul_le_of_nonneg_right [MulPosMono α] (h : a * b ≤ c) (hle : d ≤ a)
    (b0 : 0 ≤ b) : d * b ≤ c :=
  (mul_le_mul_of_nonneg_right hle b0).trans h
#align mul_le_of_mul_le_of_nonneg_right mul_le_of_mul_le_of_nonneg_right

theorem le_mul_of_le_mul_of_nonneg_right [MulPosMono α] (h : a ≤ b * c) (hle : b ≤ d)
    (c0 : 0 ≤ c) : a ≤ d * c :=
  h.trans (mul_le_mul_of_nonneg_right hle c0)
#align le_mul_of_le_mul_of_nonneg_right le_mul_of_le_mul_of_nonneg_right

end Preorder

section PartialOrder

variable [PartialOrder α]

theorem posMulMono_iff_covariant_pos :
    PosMulMono α ↔ CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) :=
  ⟨@PosMulMono.to_covariantClass_pos_mul_le _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_lt
      · simp [← ha]
      · exact @CovariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, ha⟩ _ _ h ⟩⟩
#align pos_mul_mono_iff_covariant_pos posMulMono_iff_covariant_pos

theorem mulPosMono_iff_covariant_pos :
    MulPosMono α ↔ CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) :=
  ⟨@MulPosMono.to_covariantClass_pos_mul_le _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_lt
      · simp [← ha]
      · exact @CovariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, ha⟩ _ _ h ⟩⟩
#align mul_pos_mono_iff_covariant_pos mulPosMono_iff_covariant_pos

theorem posMulReflectLT_iff_contravariant_pos :
    PosMulReflectLT α ↔ ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨@PosMulReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_lt
      · simp [← ha] at h
      · exact @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨_, ha⟩ _ _ h ⟩⟩
#align pos_mul_reflect_lt_iff_contravariant_pos posMulReflectLT_iff_contravariant_pos

theorem mulPosReflectLT_iff_contravariant_pos :
    MulPosReflectLT α ↔ ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨@MulPosReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_lt
      · simp [← ha] at h
      · exact @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨_, ha⟩ _ _ h ⟩⟩
#align mul_pos_reflect_lt_iff_contravariant_pos mulPosReflectLT_iff_contravariant_pos

-- Porting note: mathlib3 proofs would look like `StrictMono.monotone <| @CovariantClass.elim ..`
-- but implicit argument handling causes that to break
-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosMulMono [PosMulStrictMono α] : PosMulMono α :=
  posMulMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)
#align pos_mul_strict_mono.to_pos_mul_mono PosMulStrictMono.toPosMulMono

-- Porting note: mathlib3 proofs would look like `StrictMono.monotone <| @CovariantClass.elim ..`
-- but implicit argument handling causes that to break
-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toMulPosMono [MulPosStrictMono α] : MulPosMono α :=
  mulPosMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)
#align mul_pos_strict_mono.to_mul_pos_mono MulPosStrictMono.toMulPosMono

-- see Note [lower instance priority]
instance (priority := 100) PosMulReflectLE.toPosMulReflectLT [PosMulReflectLE α] :
    PosMulReflectLT α :=
  posMulReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_left h.le a.2).lt_of_ne <| by
        rintro rfl
        simp at h⟩
#align pos_mul_mono_rev.to_pos_mul_reflect_lt PosMulReflectLE.toPosMulReflectLT

-- see Note [lower instance priority]
instance (priority := 100) MulPosReflectLE.toMulPosReflectLT [MulPosReflectLE α] :
    MulPosReflectLT α :=
  mulPosReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_right h.le a.2).lt_of_ne <| by
        rintro rfl
        simp at h⟩
#align mul_pos_mono_rev.to_mul_pos_reflect_lt MulPosReflectLE.toMulPosReflectLT

theorem mul_left_cancel_iff_of_pos [PosMulReflectLE α] (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_left h.le a0).antisymm <|
    le_of_mul_le_mul_of_pos_left h.ge a0, congr_arg _⟩
#align mul_left_cancel_iff_of_pos mul_left_cancel_iff_of_pos

theorem mul_right_cancel_iff_of_pos [MulPosReflectLE α] (b0 : 0 < b) : a * b = c * b ↔ a = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_right h.le b0).antisymm <|
    le_of_mul_le_mul_of_pos_right h.ge b0, congr_arg (· * b)⟩
#align mul_right_cancel_iff_of_pos mul_right_cancel_iff_of_pos

theorem mul_eq_mul_iff_eq_and_eq_of_pos [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a ≤ b) (hcd : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine' ⟨fun h ↦ _, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine' ⟨fun hab ↦ h.not_lt _, fun hcd ↦ h.not_lt _⟩
  · exact (mul_le_mul_of_nonneg_left hcd a0.le).trans_lt (mul_lt_mul_of_pos_right hab d0)
  · exact (mul_lt_mul_of_pos_left hcd a0).trans_le (mul_le_mul_of_nonneg_right hab d0.le)
#align mul_eq_mul_iff_eq_and_eq_of_pos mul_eq_mul_iff_eq_and_eq_of_pos

theorem mul_eq_mul_iff_eq_and_eq_of_pos' [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a ≤ b) (hcd : c ≤ d) (b0 : 0 < b) (c0 : 0 < c) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine' ⟨fun h ↦ _, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine' ⟨fun hab ↦ h.not_lt _, fun hcd ↦ h.not_lt _⟩
  · exact (mul_lt_mul_of_pos_right hab c0).trans_le (mul_le_mul_of_nonneg_left hcd b0.le)
  · exact (mul_le_mul_of_nonneg_right hab c0.le).trans_lt (mul_lt_mul_of_pos_left hcd b0)
#align mul_eq_mul_iff_eq_and_eq_of_pos' mul_eq_mul_iff_eq_and_eq_of_pos'

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem pos_and_pos_or_neg_and_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) :
    0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rcases lt_trichotomy a 0 with (ha | rfl | ha)
  · refine' Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => _) hab⟩
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_mul] at hab
    exact hab.false.elim
  · refine' Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => _) hab⟩
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hb
#align pos_and_pos_or_neg_and_neg_of_mul_pos pos_and_pos_or_neg_and_neg_of_mul_pos


theorem neg_of_mul_pos_right [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.1.not_le ha).2
#align neg_of_mul_pos_right neg_of_mul_pos_right

theorem neg_of_mul_pos_left [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b ≤ 0) : a < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.2.not_le ha).1
#align neg_of_mul_pos_left neg_of_mul_pos_left

theorem neg_iff_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : a < 0 ↔ b < 0 :=
  ⟨neg_of_mul_pos_right hab ∘ le_of_lt, neg_of_mul_pos_left hab ∘ le_of_lt⟩
#align neg_iff_neg_of_mul_pos neg_iff_neg_of_mul_pos

theorem Left.neg_of_mul_neg_left [PosMulMono α] (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun h2 : b ≥ 0 => (Left.mul_nonneg h1 h2).not_lt h
#align left.neg_of_mul_neg_left Left.neg_of_mul_neg_left

theorem Right.neg_of_mul_neg_left [MulPosMono α] (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun h2 : b ≥ 0 => (Right.mul_nonneg h1 h2).not_lt h
#align right.neg_of_mul_neg_left Right.neg_of_mul_neg_left

theorem Left.neg_of_mul_neg_right [PosMulMono α] (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun h2 : a ≥ 0 => (Left.mul_nonneg h2 h1).not_lt h
#align left.neg_of_mul_neg_right Left.neg_of_mul_neg_right

theorem Right.neg_of_mul_neg_right [MulPosMono α] (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun h2 : a ≥ 0 => (Right.mul_nonneg h2 h1).not_lt h
#align right.neg_of_mul_neg_right Right.neg_of_mul_neg_right

end LinearOrder

end MulZeroClass

section MulOneClass

variable [MulOneClass α] [Zero α]

section Preorder

variable [Preorder α]

/-! Lemmas of the form `a ≤ a * b ↔ 1 ≤ b` and `a * b ≤ a ↔ b ≤ 1`,
which assume left covariance. -/


@[simp]
lemma le_mul_iff_one_le_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_left a0)
#align le_mul_iff_one_le_right le_mul_iff_one_le_right

@[simp]
theorem lt_mul_iff_one_lt_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_left a0)
#align lt_mul_iff_one_lt_right lt_mul_iff_one_lt_right

@[simp]
lemma mul_le_iff_le_one_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_left a0)
#align mul_le_iff_le_one_right mul_le_iff_le_one_right

@[simp]
theorem mul_lt_iff_lt_one_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_left a0)
#align mul_lt_iff_lt_one_right mul_lt_iff_lt_one_right

/-! Lemmas of the form `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`,
which assume right covariance. -/


@[simp]
lemma le_mul_iff_one_le_left [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) : a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_right a0)
#align le_mul_iff_one_le_left le_mul_iff_one_le_left

@[simp]
theorem lt_mul_iff_one_lt_left [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_right a0)
#align lt_mul_iff_one_lt_left lt_mul_iff_one_lt_left

@[simp]
lemma mul_le_iff_le_one_left [MulPosMono α] [MulPosReflectLE α] (b0 : 0 < b) : a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_right b0)
#align mul_le_iff_le_one_left mul_le_iff_le_one_left

@[simp]
theorem mul_lt_iff_lt_one_left [MulPosStrictMono α] [MulPosReflectLT α] (b0 : 0 < b) :
    a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_right b0)
#align mul_lt_iff_lt_one_left mul_lt_iff_lt_one_left

/-! Lemmas of the form `1 ≤ b → a ≤ a * b`.

Variants with `< 0` and `≤ 0` instead of `0 <` and `0 ≤` appear in `Mathlib/Algebra/Order/Ring/Defs`
(which imports this file) as they need additional results which are not yet available here. -/


theorem mul_le_of_le_one_left [MulPosMono α] (hb : 0 ≤ b) (h : a ≤ 1) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb
#align mul_le_of_le_one_left mul_le_of_le_one_left

theorem le_mul_of_one_le_left [MulPosMono α] (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb
#align le_mul_of_one_le_left le_mul_of_one_le_left

theorem mul_le_of_le_one_right [PosMulMono α] (ha : 0 ≤ a) (h : b ≤ 1) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha
#align mul_le_of_le_one_right mul_le_of_le_one_right

theorem le_mul_of_one_le_right [PosMulMono α] (ha : 0 ≤ a) (h : 1 ≤ b) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha
#align le_mul_of_one_le_right le_mul_of_one_le_right

theorem mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 0 < b) (h : a < 1) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb
#align mul_lt_of_lt_one_left mul_lt_of_lt_one_left

theorem lt_mul_of_one_lt_left [MulPosStrictMono α] (hb : 0 < b) (h : 1 < a) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb
#align lt_mul_of_one_lt_left lt_mul_of_one_lt_left

theorem mul_lt_of_lt_one_right [PosMulStrictMono α] (ha : 0 < a) (h : b < 1) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha
#align mul_lt_of_lt_one_right mul_lt_of_lt_one_right

theorem lt_mul_of_one_lt_right [PosMulStrictMono α] (ha : 0 < a) (h : 1 < b) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha
#align lt_mul_of_one_lt_right lt_mul_of_one_lt_right

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`. -/


/- Yaël: What's the point of these lemmas? They just chain an existing lemma with an assumption in
all possible ways, thereby artificially inflating the API and making the truly relevant lemmas hard
to find -/
theorem mul_le_of_le_of_le_one_of_nonneg [PosMulMono α] (h : b ≤ c) (ha : a ≤ 1) (hb : 0 ≤ b) :
    b * a ≤ c :=
  (mul_le_of_le_one_right hb ha).trans h
#align mul_le_of_le_of_le_one_of_nonneg mul_le_of_le_of_le_one_of_nonneg

theorem mul_lt_of_le_of_lt_one_of_pos [PosMulStrictMono α] (bc : b ≤ c) (ha : a < 1) (b0 : 0 < b) :
    b * a < c :=
  (mul_lt_of_lt_one_right b0 ha).trans_le bc
#align mul_lt_of_le_of_lt_one_of_pos mul_lt_of_le_of_lt_one_of_pos

theorem mul_lt_of_lt_of_le_one_of_nonneg [PosMulMono α] (h : b < c) (ha : a ≤ 1) (hb : 0 ≤ b) :
    b * a < c :=
  (mul_le_of_le_one_right hb ha).trans_lt h
#align mul_lt_of_lt_of_le_one_of_nonneg mul_lt_of_lt_of_le_one_of_nonneg

/-- Assumes left covariance. -/
theorem Left.mul_le_one_of_le_of_le [PosMulMono α] (ha : a ≤ 1) (hb : b ≤ 1) (a0 : 0 ≤ a) :
    a * b ≤ 1 :=
  mul_le_of_le_of_le_one_of_nonneg ha hb a0
#align left.mul_le_one_of_le_of_le Left.mul_le_one_of_le_of_le

/-- Assumes left covariance. -/
theorem Left.mul_lt_of_le_of_lt_one_of_pos [PosMulStrictMono α] (ha : a ≤ 1) (hb : b < 1)
    (a0 : 0 < a) : a * b < 1 :=
  _root_.mul_lt_of_le_of_lt_one_of_pos ha hb a0
#align left.mul_lt_of_le_of_lt_one_of_pos Left.mul_lt_of_le_of_lt_one_of_pos

/-- Assumes left covariance. -/
theorem Left.mul_lt_of_lt_of_le_one_of_nonneg [PosMulMono α] (ha : a < 1) (hb : b ≤ 1)
    (a0 : 0 ≤ a) : a * b < 1 :=
  _root_.mul_lt_of_lt_of_le_one_of_nonneg ha hb a0
#align left.mul_lt_of_lt_of_le_one_of_nonneg Left.mul_lt_of_lt_of_le_one_of_nonneg

theorem mul_le_of_le_of_le_one' [PosMulMono α] [MulPosMono α] (bc : b ≤ c) (ha : a ≤ 1) (a0 : 0 ≤ a)
    (c0 : 0 ≤ c) : b * a ≤ c :=
  (mul_le_mul_of_nonneg_right bc a0).trans <| mul_le_of_le_one_right c0 ha
#align mul_le_of_le_of_le_one' mul_le_of_le_of_le_one'

theorem mul_lt_of_lt_of_le_one' [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : a ≤ 1)
    (a0 : 0 < a) (c0 : 0 ≤ c) : b * a < c :=
  (mul_lt_mul_of_pos_right bc a0).trans_le <| mul_le_of_le_one_right c0 ha
#align mul_lt_of_lt_of_le_one' mul_lt_of_lt_of_le_one'

theorem mul_lt_of_le_of_lt_one' [PosMulStrictMono α] [MulPosMono α] (bc : b ≤ c) (ha : a < 1)
    (a0 : 0 ≤ a) (c0 : 0 < c) : b * a < c :=
  (mul_le_mul_of_nonneg_right bc a0).trans_lt <| mul_lt_of_lt_one_right c0 ha
#align mul_lt_of_le_of_lt_one' mul_lt_of_le_of_lt_one'

theorem mul_lt_of_lt_of_lt_one_of_pos [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : a ≤ 1)
    (a0 : 0 < a) (c0 : 0 ≤ c) : b * a < c :=
  (mul_lt_mul_of_pos_right bc a0).trans_le <| mul_le_of_le_one_right c0 ha
#align mul_lt_of_lt_of_lt_one_of_pos mul_lt_of_lt_of_lt_one_of_pos

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`. -/


theorem le_mul_of_le_of_one_le_of_nonneg [PosMulMono α] (h : b ≤ c) (ha : 1 ≤ a) (hc : 0 ≤ c) :
    b ≤ c * a :=
  h.trans <| le_mul_of_one_le_right hc ha
#align le_mul_of_le_of_one_le_of_nonneg le_mul_of_le_of_one_le_of_nonneg

theorem lt_mul_of_le_of_one_lt_of_pos [PosMulStrictMono α] (bc : b ≤ c) (ha : 1 < a) (c0 : 0 < c) :
    b < c * a :=
  bc.trans_lt <| lt_mul_of_one_lt_right c0 ha
#align lt_mul_of_le_of_one_lt_of_pos lt_mul_of_le_of_one_lt_of_pos

theorem lt_mul_of_lt_of_one_le_of_nonneg [PosMulMono α] (h : b < c) (ha : 1 ≤ a) (hc : 0 ≤ c) :
    b < c * a :=
  h.trans_le <| le_mul_of_one_le_right hc ha
#align lt_mul_of_lt_of_one_le_of_nonneg lt_mul_of_lt_of_one_le_of_nonneg

/-- Assumes left covariance. -/
theorem Left.one_le_mul_of_le_of_le [PosMulMono α] (ha : 1 ≤ a) (hb : 1 ≤ b) (a0 : 0 ≤ a) :
    1 ≤ a * b :=
  le_mul_of_le_of_one_le_of_nonneg ha hb a0
#align left.one_le_mul_of_le_of_le Left.one_le_mul_of_le_of_le

/-- Assumes left covariance. -/
theorem Left.one_lt_mul_of_le_of_lt_of_pos [PosMulStrictMono α] (ha : 1 ≤ a) (hb : 1 < b)
    (a0 : 0 < a) : 1 < a * b :=
  lt_mul_of_le_of_one_lt_of_pos ha hb a0
#align left.one_lt_mul_of_le_of_lt_of_pos Left.one_lt_mul_of_le_of_lt_of_pos

/-- Assumes left covariance. -/
theorem Left.lt_mul_of_lt_of_one_le_of_nonneg [PosMulMono α] (ha : 1 < a) (hb : 1 ≤ b)
    (a0 : 0 ≤ a) : 1 < a * b :=
  _root_.lt_mul_of_lt_of_one_le_of_nonneg ha hb a0
#align left.lt_mul_of_lt_of_one_le_of_nonneg Left.lt_mul_of_lt_of_one_le_of_nonneg

theorem le_mul_of_le_of_one_le' [PosMulMono α] [MulPosMono α] (bc : b ≤ c) (ha : 1 ≤ a)
    (a0 : 0 ≤ a) (b0 : 0 ≤ b) : b ≤ c * a :=
  (le_mul_of_one_le_right b0 ha).trans <| mul_le_mul_of_nonneg_right bc a0
#align le_mul_of_le_of_one_le' le_mul_of_le_of_one_le'

theorem lt_mul_of_le_of_one_lt' [PosMulStrictMono α] [MulPosMono α] (bc : b ≤ c) (ha : 1 < a)
    (a0 : 0 ≤ a) (b0 : 0 < b) : b < c * a :=
  (lt_mul_of_one_lt_right b0 ha).trans_le <| mul_le_mul_of_nonneg_right bc a0
#align lt_mul_of_le_of_one_lt' lt_mul_of_le_of_one_lt'

theorem lt_mul_of_lt_of_one_le' [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : 1 ≤ a)
    (a0 : 0 < a) (b0 : 0 ≤ b) : b < c * a :=
  (le_mul_of_one_le_right b0 ha).trans_lt <| mul_lt_mul_of_pos_right bc a0
#align lt_mul_of_lt_of_one_le' lt_mul_of_lt_of_one_le'

theorem lt_mul_of_lt_of_one_lt_of_pos [PosMulStrictMono α] [MulPosStrictMono α] (bc : b < c)
    (ha : 1 < a) (a0 : 0 < a) (b0 : 0 < b) : b < c * a :=
  (lt_mul_of_one_lt_right b0 ha).trans <| mul_lt_mul_of_pos_right bc a0
#align lt_mul_of_lt_of_one_lt_of_pos lt_mul_of_lt_of_one_lt_of_pos

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`. -/


theorem mul_le_of_le_one_of_le_of_nonneg [MulPosMono α] (ha : a ≤ 1) (h : b ≤ c) (hb : 0 ≤ b) :
    a * b ≤ c :=
  (mul_le_of_le_one_left hb ha).trans h
#align mul_le_of_le_one_of_le_of_nonneg mul_le_of_le_one_of_le_of_nonneg

theorem mul_lt_of_lt_one_of_le_of_pos [MulPosStrictMono α] (ha : a < 1) (h : b ≤ c) (hb : 0 < b) :
    a * b < c :=
  (mul_lt_of_lt_one_left hb ha).trans_le h
#align mul_lt_of_lt_one_of_le_of_pos mul_lt_of_lt_one_of_le_of_pos

theorem mul_lt_of_le_one_of_lt_of_nonneg [MulPosMono α] (ha : a ≤ 1) (h : b < c) (hb : 0 ≤ b) :
    a * b < c :=
  (mul_le_of_le_one_left hb ha).trans_lt h
#align mul_lt_of_le_one_of_lt_of_nonneg mul_lt_of_le_one_of_lt_of_nonneg

/-- Assumes right covariance. -/
theorem Right.mul_lt_one_of_lt_of_le_of_pos [MulPosStrictMono α] (ha : a < 1) (hb : b ≤ 1)
    (b0 : 0 < b) : a * b < 1 :=
  mul_lt_of_lt_one_of_le_of_pos ha hb b0
#align right.mul_lt_one_of_lt_of_le_of_pos Right.mul_lt_one_of_lt_of_le_of_pos

/-- Assumes right covariance. -/
theorem Right.mul_lt_one_of_le_of_lt_of_nonneg [MulPosMono α] (ha : a ≤ 1) (hb : b < 1)
    (b0 : 0 ≤ b) : a * b < 1 :=
  mul_lt_of_le_one_of_lt_of_nonneg ha hb b0
#align right.mul_lt_one_of_le_of_lt_of_nonneg Right.mul_lt_one_of_le_of_lt_of_nonneg

theorem mul_lt_of_lt_one_of_lt_of_pos [PosMulStrictMono α] [MulPosStrictMono α] (ha : a < 1)
    (bc : b < c) (a0 : 0 < a) (c0 : 0 < c) : a * b < c :=
  (mul_lt_mul_of_pos_left bc a0).trans <| mul_lt_of_lt_one_left c0 ha
#align mul_lt_of_lt_one_of_lt_of_pos mul_lt_of_lt_one_of_lt_of_pos

/-- Assumes right covariance. -/
theorem Right.mul_le_one_of_le_of_le [MulPosMono α] (ha : a ≤ 1) (hb : b ≤ 1) (b0 : 0 ≤ b) :
    a * b ≤ 1 :=
  mul_le_of_le_one_of_le_of_nonneg ha hb b0
#align right.mul_le_one_of_le_of_le Right.mul_le_one_of_le_of_le

theorem mul_le_of_le_one_of_le' [PosMulMono α] [MulPosMono α] (ha : a ≤ 1) (bc : b ≤ c) (a0 : 0 ≤ a)
    (c0 : 0 ≤ c) : a * b ≤ c :=
  (mul_le_mul_of_nonneg_left bc a0).trans <| mul_le_of_le_one_left c0 ha
#align mul_le_of_le_one_of_le' mul_le_of_le_one_of_le'

theorem mul_lt_of_lt_one_of_le' [PosMulMono α] [MulPosStrictMono α] (ha : a < 1) (bc : b ≤ c)
    (a0 : 0 ≤ a) (c0 : 0 < c) : a * b < c :=
  (mul_le_mul_of_nonneg_left bc a0).trans_lt <| mul_lt_of_lt_one_left c0 ha
#align mul_lt_of_lt_one_of_le' mul_lt_of_lt_one_of_le'

theorem mul_lt_of_le_one_of_lt' [PosMulStrictMono α] [MulPosMono α] (ha : a ≤ 1) (bc : b < c)
    (a0 : 0 < a) (c0 : 0 ≤ c) : a * b < c :=
  (mul_lt_mul_of_pos_left bc a0).trans_le <| mul_le_of_le_one_left c0 ha
#align mul_lt_of_le_one_of_lt' mul_lt_of_le_one_of_lt'

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`. -/


theorem lt_mul_of_one_lt_of_le_of_pos [MulPosStrictMono α] (ha : 1 < a) (h : b ≤ c) (hc : 0 < c) :
    b < a * c :=
  h.trans_lt <| lt_mul_of_one_lt_left hc ha
#align lt_mul_of_one_lt_of_le_of_pos lt_mul_of_one_lt_of_le_of_pos

theorem lt_mul_of_one_le_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (h : b < c) (hc : 0 ≤ c) :
    b < a * c :=
  h.trans_le <| le_mul_of_one_le_left hc ha
#align lt_mul_of_one_le_of_lt_of_nonneg lt_mul_of_one_le_of_lt_of_nonneg

theorem lt_mul_of_one_lt_of_lt_of_pos [MulPosStrictMono α] (ha : 1 < a) (h : b < c) (hc : 0 < c) :
    b < a * c :=
  h.trans <| lt_mul_of_one_lt_left hc ha
#align lt_mul_of_one_lt_of_lt_of_pos lt_mul_of_one_lt_of_lt_of_pos

/-- Assumes right covariance. -/
theorem Right.one_lt_mul_of_lt_of_le_of_pos [MulPosStrictMono α] (ha : 1 < a) (hb : 1 ≤ b)
    (b0 : 0 < b) : 1 < a * b :=
  lt_mul_of_one_lt_of_le_of_pos ha hb b0
#align right.one_lt_mul_of_lt_of_le_of_pos Right.one_lt_mul_of_lt_of_le_of_pos

/-- Assumes right covariance. -/
theorem Right.one_lt_mul_of_le_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (hb : 1 < b)
    (b0 : 0 ≤ b) : 1 < a * b :=
  lt_mul_of_one_le_of_lt_of_nonneg ha hb b0
#align right.one_lt_mul_of_le_of_lt_of_nonneg Right.one_lt_mul_of_le_of_lt_of_nonneg

/-- Assumes right covariance. -/
theorem Right.one_lt_mul_of_lt_of_lt [MulPosStrictMono α] (ha : 1 < a) (hb : 1 < b) (b0 : 0 < b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_lt_of_pos ha hb b0
#align right.one_lt_mul_of_lt_of_lt Right.one_lt_mul_of_lt_of_lt

theorem lt_mul_of_one_lt_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (h : b < c) (hc : 0 ≤ c) :
    b < a * c :=
  h.trans_le <| le_mul_of_one_le_left hc ha
#align lt_mul_of_one_lt_of_lt_of_nonneg lt_mul_of_one_lt_of_lt_of_nonneg

theorem lt_of_mul_lt_of_one_le_of_nonneg_left [PosMulMono α] (h : a * b < c) (hle : 1 ≤ b)
    (ha : 0 ≤ a) : a < c :=
  (le_mul_of_one_le_right ha hle).trans_lt h
#align lt_of_mul_lt_of_one_le_of_nonneg_left lt_of_mul_lt_of_one_le_of_nonneg_left

theorem lt_of_lt_mul_of_le_one_of_nonneg_left [PosMulMono α] (h : a < b * c) (hc : c ≤ 1)
    (hb : 0 ≤ b) : a < b :=
  h.trans_le <| mul_le_of_le_one_right hb hc
#align lt_of_lt_mul_of_le_one_of_nonneg_left lt_of_lt_mul_of_le_one_of_nonneg_left

theorem lt_of_lt_mul_of_le_one_of_nonneg_right [MulPosMono α] (h : a < b * c) (hb : b ≤ 1)
    (hc : 0 ≤ c) : a < c :=
  h.trans_le <| mul_le_of_le_one_left hc hb
#align lt_of_lt_mul_of_le_one_of_nonneg_right lt_of_lt_mul_of_le_one_of_nonneg_right

theorem le_mul_of_one_le_of_le_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (bc : b ≤ c) (c0 : 0 ≤ c) :
    b ≤ a * c :=
  bc.trans <| le_mul_of_one_le_left c0 ha
#align le_mul_of_one_le_of_le_of_nonneg le_mul_of_one_le_of_le_of_nonneg

/-- Assumes right covariance. -/
theorem Right.one_le_mul_of_le_of_le [MulPosMono α] (ha : 1 ≤ a) (hb : 1 ≤ b) (b0 : 0 ≤ b) :
    1 ≤ a * b :=
  le_mul_of_one_le_of_le_of_nonneg ha hb b0
#align right.one_le_mul_of_le_of_le Right.one_le_mul_of_le_of_le

theorem le_of_mul_le_of_one_le_of_nonneg_left [PosMulMono α] (h : a * b ≤ c) (hb : 1 ≤ b)
    (ha : 0 ≤ a) : a ≤ c :=
  (le_mul_of_one_le_right ha hb).trans h
#align le_of_mul_le_of_one_le_of_nonneg_left le_of_mul_le_of_one_le_of_nonneg_left

theorem le_of_le_mul_of_le_one_of_nonneg_left [PosMulMono α] (h : a ≤ b * c) (hc : c ≤ 1)
    (hb : 0 ≤ b) : a ≤ b :=
  h.trans <| mul_le_of_le_one_right hb hc
#align le_of_le_mul_of_le_one_of_nonneg_left le_of_le_mul_of_le_one_of_nonneg_left

theorem le_of_mul_le_of_one_le_nonneg_right [MulPosMono α] (h : a * b ≤ c) (ha : 1 ≤ a)
    (hb : 0 ≤ b) : b ≤ c :=
  (le_mul_of_one_le_left hb ha).trans h
#align le_of_mul_le_of_one_le_nonneg_right le_of_mul_le_of_one_le_nonneg_right

theorem le_of_le_mul_of_le_one_of_nonneg_right [MulPosMono α] (h : a ≤ b * c) (hb : b ≤ 1)
    (hc : 0 ≤ c) : a ≤ c :=
  h.trans <| mul_le_of_le_one_left hc hb
#align le_of_le_mul_of_le_one_of_nonneg_right le_of_le_mul_of_le_one_of_nonneg_right

end Preorder

section LinearOrder

variable [LinearOrder α]

-- Yaël: What's the point of this lemma? If we have `0 * 0 = 0`, then we can just take `b = 0`.
-- proven with `a0 : 0 ≤ a` as `exists_square_le`
theorem exists_square_le' [PosMulStrictMono α] (a0 : 0 < a) : ∃ b : α, b * b ≤ a := by
  obtain ha | ha := lt_or_le a 1
  · exact ⟨a, (mul_lt_of_lt_one_right a0 ha).le⟩
  · exact ⟨1, by rwa [mul_one]⟩
#align exists_square_le' exists_square_le'

end LinearOrder

end MulOneClass

section CancelMonoidWithZero

variable [CancelMonoidWithZero α]

section PartialOrder

variable [PartialOrder α]

theorem PosMulMono.toPosMulStrictMono [PosMulMono α] : PosMulStrictMono α :=
  ⟨fun x _ _ h => (mul_le_mul_of_nonneg_left h.le x.2.le).lt_of_ne
    (h.ne ∘ mul_left_cancel₀ x.2.ne')⟩
#align pos_mul_mono.to_pos_mul_strict_mono PosMulMono.toPosMulStrictMono

theorem posMulMono_iff_posMulStrictMono : PosMulMono α ↔ PosMulStrictMono α :=
  ⟨@PosMulMono.toPosMulStrictMono α _ _, @PosMulStrictMono.toPosMulMono α _ _⟩
#align pos_mul_mono_iff_pos_mul_strict_mono posMulMono_iff_posMulStrictMono

theorem MulPosMono.toMulPosStrictMono [MulPosMono α] : MulPosStrictMono α :=
  ⟨fun x _ _ h => (mul_le_mul_of_nonneg_right h.le x.2.le).lt_of_ne
    (h.ne ∘ mul_right_cancel₀ x.2.ne')⟩
#align mul_pos_mono.to_mul_pos_strict_mono MulPosMono.toMulPosStrictMono

theorem mulPosMono_iff_mulPosStrictMono : MulPosMono α ↔ MulPosStrictMono α :=
  ⟨@MulPosMono.toMulPosStrictMono α _ _, @MulPosStrictMono.toMulPosMono α _ _⟩
#align mul_pos_mono_iff_mul_pos_strict_mono mulPosMono_iff_mulPosStrictMono

theorem PosMulReflectLT.toPosMulReflectLE [PosMulReflectLT α] : PosMulReflectLE α :=
  ⟨fun x _ _ h =>
    h.eq_or_lt.elim (le_of_eq ∘ mul_left_cancel₀ x.2.ne.symm) fun h' =>
      (lt_of_mul_lt_mul_left h' x.2.le).le⟩
#align pos_mul_reflect_lt.to_pos_mul_mono_rev PosMulReflectLT.toPosMulReflectLE

theorem posMulReflectLE_iff_posMulReflectLT : PosMulReflectLE α ↔ PosMulReflectLT α :=
  ⟨@PosMulReflectLE.toPosMulReflectLT α _ _, @PosMulReflectLT.toPosMulReflectLE α _ _⟩
#align pos_mul_mono_rev_iff_pos_mul_reflect_lt posMulReflectLE_iff_posMulReflectLT

theorem MulPosReflectLT.toMulPosReflectLE [MulPosReflectLT α] : MulPosReflectLE α :=
  ⟨fun x _ _ h => h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.ne.symm) fun h' =>
    (lt_of_mul_lt_mul_right h' x.2.le).le⟩
#align mul_pos_reflect_lt.to_mul_pos_mono_rev MulPosReflectLT.toMulPosReflectLE

theorem mulPosReflectLE_iff_mulPosReflectLT : MulPosReflectLE α ↔ MulPosReflectLT α :=
  ⟨@MulPosReflectLE.toMulPosReflectLT α _ _, @MulPosReflectLT.toMulPosReflectLE α _ _⟩
#align mul_pos_mono_rev_iff_mul_pos_reflect_lt mulPosReflectLE_iff_mulPosReflectLT

end PartialOrder

end CancelMonoidWithZero

section CommSemigroupHasZero

variable [Mul α] [IsSymmOp α α (· * ·)] [Zero α] [Preorder α]

theorem posMulStrictMono_iff_mulPosStrictMono : PosMulStrictMono α ↔ MulPosStrictMono α := by
  simp only [PosMulStrictMono, MulPosStrictMono, IsSymmOp.symm_op]
#align pos_mul_strict_mono_iff_mul_pos_strict_mono posMulStrictMono_iff_mulPosStrictMono

theorem posMulReflectLT_iff_mulPosReflectLT : PosMulReflectLT α ↔ MulPosReflectLT α := by
  simp only [PosMulReflectLT, MulPosReflectLT, IsSymmOp.symm_op]
#align pos_mul_reflect_lt_iff_mul_pos_reflect_lt posMulReflectLT_iff_mulPosReflectLT

theorem posMulMono_iff_mulPosMono : PosMulMono α ↔ MulPosMono α := by
  simp only [PosMulMono, MulPosMono, IsSymmOp.symm_op]
#align pos_mul_mono_iff_mul_pos_mono posMulMono_iff_mulPosMono

theorem posMulReflectLE_iff_mulPosReflectLE : PosMulReflectLE α ↔ MulPosReflectLE α := by
  simp only [PosMulReflectLE, MulPosReflectLE, IsSymmOp.symm_op]
#align pos_mul_mono_rev_iff_mul_pos_mono_rev posMulReflectLE_iff_mulPosReflectLE

end CommSemigroupHasZero





section GroupWithZero

variable [GroupWithZero α] [PartialOrder α] [ZeroLEOneClass α] [PosMulReflectLT α] {a b : α}

@[simp]
theorem inv_pos : 0 < a⁻¹ ↔ 0 < a :=
  suffices ∀ a : α, 0 < a → 0 < a⁻¹ from ⟨fun h => inv_inv a ▸ this _ h, this a⟩
  fun a ha => flip lt_of_mul_lt_mul_left ha.le <| by simp [ne_of_gt ha, zero_lt_one]

alias ⟨_, inv_pos_of_pos⟩ := inv_pos

@[simp]
theorem inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a := by
  simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

alias ⟨_, inv_nonneg_of_nonneg⟩ := inv_nonneg

-- @[simp]
-- theorem inv_lt_zero : a⁻¹ < 0 ↔ a < 0 := by simp only [← not_le, inv_nonneg]

-- @[simp]
-- theorem inv_nonpos : a⁻¹ ≤ 0 ↔ a ≤ 0 := by simp only [← not_lt, inv_pos]

-- theorem one_div_neg : 1 / a < 0 ↔ a < 0 :=
--   inv_eq_one_div a ▸ inv_lt_zero

-- theorem one_div_nonpos : 1 / a ≤ 0 ↔ a ≤ 0 :=
--   inv_eq_one_div a ▸ inv_nonpos

theorem one_div_pos : 0 < 1 / a ↔ 0 < a :=
  inv_eq_one_div a ▸ inv_pos

theorem one_div_nonneg : 0 ≤ 1 / a ↔ 0 ≤ a :=
  inv_eq_one_div a ▸ inv_nonneg

-- Wants DecideableEq
theorem div_self_le_one (a : α) [DecidableEq α] : a / a ≤ 1 :=
  if h : a = 0 then by simp [h] else by simp [h]

end GroupWithZero



-- Can pull this section out
section PosMulStrictMono

variable [GroupWithZero α] [PartialOrder α] [ZeroLEOneClass α]
        [PosMulReflectLT α] [PosMulStrictMono α] {a b : α}

-- This might be able to be shifted down as doesn't seem like there are many dependencies
theorem div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [div_eq_mul_inv]
  exact mul_pos ha (inv_pos.2 hb)


section AddMonoidWithOne

variable [AddMonoidWithOne α] [NeZero (1 : α)]

-- theorem half_pos (h : 0 < a) : 0 < a / 2 :=
--   div_pos h zero_lt_two

-- theorem one_half_pos : (0 : α) < 1 / 2 :=
--   half_pos zero_lt_one

end AddMonoidWithOne

end PosMulStrictMono


section MulPosMono

variable [GroupWithZero α] [PartialOrder α] [ZeroLEOneClass α]
        [PosMulReflectLT α] [MulPosMono α] {a b : α}

theorem div_nonpos_of_nonpos_of_nonneg (ha : a ≤ 0) (hb : 0 ≤ b) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]
  exact mul_nonpos_of_nonpos_of_nonneg ha (inv_nonneg.2 hb)

  theorem le_div_iff (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b :=
  ⟨fun h => div_mul_cancel b (ne_of_lt hc).symm ▸ mul_le_mul_of_nonneg_right h hc.le, fun h =>
    calc
      a = a * c * (1 / c) := mul_mul_div a (ne_of_lt hc).symm
      _ ≤ b * (1 / c) := mul_le_mul_of_nonneg_right h (one_div_pos.2 hc).le
      _ = b / c := (div_eq_mul_one_div b c).symm
      ⟩

theorem div_le_iff (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b :=
  ⟨fun h =>
    calc
      a = a / b * b := by rw [div_mul_cancel _ (ne_of_lt hb).symm]
      _ ≤ c * b := mul_le_mul_of_nonneg_right h hb.le
      ,
    fun h =>
    calc
      a / b = a * (1 / b) := div_eq_mul_one_div a b
      _ ≤ c * b * (1 / b) := mul_le_mul_of_nonneg_right h (one_div_pos.2 hb).le
      _ = c * b / b := (div_eq_mul_one_div (c * b) b).symm
      _ = c := by refine' (div_eq_iff (ne_of_gt hb)).mpr rfl
      ⟩

theorem inv_pos_le_iff_one_le_mul (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ b * a := by
  rw [inv_eq_one_div]
  exact div_le_iff ha

theorem div_le_of_nonneg_of_le_mul (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a / b ≤ c := by
  rcases eq_or_lt_of_le hb with (rfl | hb')
  simp only [div_zero, hc]
  rwa [div_le_iff hb']

lemma mul_le_of_nonneg_of_le_div (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b / c) : a * c ≤ b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_div_iff hc] at h

theorem div_le_one_of_le (h : a ≤ b) (hb : 0 ≤ b) : a / b ≤ 1 :=
  div_le_of_nonneg_of_le_mul hb zero_le_one <| by rwa [one_mul]

-- @[mono]
theorem div_le_div_of_le (hc : 0 ≤ c) (h : a ≤ b) : a / c ≤ b / c := by
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
  exact mul_le_mul_of_nonneg_right h (one_div_nonneg.2 hc)

theorem _div_le_div_of_le_of_nonneg (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c :=
  div_le_div_of_le hc hab

theorem one_le_div (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by rw [le_div_iff hb, one_mul]

theorem div_le_one (hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b := by rw [div_le_iff hb, one_mul]

-- THIS ONE IS GIVING ME PROBLEMS
-- @[simp]
-- theorem half_le_self_iff [AddMonoidWithOne α] : a / 2 ≤ a ↔ 0 ≤ a := by
--   rw [div_le_iff (zero_lt_two' α), mul_two, le_add_iff_nonneg_left]

-- alias ⟨_, half_le_self⟩ := half_le_self_iff

end MulPosMono



section CommMulPosMono

variable [CommGroupWithZero α] [PartialOrder α] [ZeroLEOneClass α]
        [PosMulReflectLT α] [MulPosMono α] {a b : α}

theorem le_div_iff' (hc : 0 < c) : a ≤ b / c ↔ c * a ≤ b := by rw [mul_comm, le_div_iff hc]

theorem div_le_iff' (hb : 0 < b) : a / b ≤ c ↔ a ≤ b * c := by rw [mul_comm, div_le_iff hb]

theorem inv_mul_le_iff (h : 0 < b) : b⁻¹ * a ≤ c ↔ a ≤ b * c := by
  rw [inv_eq_one_div, mul_comm, ← div_eq_mul_one_div]
  exact div_le_iff' h

theorem inv_mul_le_iff' (h : 0 < b) : b⁻¹ * a ≤ c ↔ a ≤ c * b := by rw [inv_mul_le_iff h, mul_comm]

theorem mul_inv_le_iff (h : 0 < b) : a * b⁻¹ ≤ c ↔ a ≤ b * c := by rw [mul_comm, inv_mul_le_iff h]

theorem mul_inv_le_iff' (h : 0 < b) : a * b⁻¹ ≤ c ↔ a ≤ c * b := by rw [mul_comm, inv_mul_le_iff' h]

theorem inv_pos_le_iff_one_le_mul' (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [inv_eq_one_div]
  exact div_le_iff' ha

theorem inv_le_inv_of_le (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  rwa [← one_div a, le_div_iff' ha, ← div_eq_mul_inv, div_le_iff (ha.trans_le h), one_mul]

theorem inv_le_inv (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
  rw [← one_div, div_le_iff ha, ← div_eq_inv_mul, le_div_iff hb, one_mul]

theorem inv_le (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  rw [← inv_le_inv hb (inv_pos.2 ha), inv_inv]

theorem inv_le_of_inv_le (ha : 0 < a) (h : a⁻¹ ≤ b) : b⁻¹ ≤ a :=
  (inv_le ha ((inv_pos.2 ha).trans_le h)).1 h

theorem le_inv (ha : 0 < a) (hb : 0 < b) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  rw [← inv_le_inv (inv_pos.2 hb) ha, inv_inv]

theorem inv_le_one (ha : 1 ≤ a) : a⁻¹ ≤ 1 := by
  rwa [inv_le (zero_lt_one.trans_le ha) zero_lt_one, inv_one]

theorem one_le_inv (h₁ : 0 < a) (h₂ : a ≤ 1) : 1 ≤ a⁻¹ := by
  rwa [le_inv (@zero_lt_one α _ _ _ _ _) h₁, inv_one]

theorem _one_le_inv_iff : 1 ≤ a⁻¹ ↔ 0 < a ∧ a ≤ 1 :=
  ⟨fun h => ⟨inv_pos.1 (zero_lt_one.trans_le h), inv_inv a ▸ inv_le_one h⟩, and_imp.2 one_le_inv⟩

theorem div_le_div_iff (b0 : 0 < b) (d0 : 0 < d) : a / b ≤ c / d ↔ a * d ≤ c * b := by
  rw [le_div_iff d0, div_mul_eq_mul_div, div_le_iff b0]

theorem one_div_le (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ b ↔ 1 / b ≤ a := by simpa using inv_le ha hb

theorem le_one_div (ha : 0 < a) (hb : 0 < b) : a ≤ 1 / b ↔ b ≤ 1 / a := by simpa using le_inv ha hb

theorem one_div_le_one_div_of_le (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  simpa using inv_le_inv_of_le ha h

theorem one_le_one_div (h1 : 0 < a) (h2 : a ≤ 1) : 1 ≤ 1 / a := by
  rwa [le_one_div (@zero_lt_one α _ _ _ _ _) h1, one_div_one]

end CommMulPosMono







section CommPosMulMulPosMono

variable [CommGroupWithZero α] [PartialOrder α] [ZeroLEOneClass α]
        [PosMulReflectLT α] [PosMulMono α] [MulPosMono α] {a b : α}

theorem div_le_div_of_le_left (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) : a / b ≤ a / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left ((inv_le_inv (hc.trans_le h) hc).mpr h) ha

-- @[mono]
theorem _div_le_div (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hbd : d ≤ b) : a / b ≤ c / d := by
  rw [div_le_div_iff (hd.trans_le hbd) hd]
  exact mul_le_mul hac hbd hd.le hc

theorem div_le_self (ha : 0 ≤ a) (hb : 1 ≤ b) : a / b ≤ a := by
  simpa only [div_one] using div_le_div_of_le_left ha zero_lt_one hb

theorem le_div_self (ha : 0 ≤ a) (hb₀ : 0 < b) (hb₁ : b ≤ 1) : a ≤ a / b := by
  simpa only [div_one] using div_le_div_of_le_left ha hb₀ hb₁

end CommPosMulMulPosMono


section PosMulMono

variable [GroupWithZero α] [PartialOrder α] [ZeroLEOneClass α]
        [PosMulReflectLT α] [PosMulMono α] {a b : α}

theorem div_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  rw [div_eq_mul_inv]
  exact mul_nonneg ha (inv_nonneg.2 hb)

-- Relies on above that is commented out
-- theorem div_nonpos_of_nonneg_of_nonpos (ha : 0 ≤ a) (hb : b ≤ 0) : a / b ≤ 0 := by
--   rw [div_eq_mul_inv]
--   exact mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos.2 hb)

end PosMulMono


section MulPosStrictMono

variable [GroupWithZero α] [PartialOrder α] [ZeroLEOneClass α]
        [PosMulReflectLT α] [MulPosStrictMono α] {a b : α}

theorem div_lt_div_of_lt (hc : 0 < c) (h : a < b) : a / c < b / c := by
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
  exact mul_lt_mul_of_pos_right h (one_div_pos.2 hc)

end MulPosStrictMono


section LinearOrder

variable [CommGroupWithZero α] [LinearOrder α] [ZeroLEOneClass α]
        [PosMulReflectLT α] [MulPosMono α] {a b c d e : α}

theorem lt_div_iff (hc : 0 < c) : a < b / c ↔ a * c < b :=
  lt_iff_lt_of_le_iff_le <| div_le_iff hc

theorem lt_div_iff' (hc : 0 < c) : a < b / c ↔ c * a < b := by rw [mul_comm, lt_div_iff hc]

theorem div_lt_iff (hc : 0 < c) : b / c < a ↔ b < a * c :=
  lt_iff_lt_of_le_iff_le (le_div_iff hc)

theorem div_lt_iff' (hc : 0 < c) : b / c < a ↔ b < c * a := by rw [mul_comm, div_lt_iff hc]

theorem inv_pos_lt_iff_one_lt_mul (ha : 0 < a) : a⁻¹ < b ↔ 1 < b * a := by
  rw [inv_eq_one_div]
  exact div_lt_iff ha

theorem inv_pos_lt_iff_one_lt_mul' (ha : 0 < a) : a⁻¹ < b ↔ 1 < a * b := by
  rw [inv_eq_one_div]
  exact div_lt_iff' ha

theorem inv_lt_inv (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a :=
  lt_iff_lt_of_le_iff_le (inv_le_inv hb ha)

theorem inv_lt_inv_of_lt (hb : 0 < b) (h : b < a) : a⁻¹ < b⁻¹ :=
  (inv_lt_inv (hb.trans h) hb).2 h

theorem inv_lt (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a :=
  lt_iff_lt_of_le_iff_le (le_inv hb ha)

theorem inv_lt_of_inv_lt (ha : 0 < a) (h : a⁻¹ < b) : b⁻¹ < a :=
  (inv_lt ha ((inv_pos.2 ha).trans h)).1 h

theorem lt_inv (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹ :=
  lt_iff_lt_of_le_iff_le (inv_le hb ha)

theorem inv_lt_one (ha : 1 < a) : a⁻¹ < 1 := by
  rwa [inv_lt (zero_lt_one.trans ha) zero_lt_one, inv_one]

theorem one_lt_inv (h₁ : 0 < a) (h₂ : a < 1) : 1 < a⁻¹ := by
  rwa [lt_inv (@zero_lt_one α _ _ _ _ _) h₁, inv_one]

theorem inv_lt_one_iff_of_pos (h₀ : 0 < a) : a⁻¹ < 1 ↔ 1 < a :=
  ⟨fun h₁ => inv_inv a ▸ one_lt_inv (inv_pos.2 h₀) h₁, inv_lt_one⟩

-- Relies on above that is commented out
-- theorem inv_lt_one_iff : a⁻¹ < 1 ↔ a ≤ 0 ∨ 1 < a := by
--   cases' le_or_lt a 0 with ha ha
--   · simp [ha, (inv_nonpos.2 ha).trans_lt zero_lt_one]
--   · simp only [ha.not_le, false_or_iff, inv_lt_one_iff_of_pos ha]

theorem one_lt_inv_iff : 1 < a⁻¹ ↔ 0 < a ∧ a < 1 :=
  ⟨fun h => ⟨inv_pos.1 (zero_lt_one.trans h), inv_inv a ▸ inv_lt_one h⟩, and_imp.2 one_lt_inv⟩

-- theorem inv_le_one_iff : a⁻¹ ≤ 1 ↔ a ≤ 0 ∨ 1 ≤ a := by
--   rcases em (a = 1) with (rfl | ha)
--   · simp [le_rfl]
--   · simp only [Ne.le_iff_lt (Ne.symm ha), Ne.le_iff_lt (mt inv_eq_one.1 ha), inv_lt_one_iff]

section MulPosStrictMono

variable [MulPosStrictMono α]

theorem div_le_div_right (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b :=
  ⟨le_imp_le_of_lt_imp_lt <| div_lt_div_of_lt hc, div_le_div_of_le <| hc.le⟩

theorem div_lt_div_right (hc : 0 < c) : a / c < b / c ↔ a < b :=
  lt_iff_lt_of_le_iff_le <| div_le_div_right hc

end MulPosStrictMono

section PosMulStrictMono

variable [PosMulStrictMono α]

theorem div_lt_div_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b < a / c ↔ c < b := by
  simp only [div_eq_mul_inv, mul_lt_mul_left ha, inv_lt_inv hb hc]

theorem div_le_div_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b ≤ a / c ↔ c ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 (div_lt_div_left ha hc hb)

theorem div_lt_div_of_lt_left (hc : 0 < c) (hb : 0 < b) (h : b < a) : c / a < c / b :=
  (div_lt_div_left hc (hb.trans h) hb).mpr h

theorem div_lt_self (ha : 0 < a) (hb : 1 < b) : a / b < a := by
  simpa only [div_one] using div_lt_div_of_lt_left ha zero_lt_one hb

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_lt_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a < 1 / b ↔ b < a :=
  div_lt_div_left zero_lt_one ha hb

/-- For the single implications with fewer assumptions, see `one_div_le_one_div_of_le` and
  `le_of_one_div_le_one_div` -/
theorem one_div_le_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ 1 / b ↔ b ≤ a :=
  div_le_div_left zero_lt_one ha hb

-- theorem exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : ∃ c : α, 0 < c ∧ b * c < a := by
--   have : 0 < a / max (b + 1) 1 := div_pos h (lt_max_iff.2 (Or.inr zero_lt_one))
--   refine' ⟨a / max (b + 1) 1, this, _⟩
--   rw [← lt_div_iff this, div_div_cancel' h.ne']
--   exact lt_max_iff.2 (Or.inl <| lt_add_one _)

-- theorem exists_pos_lt_mul {a : α} (h : 0 < a) (b : α) : ∃ c : α, 0 < c ∧ b < c * a :=
--   let ⟨c, hc₀, hc⟩ := exists_pos_mul_lt h b;
--   ⟨c⁻¹, inv_pos.2 hc₀, by rwa [← div_eq_inv_mul, lt_div_iff hc₀]⟩

end PosMulStrictMono

theorem div_lt_div_iff (b0 : 0 < b) (d0 : 0 < d) : a / b < c / d ↔ a * d < c * b := by
  rw [lt_div_iff d0, div_mul_eq_mul_div, div_lt_iff b0]

theorem inv_mul_lt_iff (h : 0 < b) : b⁻¹ * a < c ↔ a < b * c := by
  rw [inv_eq_one_div, mul_comm, ← div_eq_mul_one_div]
  exact div_lt_iff' h

theorem inv_mul_lt_iff' (h : 0 < b) : b⁻¹ * a < c ↔ a < c * b := by rw [inv_mul_lt_iff h, mul_comm]

theorem mul_inv_lt_iff (h : 0 < b) : a * b⁻¹ < c ↔ a < b * c := by rw [mul_comm, inv_mul_lt_iff h]

theorem mul_inv_lt_iff' (h : 0 < b) : a * b⁻¹ < c ↔ a < c * b := by rw [mul_comm, inv_mul_lt_iff' h]

-- theorem div_lt_div (hac : a < c) (hbd : d ≤ b) (c0 : 0 ≤ c) (d0 : 0 < d) : a / b < c / d :=
--   (div_lt_div_iff (d0.trans_le hbd) d0).2 (mul_lt_mul hac hbd d0 c0) -- Algebra.Order.Ring.Defs

-- theorem div_lt_div' (hac : a ≤ c) (hbd : d < b) (c0 : 0 < c) (d0 : 0 < d) : a / b < c / d :=
--   (div_lt_div_iff (d0.trans hbd) d0).2 (mul_lt_mul' hac hbd d0.le c0) -- Algebra.Order.Ring.Defs

theorem one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a := by rw [lt_div_iff hb, one_mul]

theorem div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b := by rw [div_lt_iff hb, one_mul]

theorem one_div_lt (ha : 0 < a) (hb : 0 < b) : 1 / a < b ↔ 1 / b < a := by simpa using inv_lt ha hb

theorem lt_one_div (ha : 0 < a) (hb : 0 < b) : a < 1 / b ↔ b < 1 / a := by simpa using lt_inv ha hb

theorem one_div_lt_one_div_of_lt (ha : 0 < a) (h : a < b) : 1 / b < 1 / a := by
  rwa [lt_div_iff' ha, ← div_eq_mul_one_div, div_lt_one (ha.trans h)]

theorem le_of_one_div_le_one_div (ha : 0 < a) (h : 1 / a ≤ 1 / b) : b ≤ a :=
  le_imp_le_of_lt_imp_lt (one_div_lt_one_div_of_lt ha) h

theorem lt_of_one_div_lt_one_div (ha : 0 < a) (h : 1 / a < 1 / b) : b < a :=
  lt_imp_lt_of_le_imp_le (one_div_le_one_div_of_le ha) h

theorem one_lt_one_div (h1 : 0 < a) (h2 : a < 1) : 1 < 1 / a := by
  rwa [lt_one_div (@zero_lt_one α _ _ _ _ _) h1, one_div_one]

theorem mul_le_mul_of_mul_div_le (h : a * (b / c) ≤ d) (hc : 0 < c) : b * a ≤ d * c := by
  rw [← mul_div_assoc] at h
  rwa [mul_comm b, ← div_le_iff hc]

theorem div_mul_le_div_mul_of_div_le_div (h : a / b ≤ c / d) (he : 0 ≤ e) :
    a / (b * e) ≤ c / (d * e) := by
  rw [div_mul_eq_div_mul_one_div, div_mul_eq_div_mul_one_div]
  exact mul_le_mul_of_nonneg_right h (one_div_nonneg.2 he)

-- Causing issues
-- /- TODO: Unify `add_halves` and `add_halves'` into a single lemma about
-- `DivisionSemiring` + `CharZero` -/
-- theorem add_halves (a : α) : a / 2 + a / 2 = a := by
--   rw [div_add_div_same, ← two_mul, mul_div_cancel_left a two_ne_zero]

-- -- TODO: Generalize to `DivisionSemiring`
-- theorem add_self_div_two (a : α) : (a + a) / 2 = a := by
--   rw [← mul_two, mul_div_cancel a two_ne_zero]

-- @[simp]
-- theorem half_lt_self_iff : a / 2 < a ↔ 0 < a := by
--   rw [div_lt_iff (zero_lt_two' α), mul_two, lt_add_iff_pos_left]

-- alias ⟨_, half_le_self⟩ := half_le_self_iff

-- alias ⟨_, half_lt_self⟩ := half_lt_self_iff

-- alias div_two_lt_of_pos := half_lt_self

-- theorem one_half_lt_one : (1 / 2 : α) < 1 :=
--   half_lt_self zero_lt_one

-- theorem two_inv_lt_one : (2⁻¹ : α) < 1 :=
--   (one_div _).symm.trans_lt one_half_lt_one

-- theorem left_lt_add_div_two : a < (a + b) / 2 ↔ a < b := by simp [lt_div_iff, mul_two]

-- theorem add_div_two_lt_right : (a + b) / 2 < b ↔ a < b := by simp [div_lt_iff, mul_two]

-- theorem add_thirds (a : α) : a / 3 + a / 3 + a / 3 = a := by
--   rw [div_add_div_same, div_add_div_same, ← two_mul, ← add_one_mul 2 a, two_add_one_eq_three,
--     mul_div_cancel_left a three_ne_zero]

end LinearOrder


-- Wants OrderedSemiring
-- theorem _zpow_nonneg (ha : 0 ≤ a) : ∀ n : ℤ, 0 ≤ a ^ n
--   | (n : ℕ) => by
--     rw [zpow_ofNat]
--     exact pow_nonneg ha _
--   | -(n + 1 : ℕ) => by
--     rw [zpow_neg, _inv_nonneg, zpow_ofNat]
--     exact pow_nonneg ha _

-- Wants StrictOrderedSemiring
-- theorem _zpow_pos_of_pos (ha : 0 < a) : ∀ n : ℤ, 0 < a ^ n
--   | (n : ℕ) => by
--     rw [zpow_ofNat]
--     exact pow_pos ha _
--   | -(n + 1 : ℕ) => by
--     rw [zpow_neg, _inv_pos, zpow_ofNat]
--     exact pow_pos ha _


-- open Function OrderDual

-- variable {ι α β : Type*}

-- section LinearOrderedSemifield

-- variable [LinearOrderedSemifield α] {a b c d e : α} {m n : ℤ}

-- /-- `Equiv.mulLeft₀` as an order_iso. -/
-- @[simps! (config := { simpRhs := true })]
-- def OrderIso.mulLeft₀ (a : α) (ha : 0 < a) : α ≃o α :=
--   { Equiv.mulLeft₀ a ha.ne' with map_rel_iff' := @fun _ _ => mul_le_mul_left ha }
-- #align order_iso.mul_left₀ OrderIso.mulLeft₀
-- #align order_iso.mul_left₀_symm_apply OrderIso.mulLeft₀_symm_apply
-- #align order_iso.mul_left₀_apply OrderIso.mulLeft₀_apply

-- /-- `Equiv.mulRight₀` as an order_iso. -/
-- @[simps! (config := { simpRhs := true })]
-- def OrderIso.mulRight₀ (a : α) (ha : 0 < a) : α ≃o α :=
--   { Equiv.mulRight₀ a ha.ne' with map_rel_iff' := @fun _ _ => mul_le_mul_right ha }
-- #align order_iso.mul_right₀ OrderIso.mulRight₀
-- #align order_iso.mul_right₀_symm_apply OrderIso.mulRight₀_symm_apply
-- #align order_iso.mul_right₀_apply OrderIso.mulRight₀_apply


-- -- Relies on Mathlib.Algebra.Order.Ring.Defs which causes circular import
-- theorem Monotone.div_const {β : Type*} [Preorder β] {f : β → α} (hf : Monotone f) {c : α}
--     (hc : 0 ≤ c) : Monotone fun x => f x / c := by
--   haveI := @LinearOrder.decidableLE α _
--   simpa only [div_eq_mul_inv] using (monotone_mul_right_of_nonneg (inv_nonneg.2 hc)).comp hf

-- theorem StrictMono.div_const {β : Type*} [Preorder β] {f : β → α} (hf : StrictMono f) {c : α}
--     (hc : 0 < c) : StrictMono fun x => f x / c := by
--   simpa only [div_eq_mul_inv] using hf.mul_const (inv_pos.2 hc)

-- -- see Note [lower instance priority]
-- instance (priority := 100) LinearOrderedSemiField.toDenselyOrdered : DenselyOrdered α where
--   dense a₁ a₂ h :=
--     ⟨(a₁ + a₂) / 2,
--       calc
--         a₁ = (a₁ + a₁) / 2 := (add_self_div_two a₁).symm
--         _ < (a₁ + a₂) / 2 := div_lt_div_of_lt zero_lt_two (add_lt_add_left h _)
--         ,
--       calc
--         (a₁ + a₂) / 2 < (a₂ + a₂) / 2 := div_lt_div_of_lt zero_lt_two (add_lt_add_right h _)
--         _ = a₂ := add_self_div_two a₂
--         ⟩

-- theorem min_div_div_right {c : α} (hc : 0 ≤ c) (a b : α) : min (a / c) (b / c) = min a b / c :=
--   Eq.symm <| Monotone.map_min fun _ _ => div_le_div_of_le hc

-- theorem max_div_div_right {c : α} (hc : 0 ≤ c) (a b : α) : max (a / c) (b / c) = max a b / c :=
--   Eq.symm <| Monotone.map_max fun _ _ => div_le_div_of_le hc

-- theorem one_div_strictAntiOn : StrictAntiOn (fun x : α => 1 / x) (Set.Ioi 0) :=
--   fun _ x1 _ y1 xy => (one_div_lt_one_div (Set.mem_Ioi.mp y1) (Set.mem_Ioi.mp x1)).mpr xy

-- theorem one_div_pow_le_one_div_pow_of_le (a1 : 1 ≤ a) {m n : ℕ} (mn : m ≤ n) :
--     1 / a ^ n ≤ 1 / a ^ m := by
--   refine' (one_div_le_one_div _ _).mpr (pow_le_pow_right a1 mn) <;>
--     exact pow_pos (zero_lt_one.trans_le a1) _

-- theorem one_div_pow_lt_one_div_pow_of_lt (a1 : 1 < a) {m n : ℕ} (mn : m < n) :
--     1 / a ^ n < 1 / a ^ m := by
--   refine (one_div_lt_one_div ?_ ?_).2 (pow_lt_pow_right a1 mn) <;>
--     exact pow_pos (zero_lt_one.trans a1) _

-- theorem one_div_pow_anti (a1 : 1 ≤ a) : Antitone fun n : ℕ => 1 / a ^ n := fun _ _ =>
--   one_div_pow_le_one_div_pow_of_le a1

-- theorem one_div_pow_strictAnti (a1 : 1 < a) : StrictAnti fun n : ℕ => 1 / a ^ n := fun _ _ =>
--   one_div_pow_lt_one_div_pow_of_lt a1

-- theorem inv_strictAntiOn : StrictAntiOn (fun x : α => x⁻¹) (Set.Ioi 0) := fun _ hx _ hy xy =>
--   (inv_lt_inv hy hx).2 xy

-- theorem inv_pow_le_inv_pow_of_le (a1 : 1 ≤ a) {m n : ℕ} (mn : m ≤ n) : (a ^ n)⁻¹ ≤ (a ^ m)⁻¹ := by
--   convert one_div_pow_le_one_div_pow_of_le a1 mn using 1 <;> simp

-- theorem inv_pow_lt_inv_pow_of_lt (a1 : 1 < a) {m n : ℕ} (mn : m < n) : (a ^ n)⁻¹ < (a ^ m)⁻¹ := by
--   convert one_div_pow_lt_one_div_pow_of_lt a1 mn using 1 <;> simp

-- theorem inv_pow_anti (a1 : 1 ≤ a) : Antitone fun n : ℕ => (a ^ n)⁻¹ := fun _ _ =>
--   inv_pow_le_inv_pow_of_le a1

-- theorem inv_pow_strictAnti (a1 : 1 < a) : StrictAnti fun n : ℕ => (a ^ n)⁻¹ := fun _ _ =>
--   inv_pow_lt_inv_pow_of_lt a1

-- /-! ### Results about `IsGLB` -/


-- theorem IsGLB.mul_left {s : Set α} (ha : 0 ≤ a) (hs : IsGLB s b) :
--     IsGLB ((fun b => a * b) '' s) (a * b) := by
--   rcases lt_or_eq_of_le ha with (ha | rfl)
--   · exact (OrderIso.mulLeft₀ _ ha).isGLB_image'.2 hs
--   · simp_rw [zero_mul]
--     rw [hs.nonempty.image_const]
--     exact isGLB_singleton

-- theorem IsGLB.mul_right {s : Set α} (ha : 0 ≤ a) (hs : IsGLB s b) :
--     IsGLB ((fun b => b * a) '' s) (b * a) := by simpa [mul_comm] using hs.mul_left ha

-- end LinearOrderedSemifield

-- section

-- variable [LinearOrderedField α] {a b c d : α} {n : ℤ}

-- /-! ### Lemmas about pos, nonneg, nonpos, neg -/


-- theorem div_pos_iff : 0 < a / b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
--   simp only [division_def, mul_pos_iff, inv_pos, inv_lt_zero]

-- theorem div_neg_iff : a / b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
--   simp [division_def, mul_neg_iff]

-- theorem div_nonneg_iff : 0 ≤ a / b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
--   simp [division_def, mul_nonneg_iff]

-- theorem div_nonpos_iff : a / b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
--   simp [division_def, mul_nonpos_iff]

-- theorem div_nonneg_of_nonpos (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a / b :=
--   div_nonneg_iff.2 <| Or.inr ⟨ha, hb⟩

-- theorem div_pos_of_neg_of_neg (ha : a < 0) (hb : b < 0) : 0 < a / b :=
--   div_pos_iff.2 <| Or.inr ⟨ha, hb⟩

-- theorem div_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) : a / b < 0 :=
--   div_neg_iff.2 <| Or.inr ⟨ha, hb⟩

-- theorem div_neg_of_pos_of_neg (ha : 0 < a) (hb : b < 0) : a / b < 0 :=
--   div_neg_iff.2 <| Or.inl ⟨ha, hb⟩

-- /-! ### Relating one division with another term -/


-- theorem div_le_iff_of_neg (hc : c < 0) : b / c ≤ a ↔ a * c ≤ b :=
--   ⟨fun h => div_mul_cancel b (ne_of_lt hc) ▸ mul_le_mul_of_nonpos_right h hc.le, fun h =>
--     calc
--       a = a * c * (1 / c) := mul_mul_div a (ne_of_lt hc)
--       _ ≥ b * (1 / c) := mul_le_mul_of_nonpos_right h (one_div_neg.2 hc).le
--       _ = b / c := (div_eq_mul_one_div b c).symm
--       ⟩

-- theorem div_le_iff_of_neg' (hc : c < 0) : b / c ≤ a ↔ c * a ≤ b := by
--   rw [mul_comm, div_le_iff_of_neg hc]

-- theorem le_div_iff_of_neg (hc : c < 0) : a ≤ b / c ↔ b ≤ a * c := by
--   rw [← neg_neg c, mul_neg, div_neg, le_neg, div_le_iff (neg_pos.2 hc), neg_mul]

-- theorem le_div_iff_of_neg' (hc : c < 0) : a ≤ b / c ↔ b ≤ c * a := by
--   rw [mul_comm, le_div_iff_of_neg hc]

-- theorem div_lt_iff_of_neg (hc : c < 0) : b / c < a ↔ a * c < b :=
--   lt_iff_lt_of_le_iff_le <| le_div_iff_of_neg hc

-- theorem div_lt_iff_of_neg' (hc : c < 0) : b / c < a ↔ c * a < b := by
--   rw [mul_comm, div_lt_iff_of_neg hc]

-- theorem lt_div_iff_of_neg (hc : c < 0) : a < b / c ↔ b < a * c :=
--   lt_iff_lt_of_le_iff_le <| div_le_iff_of_neg hc

-- theorem lt_div_iff_of_neg' (hc : c < 0) : a < b / c ↔ b < c * a := by
--   rw [mul_comm, lt_div_iff_of_neg hc]

-- theorem div_le_one_of_ge (h : b ≤ a) (hb : b ≤ 0) : a / b ≤ 1 := by
--   simpa only [neg_div_neg_eq] using div_le_one_of_le (neg_le_neg h) (neg_nonneg_of_nonpos hb)

-- /-! ### Bi-implications of inequalities using inversions -/


-- theorem inv_le_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
--   rw [← one_div, div_le_iff_of_neg ha, ← div_eq_inv_mul, div_le_iff_of_neg hb, one_mul]

-- theorem inv_le_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
--   rw [← inv_le_inv_of_neg hb (inv_lt_zero.2 ha), inv_inv]

-- theorem le_inv_of_neg (ha : a < 0) (hb : b < 0) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
--   rw [← inv_le_inv_of_neg (inv_lt_zero.2 hb) ha, inv_inv]

-- theorem inv_lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b⁻¹ ↔ b < a :=
--   lt_iff_lt_of_le_iff_le (inv_le_inv_of_neg hb ha)

-- theorem inv_lt_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b ↔ b⁻¹ < a :=
--   lt_iff_lt_of_le_iff_le (le_inv_of_neg hb ha)

-- theorem lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a < b⁻¹ ↔ b < a⁻¹ :=
--   lt_iff_lt_of_le_iff_le (inv_le_of_neg hb ha)

-- /-! ### Relating two divisions -/


-- theorem div_le_div_of_nonpos_of_le (hc : c ≤ 0) (h : b ≤ a) : a / c ≤ b / c := by
--   rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
--   exact mul_le_mul_of_nonpos_right h (one_div_nonpos.2 hc)

-- theorem div_lt_div_of_neg_of_lt (hc : c < 0) (h : b < a) : a / c < b / c := by
--   rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
--   exact mul_lt_mul_of_neg_right h (one_div_neg.2 hc)

-- theorem div_le_div_right_of_neg (hc : c < 0) : a / c ≤ b / c ↔ b ≤ a :=
--   ⟨le_imp_le_of_lt_imp_lt <| div_lt_div_of_neg_of_lt hc, div_le_div_of_nonpos_of_le <| hc.le⟩

-- theorem div_lt_div_right_of_neg (hc : c < 0) : a / c < b / c ↔ b < a :=
--   lt_iff_lt_of_le_iff_le <| div_le_div_right_of_neg hc

-- /-! ### Relating one division and involving `1` -/


-- theorem one_le_div_of_neg (hb : b < 0) : 1 ≤ a / b ↔ a ≤ b := by rw [le_div_iff_of_neg hb, one_mul]

-- theorem div_le_one_of_neg (hb : b < 0) : a / b ≤ 1 ↔ b ≤ a := by rw [div_le_iff_of_neg hb, one_mul]

-- theorem one_lt_div_of_neg (hb : b < 0) : 1 < a / b ↔ a < b := by rw [lt_div_iff_of_neg hb, one_mul]

-- theorem div_lt_one_of_neg (hb : b < 0) : a / b < 1 ↔ b < a := by rw [div_lt_iff_of_neg hb, one_mul]

-- theorem one_div_le_of_neg (ha : a < 0) (hb : b < 0) : 1 / a ≤ b ↔ 1 / b ≤ a := by
--   simpa using inv_le_of_neg ha hb

-- theorem one_div_lt_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < b ↔ 1 / b < a := by
--   simpa using inv_lt_of_neg ha hb

-- theorem le_one_div_of_neg (ha : a < 0) (hb : b < 0) : a ≤ 1 / b ↔ b ≤ 1 / a := by
--   simpa using le_inv_of_neg ha hb

-- theorem lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : a < 1 / b ↔ b < 1 / a := by
--   simpa using lt_inv_of_neg ha hb

-- theorem one_lt_div_iff : 1 < a / b ↔ 0 < b ∧ b < a ∨ b < 0 ∧ a < b := by
--   rcases lt_trichotomy b 0 with (hb | rfl | hb)
--   · simp [hb, hb.not_lt, one_lt_div_of_neg]
--   · simp [lt_irrefl, zero_le_one]
--   · simp [hb, hb.not_lt, one_lt_div]

-- theorem one_le_div_iff : 1 ≤ a / b ↔ 0 < b ∧ b ≤ a ∨ b < 0 ∧ a ≤ b := by
--   rcases lt_trichotomy b 0 with (hb | rfl | hb)
--   · simp [hb, hb.not_lt, one_le_div_of_neg]
--   · simp [lt_irrefl, zero_lt_one.not_le, zero_lt_one]
--   · simp [hb, hb.not_lt, one_le_div]

-- theorem div_lt_one_iff : a / b < 1 ↔ 0 < b ∧ a < b ∨ b = 0 ∨ b < 0 ∧ b < a := by
--   rcases lt_trichotomy b 0 with (hb | rfl | hb)
--   · simp [hb, hb.not_lt, hb.ne, div_lt_one_of_neg]
--   · simp [zero_lt_one]
--   · simp [hb, hb.not_lt, div_lt_one, hb.ne.symm]

-- theorem div_le_one_iff : a / b ≤ 1 ↔ 0 < b ∧ a ≤ b ∨ b = 0 ∨ b < 0 ∧ b ≤ a := by
--   rcases lt_trichotomy b 0 with (hb | rfl | hb)
--   · simp [hb, hb.not_lt, hb.ne, div_le_one_of_neg]
--   · simp [zero_le_one]
--   · simp [hb, hb.not_lt, div_le_one, hb.ne.symm]

-- /-! ### Relating two divisions, involving `1` -/


-- theorem one_div_le_one_div_of_neg_of_le (hb : b < 0) (h : a ≤ b) : 1 / b ≤ 1 / a := by
--   rwa [div_le_iff_of_neg' hb, ← div_eq_mul_one_div, div_le_one_of_neg (h.trans_lt hb)]

-- theorem one_div_lt_one_div_of_neg_of_lt (hb : b < 0) (h : a < b) : 1 / b < 1 / a := by
--   rwa [div_lt_iff_of_neg' hb, ← div_eq_mul_one_div, div_lt_one_of_neg (h.trans hb)]

-- theorem le_of_neg_of_one_div_le_one_div (hb : b < 0) (h : 1 / a ≤ 1 / b) : b ≤ a :=
--   le_imp_le_of_lt_imp_lt (one_div_lt_one_div_of_neg_of_lt hb) h

-- theorem lt_of_neg_of_one_div_lt_one_div (hb : b < 0) (h : 1 / a < 1 / b) : b < a :=
--   lt_imp_lt_of_le_imp_le (one_div_le_one_div_of_neg_of_le hb) h

-- /-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_neg_of_lt` and
--   `lt_of_one_div_lt_one_div` -/
-- theorem one_div_le_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a ≤ 1 / b ↔ b ≤ a := by
--   simpa [one_div] using inv_le_inv_of_neg ha hb

-- /-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
--   `lt_of_one_div_lt_one_div` -/
-- theorem one_div_lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < 1 / b ↔ b < a :=
--   lt_iff_lt_of_le_iff_le (one_div_le_one_div_of_neg hb ha)

-- theorem one_div_lt_neg_one (h1 : a < 0) (h2 : -1 < a) : 1 / a < -1 :=
--   suffices 1 / a < 1 / -1 by rwa [one_div_neg_one_eq_neg_one] at this
--   one_div_lt_one_div_of_neg_of_lt h1 h2

-- theorem one_div_le_neg_one (h1 : a < 0) (h2 : -1 ≤ a) : 1 / a ≤ -1 :=
--   suffices 1 / a ≤ 1 / -1 by rwa [one_div_neg_one_eq_neg_one] at this
--   one_div_le_one_div_of_neg_of_le h1 h2

-- /-! ### Results about halving -/


-- theorem sub_self_div_two (a : α) : a - a / 2 = a / 2 := by
--   suffices a / 2 + a / 2 - a / 2 = a / 2 by rwa [add_halves] at this
--   rw [add_sub_cancel]

-- theorem div_two_sub_self (a : α) : a / 2 - a = -(a / 2) := by
--   suffices a / 2 - (a / 2 + a / 2) = -(a / 2) by rwa [add_halves] at this
--   rw [sub_add_eq_sub_sub, sub_self, zero_sub]

-- theorem add_sub_div_two_lt (h : a < b) : a + (b - a) / 2 < b := by
--   rwa [← div_sub_div_same, sub_eq_add_neg, add_comm (b / 2), ← add_assoc, ← sub_eq_add_neg, ←
--     lt_sub_iff_add_lt, sub_self_div_two, sub_self_div_two, div_lt_div_right (zero_lt_two' α)]

-- /-- An inequality involving `2`. -/
-- theorem sub_one_div_inv_le_two (a2 : 2 ≤ a) : (1 - 1 / a)⁻¹ ≤ 2 := by
--   -- Take inverses on both sides to obtain `2⁻¹ ≤ 1 - 1 / a`
--   refine' (inv_le_inv_of_le (inv_pos.2 <| zero_lt_two' α) _).trans_eq (inv_inv (2 : α))
--   -- move `1 / a` to the left and `2⁻¹` to the right.
--   rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
--   -- take inverses on both sides and use the assumption `2 ≤ a`.
--   convert (one_div a).le.trans (inv_le_inv_of_le zero_lt_two a2) using 1
--   -- show `1 - 1 / 2 = 1 / 2`.
--   rw [sub_eq_iff_eq_add, ← two_mul, mul_inv_cancel two_ne_zero]

-- /-! ### Results about `IsLUB` -/


-- -- TODO: Generalize to `LinearOrderedSemifield`
-- theorem IsLUB.mul_left {s : Set α} (ha : 0 ≤ a) (hs : IsLUB s b) :
--     IsLUB ((fun b => a * b) '' s) (a * b) := by
--   rcases lt_or_eq_of_le ha with (ha | rfl)
--   · exact (OrderIso.mulLeft₀ _ ha).isLUB_image'.2 hs
--   · simp_rw [zero_mul]
--     rw [hs.nonempty.image_const]
--     exact isLUB_singleton

-- -- TODO: Generalize to `LinearOrderedSemifield`
-- theorem IsLUB.mul_right {s : Set α} (ha : 0 ≤ a) (hs : IsLUB s b) :
--     IsLUB ((fun b => b * a) '' s) (b * a) := by simpa [mul_comm] using hs.mul_left ha

-- /-! ### Miscellaneous lemmmas -/


-- theorem mul_sub_mul_div_mul_neg_iff (hc : c ≠ 0) (hd : d ≠ 0) :
--     (a * d - b * c) / (c * d) < 0 ↔ a / c < b / d := by
--   rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_lt_zero]

-- theorem mul_sub_mul_div_mul_nonpos_iff (hc : c ≠ 0) (hd : d ≠ 0) :
--     (a * d - b * c) / (c * d) ≤ 0 ↔ a / c ≤ b / d := by
--   rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_nonpos]

-- alias ⟨div_lt_div_of_mul_sub_mul_div_neg, mul_sub_mul_div_mul_neg⟩ := mul_sub_mul_div_mul_neg_iff

-- alias ⟨div_le_div_of_mul_sub_mul_div_nonpos, mul_sub_mul_div_mul_nonpos⟩ :=
--   mul_sub_mul_div_mul_nonpos_iff

-- theorem exists_add_lt_and_pos_of_lt (h : b < a) : ∃ c, b + c < a ∧ 0 < c :=
--   ⟨(a - b) / 2, add_sub_div_two_lt h, div_pos (sub_pos_of_lt h) zero_lt_two⟩

-- theorem le_of_forall_sub_le (h : ∀ ε > 0, b - ε ≤ a) : b ≤ a := by
--   contrapose! h
--   simpa only [@and_comm ((0 : α) < _), lt_sub_iff_add_lt, gt_iff_lt] using
--     exists_add_lt_and_pos_of_lt h

-- theorem mul_self_inj_of_nonneg (a0 : 0 ≤ a) (b0 : 0 ≤ b) : a * a = b * b ↔ a = b :=
--   mul_self_eq_mul_self_iff.trans <|
--     or_iff_left_of_imp fun h => by
--       subst a
--       have : b = 0 := le_antisymm (neg_nonneg.1 a0) b0
--       rw [this, neg_zero]

-- theorem min_div_div_right_of_nonpos (hc : c ≤ 0) (a b : α) : min (a / c) (b / c) = max a b / c :=
--   Eq.symm <| Antitone.map_max fun _ _ => div_le_div_of_nonpos_of_le hc

-- theorem max_div_div_right_of_nonpos (hc : c ≤ 0) (a b : α) : max (a / c) (b / c) = min a b / c :=
--   Eq.symm <| Antitone.map_min fun _ _ => div_le_div_of_nonpos_of_le hc

-- theorem abs_inv (a : α) : |a⁻¹| = |a|⁻¹ :=
--   map_inv₀ (absHom : α →*₀ α) a

-- theorem abs_div (a b : α) : |a / b| = |a| / |b| :=
--   map_div₀ (absHom : α →*₀ α) a b

-- theorem abs_one_div (a : α) : |1 / a| = 1 / |a| := by rw [abs_div, abs_one]


-- end GroupWithZero
