/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
import Mathlib.Algebra.CovariantAndContravariant
import Mathlib.Algebra.GroupWithZero.Defs

#align_import algebra.order.ring.lemmas from "leanprover-community/mathlib"@"44e29dbcff83ba7114a464d592b8c3743987c1e5"

/-!
# Multiplication by ·positive· elements is monotonic

Let `α` be a type with `<` and `0`.  We use the type `{x : α // 0 < x}` of positive elements of `α`
to prove results about monotonicity of multiplication.  We also introduce the local notation `α>0`
for the subtype `{x : α // 0 < x}`:

If the type `α` also has a multiplication, then we combine this with (`Contravariant`)
`CovariantClass`es to assume that multiplication by positive elements is (strictly) monotone on a
`MulZeroClass`, `MonoidWithZero`,...
More specifically, we use extensively the following typeclasses:

* monotone left
* * `CovariantClass α>0 α (fun x y ↦ x * y) (≤)`, abbreviated `PosMulMono α`,
    expressing that multiplication by positive elements on the left is monotone;
* * `CovariantClass α>0 α (fun x y ↦ x * y) (<)`, abbreviated `PosMulStrictMono α`,
    expressing that multiplication by positive elements on the left is strictly monotone;
* monotone right
* * `CovariantClass α>0 α (fun x y ↦ y * x) (≤)`, abbreviated `MulPosMono α`,
    expressing that multiplication by positive elements on the right is monotone;
* * `CovariantClass α>0 α (fun x y ↦ y * x) (<)`, abbreviated `MulPosStrictMono α`,
    expressing that multiplication by positive elements on the right is strictly monotone.
* reverse monotone left
* * `ContravariantClass α>0 α (fun x y ↦ x * y) (≤)`, abbreviated `PosMulMonoRev α`,
    expressing that multiplication by positive elements on the left is reverse monotone;
* * `ContravariantClass α>0 α (fun x y ↦ x * y) (<)`, abbreviated `PosMulReflectLT α`,
    expressing that multiplication by positive elements on the left is strictly reverse monotone;
* reverse reverse monotone right
* * `ContravariantClass α>0 α (fun x y ↦ y * x) (≤)`, abbreviated `MulPosMonoRev α`,
    expressing that multiplication by positive elements on the right is reverse monotone;
* * `ContravariantClass α>0 α (fun x y ↦ y * x) (<)`, abbreviated `MulPosReflectLT α`,
    expressing that multiplication by positive elements on the right is strictly reverse monotone.

## Notation

The following is local notation in this file:
* `α≥0`: `{x : α // 0 ≤ x}`
* `α>0`: `{x : α // 0 < x}`
-/


variable (α : Type*)

-- mathport name: «exprα≥0»
/- Notations for nonnegative and positive elements
https://
leanprover.zulipchat.com/#narrow/stream/113488-general/topic/notation.20for.20positive.20elements
-/
section Abbreviations

variable [Mul α] [Zero α] [Preorder α]

set_option quotPrecheck false in
/-- Local notation for the nonnegative elements of a type `α`. TODO: actually make local. -/
notation "α≥0" => { x : α // 0 ≤ x }

-- mathport name: «exprα>0»
set_option quotPrecheck false in
/-- Local notation for the positive elements of a type `α`. TODO: actually make local. -/
notation "α>0" => { x : α // 0 < x }

/-- `PosMulMono α` is an abbreviation for `CovariantClass α≥0 α (fun x y ↦ x * y) (≤)`,
expressing that multiplication by nonnegative elements on the left is monotone. -/
abbrev PosMulMono : Prop :=
  CovariantClass α≥0 α (fun x y => x * y) (· ≤ ·)
#align pos_mul_mono PosMulMono

/-- `MulPosMono α` is an abbreviation for `CovariantClass α≥0 α (fun x y ↦ y * x) (≤)`,
expressing that multiplication by nonnegative elements on the right is monotone. -/
abbrev MulPosMono : Prop :=
  CovariantClass α≥0 α (fun x y => y * x) (· ≤ ·)
#align mul_pos_mono MulPosMono

/-- `PosMulStrictMono α` is an abbreviation for `CovariantClass α>0 α (fun x y ↦ x * y) (<)`,
expressing that multiplication by positive elements on the left is strictly monotone. -/
abbrev PosMulStrictMono : Prop :=
  CovariantClass α>0 α (fun x y => x * y) (· < ·)
#align pos_mul_strict_mono PosMulStrictMono

/-- `MulPosStrictMono α` is an abbreviation for `CovariantClass α>0 α (fun x y ↦ y * x) (<)`,
expressing that multiplication by positive elements on the right is strictly monotone. -/
abbrev MulPosStrictMono : Prop :=
  CovariantClass α>0 α (fun x y => y * x) (· < ·)
#align mul_pos_strict_mono MulPosStrictMono

/-- `PosMulReflectLT α` is an abbreviation for `ContravariantClas α≥0 α (fun x y ↦ x * y) (<)`,
expressing that multiplication by nonnegative elements on the left is strictly reverse monotone. -/
abbrev PosMulReflectLT : Prop :=
  ContravariantClass α≥0 α (fun x y => x * y) (· < ·)
#align pos_mul_reflect_lt PosMulReflectLT

/-- `MulPosReflectLT α` is an abbreviation for `ContravariantClas α≥0 α (fun x y ↦ y * x) (<)`,
expressing that multiplication by nonnegative elements on the right is strictly reverse monotone. -/
abbrev MulPosReflectLT : Prop :=
  ContravariantClass α≥0 α (fun x y => y * x) (· < ·)
#align mul_pos_reflect_lt MulPosReflectLT

/-- `PosMulMonoRev α` is an abbreviation for `ContravariantClas α>0 α (fun x y ↦ x * y) (≤)`,
expressing that multiplication by positive elements on the left is reverse monotone. -/
abbrev PosMulMonoRev : Prop :=
  ContravariantClass α>0 α (fun x y => x * y) (· ≤ ·)
#align pos_mul_mono_rev PosMulMonoRev

/-- `MulPosMonoRev α` is an abbreviation for `ContravariantClas α>0 α (fun x y ↦ y * x) (≤)`,
expressing that multiplication by positive elements on the right is reverse monotone. -/
abbrev MulPosMonoRev : Prop :=
  ContravariantClass α>0 α (fun x y => y * x) (· ≤ ·)
#align mul_pos_mono_rev MulPosMonoRev

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

theorem le_of_mul_le_mul_left [PosMulMonoRev α] (bc : a * b ≤ a * c) (a0 : 0 < a) : b ≤ c :=
  @ContravariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc
#align le_of_mul_le_mul_left le_of_mul_le_mul_left

theorem le_of_mul_le_mul_right [MulPosMonoRev α] (bc : b * a ≤ c * a) (a0 : 0 < a) : b ≤ c :=
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
theorem mul_le_mul_left [PosMulMono α] [PosMulMonoRev α] (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c :=
  @rel_iff_cov α>0 α (fun x y => x * y) (· ≤ ·) _ _ ⟨a, a0⟩ _ _
#align mul_le_mul_left mul_le_mul_left

@[simp]
theorem mul_le_mul_right [MulPosMono α] [MulPosMonoRev α] (a0 : 0 < a) : b * a ≤ c * a ↔ b ≤ c :=
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
instance (priority := 100) PosMulStrictMono.toPosMulMonoRev [PosMulStrictMono α] :
    PosMulMonoRev α :=
  ⟨fun x _ _ h => le_of_not_lt fun h' => h.not_lt <| mul_lt_mul_of_pos_left h' x.prop⟩

-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toMulPosMonoRev [MulPosStrictMono α] :
    MulPosMonoRev α :=
  ⟨fun x _ _ h => le_of_not_lt fun h' => h.not_lt <| mul_lt_mul_of_pos_right h' x.prop⟩

theorem PosMulMonoRev.toPosMulStrictMono [PosMulMonoRev α] : PosMulStrictMono α :=
  ⟨fun x _ _ h => lt_of_not_ge fun h' => h.not_le <| le_of_mul_le_mul_of_pos_left h' x.prop⟩
#align pos_mul_mono_rev.to_pos_mul_strict_mono PosMulMonoRev.toPosMulStrictMono

theorem MulPosMonoRev.toMulPosStrictMono [MulPosMonoRev α] : MulPosStrictMono α :=
  ⟨fun x _ _ h => lt_of_not_ge fun h' => h.not_le <| le_of_mul_le_mul_of_pos_right h' x.prop⟩
#align mul_pos_mono_rev.to_mul_pos_strict_mono MulPosMonoRev.toMulPosStrictMono

theorem posMulStrictMono_iff_posMulMonoRev : PosMulStrictMono α ↔ PosMulMonoRev α :=
  ⟨@PosMulStrictMono.toPosMulMonoRev _ _ _ _, @PosMulMonoRev.toPosMulStrictMono _ _ _ _⟩
#align pos_mul_strict_mono_iff_pos_mul_mono_rev posMulStrictMono_iff_posMulMonoRev

theorem mulPosStrictMono_iff_mulPosMonoRev : MulPosStrictMono α ↔ MulPosMonoRev α :=
  ⟨@MulPosStrictMono.toMulPosMonoRev _ _ _ _, @MulPosMonoRev.toMulPosStrictMono _ _ _ _⟩
#align mul_pos_strict_mono_iff_mul_pos_mono_rev mulPosStrictMono_iff_mulPosMonoRev

theorem PosMulReflectLT.toPosMulMono [PosMulReflectLT α] : PosMulMono α :=
  ⟨fun x _ _ h => le_of_not_lt fun h' => h.not_lt <| lt_of_mul_lt_mul_left h' x.prop⟩
#align pos_mul_reflect_lt.to_pos_mul_mono PosMulReflectLT.toPosMulMono

theorem MulPosReflectLT.toMulPosMono [MulPosReflectLT α] : MulPosMono α :=
  ⟨fun x _ _ h => le_of_not_lt fun h' => h.not_lt <| lt_of_mul_lt_mul_right h' x.prop⟩
#align mul_pos_reflect_lt.to_mul_pos_mono MulPosReflectLT.toMulPosMono

theorem PosMulMono.toPosMulReflectLT [PosMulMono α] : PosMulReflectLT α :=
  ⟨fun x _ _ h => lt_of_not_ge fun h' => h.not_le <| mul_le_mul_of_nonneg_left h' x.prop⟩
#align pos_mul_mono.to_pos_mul_reflect_lt PosMulMono.toPosMulReflectLT

theorem MulPosMono.toMulPosReflectLT [MulPosMono α] : MulPosReflectLT α :=
  ⟨fun x _ _ h => lt_of_not_ge fun h' => h.not_le <| mul_le_mul_of_nonneg_right h' x.prop⟩
#align mul_pos_mono.to_mul_pos_reflect_lt MulPosMono.toMulPosReflectLT

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
  -- 🎉 no goals
#align left.mul_pos Left.mul_pos

alias mul_pos := Left.mul_pos
#align mul_pos mul_pos

theorem mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha
  -- 🎉 no goals
#align mul_neg_of_pos_of_neg mul_neg_of_pos_of_neg

@[simp]
theorem zero_lt_mul_left [PosMulStrictMono α] [PosMulReflectLT α] (h : 0 < c) :
    0 < c * b ↔ 0 < b := by
  rw [←mul_zero c, mul_lt_mul_left h]
  -- ⊢ 0 < b ↔ c * 0 < b
  simp
  -- 🎉 no goals
#align zero_lt_mul_left zero_lt_mul_left

/-- Assumes right covariance. -/
theorem Right.mul_pos [MulPosStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb
  -- 🎉 no goals
#align right.mul_pos Right.mul_pos

theorem mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb
  -- 🎉 no goals
#align mul_neg_of_neg_of_pos mul_neg_of_neg_of_pos

@[simp]
theorem zero_lt_mul_right [MulPosStrictMono α] [MulPosReflectLT α] (h : 0 < c) :
    0 < b * c ↔ 0 < b := by
  rw [←zero_mul c, mul_lt_mul_right h]
  -- ⊢ 0 < b ↔ 0 * c < b
  simp
  -- 🎉 no goals
#align zero_lt_mul_right zero_lt_mul_right

/-- Assumes left covariance. -/
theorem Left.mul_nonneg [PosMulMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha
  -- 🎉 no goals
#align left.mul_nonneg Left.mul_nonneg

alias mul_nonneg := Left.mul_nonneg
#align mul_nonneg mul_nonneg

theorem mul_nonpos_of_nonneg_of_nonpos [PosMulMono α] (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha
  -- 🎉 no goals
#align mul_nonpos_of_nonneg_of_nonpos mul_nonpos_of_nonneg_of_nonpos

/-- Assumes right covariance. -/
theorem Right.mul_nonneg [MulPosMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb
  -- 🎉 no goals
#align right.mul_nonneg Right.mul_nonneg

theorem mul_nonpos_of_nonpos_of_nonneg [MulPosMono α] (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb
  -- 🎉 no goals
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
      -- ⊢ ↑a * b ≤ ↑a * c
      · simp [←ha]
        -- 🎉 no goals
      · exact @CovariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, ha⟩ _ _ h ⟩⟩
        -- 🎉 no goals
#align pos_mul_mono_iff_covariant_pos posMulMono_iff_covariant_pos

theorem mulPosMono_iff_covariant_pos :
    MulPosMono α ↔ CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) :=
  ⟨@MulPosMono.to_covariantClass_pos_mul_le _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_lt
      -- ⊢ b * ↑a ≤ c * ↑a
      · simp [←ha]
        -- 🎉 no goals
      · exact @CovariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, ha⟩ _ _ h ⟩⟩
        -- 🎉 no goals
#align mul_pos_mono_iff_covariant_pos mulPosMono_iff_covariant_pos

theorem posMulReflectLT_iff_contravariant_pos :
    PosMulReflectLT α ↔ ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨@PosMulReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_lt
      -- ⊢ b < c
      · simp [←ha] at h
        -- 🎉 no goals
      · exact @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨_, ha⟩ _ _ h ⟩⟩
        -- 🎉 no goals
#align pos_mul_reflect_lt_iff_contravariant_pos posMulReflectLT_iff_contravariant_pos

theorem mulPosReflectLT_iff_contravariant_pos :
    MulPosReflectLT α ↔ ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨@MulPosReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_lt
      -- ⊢ b < c
      · simp [←ha] at h
        -- 🎉 no goals
      · exact @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨_, ha⟩ _ _ h ⟩⟩
        -- 🎉 no goals
#align mul_pos_reflect_lt_iff_contravariant_pos mulPosReflectLT_iff_contravariant_pos

-- Porting note: mathlib3 proofs would look like `StrictMono.monotone <| @CovariantClass.elim ..`
-- but implicit argument handling causes that to break
-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosMulMono [PosMulStrictMono α] : PosMulMono α :=
  posMulMono_iff_covariant_pos.2 <|
    ⟨fun a _ _ h => StrictMono.monotone (λ _ _ h' => mul_lt_mul_of_pos_left h' a.prop) h⟩
#align pos_mul_strict_mono.to_pos_mul_mono PosMulStrictMono.toPosMulMono

-- Porting note: mathlib3 proofs would look like `StrictMono.monotone <| @CovariantClass.elim ..`
-- but implicit argument handling causes that to break
-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toMulPosMono [MulPosStrictMono α] : MulPosMono α :=
  mulPosMono_iff_covariant_pos.2 <|
    ⟨fun a _ _ h => StrictMono.monotone (λ _ _ h' => mul_lt_mul_of_pos_right h' a.prop) h⟩
#align mul_pos_strict_mono.to_mul_pos_mono MulPosStrictMono.toMulPosMono

-- see Note [lower instance priority]
instance (priority := 100) PosMulMonoRev.toPosMulReflectLT [PosMulMonoRev α] :
    PosMulReflectLT α :=
  posMulReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_left h.le a.2).lt_of_ne <| by
        rintro rfl
        -- ⊢ False
        simp at h⟩
        -- 🎉 no goals
#align pos_mul_mono_rev.to_pos_mul_reflect_lt PosMulMonoRev.toPosMulReflectLT

-- see Note [lower instance priority]
instance (priority := 100) MulPosMonoRev.toMulPosReflectLT [MulPosMonoRev α] :
    MulPosReflectLT α :=
  mulPosReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_right h.le a.2).lt_of_ne <| by
        rintro rfl
        -- ⊢ False
        simp at h⟩
        -- 🎉 no goals
#align mul_pos_mono_rev.to_mul_pos_reflect_lt MulPosMonoRev.toMulPosReflectLT

theorem mul_left_cancel_iff_of_pos [PosMulMonoRev α] (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_left h.le a0).antisymm <|
    le_of_mul_le_mul_of_pos_left h.ge a0, congr_arg _⟩
#align mul_left_cancel_iff_of_pos mul_left_cancel_iff_of_pos

theorem mul_right_cancel_iff_of_pos [MulPosMonoRev α] (b0 : 0 < b) : a * b = c * b ↔ a = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_right h.le b0).antisymm <|
    le_of_mul_le_mul_of_pos_right h.ge b0, congr_arg (· * b)⟩
#align mul_right_cancel_iff_of_pos mul_right_cancel_iff_of_pos

theorem mul_eq_mul_iff_eq_and_eq_of_pos [PosMulStrictMono α] [MulPosStrictMono α] [PosMulMonoRev α]
    [MulPosMonoRev α] (hac : a ≤ b) (hbd : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine' ⟨fun h => _, fun h => congr_arg₂ (· * ·) h.1 h.2⟩
  -- ⊢ a = b ∧ c = d
  rcases hac.eq_or_lt with (rfl | hac)
  -- ⊢ a = a ∧ c = d
  · exact ⟨rfl, (mul_left_cancel_iff_of_pos a0).mp h⟩
    -- 🎉 no goals
  rcases eq_or_lt_of_le hbd with (rfl | hbd)
  -- ⊢ a = b ∧ c = c
  · exact ⟨(mul_right_cancel_iff_of_pos d0).mp h, rfl⟩
    -- 🎉 no goals
  exact ((mul_lt_mul_of_pos_of_pos hac hbd a0 d0).ne h).elim
  -- 🎉 no goals
#align mul_eq_mul_iff_eq_and_eq_of_pos mul_eq_mul_iff_eq_and_eq_of_pos

theorem mul_eq_mul_iff_eq_and_eq_of_pos' [PosMulStrictMono α] [MulPosStrictMono α] [PosMulMonoRev α]
    [MulPosMonoRev α] (hac : a ≤ b) (hbd : c ≤ d) (b0 : 0 < b) (c0 : 0 < c) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine' ⟨fun h => _, fun h => congr_arg₂ (· * ·) h.1 h.2⟩
  -- ⊢ a = b ∧ c = d
  rcases hac.eq_or_lt with (rfl | hac)
  -- ⊢ a = a ∧ c = d
  · exact ⟨rfl, (mul_left_cancel_iff_of_pos b0).mp h⟩
    -- 🎉 no goals
  rcases eq_or_lt_of_le hbd with (rfl | hbd)
  -- ⊢ a = b ∧ c = c
  · exact ⟨(mul_right_cancel_iff_of_pos c0).mp h, rfl⟩
    -- 🎉 no goals
  exact ((mul_lt_mul_of_lt_of_lt' hac hbd b0 c0).ne h).elim
  -- 🎉 no goals
#align mul_eq_mul_iff_eq_and_eq_of_pos' mul_eq_mul_iff_eq_and_eq_of_pos'

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem pos_and_pos_or_neg_and_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) :
    0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rcases lt_trichotomy a 0 with (ha | rfl | ha)
  · refine' Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => _) hab⟩
    -- ⊢ a * b ≤ 0
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hb
    -- 🎉 no goals
  · rw [zero_mul] at hab
    -- ⊢ 0 < 0 ∧ 0 < b ∨ 0 < 0 ∧ b < 0
    exact hab.false.elim
    -- 🎉 no goals
  · refine' Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => _) hab⟩
    -- ⊢ a * b ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hb
    -- 🎉 no goals
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
theorem le_mul_iff_one_le_right [PosMulMono α] [PosMulMonoRev α] (a0 : 0 < a) : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_left a0)
                -- 🎉 no goals
#align le_mul_iff_one_le_right le_mul_iff_one_le_right

@[simp]
theorem lt_mul_iff_one_lt_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_left a0)
                -- 🎉 no goals
#align lt_mul_iff_one_lt_right lt_mul_iff_one_lt_right

@[simp]
theorem mul_le_iff_le_one_right [PosMulMono α] [PosMulMonoRev α] (a0 : 0 < a) : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_left a0)
                -- 🎉 no goals
#align mul_le_iff_le_one_right mul_le_iff_le_one_right

@[simp]
theorem mul_lt_iff_lt_one_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_left a0)
                -- 🎉 no goals
#align mul_lt_iff_lt_one_right mul_lt_iff_lt_one_right

/-! Lemmas of the form `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`,
which assume right covariance. -/


@[simp]
theorem le_mul_iff_one_le_left [MulPosMono α] [MulPosMonoRev α] (a0 : 0 < a) : a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_right a0)
                -- 🎉 no goals
#align le_mul_iff_one_le_left le_mul_iff_one_le_left

@[simp]
theorem lt_mul_iff_one_lt_left [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_right a0)
                -- 🎉 no goals
#align lt_mul_iff_one_lt_left lt_mul_iff_one_lt_left

@[simp]
theorem mul_le_iff_le_one_left [MulPosMono α] [MulPosMonoRev α] (b0 : 0 < b) : a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_right b0)
                -- 🎉 no goals
#align mul_le_iff_le_one_left mul_le_iff_le_one_left

@[simp]
theorem mul_lt_iff_lt_one_left [MulPosStrictMono α] [MulPosReflectLT α] (b0 : 0 < b) :
    a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_right b0)
                -- 🎉 no goals
#align mul_lt_iff_lt_one_left mul_lt_iff_lt_one_left

/-! Lemmas of the form `1 ≤ b → a ≤ a * b`.

Variants with `< 0` and `≤ 0` instead of `0 <` and `0 ≤` appear in `Mathlib/Algebra/Order/Ring/Defs`
(which imports this file) as they need additional results which are not yet available here. -/


theorem mul_le_of_le_one_left [MulPosMono α] (hb : 0 ≤ b) (h : a ≤ 1) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb
  -- 🎉 no goals
#align mul_le_of_le_one_left mul_le_of_le_one_left

theorem le_mul_of_one_le_left [MulPosMono α] (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb
  -- 🎉 no goals
#align le_mul_of_one_le_left le_mul_of_one_le_left

theorem mul_le_of_le_one_right [PosMulMono α] (ha : 0 ≤ a) (h : b ≤ 1) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha
  -- 🎉 no goals
#align mul_le_of_le_one_right mul_le_of_le_one_right

theorem le_mul_of_one_le_right [PosMulMono α] (ha : 0 ≤ a) (h : 1 ≤ b) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha
  -- 🎉 no goals
#align le_mul_of_one_le_right le_mul_of_one_le_right

theorem mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 0 < b) (h : a < 1) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb
  -- 🎉 no goals
#align mul_lt_of_lt_one_left mul_lt_of_lt_one_left

theorem lt_mul_of_one_lt_left [MulPosStrictMono α] (hb : 0 < b) (h : 1 < a) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb
  -- 🎉 no goals
#align lt_mul_of_one_lt_left lt_mul_of_one_lt_left

theorem mul_lt_of_lt_one_right [PosMulStrictMono α] (ha : 0 < a) (h : b < 1) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha
  -- 🎉 no goals
#align mul_lt_of_lt_one_right mul_lt_of_lt_one_right

theorem lt_mul_of_one_lt_right [PosMulStrictMono α] (ha : 0 < a) (h : 1 < b) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha
  -- 🎉 no goals
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


theorem mul_le_of_le_one_of_le_of_nonneg [MulPosMono α] (ha : a ≤ 1) (h : b ≤ c) (hb : 0 ≤ b)
    : a * b ≤ c :=
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

theorem le_mul_of_one_le_of_le_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (bc : b ≤ c) (c0 : 0 ≤ c)
    : b ≤ a * c :=
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
  -- ⊢ ∃ b, b * b ≤ a
  · exact ⟨a, (mul_lt_of_lt_one_right a0 ha).le⟩
    -- 🎉 no goals
  · exact ⟨1, by rwa [mul_one]⟩
    -- 🎉 no goals
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

theorem PosMulReflectLT.toPosMulMonoRev [PosMulReflectLT α] : PosMulMonoRev α :=
  ⟨fun x _ _ h =>
    h.eq_or_lt.elim (le_of_eq ∘ mul_left_cancel₀ x.2.ne.symm) fun h' =>
      (lt_of_mul_lt_mul_left h' x.2.le).le⟩
#align pos_mul_reflect_lt.to_pos_mul_mono_rev PosMulReflectLT.toPosMulMonoRev

theorem posMulMonoRev_iff_posMulReflectLT : PosMulMonoRev α ↔ PosMulReflectLT α :=
  ⟨@PosMulMonoRev.toPosMulReflectLT α _ _, @PosMulReflectLT.toPosMulMonoRev α _ _⟩
#align pos_mul_mono_rev_iff_pos_mul_reflect_lt posMulMonoRev_iff_posMulReflectLT

theorem MulPosReflectLT.toMulPosMonoRev [MulPosReflectLT α] : MulPosMonoRev α :=
  ⟨fun x _ _ h => h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.ne.symm) fun h' =>
    (lt_of_mul_lt_mul_right h' x.2.le).le⟩
#align mul_pos_reflect_lt.to_mul_pos_mono_rev MulPosReflectLT.toMulPosMonoRev

theorem mulPosMonoRev_iff_mulPosReflectLT : MulPosMonoRev α ↔ MulPosReflectLT α :=
  ⟨@MulPosMonoRev.toMulPosReflectLT α _ _, @MulPosReflectLT.toMulPosMonoRev α _ _⟩
#align mul_pos_mono_rev_iff_mul_pos_reflect_lt mulPosMonoRev_iff_mulPosReflectLT

end PartialOrder

end CancelMonoidWithZero

section CommSemigroupHasZero

variable [CommSemigroup α] [Zero α] [Preorder α]

theorem posMulStrictMono_iff_mulPosStrictMono : PosMulStrictMono α ↔ MulPosStrictMono α := by
  simp only [PosMulStrictMono, MulPosStrictMono, mul_comm]
  -- 🎉 no goals
#align pos_mul_strict_mono_iff_mul_pos_strict_mono posMulStrictMono_iff_mulPosStrictMono

theorem posMulReflectLT_iff_mulPosReflectLT : PosMulReflectLT α ↔ MulPosReflectLT α := by
  simp only [PosMulReflectLT, MulPosReflectLT, mul_comm]
  -- 🎉 no goals
#align pos_mul_reflect_lt_iff_mul_pos_reflect_lt posMulReflectLT_iff_mulPosReflectLT

theorem posMulMono_iff_mulPosMono : PosMulMono α ↔ MulPosMono α := by
  simp only [PosMulMono, MulPosMono, mul_comm]
  -- 🎉 no goals
#align pos_mul_mono_iff_mul_pos_mono posMulMono_iff_mulPosMono

theorem posMulMonoRev_iff_mulPosMonoRev : PosMulMonoRev α ↔ MulPosMonoRev α := by
  simp only [PosMulMonoRev, MulPosMonoRev, mul_comm]
  -- 🎉 no goals
#align pos_mul_mono_rev_iff_mul_pos_mono_rev posMulMonoRev_iff_mulPosMonoRev

end CommSemigroupHasZero
