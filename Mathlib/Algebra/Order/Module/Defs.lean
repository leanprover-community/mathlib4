/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Algebra.SMulWithZero
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Order.Module.Synonym

/-!
# Scalar multiplication by ·positive· elements is monotonic

Let `α` be a type with `<` and `0`.  We use the type `{x : α // 0 < x}` of positive elements of `α`
to prove results about monotonicity of scalar multiplication.  We also introduce the local notation `α>0`
for the subtype `{x : α // 0 < x}`:

If the type `α` also has a scalar multiplication, then we combine this with (`Contravariant`)
`CovariantClass`es to assume that scalar multiplication by positive elements is (strictly) monotone on a
`SMulZeroClass`, `MonoidWithZero`,...
More specifically, we use extensively the following typeclasses:

• monotone left
• • `CovariantClass α>0 β (fun a b ↦ (a : α) • b) (≤)`, abbreviated `PosSMulMono α`,
    expressing that scalar multiplication by positive elements on the left is monotone;
• • `CovariantClass α>0 β (fun a b ↦ (a : α) • b) (<)`, abbreviated `PosSMulStrictMono α`,
    expressing that scalar multiplication by positive elements on the left is strictly monotone;
• reverse monotone left
• • `ContravariantClass α>0 β (fun a b ↦ (a : α) • b) (≤)`, abbreviated `PosSMulMonoRev α`,
    expressing that scalar multiplication by positive elements on the left is reverse monotone;
• • `ContravariantClass α>0 β (fun a b ↦ (a : α) • b) (<)`, abbreviated `PosSMulReflectLT α`,
    expressing that scalar multiplication by positive elements on the left is strictly reverse monotone;

## Notation

The following is local notation in this file:
• `α≥0`: `{x : α // 0 ≤ x}`
• `α>0`: `{x : α // 0 < x}`
-/

class CovariantClass' (α β γ : Type*) (μ : α → β → γ) (r : α → α → Prop) (s : γ → γ → Prop) : Prop
    where
  elim : ∀ b ⦃a₁ a₂⦄, r a₁ a₂ → s (μ a₁ b) (μ a₂ b)

class ContravariantClass' (α β γ : Type*) (μ : α → β → γ) (r : α → α → Prop) (s : γ → γ → Prop) : Prop
    where
  elim : ∀ b ⦃a₁ a₂⦄, s (μ a₁ b) (μ a₂ b) → r a₁ a₂

variable (α β : Type*)

set_option quotPrecheck false in
/-- Local notation for the nonnegative elements of a type `α`. TODO: actually make local. -/
notation "α≥0" => {x : α // 0 ≤ x}

set_option quotPrecheck false in
/-- Local notation for the positive elements of a type `α`. TODO: actually make local. -/
notation "α>0" => {x : α // 0 < x}

set_option quotPrecheck false in
/-- Local notation for the nonnegative elements of a type `α`. TODO: actually make local. -/
notation "β≥0" => {x : β // 0 ≤ x}

set_option quotPrecheck false in
/-- Local notation for the positive elements of a type `α`. TODO: actually make local. -/
notation "β>0" => {x : β // 0 < x}

section Abbreviations
variable [SMul α β] [Preorder α] [Preorder β]

section Left
variable [Zero α]

/-- Typeclass for monotonicity of scalar multiplication by nonnegative elements on the left,
namely `b₁ ≤ b₂ → a • b₁ ≤ a • b₂` if `0 ≤ a`.

This is an abbreviation for `CovariantClass α≥0 β (fun a b ↦ (a : α) • b) (≤)`,
expressing that scalar multiplication by nonnegative elements on the left is monotone. -/
abbrev PosSMulMono : Prop := CovariantClass α≥0 β (fun a b ↦ (a : α) • b) (· ≤ ·)

/-- `PosSMulStrictMono α` is an abbreviation for `CovariantClass α>0 β (fun a b ↦ (a : α) • b) (<)`,
expressing that scalar multiplication by positive elements on the left is strictly monotone. -/
abbrev PosSMulStrictMono : Prop := CovariantClass α>0 β (fun a b ↦ (a : α) • b) (· < ·)

/-- `PosSMulReflectLT α` is an abbreviation for `ContravariantClass α≥0 β (fun a b ↦ (a : α) • b) (<)`,
expressing that scalar multiplication by nonnegative elements on the left is strictly reverse monotone. -/
abbrev PosSMulReflectLT : Prop := ContravariantClass α≥0 β (fun a b ↦ (a : α) • b) (· < ·)

/-- `PosSMulMonoRev α` is an abbreviation for `ContravariantClass α>0 β (fun a b ↦ (a : α) • b) (≤)`,
expressing that scalar multiplication by positive elements on the left is reverse monotone. -/
abbrev PosSMulMonoRev : Prop := ContravariantClass α>0 β (fun a b ↦ (a : α) • b) (· ≤ ·)

end Left

section Right
variable [Zero β]

/-- `SMulPosMono α` is an abbreviation for `CovariantClass' α β≥0 (fun a b ↦ (a : α) • b) (≤) (≤)`,
expressing that multiplication by nonnegative elements on the right is monotone. -/
abbrev SMulPosMono : Prop := CovariantClass' α β≥0 β (fun a b ↦ a • b) (· ≤ ·) (· ≤ ·)

/-- `SMulPosStrictMono α` is an abbreviation for `CovariantClass α β>0 (fun a b ↦ a • b) (<) (<)`,
expressing that scalar multiplication by positive elements on the right is strictly monotone. -/
abbrev SMulPosStrictMono : Prop := CovariantClass' α β>0 β (fun a b ↦ (a : α) • b) (· < ·) (· < ·)

/-- `SMulPosReflectLT α` is an abbreviation for `ContravariantClas α≥0 α (fun a b ↦ a • b) (<)`,
expressing that scalar multiplication by nonnegative elements on the right is strictly reverse monotone. -/
abbrev SMulPosReflectLT : Prop := ContravariantClass' α β≥0 β (fun a b ↦ a • b) (· < ·) (· < ·)

/-- `SMulPosMonoRev α` is an abbreviation for `ContravariantClas α>0 α (fun a b ↦ (a : α) • b) (≤)`,
expressing that smultiplication by positive elements on the right is reverse monotone. -/
abbrev SMulPosMonoRev : Prop := ContravariantClass' α β>0 β (fun a b ↦ a • b) (· ≤ ·) (· ≤ ·)

end Right
end Abbreviations

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

section SMul
variable [SMul α β]

section Preorder
variable [Preorder α] [Preorder β]

section Left
variable [Zero α]

lemma monotone_smul_left_of_nonneg [PosSMulMono α β] (ha : 0 ≤ a) : Monotone ((a • ·) : β → β) :=
  @CovariantClass.elim α≥0 β (fun a b ↦ (a : α) • b) (· ≤ ·) _ ⟨a, ha⟩

lemma strictMono_smul_left_of_pos [PosSMulStrictMono α β] (ha : 0 < a) :
     StrictMono ((a • ·) : β → β) :=
  @CovariantClass.elim α>0 β (fun a b ↦ (a : α) • b) (· < ·) _ ⟨a, ha⟩

lemma smul_le_smul_of_nonneg_left [PosSMulMono α β] (hb : b₁ ≤ b₂) (ha : 0 ≤ a) : a • b₁ ≤ a • b₂ :=
  monotone_smul_left_of_nonneg ha hb

lemma smul_lt_smul_of_pos_left [PosSMulStrictMono α β] (hb : b₁ < b₂) (ha : 0 < a) :
    a • b₁ < a • b₂ := strictMono_smul_left_of_pos ha hb

lemma lt_of_smul_lt_smul_left [PosSMulReflectLT α β] (h : a • b₁ < a • b₂) (ha : 0 ≤ a) : b₁ < b₂ :=
  @ContravariantClass.elim α≥0 β (fun a b ↦ (a : α) • b) (· < ·) _ ⟨a, ha⟩ _ _ h

lemma le_of_smul_le_smul_left [PosSMulMonoRev α β] (h : a • b₁ ≤ a • b₂) (ha : 0 < a) : b₁ ≤ b₂ :=
  @ContravariantClass.elim α>0 β (fun a b ↦ (a : α) • b) (· ≤ ·) _ ⟨a, ha⟩ _ _ h

alias lt_of_smul_lt_smul_of_nonneg_left := lt_of_smul_lt_smul_left
alias le_of_smul_le_smul_of_pos_left := le_of_smul_le_smul_left

instance PosSMulMono.to_covariantClass_pos_smul_le [PosSMulMono α β] :
    CovariantClass α>0 β (fun a b ↦ (a : α) • b) (· ≤ ·) :=
  ⟨fun a _ _ hb ↦ smul_le_smul_of_nonneg_left hb a.2.le⟩

instance PosSMulReflectLT.to_contravariantClass_pos_smul_lt [PosSMulReflectLT α β] :
    ContravariantClass α>0 β (fun a b ↦ (a : α) • b) (· < ·) :=
  ⟨fun a _ _ hb ↦ lt_of_smul_lt_smul_of_nonneg_left hb a.2.le⟩

@[simp]
lemma smul_le_smul_iff_of_pos_left [PosSMulMono α β] [PosSMulMonoRev α β] (ha : 0 < a) :
    a • b₁ ≤ a • b₂ ↔ b₁ ≤ b₂ :=
  @rel_iff_cov α>0 β (fun a b ↦ (a : α) • b) (· ≤ ·) _ _ ⟨a, ha⟩ _ _

@[simp]
lemma smul_lt_smul_iff_of_pos_left [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    a • b₁ < a • b₂ ↔ b₁ < b₂ :=
  ⟨fun h ↦ lt_of_smul_lt_smul_left h ha.le, fun hb ↦ smul_lt_smul_of_pos_left hb ha⟩

end Left

section Right
variable [Zero β]

lemma monotone_smul_right_of_nonneg [SMulPosMono α β] (hb : 0 ≤ b) : Monotone ((· • b) : α → β) :=
  @CovariantClass'.elim α β≥0 β (fun a b ↦ (a : α) • b) _ _ _ ⟨b, hb⟩

lemma strictMono_smul_right_of_pos [SMulPosStrictMono α β] (hb : 0 < b) :
     StrictMono ((· • b) : α → β) :=
  @CovariantClass'.elim α β>0 β (fun a b ↦ a • b) _ _ _ ⟨b, hb⟩

lemma smul_le_smul_of_nonneg_right [SMulPosMono α β] (ha : a₁ ≤ a₂) (hb : 0 ≤ b) :
    a₁ • b ≤ a₂ • b := monotone_smul_right_of_nonneg hb ha

lemma smul_lt_smul_of_pos_right [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : 0 < b) :
    a₁ • b < a₂ • b := strictMono_smul_right_of_pos hb ha

lemma lt_of_smul_lt_smul_right [SMulPosReflectLT α β] (h : a₁ • b < a₂ • b) (hb : 0 ≤ b) :
    a₁ < a₂ :=
  @ContravariantClass'.elim α β≥0 β (fun a b ↦ a • b) _ _ _ ⟨b, hb⟩ _ _ h

lemma le_of_smul_le_smul_right [SMulPosMonoRev α β] (h : a₁ • b ≤ a₂ • b) (hb : 0 < b) : a₁ ≤ a₂ :=
  @ContravariantClass'.elim α β>0 β (fun a b ↦ (a : α) • b) _ _ _ ⟨b, hb⟩ _ _ h

alias lt_of_smul_lt_smul_of_nonneg_right := lt_of_smul_lt_smul_right
alias le_of_smul_le_smul_of_pos_right := le_of_smul_le_smul_right

instance SMulPosMono.to_covariantClass_pos_smul_le [SMulPosMono α β] :
    CovariantClass' α β>0 β (fun a b ↦ a • b) (· ≤ ·) (· ≤ ·) :=
  ⟨fun a _ _ hb ↦ smul_le_smul_of_nonneg_right hb a.2.le⟩

instance SMulPosReflectLT.to_contravariantClass_pos_smul_lt [SMulPosReflectLT α β] :
    ContravariantClass' α β>0 β (fun a b ↦ a • b) (· < ·) (· < ·) :=
  ⟨fun b _ _ ha => @ContravariantClass'.elim α β≥0 β (fun a b ↦ a • b) _ _ _ ⟨_, b.2.le⟩ _ _ ha⟩

@[simp]
lemma smul_le_smul_iff_of_pos_right [SMulPosMono α β] [SMulPosMonoRev α β] (hb : 0 < b) :
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
instance (priority := 100) PosSMulStrictMono.toPosSMulMonoRev [PosSMulStrictMono α β] :
    PosSMulMonoRev α β :=
  ⟨(covariant_lt_iff_contravariant_le _ _ _).1 CovariantClass.elim⟩

lemma PosSMulMonoRev.toPosSMulStrictMono [PosSMulMonoRev α β] : PosSMulStrictMono α β :=
  ⟨(covariant_lt_iff_contravariant_le _ _ _).2 ContravariantClass.elim⟩

lemma posSMulStrictMono_iff_posSMulMonoRev : PosSMulStrictMono α β ↔ PosSMulMonoRev α β :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ PosSMulMonoRev.toPosSMulStrictMono⟩

lemma PosSMulMono.toPosSMulReflectLT [PosSMulMono α β] : PosSMulReflectLT α β :=
  ⟨(covariant_le_iff_contravariant_lt _ _ _).1 CovariantClass.elim⟩

lemma PosSMulReflectLT.toPosSMulMono [PosSMulReflectLT α β] : PosSMulMono α β :=
  ⟨(covariant_le_iff_contravariant_lt _ _ _).2 ContravariantClass.elim⟩

lemma posSMulMono_iff_posSMulReflectLT : PosSMulMono α β ↔ PosSMulReflectLT α β :=
  ⟨fun _ ↦ PosSMulMono.toPosSMulReflectLT, fun _ ↦ PosSMulReflectLT.toPosSMulMono⟩

end Left

section Right
variable [Zero β]

lemma SMulPosMonoRev.toSMulPosStrictMono [SMulPosMonoRev α β] : SMulPosStrictMono α β :=
  ⟨fun b _a₁ _a₂ ha ↦ not_le.1 fun h ↦ ha.not_le $ le_of_smul_le_smul_of_pos_right h b.2⟩

lemma SMulPosReflectLT.toSMulPosMono [SMulPosReflectLT α β] : SMulPosMono α β :=
  ⟨fun b _a₁ _a₂ ha ↦ not_lt.1 fun h ↦ ha.not_lt $ lt_of_smul_lt_smul_right h b.2⟩

end Right
end LinearOrder

section LinearOrder
variable [LinearOrder α] [Preorder β]

section Right
variable [Zero β]

-- See note [lower instance priority]
instance (priority := 100) SMulPosStrictMono.toSMulPosMonoRev [SMulPosStrictMono α β] :
    SMulPosMonoRev α β :=
  ⟨fun b _a₁ _a₂ h ↦ not_lt.1 fun ha ↦ h.not_lt $ smul_lt_smul_of_pos_right ha b.2⟩

lemma SMulPosMono.toSMulPosReflectLT [SMulPosMono α β] : SMulPosReflectLT α β :=
  ⟨fun b _a₁ _a₂ h ↦ not_le.1 fun ha ↦ h.not_le $ smul_le_smul_of_nonneg_right ha b.2⟩

end Right
end LinearOrder

section LinearOrder
variable [LinearOrder α] [LinearOrder β]

section Right
variable [Zero β]

lemma smulPosStrictMono_iff_smulPosMonoRev : SMulPosStrictMono α β ↔ SMulPosMonoRev α β :=
  ⟨@SMulPosStrictMono.toSMulPosMonoRev _ _ _ _ _ _, @SMulPosMonoRev.toSMulPosStrictMono _ _ _ _ _ _⟩

lemma smulPosMono_iff_smulPosReflectLT : SMulPosMono α β ↔ SMulPosReflectLT α β :=
  ⟨@SMulPosMono.toSMulPosReflectLT _ _ _ _ _ _, @SMulPosReflectLT.toSMulPosMono _ _ _ _ _ _⟩

end Right
end LinearOrder
end SMul

section SMulZeroClass
variable [Zero α] [Zero β] [SMulZeroClass α β]

section Preorder
variable [Preorder α] [Preorder β]

lemma smul_pos [PosSMulStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0 < a • b := by
  simpa only [smul_zero] using smul_lt_smul_of_pos_left hb ha

lemma smul_neg_of_pos_of_neg [PosSMulStrictMono α β] (ha : 0 < a) (hb : b < 0) : a • b < 0 := by
  simpa only [smul_zero] using smul_lt_smul_of_pos_left hb ha

@[simp]
lemma smul_pos_iff_of_pos_left [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    0 < a • b ↔ 0 < b := by
  simpa only [smul_zero] using smul_lt_smul_iff_of_pos_left ha (b₁ := 0) (b₂ := b)

lemma smul_nonneg [PosSMulMono α β] (ha : 0 ≤ a) (hb : 0 ≤ b₁) : 0 ≤ a • b₁ := by
  simpa only [smul_zero] using smul_le_smul_of_nonneg_left hb ha

lemma smul_nonpos_of_nonneg_of_nonpos [PosSMulMono α β] (ha : 0 ≤ a) (hb : b ≤ 0) : a • b ≤ 0 := by
  simpa only [smul_zero] using smul_le_smul_of_nonneg_left hb ha

lemma pos_of_smul_pos_right [PosSMulReflectLT α β] (h : 0 < a • b) (ha : 0 ≤ a) : 0 < b :=
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

@[simp]
lemma smul_pos_iff_of_pos_right [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) :
    0 < a • b ↔ 0 < a := by
  simpa only [zero_smul] using smul_lt_smul_iff_of_pos_right hb (a₁ := 0) (a₂ := a)

lemma smul_nonneg' [SMulPosMono α β] (ha : 0 ≤ a) (hb : 0 ≤ b₁) : 0 ≤ a • b₁ := by
  simpa only [zero_smul] using smul_le_smul_of_nonneg_right ha hb

lemma smul_nonpos_of_nonpos_of_nonneg [SMulPosMono α β] (ha : a ≤ 0) (hb : 0 ≤ b) : a • b ≤ 0 := by
  simpa only [zero_smul] using smul_le_smul_of_nonneg_right ha hb

lemma pos_of_smul_pos_left [SMulPosReflectLT α β] (h : 0 < a • b) (hb : 0 ≤ b) : 0 < a :=
  lt_of_smul_lt_smul_right (by rwa [zero_smul]) hb

lemma pos_iff_pos_of_smul_pos [PosSMulReflectLT α β] [SMulPosReflectLT α β] (hab : 0 < a • b) :
    0 < a ↔ 0 < b :=
  ⟨pos_of_smul_pos_right hab ∘ le_of_lt, pos_of_smul_pos_left hab ∘ le_of_lt⟩

end Preorder

section PartialOrder
variable [PartialOrder α] [Preorder β]

lemma posSMulMono_iff_covariant_pos :
    PosSMulMono α β ↔ CovariantClass α>0 β (fun a b ↦ (a : α) • b) (· ≤ ·) :=
  ⟨@PosSMulMono.to_covariantClass_pos_smul_le _ _ _ _ _ _, fun h ↦
    ⟨fun a b₁ b₂ h ↦ by
      obtain ha | ha := a.2.eq_or_lt
      · simp [← ha]
      · exact @CovariantClass.elim α>0 β (fun a b ↦ (a : α) • b) (· ≤ ·) _ ⟨_, ha⟩ _ _ h⟩⟩

lemma posSMulReflectLT_iff_contravariant_pos :
    PosSMulReflectLT α β ↔ ContravariantClass α>0 β (fun a b ↦ (a : α) • b) (· < ·) :=
  ⟨@PosSMulReflectLT.to_contravariantClass_pos_smul_lt _ _ _ _ _ _, fun h ↦
    ⟨fun a b₁ b₂ h ↦ by
      obtain ha | ha := a.2.eq_or_lt
      · simp [← ha] at h
      · exact @ContravariantClass.elim α>0 β (fun a b ↦ (a : α) • b) (· < ·) _ ⟨_, ha⟩ _ _ h⟩⟩

end PartialOrder

section PartialOrder
variable [Preorder α] [PartialOrder β]

lemma smulPosMono_iff_covariant_pos :
    SMulPosMono α β ↔ CovariantClass' α β>0 β (fun a b ↦ a • b) (· ≤ ·) (· ≤ ·) :=
  ⟨@SMulPosMono.to_covariantClass_pos_smul_le _ _ _ _ _ _, fun h ↦
    ⟨fun b a₁ a₂ h ↦ by
      obtain hb | hb := b.2.eq_or_lt
      · simp [← hb]
      · exact @CovariantClass'.elim α β>0 β (fun a b ↦ a • b) _ _ _ ⟨_, hb⟩ _ _ h⟩⟩

lemma smulPosReflectLT_iff_contravariant_pos :
    SMulPosReflectLT α β ↔ ContravariantClass' α β>0 β (fun a b ↦ a • b) (· < ·) (· < ·) :=
  ⟨@SMulPosReflectLT.to_contravariantClass_pos_smul_lt _ _ _ _ _ _, fun h ↦
    ⟨fun b a₁ a₂ h ↦ by
      obtain hb | hb := b.2.eq_or_lt
      · simp [← hb] at h
      · exact @ContravariantClass'.elim α β>0 β (fun a b ↦ a • b) _ _ _ ⟨_, hb⟩ _ _ h⟩⟩

end PartialOrder

section PartialOrder
variable [PartialOrder α] [PartialOrder β]

-- See note [lower instance priority]
instance (priority := 100) PosSMulStrictMono.toPosSMulMono [PosSMulStrictMono α β] :
    PosSMulMono α β :=
  posSMulMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)

-- See note [lower instance priority]
instance (priority := 100) SMulPosStrictMono.toSMulPosMono [SMulPosStrictMono α β] :
    SMulPosMono α β :=
  smulPosMono_iff_covariant_pos.2
    ⟨fun b ↦ StrictMono.monotone $ fun _a₁ _a₂ ha ↦ smul_lt_smul_of_pos_right ha b.2⟩

-- See note [lower instance priority]
instance (priority := 100) PosSMulMonoRev.toPosSMulReflectLT [PosSMulMonoRev α β] :
    PosSMulReflectLT α β :=
  posSMulReflectLT_iff_contravariant_pos.2
    ⟨fun a b₁ b₂ h ↦ (le_of_smul_le_smul_of_pos_left h.le a.2).lt_of_ne $ by rintro rfl; simp at h⟩

-- See note [lower instance priority]
instance (priority := 100) SMulPosMonoRev.toSMulPosReflectLT [SMulPosMonoRev α β] :
    SMulPosReflectLT α β :=
  smulPosReflectLT_iff_contravariant_pos.2
    ⟨fun b a₁ a₂ h ↦ (le_of_smul_le_smul_of_pos_right h.le b.2).lt_of_ne $ by rintro rfl; simp at h⟩

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
  · refine' Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb ↦ _) hab⟩
    exact smul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_smul] at hab
    exact hab.false.elim
  · refine' Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb ↦ _) hab⟩
    exact smul_nonpos_of_nonneg_of_nonpos ha.le hb

lemma neg_of_smul_pos_right [PosSMulMono α β] [SMulPosMono α β] (h : 0 < a • b) (ha : a ≤ 0) : b < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_smul_pos h).resolve_left fun h ↦ h.1.not_le ha).2

lemma neg_of_smul_pos_left [PosSMulMono α β] [SMulPosMono α β] (h : 0 < a • b) (ha : b ≤ 0) : a < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_smul_pos h).resolve_left fun h ↦ h.2.not_le ha).1

lemma neg_iff_neg_of_smul_pos [PosSMulMono α β] [SMulPosMono α β] (hab : 0 < a • b) : a < 0 ↔ b < 0 :=
  ⟨neg_of_smul_pos_right hab ∘ le_of_lt, neg_of_smul_pos_left hab ∘ le_of_lt⟩

lemma neg_of_smul_neg_left [PosSMulMono α β] (h : a • b < 0) (ha : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun hb ↦ (smul_nonneg ha hb).not_lt h

lemma neg_of_smul_neg_left' [SMulPosMono α β] (h : a • b < 0) (ha : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun hb ↦ (smul_nonneg' ha hb).not_lt h

lemma neg_of_smul_neg_right [PosSMulMono α β] (h : a • b < 0) (hb : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun ha ↦ (smul_nonneg ha hb).not_lt h

lemma neg_of_smul_neg_right' [SMulPosMono α β] (h : a • b < 0) (hb : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun ha ↦ (smul_nonneg' ha hb).not_lt h

end LinearOrder
end SMulWithZero

section MulAction
variable [Monoid α] [Zero α] [Zero β] [MulAction α β]

section Preorder
variable [Preorder α] [Preorder β]

@[simp]
lemma le_smul_iff_one_le_left [SMulPosMono α β] [SMulPosMonoRev α β] (hb : 0 < b) :
    b ≤ a • b ↔ 1 ≤ a := Iff.trans (by rw [one_smul]) (smul_le_smul_iff_of_pos_right hb)

@[simp]
lemma lt_smul_iff_one_lt_left [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) :
    b < a • b ↔ 1 < a := Iff.trans (by rw [one_smul]) (smul_lt_smul_iff_of_pos_right hb)

@[simp]
lemma smul_le_iff_le_one_left [SMulPosMono α β] [SMulPosMonoRev α β] (hb : 0 < b) :
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
  ⟨fun a _b₁ _b₂ hb ↦ (smul_le_smul_of_nonneg_left hb.le a.2.le).lt_of_ne $
    (smul_right_injective _ a.2.ne').ne hb.ne⟩

lemma PosSMulReflectLT.toPosSMulMonoRev [PosSMulReflectLT α β] : PosSMulMonoRev α β :=
  ⟨fun a _b₁ _b₂ h ↦
    h.eq_or_lt.elim (fun h ↦ (smul_right_injective _ a.2.ne' h).le) fun h' ↦
      (lt_of_smul_lt_smul_left h' a.2.le).le⟩

end PartialOrder

section PartialOrder
variable [PartialOrder α] [PartialOrder β]

lemma posSMulMono_iff_posSMulStrictMono : PosSMulMono α β ↔ PosSMulStrictMono α β :=
  ⟨fun _ ↦ PosSMulMono.toPosSMulStrictMono, fun _ ↦ inferInstance⟩

lemma posSMulMonoRev_iff_posSMulReflectLT : PosSMulMonoRev α β ↔ PosSMulReflectLT α β :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ PosSMulReflectLT.toPosSMulMonoRev⟩

end PartialOrder
end Semiring

section Ring
variable [Ring α] [AddCommGroup β] [Module α β] [NoZeroSMulDivisors α β]

section PartialOrder
variable [PartialOrder α] [PartialOrder β]

lemma SMulPosMono.toSMulPosStrictMono [SMulPosMono α β] : SMulPosStrictMono α β :=
  ⟨fun b _a₁ _a₂ ha ↦ (smul_le_smul_of_nonneg_right ha.le b.2.le).lt_of_ne $
    (smul_left_injective _ b.2.ne').ne ha.ne⟩

lemma smulPosMono_iff_smulPosStrictMono : SMulPosMono α β ↔ SMulPosStrictMono α β :=
  ⟨fun _ ↦ SMulPosMono.toSMulPosStrictMono, fun _ ↦ inferInstance⟩

lemma SMulPosReflectLT.toSMulPosMonoRev [SMulPosReflectLT α β] : SMulPosMonoRev α β :=
  ⟨fun b _a₁ _a₂ h ↦ h.eq_or_lt.elim (fun h ↦ (smul_left_injective _ b.2.ne' h).le) fun h' ↦
    (lt_of_smul_lt_smul_right h' b.2.le).le⟩

lemma smulPosMonoRev_iff_smulPosReflectLT : SMulPosMonoRev α β ↔ SMulPosReflectLT α β :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ SMulPosReflectLT.toSMulPosMonoRev⟩

end PartialOrder
end Ring

section OrderedRing
variable [OrderedRing α] [OrderedAddCommGroup β] [Module α β]

instance PosSMulMono.toSMulPosMono [PosSMulMono α β] : SMulPosMono α β where
  elim b a₁ a₂ ha := by rw [←sub_nonneg, ←sub_smul]; exact smul_nonneg (sub_nonneg.2 ha) b.2

instance PosSMulStrictMono.toSMulPosStrictMono [PosSMulStrictMono α β] : SMulPosStrictMono α β where
  elim b a₁ a₂ ha := by rw [←sub_pos, ←sub_smul]; exact smul_pos (sub_pos.2 ha) b.2

end OrderedRing

namespace OrderDual

section Left
variable [Preorder α] [Preorder β] [SMul α β] [Zero α]

instance instPosSMulMono [PosSMulMono α β] : PosSMulMono α βᵒᵈ where
  elim a _b₁ _b₂ hb := smul_le_smul_of_nonneg_left (β := β) hb a.2
instance instPosSMulStrictMono [PosSMulStrictMono α β] : PosSMulStrictMono α βᵒᵈ where
  elim a _b₁ _b₂ hb := smul_lt_smul_of_pos_left (β := β) hb a.2
instance instPosSMulReflectLT [PosSMulReflectLT α β] : PosSMulReflectLT α βᵒᵈ where
  elim a _b₁ _b₂ h := lt_of_smul_lt_smul_of_nonneg_left (β := β) h a.2
instance instPosSMulMonoRev [PosSMulMonoRev α β] : PosSMulMonoRev α βᵒᵈ where
  elim a _b₁ _b₂ h := le_of_smul_le_smul_of_pos_left (β := β) h a.2

end Left

section Right
variable [Preorder α] [Ring α] [OrderedAddCommGroup β] [Module α β]

instance instSMulPosMono [SMulPosMono α β] : SMulPosMono α βᵒᵈ where
  elim b a₁ a₂ ha := by
    rw [←neg_le_neg_iff, ←smul_neg, ←smul_neg]
    exact smul_le_smul_of_nonneg_right (β := β) ha $ neg_nonneg.2 b.2

instance instSMulPosStrictMono [SMulPosStrictMono α β] : SMulPosStrictMono α βᵒᵈ where
  elim b a₁ a₂ ha := by
    rw [←neg_lt_neg_iff, ←smul_neg, ←smul_neg]
    exact smul_lt_smul_of_pos_right (β := β) ha $ neg_pos.2 b.2

instance instSMulPosReflectLT [SMulPosReflectLT α β] : SMulPosReflectLT α βᵒᵈ where
  elim b a₁ a₂ h := by
    rw [←neg_lt_neg_iff, ←smul_neg, ←smul_neg] at h
    exact lt_of_smul_lt_smul_right (β := β) h $ neg_nonneg.2 b.2

instance instSMulPosMonoRev [SMulPosMonoRev α β] : SMulPosMonoRev α βᵒᵈ where
  elim b a₁ a₂ h := by
    rw [←neg_le_neg_iff, ←smul_neg, ←smul_neg] at h
    exact le_of_smul_le_smul_right (β := β) h $ neg_pos.2 b.2

end Right
end OrderDual
