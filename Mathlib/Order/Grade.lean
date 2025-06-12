/-
Copyright (c) 2022 Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton, Vladimir Ivanov
-/
import Mathlib.Data.Int.SuccPred
import Mathlib.Order.Fin.Basic

/-!
# Graded orders

This file defines graded orders, also known as ranked orders.

An `𝕆`-graded order is an order `α` equipped with a distinguished "grade" function `α → 𝕆` which
should be understood as giving the "height" of the elements. Usual graded orders are `ℕ`-graded,
cograded orders are `ℕᵒᵈ`-graded, but we can also grade by `ℤ`, and polytopes are naturally
`Fin n`-graded.

Visually, `grade ℕ a` is the height of `a` in the Hasse diagram of `α`.

## Main declarations

* `GradeOrder`: Graded order.
* `GradeMinOrder`: Graded order where minimal elements have minimal grades.
* `GradeMaxOrder`: Graded order where maximal elements have maximal grades.
* `GradeBoundedOrder`: Graded order where minimal elements have minimal grades and maximal
  elements have maximal grades.
* `grade`: The grade of an element. Because an order can admit several gradings, the first argument
  is the order we grade by.

## How to grade your order

Here are the translations between common references and our `GradeOrder`:
* [Stanley][stanley2012] defines a graded order of rank `n` as an order where all maximal chains
  have "length" `n` (so the number of elements of a chain is `n + 1`). This corresponds to
  `GradeBoundedOrder (Fin (n + 1)) α`.
* [Engel][engel1997]'s ranked orders are somewhere between `GradeOrder ℕ α` and
  `GradeMinOrder ℕ α`, in that he requires `∃ a, IsMin a ∧ grade ℕ a = 0` rather than
  `∀ a, IsMin a → grade ℕ a = 0`. He defines a graded order as an order where all minimal elements
  have grade `0` and all maximal elements have the same grade. This is roughly a less bundled
  version of `GradeBoundedOrder (Fin n) α`, assuming we discard orders with infinite chains.

## Implementation notes

One possible definition of graded orders is as the bounded orders whose flags (maximal chains)
all have the same finite length (see Stanley p. 99). However, this means that all graded orders must
have minimal and maximal elements and that the grade is not data.

Instead, we define graded orders by their grade function, without talking about flags yet.

## References

* [Konrad Engel, *Sperner Theory*][engel1997]
* [Richard Stanley, *Enumerative Combinatorics*][stanley2012]
-/

open Nat OrderDual

variable {𝕆 ℙ α β : Type*}

/-- An `𝕆`-graded order is an order `α` equipped with a strictly monotone function
`grade 𝕆 : α → 𝕆` which preserves order covering (`CovBy`). -/
class GradeOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] where
  /-- The grading function. -/
  protected grade : α → 𝕆
  /-- `grade` is strictly monotonic. -/
  grade_strictMono : StrictMono grade
  /-- `grade` preserves `CovBy`. -/
  covBy_grade ⦃a b : α⦄ : a ⋖ b → grade a ⋖ grade b

/-- An `𝕆`-graded order where minimal elements have minimal grades. -/
class GradeMinOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] extends GradeOrder 𝕆 α where
  /-- Minimal elements have minimal grades. -/
  isMin_grade ⦃a : α⦄ : IsMin a → IsMin (grade a)

/-- An `𝕆`-graded order where maximal elements have maximal grades. -/
class GradeMaxOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] extends GradeOrder 𝕆 α where
  /-- Maximal elements have maximal grades. -/
  isMax_grade ⦃a : α⦄ : IsMax a → IsMax (grade a)

/-- An `𝕆`-graded order where minimal elements have minimal grades and maximal elements have maximal
grades. -/
class GradeBoundedOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] extends GradeMinOrder 𝕆 α,
  GradeMaxOrder 𝕆 α

section Preorder -- grading
variable [Preorder 𝕆]

section Preorder -- graded order
variable [Preorder α]

section GradeOrder
variable (𝕆)
variable [GradeOrder 𝕆 α] {a b : α}

/-- The grade of an element in a graded order. Morally, this is the number of elements you need to
go down by to get to `⊥`. -/
def grade : α → 𝕆 :=
  GradeOrder.grade

protected theorem CovBy.grade (h : a ⋖ b) : grade 𝕆 a ⋖ grade 𝕆 b :=
  GradeOrder.covBy_grade h

variable {𝕆}

theorem grade_strictMono : StrictMono (grade 𝕆 : α → 𝕆) :=
  GradeOrder.grade_strictMono

theorem covBy_iff_lt_covBy_grade : a ⋖ b ↔ a < b ∧ grade 𝕆 a ⋖ grade 𝕆 b :=
  ⟨fun h => ⟨h.1, h.grade _⟩,
    And.imp_right fun h _ ha hb => h.2 (grade_strictMono ha) <| grade_strictMono hb⟩

end GradeOrder

section GradeMinOrder

variable (𝕆)
variable [GradeMinOrder 𝕆 α] {a : α}

protected theorem IsMin.grade (h : IsMin a) : IsMin (grade 𝕆 a) :=
  GradeMinOrder.isMin_grade h

variable {𝕆}

@[simp]
theorem isMin_grade_iff : IsMin (grade 𝕆 a) ↔ IsMin a :=
  ⟨grade_strictMono.isMin_of_apply, IsMin.grade _⟩

end GradeMinOrder

section GradeMaxOrder

variable (𝕆)
variable [GradeMaxOrder 𝕆 α] {a : α}

protected theorem IsMax.grade (h : IsMax a) : IsMax (grade 𝕆 a) :=
  GradeMaxOrder.isMax_grade h

variable {𝕆}

@[simp]
theorem isMax_grade_iff : IsMax (grade 𝕆 a) ↔ IsMax a :=
  ⟨grade_strictMono.isMax_of_apply, IsMax.grade _⟩

end GradeMaxOrder

end Preorder

-- graded order
theorem grade_mono [PartialOrder α] [GradeOrder 𝕆 α] : Monotone (grade 𝕆 : α → 𝕆) :=
  grade_strictMono.monotone

section LinearOrder

-- graded order
variable [LinearOrder α] [GradeOrder 𝕆 α] {a b : α}

theorem grade_injective : Function.Injective (grade 𝕆 : α → 𝕆) :=
  grade_strictMono.injective

@[simp]
theorem grade_le_grade_iff : grade 𝕆 a ≤ grade 𝕆 b ↔ a ≤ b :=
  grade_strictMono.le_iff_le

@[simp]
theorem grade_lt_grade_iff : grade 𝕆 a < grade 𝕆 b ↔ a < b :=
  grade_strictMono.lt_iff_lt

@[simp]
theorem grade_eq_grade_iff : grade 𝕆 a = grade 𝕆 b ↔ a = b :=
  grade_injective.eq_iff

theorem grade_ne_grade_iff : grade 𝕆 a ≠ grade 𝕆 b ↔ a ≠ b :=
  grade_injective.ne_iff

theorem grade_covBy_grade_iff : grade 𝕆 a ⋖ grade 𝕆 b ↔ a ⋖ b :=
  (covBy_iff_lt_covBy_grade.trans <| and_iff_right_of_imp fun h => grade_lt_grade_iff.1 h.1).symm

end LinearOrder

-- graded order
end Preorder

-- grading
section PartialOrder

variable [PartialOrder 𝕆] [Preorder α]

@[simp]
theorem grade_bot [OrderBot 𝕆] [OrderBot α] [GradeMinOrder 𝕆 α] : grade 𝕆 (⊥ : α) = ⊥ :=
  (isMin_bot.grade _).eq_bot

@[simp]
theorem grade_top [OrderTop 𝕆] [OrderTop α] [GradeMaxOrder 𝕆 α] : grade 𝕆 (⊤ : α) = ⊤ :=
  (isMax_top.grade _).eq_top

end PartialOrder

/-! ### Instances -/

section Preorder
variable [Preorder 𝕆] [Preorder ℙ] [Preorder α] [Preorder β]

instance Preorder.toGradeBoundedOrder : GradeBoundedOrder α α where
  grade := id
  isMin_grade _ := id
  isMax_grade _ := id
  grade_strictMono := strictMono_id
  covBy_grade _ _ := id

@[simp]
theorem grade_self (a : α) : grade α a = a :=
  rfl

/-! #### Dual -/

instance OrderDual.gradeOrder [GradeOrder 𝕆 α] : GradeOrder 𝕆ᵒᵈ αᵒᵈ where
  grade := toDual ∘ grade 𝕆 ∘ ofDual
  grade_strictMono := grade_strictMono.dual
  covBy_grade _ _ h := (h.ofDual.grade _).toDual

instance OrderDual.gradeMinOrder [GradeMaxOrder 𝕆 α] : GradeMinOrder 𝕆ᵒᵈ αᵒᵈ :=
  { OrderDual.gradeOrder with isMin_grade := fun _ => IsMax.grade (α := α) 𝕆 }

instance OrderDual.gradeMaxOrder [GradeMinOrder 𝕆 α] : GradeMaxOrder 𝕆ᵒᵈ αᵒᵈ :=
  { OrderDual.gradeOrder with isMax_grade := fun _ => IsMin.grade (α := α) 𝕆 }

instance [GradeBoundedOrder 𝕆 α] : GradeBoundedOrder 𝕆ᵒᵈ αᵒᵈ :=
  { OrderDual.gradeMinOrder, OrderDual.gradeMaxOrder with }

@[simp]
theorem grade_toDual [GradeOrder 𝕆 α] (a : α) : grade 𝕆ᵒᵈ (toDual a) = toDual (grade 𝕆 a) :=
  rfl

@[simp]
theorem grade_ofDual [GradeOrder 𝕆 α] (a : αᵒᵈ) : grade 𝕆 (ofDual a) = ofDual (grade 𝕆ᵒᵈ a) :=
  rfl

/-! #### Lifting a graded order -/

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
abbrev GradeOrder.liftLeft [GradeOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) : GradeOrder ℙ α where
  grade := f ∘ grade 𝕆
  grade_strictMono := hf.comp grade_strictMono
  covBy_grade _ _ h := hcovBy _ _ <| h.grade _

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
abbrev GradeMinOrder.liftLeft [GradeMinOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a)) : GradeMinOrder ℙ α :=
  { GradeOrder.liftLeft f hf hcovBy with isMin_grade := fun _ ha => hmin _ <| ha.grade _ }

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
abbrev GradeMaxOrder.liftLeft [GradeMaxOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeMaxOrder ℙ α :=
  { GradeOrder.liftLeft f hf hcovBy with isMax_grade := fun _ ha => hmax _ <| ha.grade _ }

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
abbrev GradeBoundedOrder.liftLeft [GradeBoundedOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a))
    (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeBoundedOrder ℙ α :=
  { GradeMinOrder.liftLeft f hf hcovBy hmin, GradeMaxOrder.liftLeft f hf hcovBy hmax with }

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
abbrev GradeOrder.liftRight [GradeOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) : GradeOrder 𝕆 α where
  grade := grade 𝕆 ∘ f
  grade_strictMono := grade_strictMono.comp hf
  covBy_grade _ _ h := (hcovBy _ _ h).grade _

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
abbrev GradeMinOrder.liftRight [GradeMinOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a)) : GradeMinOrder 𝕆 α :=
  { GradeOrder.liftRight f hf hcovBy with isMin_grade := fun _ ha => (hmin _ ha).grade _ }

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
abbrev GradeMaxOrder.liftRight [GradeMaxOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeMaxOrder 𝕆 α :=
  { GradeOrder.liftRight f hf hcovBy with isMax_grade := fun _ ha => (hmax _ ha).grade _ }

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
abbrev GradeBoundedOrder.liftRight [GradeBoundedOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a))
    (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeBoundedOrder 𝕆 α :=
  { GradeMinOrder.liftRight f hf hcovBy hmin, GradeMaxOrder.liftRight f hf hcovBy hmax with }

/-! #### `Fin n`-graded to `ℕ`-graded to `ℤ`-graded -/


-- See note [reducible non-instances]
/-- A `Fin n`-graded order is also `ℕ`-graded. We do not mark this an instance because `n` is not
inferable. -/
abbrev GradeOrder.finToNat (n : ℕ) [GradeOrder (Fin n) α] : GradeOrder ℕ α :=
  (GradeOrder.liftLeft (_ : Fin n → ℕ) Fin.val_strictMono) fun _ _ => CovBy.coe_fin

-- See note [reducible non-instances]
/-- A `Fin n`-graded order is also `ℕ`-graded. We do not mark this an instance because `n` is not
inferable. -/
abbrev GradeMinOrder.finToNat (n : ℕ) [GradeMinOrder (Fin n) α] : GradeMinOrder ℕ α :=
  (GradeMinOrder.liftLeft (_ : Fin n → ℕ) Fin.val_strictMono fun _ _ => CovBy.coe_fin) fun a h => by
    cases n
    · exact a.elim0
    rw [h.eq_bot, Fin.bot_eq_zero]
    exact isMin_bot

instance GradeOrder.natToInt [GradeOrder ℕ α] : GradeOrder ℤ α :=
  (GradeOrder.liftLeft _ Int.natCast_strictMono) fun _ _ => CovBy.intCast

theorem GradeOrder.wellFoundedLT (𝕆 : Type*) [Preorder 𝕆] [GradeOrder 𝕆 α]
    [WellFoundedLT 𝕆] : WellFoundedLT α :=
  (grade_strictMono (𝕆 := 𝕆)).wellFoundedLT

theorem GradeOrder.wellFoundedGT (𝕆 : Type*) [Preorder 𝕆] [GradeOrder 𝕆 α]
    [WellFoundedGT 𝕆] : WellFoundedGT α :=
  (grade_strictMono (𝕆 := 𝕆)).wellFoundedGT

instance [GradeOrder ℕ α] : WellFoundedLT α :=
  GradeOrder.wellFoundedLT ℕ

instance [GradeOrder ℕᵒᵈ α] : WellFoundedGT α :=
  GradeOrder.wellFoundedGT ℕᵒᵈ

end Preorder

/-!
### Grading a flag

A flag inherits the grading of its ambient order.
-/

namespace Flag
variable [PartialOrder α] {s : Flag α} {a b : s}

@[simp, norm_cast]
lemma coe_wcovBy_coe : (a : α) ⩿ b ↔ a ⩿ b := by
  refine and_congr_right' ⟨fun h c hac ↦ h hac, fun h c hac hcb ↦
    @h ⟨c, mem_iff_forall_le_or_ge.2 fun d hd ↦ ?_⟩ hac hcb⟩
  classical
  obtain hda | had := le_or_gt (⟨d, hd⟩ : s) a
  · exact .inr ((Subtype.coe_le_coe.2 hda).trans hac.le)
  obtain hbd | hdb := le_or_gt b ⟨d, hd⟩
  · exact .inl (hcb.le.trans hbd)
  · cases h had hdb

@[simp, norm_cast]
lemma coe_covBy_coe : (a : α) ⋖ b ↔ a ⋖ b := by simp [covBy_iff_wcovBy_and_not_le]

@[simp]
lemma isMax_coe : IsMax (a : α) ↔ IsMax a where
  mp h b hab := h hab
  mpr h b hab := by
    refine @h ⟨b, mem_iff_forall_le_or_ge.2 fun c hc ↦ ?_⟩ hab
    classical
    exact .inr <| hab.trans' <| h.isTop ⟨c, hc⟩

@[simp]
lemma isMin_coe : IsMin (a : α) ↔ IsMin a where
  mp h b hba := h hba
  mpr h b hba := by
    refine @h ⟨b, mem_iff_forall_le_or_ge.2 fun c hc ↦ ?_⟩ hba
    classical
    exact .inl <| hba.trans <| h.isBot ⟨c, hc⟩

variable [Preorder 𝕆]

instance [GradeOrder 𝕆 α] (s : Flag α) : GradeOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) fun _ _ ↦ coe_covBy_coe.2

instance [GradeMinOrder 𝕆 α] (s : Flag α) : GradeMinOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) (fun _ _ ↦ coe_covBy_coe.2) fun _ ↦ isMin_coe.2

instance [GradeMaxOrder 𝕆 α] (s : Flag α) : GradeMaxOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) (fun _ _ ↦ coe_covBy_coe.2) fun _ ↦ isMax_coe.2

instance [GradeBoundedOrder 𝕆 α] (s : Flag α) : GradeBoundedOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) (fun _ _ ↦ coe_covBy_coe.2) (fun _ ↦ isMin_coe.2)
    fun _ ↦ isMax_coe.2

@[simp, norm_cast] lemma grade_coe [GradeOrder 𝕆 α] (a : s) : grade 𝕆 (a : α) = grade 𝕆 a := rfl

end Flag
