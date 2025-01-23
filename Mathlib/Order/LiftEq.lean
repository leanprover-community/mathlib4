/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.InitialSeg

/-!
# Relating elements of distinct well-orders

Let `α` and `β` be well-ordered sets. There always exists some well-order `γ` such that `α` and `β`
are both initial segments of it. This then allows us to compare elements of `α` and `β` as if they
belonged to the same well-order. Importantly, these relationships are independent of our choice of
`γ`.

The intended usage for this file is to easily compare ordinals or cardinals in different universes.

## Main declarations

* `liftEQ`: two elements have the same order type
* `liftLE`: an element has an order type less or equal to another
* `liftLT`: an element has an order type less than another
-/

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w} [LinearOrder α] [LinearOrder β] [LinearOrder γ]
  [WellFoundedLT α] [WellFoundedLT β] [WellFoundedLT γ]
  {x : α} {y : β}

/-- We write `x =ᵤ y` when the order types of `x` and `y` are equal.

Note that `x` and `y` may come from distinct well-orders, or even well-orders in different
universes. -/
def liftEQ (x : α) (y : β) : Prop :=
  toLex ((InitialSeg.leAdd (· < ·) (· < ·)) x) =
    toLex ((RelEmbedding.sumLexInr (· < ·) (· < ·)).collapse y)

/-- We write `x ≤ᵤ y` when the order type of `x` is less or equal to the order type of `y`.

Note that `x` and `y` may come from distinct well-orders, or even well-orders in different
universes. -/
def liftLE (x : α) (y : β) : Prop :=
  toLex ((InitialSeg.leAdd (· < ·) (· < ·)) x) ≤
    toLex ((RelEmbedding.sumLexInr (· < ·) (· < ·)).collapse y)

/-- We write `x <ᵤ y` when the order type of `x` is less to the order type of `y`.

Note that `x` and `y` may come from distinct well-orders, or even well-orders in different
universes. -/
def liftLT (x : α) (y : β) : Prop :=
  toLex ((InitialSeg.leAdd (· < ·) (· < ·)) x) <
    toLex ((RelEmbedding.sumLexInr (· < ·) (· < ·)).collapse y)

@[inherit_doc] infix:50 " =ᵤ " => liftEQ
@[inherit_doc] infix:50 " ≤ᵤ " => liftLE
@[inherit_doc] infix:50 " <ᵤ " => liftLT

omit [WellFoundedLT α] [WellFoundedLT β] in
theorem InitialSeg.cmp_congr {δ : Type*} [LinearOrder δ] [WellFoundedLT δ]
    (f₁ : α ≤i γ) (g₁ : β ≤i γ) (f₂ : α ≤i δ) (g₂ : β ≤i δ) (x : α) (y : β) :
    cmp (f₁ x) (g₁ y) = cmp (f₂ x) (g₂ y) := by
  obtain h | h := @InitialSeg.total γ δ (· < ·) (· < ·) _ _
  · rw [← h.strictMono.cmp_map_eq, ← InitialSeg.trans_apply, ← InitialSeg.trans_apply,
      ← f₂.eq, ← g₂.eq]
  · rw [← h.strictMono.cmp_map_eq, ← InitialSeg.trans_apply, ← InitialSeg.trans_apply,
      (f₂.trans h).eq, (g₂.trans h).eq]

/-- For any initial segment embeddings `f` and `g` into the same type,
`x =ᵤ y` is equivalent to `f x = g y`. -/
theorem liftEQ_iff (f : α ≤i γ) (g : β ≤i γ) {x : α} {y : β} : f x = g y ↔ x =ᵤ y :=
  eq_iff_eq_of_cmp_eq_cmp <| InitialSeg.cmp_congr (δ := α ⊕ₗ β)
    f g (InitialSeg.leAdd _ _) (RelEmbedding.sumLexInr _ _).collapse x y

/-- For any initial segment embeddings `f` and `g` into the same type,
`x ≤ᵤ y` is equivalent to `f x ≤ g y`. -/
theorem liftLE_iff (f : α ≤i γ) (g : β ≤i γ) {x : α} {y : β} : f x ≤ g y ↔ x ≤ᵤ y :=
  le_iff_le_of_cmp_eq_cmp <| InitialSeg.cmp_congr (δ := α ⊕ₗ β)
    f g (InitialSeg.leAdd _ _) (RelEmbedding.sumLexInr _ _).collapse x y

/-- For any initial segment embeddings `f` and `g` into the same type,
`x <ᵤ y` is equivalent to `f x < g y`. -/
theorem liftLT_iff (f : α ≤i γ) (g : β ≤i γ) {x : α} {y : β} : f x < g y ↔ x <ᵤ y :=
  lt_iff_lt_of_cmp_eq_cmp <| InitialSeg.cmp_congr (δ := α ⊕ₗ β)
    f g (InitialSeg.leAdd _ _) (RelEmbedding.sumLexInr _ _).collapse x y

alias ⟨liftEQ.intro, _⟩ := liftEQ_iff
alias ⟨liftLE.intro, _⟩ := liftLE_iff
alias ⟨liftLT.intro, _⟩ := liftLT_iff

@[refl, simp]
theorem liftEQ_refl (x : α) : x =ᵤ x :=
  liftEQ.intro (InitialSeg.refl _) (InitialSeg.refl _) rfl

@[refl, simp]
theorem liftLE_refl (x : α) : x ≤ᵤ x :=
  liftLE.intro (InitialSeg.refl _) (InitialSeg.refl _) le_rfl

instance : IsRefl α (· =ᵤ ·) where refl := liftEQ_refl
instance : IsRefl α (· ≤ᵤ ·) where refl := liftLE_refl

@[simp]
theorem not_liftLE : ¬ x ≤ᵤ y ↔ y <ᵤ x := by
  rw [← liftLE_iff (γ := α ⊕ₗ β) (InitialSeg.leAdd _ _) (RelEmbedding.sumLexInr _ _).collapse,
    not_le, liftLT_iff]

@[simp]
theorem not_liftLT : ¬ x <ᵤ y ↔ y ≤ᵤ x := by
  rw [← not_liftLE, not_not]

theorem liftLT_irrefl (x : α) : ¬ x <ᵤ x := by
  simp

instance : IsIrrefl α (· <ᵤ ·) where irrefl := liftLT_irrefl
