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

## TODO

Replace instances of `Cardinal.lift x = Cardinal.lift y` or `Ordinal.lift x = Ordinal.lift y` by
`x =ᵤ y`, and likewise for the other order relations.
-/

universe u v w

variable {α : Type u} {β : Type v} {γ δ : Type*}
  [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]
  [WellFoundedLT α] [WellFoundedLT β] [WellFoundedLT γ] [WellFoundedLT δ]
  {x : α} {y : β} {z : γ}

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
theorem InitialSeg.cmp_congr
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

@[simp]
theorem liftEQ_iff_eq {y : α} : x =ᵤ y ↔ x = y :=
  (liftEQ_iff (InitialSeg.refl _) (InitialSeg.refl _)).symm

@[simp]
theorem liftLE_iff_le {y : α} : x ≤ᵤ y ↔ x ≤ y :=
  (liftLE_iff (InitialSeg.refl _) (InitialSeg.refl _)).symm

@[simp]
theorem liftLT_iff_lt {y : α} : x <ᵤ y ↔ x < y :=
  (liftLT_iff (InitialSeg.refl _) (InitialSeg.refl _)).symm

alias ⟨_, LE.le.liftLE⟩ := liftLE_iff_le
alias ⟨_, LT.lt.liftLT⟩ := liftLT_iff_lt

instance : IsEquiv α (· =ᵤ ·) := by
  convert inferInstanceAs (IsEquiv α (· = ·)); ext; simp

instance : IsLinearOrder α (· ≤ᵤ ·) := by
  convert inferInstanceAs (IsLinearOrder α (· ≤ ·)); ext; simp

instance : IsWellOrder α (· <ᵤ ·) := by
  convert inferInstanceAs (IsWellOrder α (· < ·)); ext; simp

@[refl] theorem liftEQ.refl (x : α) : x =ᵤ x := by simp
@[refl] theorem liftLE.refl (x : α) : x ≤ᵤ x := by simp
theorem liftLT_irrefl (x : α) : ¬ x <ᵤ x := by simp

theorem liftLE_of_liftEQ (h : x =ᵤ y) : x ≤ᵤ y := h.le
theorem liftLE_of_liftLT (h : x <ᵤ y) : x ≤ᵤ y := h.le
theorem liftLE_iff_liftLT_or_liftEQ : x ≤ᵤ y ↔ x <ᵤ y ∨ x =ᵤ y := le_iff_lt_or_eq

alias liftEQ.liftLE := liftLE_of_liftEQ
alias liftLT.liftLE := liftLE_of_liftLT

theorem liftEQ.comm : x =ᵤ y ↔ y =ᵤ x := by
  rw [← liftEQ_iff (γ := α ⊕ₗ β) (RelEmbedding.sumLexInr _ _).collapse (InitialSeg.leAdd _ _),
    eq_comm, liftEQ_iff]

@[symm] alias ⟨liftEQ.symm, _⟩ := liftEQ.comm

@[simp]
theorem not_liftLE : ¬ x ≤ᵤ y ↔ y <ᵤ x := by
  rw [← liftLE_iff (γ := α ⊕ₗ β) (InitialSeg.leAdd _ _) (RelEmbedding.sumLexInr _ _).collapse,
    not_le, liftLT_iff]

@[simp]
theorem not_liftLT : ¬ x <ᵤ y ↔ y ≤ᵤ x := by
  rw [← not_liftLE, not_not]

theorem liftLE_antisymm_iff : x =ᵤ y ↔ x ≤ᵤ y ∧ y ≤ᵤ x := by
  rw [← liftLE_iff (γ := α ⊕ₗ β) (RelEmbedding.sumLexInr _ _).collapse (InitialSeg.leAdd _ _)]
  exact le_antisymm_iff

theorem liftLE_antisymm (h₁ : x ≤ᵤ y) (h₂ : y ≤ᵤ x) : x =ᵤ y :=
  liftLE_antisymm_iff.2 ⟨h₁, h₂⟩

alias liftLE.antisymm := liftLE_antisymm

theorem liftLE_total (x : α) (y : β) : x ≤ᵤ y ∨ y ≤ᵤ x := by
  rw [← liftLE_iff (γ := α ⊕ₗ β) (RelEmbedding.sumLexInr _ _).collapse (InitialSeg.leAdd _ _)]
  exact le_total ..

theorem liftLT_trichotomy (x : α) (y : β) : x <ᵤ y ∨ x =ᵤ y ∨ y <ᵤ x := by
  rw [← liftEQ_iff (γ := α ⊕ₗ β) (InitialSeg.leAdd _ _) (RelEmbedding.sumLexInr _ _).collapse,
    ← liftLT_iff (γ := α ⊕ₗ β) (RelEmbedding.sumLexInr _ _).collapse (InitialSeg.leAdd _ _)]
  exact lt_trichotomy ..

theorem liftLE_trans (h₁ : x ≤ᵤ y) (h₂ : y ≤ᵤ z) : x ≤ᵤ z := by
  let f : α ≤i α ⊕ₗ β ⊕ₗ γ := InitialSeg.leAdd _ _
  let g : β ≤i α ⊕ₗ β ⊕ₗ γ := (InitialSeg.leAdd _ _).trans (RelEmbedding.sumLexInr _ _).collapse
  let h : γ ≤i α ⊕ₗ β ⊕ₗ γ := (RelEmbedding.sumLexInr _ _).collapse.trans
    (RelEmbedding.sumLexInr _ _).collapse
  rw [← liftLE_iff f g] at h₁
  rw [← liftLE_iff g h] at h₂
  rw [← liftLE_iff f h]
  exact h₁.trans h₂

theorem liftLT_of_liftLT_of_liftLE (h₁ : x <ᵤ y) (h₂ : y ≤ᵤ z) : x <ᵤ z := by
  let f : α ≤i α ⊕ₗ β ⊕ₗ γ := InitialSeg.leAdd _ _
  let g : β ≤i α ⊕ₗ β ⊕ₗ γ := (InitialSeg.leAdd _ _).trans (RelEmbedding.sumLexInr _ _).collapse
  let h : γ ≤i α ⊕ₗ β ⊕ₗ γ := (RelEmbedding.sumLexInr _ _).collapse.trans
    (RelEmbedding.sumLexInr _ _).collapse
  rw [← liftLT_iff f g] at h₁
  rw [← liftLE_iff g h] at h₂
  rw [← liftLT_iff f h]
  exact h₁.trans_le h₂

theorem liftLT_of_liftLE_of_liftLT (h₁ : x ≤ᵤ y) (h₂ : y <ᵤ z) : x <ᵤ z := by
  let f : α ≤i α ⊕ₗ β ⊕ₗ γ := InitialSeg.leAdd _ _
  let g : β ≤i α ⊕ₗ β ⊕ₗ γ := (InitialSeg.leAdd _ _).trans (RelEmbedding.sumLexInr _ _).collapse
  let h : γ ≤i α ⊕ₗ β ⊕ₗ γ := (RelEmbedding.sumLexInr _ _).collapse.trans
    (RelEmbedding.sumLexInr _ _).collapse
  rw [← liftLE_iff f g] at h₁
  rw [← liftLT_iff g h] at h₂
  rw [← liftLT_iff f h]
  exact h₁.trans_lt h₂

theorem liftLT_trans (h₁ : x <ᵤ y) (h₂ : y <ᵤ z) : x <ᵤ z :=
  liftLT_of_liftLE_of_liftLT h₁.liftLE h₂

theorem liftEQ_trans (h₁ : x =ᵤ y) (h₂ : y =ᵤ z) : x =ᵤ z :=
  (liftLE_trans h₁.liftLE h₂.liftLE).antisymm (liftLE_trans h₂.symm.liftLE h₁.symm.liftLE)

theorem liftLE_of_liftLE_of_liftEQ (h₁ : x ≤ᵤ y) (h₂ : y =ᵤ z) : x ≤ᵤ z :=
  liftLE_trans h₁ h₂.liftLE

theorem liftLE_of_liftEQ_of_liftLE (h₁ : x =ᵤ y) (h₂ : y ≤ᵤ z) : x ≤ᵤ z :=
  liftLE_trans h₁.liftLE h₂

theorem liftLT_of_liftLT_of_liftEQ (h₁ : x <ᵤ y) (h₂ : y =ᵤ z) : x <ᵤ z :=
  liftLT_of_liftLT_of_liftLE h₁ h₂.liftLE

theorem liftLT_of_liftEQ_of_liftLT (h₁ : x =ᵤ y) (h₂ : y <ᵤ z) : x <ᵤ z :=
  liftLT_of_liftLE_of_liftLT h₁.liftLE h₂

alias liftLE.trans := liftLE_trans
alias liftLT.trans_liftLE := liftLT_of_liftLT_of_liftLE
alias liftLE.trans_liftLT := liftLT_of_liftLE_of_liftLT
alias liftLT.trans := liftLT_trans
alias liftEQ.trans := liftEQ_trans
alias liftEQ.trans_liftLE := liftLE_of_liftEQ_of_liftLE
alias liftLE.trans_liftEQ := liftLE_of_liftLE_of_liftEQ
alias liftEQ.trans_liftLT := liftLT_of_liftEQ_of_liftLT
alias liftLT.trans_liftEQ := liftLT_of_liftLT_of_liftEQ

instance : @Trans α β γ (· ≤ᵤ ·) (· ≤ᵤ ·) (· ≤ᵤ ·) where trans := liftLE_trans
instance : @Trans α β γ (· <ᵤ ·) (· ≤ᵤ ·) (· <ᵤ ·) where trans := liftLT_of_liftLT_of_liftLE
instance : @Trans α β γ (· ≤ᵤ ·) (· <ᵤ ·) (· <ᵤ ·) where trans := liftLT_of_liftLE_of_liftLT
instance : @Trans α β γ (· <ᵤ ·) (· <ᵤ ·) (· <ᵤ ·) where trans := liftLT_trans
instance : @Trans α β γ (· =ᵤ ·) (· =ᵤ ·) (· =ᵤ ·) where trans := liftEQ_trans
instance : @Trans α β γ (· ≤ᵤ ·) (· =ᵤ ·) (· ≤ᵤ ·) where trans := liftLE_of_liftLE_of_liftEQ
instance : @Trans α β γ (· =ᵤ ·) (· ≤ᵤ ·) (· ≤ᵤ ·) where trans := liftLE_of_liftEQ_of_liftLE
instance : @Trans α β γ (· <ᵤ ·) (· =ᵤ ·) (· <ᵤ ·) where trans := liftLT_of_liftLT_of_liftEQ
instance : @Trans α β γ (· =ᵤ ·) (· <ᵤ ·) (· <ᵤ ·) where trans := liftLT_of_liftEQ_of_liftLT

namespace InitialSeg

theorem apply_liftEQ (f : α ≤i β) (x : α) : f x =ᵤ x :=
  liftEQ.intro (.refl _) f rfl

variable {f : α ≤i γ} {g : β ≤i δ}

@[simp]
theorem apply_liftLE_iff : f x ≤ᵤ y ↔ x ≤ᵤ y :=
  ⟨(apply_liftEQ f x).symm.trans_liftLE, (apply_liftEQ f x).trans_liftLE⟩

@[simp]
theorem liftLE_apply_iff : y ≤ᵤ f x ↔ y ≤ᵤ x :=
  ⟨fun h ↦ h.trans_liftEQ (apply_liftEQ f x), fun h ↦ h.trans_liftEQ (apply_liftEQ f x).symm⟩

theorem apply_liftLE_apply_iff : f x ≤ᵤ g y ↔ x ≤ᵤ y := by simp

@[simp] theorem apply_liftEQ_iff : f x =ᵤ y ↔ x =ᵤ y := by simp [liftLE_antisymm_iff]
@[simp] theorem liftEQ_apply_iff : y =ᵤ f x ↔ y =ᵤ x := by simp [liftLE_antisymm_iff]
theorem apply_liftEQ_apply_iff : f x =ᵤ g y ↔ x =ᵤ y := by simp

@[simp] theorem apply_liftLT_iff : f x <ᵤ y ↔ x <ᵤ y := by simp [← not_liftLE]
@[simp] theorem liftLT_apply_iff : y <ᵤ f x ↔ y <ᵤ x := by simp [← not_liftLE]
theorem apply_liftLT_apply_iff : f x <ᵤ g y ↔ x <ᵤ y := by simp

end InitialSeg
