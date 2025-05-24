/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# `List.count` as a bundled homomorphism

In this file we define `FreeMonoid.countP`, `FreeMonoid.count`, `FreeAddMonoid.countP`, and
`FreeAddMonoid.count`. These are `List.countP` and `List.count` bundled as multiplicative and
additive homomorphisms from `FreeMonoid` and `FreeAddMonoid`.

We do not use `to_additive` too much because it can't map `Multiplicative ℕ` to `ℕ`.
-/

variable {α : Type*} (p : α → Prop) [DecidablePred p]

namespace FreeMonoid
/-- `List.countP` lifted to free monoids -/
@[to_additive "`List.countP` lifted to free additive monoids"]
def countP' (l : FreeMonoid α) : ℕ := l.toList.countP p

@[to_additive]
lemma countP'_one : (1 : FreeMonoid α).countP' p = 0 := rfl

@[to_additive]
lemma countP'_mul (l₁ l₂ : FreeMonoid α) : (l₁ * l₂).countP' p = l₁.countP' p + l₂.countP' p := by
  dsimp [countP']
  simp only [List.countP_append]

/-- `List.countP` as a bundled multiplicative monoid homomorphism. -/
def countP : FreeMonoid α →* Multiplicative ℕ where
  toFun := .ofAdd ∘ FreeMonoid.countP' p
  map_one' := by
    simp [countP'_one p]
  map_mul' x y := by
    simp [countP'_mul p]

theorem countP_apply (l : FreeMonoid α) : l.countP p = .ofAdd (l.toList.countP p) := rfl

lemma countP_of (x : α) : (of x).countP p =
    if p x then Multiplicative.ofAdd 1 else Multiplicative.ofAdd 0 := by
  rw [countP_apply, toList_of, List.countP_singleton, apply_ite (Multiplicative.ofAdd)]
  simp only [decide_eq_true_eq]


/-- `List.count` as a bundled additive monoid homomorphism. -/
def count [DecidableEq α] (x : α) : FreeMonoid α →* Multiplicative ℕ := countP (· = x)

theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) :
    count x l = Multiplicative.ofAdd (l.toList.count x) := rfl

theorem count_of [DecidableEq α] (x y : α) :
    count x (of y) = Pi.mulSingle (M := fun _ => Multiplicative ℕ) x (Multiplicative.ofAdd 1) y :=
  by simp only [count, eq_comm, countP_of, ofAdd_zero, Pi.mulSingle_apply]

end FreeMonoid

namespace FreeAddMonoid

/-- `List.countP` as a bundled additive monoid homomorphism. -/
def countP : FreeAddMonoid α →+ ℕ where
  toFun := FreeAddMonoid.countP' p
  map_zero' := countP'_zero p
  map_add' := countP'_add p

theorem countP_apply (l : FreeAddMonoid α) : l.countP p = l.toList.countP p := rfl

theorem countP_of (x : α) : countP p (of x) = if p x then 1 else 0 := by
  rw [countP_apply, toList_of, List.countP_singleton]
  simp only [decide_eq_true_eq]

/-- `List.count` as a bundled additive monoid homomorphism. -/
-- Porting note: was (x = ·)
def count [DecidableEq α] (x : α) : FreeAddMonoid α →+ ℕ := countP (· = x)

lemma count_of [DecidableEq α] (x y : α) : count x (of y) = (Pi.single x 1 : α → ℕ) y := by
  dsimp [count]
  rw [countP_of]
  simp [Pi.single, Function.update]

theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) : l.count x = l.toList.count x :=
  rfl

end FreeAddMonoid
