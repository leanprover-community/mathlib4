/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init.Data.Ordering.Basic
import Mathlib.Order.Synonym

#align_import order.compare from "leanprover-community/mathlib"@"c4658a649d216f57e99621708b09dcb3dcccbd23"

/-!
# Comparison

This file provides basic results about orderings and comparison in linear orders.


## Definitions

* `CmpLE`: An `Ordering` from `≤`.
* `Ordering.Compares`: Turns an `Ordering` into `<` and `=` propositions.
* `linearOrderOfCompares`: Constructs a `LinearOrder` instance from the fact that any two
  elements that are not one strictly less than the other either way are equal.
-/


variable {α β : Type*}

/-- Like `cmp`, but uses a `≤` on the type instead of `<`. Given two elements `x` and `y`, returns a
three-way comparison result `Ordering`. -/
def cmpLE {α} [LE α] [@DecidableRel α (· ≤ ·)] (x y : α) : Ordering :=
  if x ≤ y then if y ≤ x then Ordering.eq else Ordering.lt else Ordering.gt
#align cmp_le cmpLE

theorem cmpLE_swap {α} [LE α] [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x y : α) :
    (cmpLE x y).swap = cmpLE y x := by
  by_cases xy:x ≤ y <;> by_cases yx:y ≤ x <;> simp [cmpLE, *, Ordering.swap]
  -- ⊢ Ordering.swap (cmpLE x y) = cmpLE y x
                        -- ⊢ Ordering.swap (cmpLE x y) = cmpLE y x
                        -- ⊢ Ordering.swap (cmpLE x y) = cmpLE y x
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- ⊢ False
  cases not_or_of_not xy yx (total_of _ _ _)
  -- 🎉 no goals
#align cmp_le_swap cmpLE_swap

theorem cmpLE_eq_cmp {α} [Preorder α] [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)]
    [@DecidableRel α (· < ·)] (x y : α) : cmpLE x y = cmp x y := by
  by_cases xy:x ≤ y <;> by_cases yx:y ≤ x <;> simp [cmpLE, lt_iff_le_not_le, *, cmp, cmpUsing]
  -- ⊢ cmpLE x y = cmp x y
                        -- ⊢ cmpLE x y = cmp x y
                        -- ⊢ cmpLE x y = cmp x y
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- ⊢ False
  cases not_or_of_not xy yx (total_of _ _ _)
  -- 🎉 no goals
#align cmp_le_eq_cmp cmpLE_eq_cmp

namespace Ordering

/-- `Compares o a b` means that `a` and `b` have the ordering relation `o` between them, assuming
that the relation `a < b` is defined. -/
-- Porting note: we have removed `@[simp]` here in favour of separate simp lemmas,
-- otherwise this definition will unfold to a match.
def Compares [LT α] : Ordering → α → α → Prop
  | lt, a, b => a < b
  | eq, a, b => a = b
  | gt, a, b => a > b
#align ordering.compares Ordering.Compares

@[simp]
lemma compares_lt [LT α] (a b : α) : Compares lt a b = (a < b) := rfl

@[simp]
lemma compares_eq [LT α] (a b : α) : Compares eq a b = (a = b) := rfl

@[simp]
lemma compares_gt [LT α] (a b : α) : Compares gt a b = (a > b) := rfl

theorem compares_swap [LT α] {a b : α} {o : Ordering} : o.swap.Compares a b ↔ o.Compares b a := by
  cases o
  · exact Iff.rfl
    -- 🎉 no goals
  · exact eq_comm
    -- 🎉 no goals
  · exact Iff.rfl
    -- 🎉 no goals
#align ordering.compares_swap Ordering.compares_swap

alias ⟨Compares.of_swap, Compares.swap⟩ := compares_swap
#align ordering.compares.of_swap Ordering.Compares.of_swap
#align ordering.compares.swap Ordering.Compares.swap

theorem swap_eq_iff_eq_swap {o o' : Ordering} : o.swap = o' ↔ o = o'.swap := by
  rw [← swap_inj, swap_swap]
  -- 🎉 no goals
#align ordering.swap_eq_iff_eq_swap Ordering.swap_eq_iff_eq_swap

theorem Compares.eq_lt [Preorder α] : ∀ {o} {a b : α}, Compares o a b → (o = lt ↔ a < b)
  | lt, a, b, h => ⟨fun _ => h, fun _ => rfl⟩
  | eq, a, b, h => ⟨fun h => by injection h, fun h' => (ne_of_lt h' h).elim⟩
                                -- 🎉 no goals
  | gt, a, b, h => ⟨fun h => by injection h, fun h' => (lt_asymm h h').elim⟩
                                -- 🎉 no goals
#align ordering.compares.eq_lt Ordering.Compares.eq_lt

theorem Compares.ne_lt [Preorder α] : ∀ {o} {a b : α}, Compares o a b → (o ≠ lt ↔ b ≤ a)
  | lt, a, b, h => ⟨absurd rfl, fun h' => (not_le_of_lt h h').elim⟩
  | eq, a, b, h => ⟨fun _ => ge_of_eq h, fun _ h => by injection h⟩
                                                       -- 🎉 no goals
  | gt, a, b, h => ⟨fun _ => le_of_lt h, fun _ h => by injection h⟩
                                                       -- 🎉 no goals
#align ordering.compares.ne_lt Ordering.Compares.ne_lt

theorem Compares.eq_eq [Preorder α] : ∀ {o} {a b : α}, Compares o a b → (o = eq ↔ a = b)
  | lt, a, b, h => ⟨fun h => by injection h, fun h' => (ne_of_lt h h').elim⟩
                                -- 🎉 no goals
  | eq, a, b, h => ⟨fun _ => h, fun _ => rfl⟩
  | gt, a, b, h => ⟨fun h => by injection h, fun h' => (ne_of_gt h h').elim⟩
                                -- 🎉 no goals
#align ordering.compares.eq_eq Ordering.Compares.eq_eq

theorem Compares.eq_gt [Preorder α] {o} {a b : α} (h : Compares o a b) : o = gt ↔ b < a :=
  swap_eq_iff_eq_swap.symm.trans h.swap.eq_lt
#align ordering.compares.eq_gt Ordering.Compares.eq_gt

theorem Compares.ne_gt [Preorder α] {o} {a b : α} (h : Compares o a b) : o ≠ gt ↔ a ≤ b :=
  (not_congr swap_eq_iff_eq_swap.symm).trans h.swap.ne_lt
#align ordering.compares.ne_gt Ordering.Compares.ne_gt

theorem Compares.le_total [Preorder α] {a b : α} : ∀ {o}, Compares o a b → a ≤ b ∨ b ≤ a
  | lt, h => Or.inl (le_of_lt h)
  | eq, h => Or.inl (le_of_eq h)
  | gt, h => Or.inr (le_of_lt h)
#align ordering.compares.le_total Ordering.Compares.le_total

theorem Compares.le_antisymm [Preorder α] {a b : α} : ∀ {o}, Compares o a b → a ≤ b → b ≤ a → a = b
  | lt, h, _, hba => (not_le_of_lt h hba).elim
  | eq, h, _, _ => h
  | gt, h, hab, _ => (not_le_of_lt h hab).elim
#align ordering.compares.le_antisymm Ordering.Compares.le_antisymm

theorem Compares.inj [Preorder α] {o₁} :
    ∀ {o₂} {a b : α}, Compares o₁ a b → Compares o₂ a b → o₁ = o₂
  | lt, _, _, h₁, h₂ => h₁.eq_lt.2 h₂
  | eq, _, _, h₁, h₂ => h₁.eq_eq.2 h₂
  | gt, _, _, h₁, h₂ => h₁.eq_gt.2 h₂
#align ordering.compares.inj Ordering.Compares.inj

-- Porting note: mathlib3 proof uses `change ... at hab`
theorem compares_iff_of_compares_impl [LinearOrder α] [Preorder β] {a b : α} {a' b' : β}
    (h : ∀ {o}, Compares o a b → Compares o a' b') (o) : Compares o a b ↔ Compares o a' b' := by
  refine' ⟨h, fun ho => _⟩
  -- ⊢ Compares o a b
  cases' lt_trichotomy a b with hab hab
  -- ⊢ Compares o a b
  · have hab : Compares Ordering.lt a b := hab
    -- ⊢ Compares o a b
    rwa [ho.inj (h hab)]
    -- 🎉 no goals
  · cases' hab with hab hab
    -- ⊢ Compares o a b
    · have hab : Compares Ordering.eq a b := hab
      -- ⊢ Compares o a b
      rwa [ho.inj (h hab)]
      -- 🎉 no goals
    · have hab : Compares Ordering.gt a b := hab
      -- ⊢ Compares o a b
      rwa [ho.inj (h hab)]
      -- 🎉 no goals
#align ordering.compares_iff_of_compares_impl Ordering.compares_iff_of_compares_impl

theorem swap_orElse (o₁ o₂) : (orElse o₁ o₂).swap = orElse o₁.swap o₂.swap := by
  cases o₁ <;> rfl
               -- 🎉 no goals
               -- 🎉 no goals
               -- 🎉 no goals
#align ordering.swap_or_else Ordering.swap_orElse

theorem orElse_eq_lt (o₁ o₂) : orElse o₁ o₂ = lt ↔ o₁ = lt ∨ o₁ = eq ∧ o₂ = lt := by
  cases o₁ <;> cases o₂ <;> exact by decide
                            -- 🎉 no goals
                            -- 🎉 no goals
                            -- 🎉 no goals
                            -- 🎉 no goals
                            -- 🎉 no goals
                            -- 🎉 no goals
                            -- 🎉 no goals
                            -- 🎉 no goals
                            -- 🎉 no goals
#align ordering.or_else_eq_lt Ordering.orElse_eq_lt

end Ordering

open Ordering OrderDual

@[simp]
theorem toDual_compares_toDual [LT α] {a b : α} {o : Ordering} :
    Compares o (toDual a) (toDual b) ↔ Compares o b a := by
  cases o
  exacts [Iff.rfl, eq_comm, Iff.rfl]
  -- 🎉 no goals
#align to_dual_compares_to_dual toDual_compares_toDual

@[simp]
theorem ofDual_compares_ofDual [LT α] {a b : αᵒᵈ} {o : Ordering} :
    Compares o (ofDual a) (ofDual b) ↔ Compares o b a := by
  cases o
  exacts [Iff.rfl, eq_comm, Iff.rfl]
  -- 🎉 no goals
#align of_dual_compares_of_dual ofDual_compares_ofDual

theorem cmp_compares [LinearOrder α] (a b : α) : (cmp a b).Compares a b := by
  obtain h | h | h := lt_trichotomy a b <;> simp [cmp, cmpUsing, h, h.not_lt]
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
#align cmp_compares cmp_compares

theorem Ordering.Compares.cmp_eq [LinearOrder α] {a b : α} {o : Ordering} (h : o.Compares a b) :
    cmp a b = o :=
  (cmp_compares a b).inj h
#align ordering.compares.cmp_eq Ordering.Compares.cmp_eq

@[simp]
theorem cmp_swap [Preorder α] [@DecidableRel α (· < ·)] (a b : α) : (cmp a b).swap = cmp b a := by
  unfold cmp cmpUsing
  -- ⊢ swap (if (fun x x_1 => x < x_1) a b then lt else if (fun x x_1 => x < x_1) b …
  by_cases h : a < b <;> by_cases h₂ : b < a <;> simp [h, h₂, Ordering.swap]
  -- ⊢ swap (if (fun x x_1 => x < x_1) a b then lt else if (fun x x_1 => x < x_1) b …
                         -- ⊢ swap (if (fun x x_1 => x < x_1) a b then lt else if (fun x x_1 => x < x_1) b …
                         -- ⊢ swap (if (fun x x_1 => x < x_1) a b then lt else if (fun x x_1 => x < x_1) b …
                                                 -- ⊢ False
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
  exact lt_asymm h h₂
  -- 🎉 no goals
#align cmp_swap cmp_swap

-- Porting note: Not sure why the simpNF linter doesn't like this. @semorrison
@[simp, nolint simpNF]
theorem cmpLE_toDual [LE α] [@DecidableRel α (· ≤ ·)] (x y : α) :
    cmpLE (toDual x) (toDual y) = cmpLE y x :=
  rfl
#align cmp_le_to_dual cmpLE_toDual

@[simp]
theorem cmpLE_ofDual [LE α] [@DecidableRel α (· ≤ ·)] (x y : αᵒᵈ) :
    cmpLE (ofDual x) (ofDual y) = cmpLE y x :=
  rfl
#align cmp_le_of_dual cmpLE_ofDual

-- Porting note: Not sure why the simpNF linter doesn't like this. @semorrison
@[simp, nolint simpNF]
theorem cmp_toDual [LT α] [@DecidableRel α (· < ·)] (x y : α) :
    cmp (toDual x) (toDual y) = cmp y x :=
  rfl
#align cmp_to_dual cmpLE_toDual

@[simp]
theorem cmp_ofDual [LT α] [@DecidableRel α (· < ·)] (x y : αᵒᵈ) :
    cmp (ofDual x) (ofDual y) = cmp y x :=
  rfl
#align cmp_of_dual cmpLE_ofDual

/-- Generate a linear order structure from a preorder and `cmp` function. -/
def linearOrderOfCompares [Preorder α] (cmp : α → α → Ordering)
    (h : ∀ a b, (cmp a b).Compares a b) : LinearOrder α :=
  let H : DecidableRel (α := α) (· ≤ ·) := fun a b => decidable_of_iff _ (h a b).ne_gt
  { inferInstanceAs (Preorder α) with
    le_antisymm := fun a b => (h a b).le_antisymm,
    le_total := fun a b => (h a b).le_total,
    toMin := minOfLe,
    toMax := maxOfLe,
    decidableLE := H,
    decidableLT := fun a b => decidable_of_iff _ (h a b).eq_lt,
    decidableEq := fun a b => decidable_of_iff _ (h a b).eq_eq }
#align linear_order_of_compares linearOrderOfCompares

variable [LinearOrder α] (x y : α)

@[simp]
theorem cmp_eq_lt_iff : cmp x y = Ordering.lt ↔ x < y :=
  Ordering.Compares.eq_lt (cmp_compares x y)
#align cmp_eq_lt_iff cmp_eq_lt_iff

@[simp]
theorem cmp_eq_eq_iff : cmp x y = Ordering.eq ↔ x = y :=
  Ordering.Compares.eq_eq (cmp_compares x y)
#align cmp_eq_eq_iff cmp_eq_eq_iff

@[simp]
theorem cmp_eq_gt_iff : cmp x y = Ordering.gt ↔ y < x :=
  Ordering.Compares.eq_gt (cmp_compares x y)
#align cmp_eq_gt_iff cmp_eq_gt_iff

@[simp]
theorem cmp_self_eq_eq : cmp x x = Ordering.eq := by rw [cmp_eq_eq_iff]
                                                     -- 🎉 no goals
#align cmp_self_eq_eq cmp_self_eq_eq

variable {x y} {β : Type*} [LinearOrder β] {x' y' : β}

theorem cmp_eq_cmp_symm : cmp x y = cmp x' y' ↔ cmp y x = cmp y' x' :=
  ⟨fun h => by rwa [← cmp_swap x', ← cmp_swap, swap_inj],
               -- 🎉 no goals
   fun h => by rwa [← cmp_swap y', ← cmp_swap, swap_inj]⟩
               -- 🎉 no goals
#align cmp_eq_cmp_symm cmp_eq_cmp_symm

theorem lt_iff_lt_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x < y ↔ x' < y' := by
  rw [← cmp_eq_lt_iff, ← cmp_eq_lt_iff, h]
  -- 🎉 no goals
#align lt_iff_lt_of_cmp_eq_cmp lt_iff_lt_of_cmp_eq_cmp

theorem le_iff_le_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x ≤ y ↔ x' ≤ y' := by
  rw [← not_lt, ← not_lt]
  -- ⊢ ¬y < x ↔ ¬y' < x'
  apply not_congr
  -- ⊢ y < x ↔ y' < x'
  apply lt_iff_lt_of_cmp_eq_cmp
  -- ⊢ cmp y x = cmp y' x'
  rwa [cmp_eq_cmp_symm]
  -- 🎉 no goals
#align le_iff_le_of_cmp_eq_cmp le_iff_le_of_cmp_eq_cmp

theorem eq_iff_eq_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x = y ↔ x' = y' := by
  rw [le_antisymm_iff, le_antisymm_iff, le_iff_le_of_cmp_eq_cmp h,
      le_iff_le_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 h)]
#align eq_iff_eq_of_cmp_eq_cmp eq_iff_eq_of_cmp_eq_cmp

theorem LT.lt.cmp_eq_lt (h : x < y) : cmp x y = Ordering.lt :=
  (cmp_eq_lt_iff _ _).2 h

theorem LT.lt.cmp_eq_gt (h : x < y) : cmp y x = Ordering.gt :=
  (cmp_eq_gt_iff _ _).2 h

theorem Eq.cmp_eq_eq (h : x = y) : cmp x y = Ordering.eq :=
  (cmp_eq_eq_iff _ _).2 h
#align eq.cmp_eq_eq Eq.cmp_eq_eq

theorem Eq.cmp_eq_eq' (h : x = y) : cmp y x = Ordering.eq :=
  h.symm.cmp_eq_eq
#align eq.cmp_eq_eq' Eq.cmp_eq_eq'
