/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Set.Image

#align_import data.nat.set from "leanprover-community/mathlib"@"cf9386b56953fb40904843af98b7a80757bbe7f9"

/-!
### Recursion on the natural numbers and `Set.range`
-/


namespace Nat

section Set

open Set

theorem zero_union_range_succ : {0} ∪ range succ = univ := by
  ext n
  -- ⊢ n ∈ {0} ∪ range succ ↔ n ∈ univ
  cases n <;> simp
  -- ⊢ zero ∈ {0} ∪ range succ ↔ zero ∈ univ
              -- 🎉 no goals
              -- 🎉 no goals
#align nat.zero_union_range_succ Nat.zero_union_range_succ

@[simp]
protected theorem range_succ : range succ = { i | 0 < i } := by
  ext (_ | i) <;> simp [succ_pos, succ_ne_zero, Set.mem_setOf]
  -- ⊢ zero ∈ range succ ↔ zero ∈ {i | 0 < i}
                  -- 🎉 no goals
                  -- 🎉 no goals
#align nat.range_succ Nat.range_succ

variable {α : Type*}

theorem range_of_succ (f : ℕ → α) : {f 0} ∪ range (f ∘ succ) = range f := by
  rw [← image_singleton, range_comp, ← image_union, zero_union_range_succ, image_univ]
  -- 🎉 no goals
#align nat.range_of_succ Nat.range_of_succ

theorem range_rec {α : Type*} (x : α) (f : ℕ → α → α) :
    (Set.range fun n => Nat.rec x f n : Set α) =
      {x} ∪ Set.range fun n => Nat.rec (f 0 x) (f ∘ succ) n := by
  convert (range_of_succ (fun n => Nat.rec x f n : ℕ → α)).symm using 4
  -- ⊢ rec (f 0 x) (f ∘ succ) x✝ = ((fun n => rec x f n) ∘ succ) x✝
  dsimp
  -- ⊢ rec (f 0 x) (f ∘ succ) x✝ = f x✝ (rec x f x✝)
  rename_i n
  -- ⊢ rec (f 0 x) (f ∘ succ) n = f n (rec x f n)
  induction' n with n ihn
  -- ⊢ rec (f 0 x) (f ∘ succ) zero = f zero (rec x f zero)
  · rfl
    -- 🎉 no goals
  · dsimp at ihn ⊢
    -- ⊢ f (succ n) (rec (f 0 x) (f ∘ succ) n) = f (succ n) (f n (rec x f n))
    rw [ihn]
    -- 🎉 no goals
#align nat.range_rec Nat.range_rec

theorem range_casesOn {α : Type*} (x : α) (f : ℕ → α) :
    (Set.range fun n => Nat.casesOn n x f : Set α) = {x} ∪ Set.range f :=
  (range_of_succ _).symm
#align nat.range_cases_on Nat.range_casesOn

end Set

end Nat
