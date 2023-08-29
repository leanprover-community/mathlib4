/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Data.Part
import Mathlib.Data.Nat.Upto
import Mathlib.Data.Stream.Defs

#align_import control.fix from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

/-!
# Fixed point

This module defines a generic `fix` operator for defining recursive
computations that are not necessarily well-founded or productive.
An instance is defined for `Part`.

## Main definition

 * class `Fix`
 * `Part.fix`
-/


universe u v

open Classical

variable {α : Type*} {β : α → Type*}

/-- `Fix α` provides a `fix` operator to define recursive computation
via the fixed point of function of type `α → α`. -/
class Fix (α : Type*) where
  /-- `fix f` represents the computation of a fixed point for `f`.-/
  fix : (α → α) → α
#align has_fix Fix

namespace Part

open Part Nat Nat.Upto

section Basic

variable (f : (∀ a, Part (β a)) → (∀ a, Part (β a)))

/-- A series of successive, finite approximation of the fixed point of `f`, defined by
`approx f n = f^[n] ⊥`. The limit of this chain is the fixed point of `f`. -/
def Fix.approx : Stream' (∀ a, Part (β a))
  | 0 => ⊥
  | Nat.succ i => f (Fix.approx i)
#align part.fix.approx Part.Fix.approx

/-- loop body for finding the fixed point of `f` -/
def fixAux {p : ℕ → Prop} (i : Nat.Upto p) (g : ∀ j : Nat.Upto p, i < j → ∀ a, Part (β a)) :
    ∀ a, Part (β a) :=
  f fun x : α => (assert ¬p i.val) fun h : ¬p i.val => g (i.succ h) (Nat.lt_succ_self _) x
#align part.fix_aux Part.fixAux

/-- The least fixed point of `f`.

If `f` is a continuous function (according to complete partial orders),
it satisfies the equations:

  1. `fix f = f (fix f)`          (is a fixed point)
  2. `∀ X, f X ≤ X → fix f ≤ X`   (least fixed point)
-/
protected def fix (x : α) : Part (β x) :=
  (Part.assert (∃ i, (Fix.approx f i x).Dom)) fun h =>
    WellFounded.fix.{1} (Nat.Upto.wf h) (fixAux f) Nat.Upto.zero x
#align part.fix Part.fix

protected theorem fix_def {x : α} (h' : ∃ i, (Fix.approx f i x).Dom) :
    Part.fix f x = Fix.approx f (Nat.succ (Nat.find h')) x := by
  let p := fun i : ℕ => (Fix.approx f i x).Dom
  -- ⊢ Part.fix f x = Fix.approx f (Nat.succ (Nat.find h')) x
  have : p (Nat.find h') := Nat.find_spec h'
  -- ⊢ Part.fix f x = Fix.approx f (Nat.succ (Nat.find h')) x
  generalize hk : Nat.find h' = k
  -- ⊢ Part.fix f x = Fix.approx f (Nat.succ k) x
  replace hk : Nat.find h' = k + (@Upto.zero p).val := hk
  -- ⊢ Part.fix f x = Fix.approx f (Nat.succ k) x
  rw [hk] at this
  -- ⊢ Part.fix f x = Fix.approx f (Nat.succ k) x
  revert hk
  -- ⊢ Nat.find h' = k + ↑Upto.zero → Part.fix f x = Fix.approx f (Nat.succ k) x
  dsimp [Part.fix]; rw [assert_pos h']; revert this
  -- ⊢ Nat.find h' = k + ↑Upto.zero → (assert (∃ i, (Fix.approx f i x).Dom) fun h = …
                    -- ⊢ Nat.find h' = k + ↑Upto.zero → WellFounded.fix (_ : WellFounded (Upto.GT fun …
                                        -- ⊢ p (k + ↑Upto.zero) → Nat.find h' = k + ↑Upto.zero → WellFounded.fix (_ : Wel …
  generalize Upto.zero = z; intro _this hk
  -- ⊢ p (k + ↑z) → Nat.find h' = k + ↑z → WellFounded.fix (_ : WellFounded (Upto.G …
                            -- ⊢ WellFounded.fix (_ : WellFounded (Upto.GT fun x_1 => (Fix.approx f x_1 x).Do …
  suffices : ∀ x',
    WellFounded.fix (Part.fix.proof_1 f x h') (fixAux f) z x' = Fix.approx f (succ k) x'
  exact this _
  -- ⊢ ∀ (x' : α), WellFounded.fix (_ : WellFounded (Upto.GT fun x_1 => (Fix.approx …
  induction k generalizing z with
  | zero =>
    intro x'
    rw [Fix.approx, WellFounded.fix_eq, fixAux]
    congr
    ext x: 1
    rw [assert_neg]
    rfl
    rw [Nat.zero_add] at _this
    simpa only [not_not, Coe]
  | succ n n_ih =>
    intro x'
    rw [Fix.approx, WellFounded.fix_eq, fixAux]
    congr
    ext : 1
    have hh : ¬(Fix.approx f z.val x).Dom := by
      apply Nat.find_min h'
      rw [hk, Nat.succ_add, ← Nat.add_succ]
      apply Nat.lt_of_succ_le
      apply Nat.le_add_left
    rw [succ_add_eq_succ_add] at _this hk
    rw [assert_pos hh, n_ih (Upto.succ z hh) _this hk]
#align part.fix_def Part.fix_def

theorem fix_def' {x : α} (h' : ¬∃ i, (Fix.approx f i x).Dom) : Part.fix f x = none := by
  dsimp [Part.fix]
  -- ⊢ (assert (∃ i, (Fix.approx f i x).Dom) fun h => WellFounded.fix (_ : WellFoun …
  rw [assert_neg h']
  -- 🎉 no goals
#align part.fix_def' Part.fix_def'

end Basic

end Part

namespace Part

instance hasFix : Fix (Part α) :=
  ⟨fun f => Part.fix (fun x u => f (x u)) ()⟩
#align part.has_fix Part.hasFix

end Part

open Sigma

namespace Pi

instance Part.hasFix {β} : Fix (α → Part β) :=
  ⟨Part.fix⟩
#align pi.part.has_fix Pi.Part.hasFix

end Pi
