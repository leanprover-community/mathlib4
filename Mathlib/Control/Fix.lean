/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module control.fix
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Part
import Mathbin.Data.Nat.Upto
import Mathbin.Data.Stream.Defs

/-!
# Fixed point

This module defines a generic `fix` operator for defining recursive
computations that are not necessarily well-founded or productive.
An instance is defined for `part`.

## Main definition

 * class `has_fix`
 * `part.fix`
-/


universe u v

open Classical

variable {α : Type _} {β : α → Type _}

/-- `has_fix α` gives us a way to calculate the fixed point
of function of type `α → α`. -/
class HasFix (α : Type _) where
  fix : (α → α) → α
#align has_fix HasFix

namespace Part

open Part Nat Nat.Upto

section Basic

variable (f : (∀ a, Part <| β a) → ∀ a, Part <| β a)

/-- A series of successive, finite approximation of the fixed point of `f`, defined by
`approx f n = f^[n] ⊥`. The limit of this chain is the fixed point of `f`. -/
def Fix.approx : Stream' <| ∀ a, Part <| β a
  | 0 => ⊥
  | Nat.succ i => f (fix.approx i)
#align part.fix.approx Part.Fix.approx

/-- loop body for finding the fixed point of `f` -/
def fixAux {p : ℕ → Prop} (i : Nat.Upto p) (g : ∀ j : Nat.Upto p, i < j → ∀ a, Part <| β a) :
    ∀ a, Part <| β a :=
  f fun x : α => (assert ¬p i.val) fun h : ¬p i.val => g (i.succ h) (Nat.lt_succ_self _) x
#align part.fix_aux Part.fixAux

/-- The least fixed point of `f`.

If `f` is a continuous function (according to complete partial orders),
it satisfies the equations:

  1. `fix f = f (fix f)`          (is a fixed point)
  2. `∀ X, f X ≤ X → fix f ≤ X`   (least fixed point)
-/
protected def fix (x : α) : Part <| β x :=
  (Part.assert (∃ i, (Fix.approx f i x).Dom)) fun h =>
    WellFounded.fix.{1} (Nat.Upto.wf h) (fixAux f) Nat.Upto.zero x
#align part.fix Part.fix

protected theorem fix_def {x : α} (h' : ∃ i, (Fix.approx f i x).Dom) :
    Part.fix f x = Fix.approx f (Nat.succ <| Nat.find h') x := by
  let p := fun i : ℕ => (fix.approx f i x).Dom
  have : p (Nat.find h') := Nat.find_spec h'
  generalize hk : Nat.find h' = k
  replace hk : Nat.find h' = k + (@upto.zero p).val := hk
  rw [hk] at this
  revert hk
  dsimp [Part.fix]; rw [assert_pos h']; revert this
  generalize upto.zero = z; intros
  suffices : ∀ x', WellFounded.fix (fix._proof_1 f x h') (fix_aux f) z x' = fix.approx f (succ k) x'
  exact this _
  induction k generalizing z <;> intro
  · rw [fix.approx, WellFounded.fix_eq, fix_aux]
    congr
    ext : 1
    rw [assert_neg]
    rfl
    rw [Nat.zero_add] at this
    simpa only [not_not, Subtype.val_eq_coe]
  · rw [fix.approx, WellFounded.fix_eq, fix_aux]
    congr
    ext : 1
    have hh : ¬(fix.approx f z.val x).Dom := by
      apply Nat.find_min h'
      rw [hk, Nat.succ_add, ← Nat.add_succ]
      apply Nat.lt_of_succ_le
      apply Nat.le_add_left
    rw [succ_add_eq_succ_add] at this hk
    rw [assert_pos hh, k_ih (upto.succ z hh) this hk]
#align part.fix_def Part.fix_def

theorem fix_def' {x : α} (h' : ¬∃ i, (Fix.approx f i x).Dom) : Part.fix f x = none := by
  dsimp [Part.fix] <;> rw [assert_neg h']
#align part.fix_def' Part.fix_def'

end Basic

end Part

namespace Part

instance : HasFix (Part α) :=
  ⟨fun f => Part.fix (fun x u => f (x u)) ()⟩

end Part

open Sigma

namespace Pi

instance Part.hasFix {β} : HasFix (α → Part β) :=
  ⟨Part.fix⟩
#align pi.part.has_fix Pi.Part.hasFix

end Pi

