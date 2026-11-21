/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Reduction relation

This file defines the **reduction** relation between multivariate polynomials,
a fundamental concept in the Characteristic Set Method.

## Main definitions

* `MvPolynomial.reducedTo q p`:
  A polynomial `q` is *reduced* with respect to `p` if either `q = 0` or
  the degree of `q` in `p`'s main variable is strictly less than the degree of `p`.
  If `p` is a constant (i.e., `max_vars p = ⊥`), then no non-zero `q` is reduced w.r.t. `p`.

* `MvPolynomial.reducedToSet q a`:
  A polynomial `q` is reduced with respect to a set `a` if it is reduced
  with respect to every element of `a`.

## References
* [Wen-Tsun Wu, *Basic principles of mechanical theorem proving in elementary geometries*]
  [wen1986basic]

-/

public section

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R] [DecidableEq R] [LinearOrder σ] {p q r : MvPolynomial σ R}

/-- `q` is reduced with respect to `p` if `q = 0` or
if the degree of `q` in the main variable of `p` is strictly less than the degree of `p`.

Note: if `p` is a constant, then no non-zero `q` is reduced with respect to `p`. -/
def reducedTo (q p : MvPolynomial σ R) : Prop :=
  if q = 0 then True
  else
    match p.vars.max with
    | ⊥ => False
    | some c => q.degreeOf c < p.degreeOf c

theorem zero_reducedTo (p : MvPolynomial σ R) : (0 : MvPolynomial σ R).reducedTo p := trivial

theorem not_reducedTo_of_bot_max_vars (hq : q ≠ 0) : p.vars.max = ⊥ → ¬q.reducedTo p :=
  fun hp ↦ by simp only [reducedTo, hq, reduceIte, hp, not_false_eq_true]

theorem max_vars_ne_bot_of_reducedTo (hq : q ≠ 0) : q.reducedTo p → p.vars.max ≠ ⊥ :=
  fun hp con ↦ not_reducedTo_of_bot_max_vars hq con hp

theorem reducedTo_iff {c : σ} (hp : p.vars.max = c) (hq : q ≠ 0) :
    q.reducedTo p ↔ q.degreeOf c < p.degreeOf c := by simp only [reducedTo, hq, reduceIte, hp]

noncomputable instance : DecidableRel (@reducedTo R σ _ _ _) := fun q p ↦
  if hq : q = 0 then isTrue <| hq ▸ zero_reducedTo p
  else
    match hp : p.vars.max with
    | ⊥ => isFalse <| not_reducedTo_of_bot_max_vars hq hp
    | some _ => decidable_of_iff _ (reducedTo_iff hp hq).symm

theorem reducedTo_of_max_vars_lt (h : q.vars.max < p.vars.max) : q.reducedTo p := by
  if hq : q = 0 then exact hq ▸ zero_reducedTo p
  else
    rcases WithBot.ne_bot_iff_exists.mp <| LT.lt.ne_bot h with ⟨c, hc⟩
    apply (reducedTo_iff hc.symm hq).mpr
    rw [(iff_not_comm.mpr mem_vars_iff_degreeOf_ne_zero).mpr <|
      Finset.notMem_of_max_lt_coe (hc ▸ h)]
    apply Nat.pos_of_ne_zero
    refine mem_vars_iff_degreeOf_ne_zero.mp ?_
    exact Finset.mem_of_max hc.symm

theorem not_reduceTo_self (h : p ≠ 0) : ¬p.reducedTo p := by
  rw [reducedTo, if_neg h]
  split
  <;> simp

variable {α : Type*} [Membership (MvPolynomial σ R) α] {p q : MvPolynomial σ R} {a : α}

/-- `q` is reduced with respect to a set `a`
if it is reduced with respect to all elements of `a`. -/
def reducedToSet (q : MvPolynomial σ R) (a : α) : Prop := ∀ p ∈ a, q.reducedTo p

theorem reducedToSet_def : q.reducedToSet a ↔ ∀ p ∈ a, q.reducedTo p := Iff.rfl

noncomputable instance : @DecidableRel _ (List (MvPolynomial σ R)) reducedToSet := by
  intro _ _
  rw [reducedToSet_def]
  apply List.decidableBAll

theorem zero_reducedToSet : (0 : MvPolynomial σ R).reducedToSet a := fun _ _ ↦ zero_reducedTo _

end MvPolynomial
