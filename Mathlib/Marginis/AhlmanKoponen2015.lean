/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Janani Lakshmanan, Kawika O'Connor, Clark Eggerman
-/

import Mathlib.Tactic.Ring.RingNF
import Mathlib.Data.ZMod.Defs

/-!

Reading "Limit Laws and Automorphism Groups of Nonrigid Structures"
by Ove Ahlman and Vera Koponen, one observes the claim cited in
the first sentence of the introduction:
"it has been shown that for any finite relational vocabulary(also called signature),
the proportion of labelled n-element structures which are rigid,
ie have no nontrivial automorphism, approaches 1 as n approaches infinity"

  While their paper is about nonrigid structures,
  we show that `Fin k` is rigid iff `k ≥ 3`.
-/

/-- The elements of `Fin 2` are 0 and 1. -/
lemma fin2 (x : Fin 2) : x = 0 ∨ x = 1 :=
  (Nat.lt_succ_iff_lt_or_eq.mp x.2).elim
    (fun h => .inl <| Fin.ext <| Nat.lt_one_iff.mp h)
    (fun h => .inr <| Fin.ext h)


/-- Automorphism of `(Fin k, +)`.  -/
def automorphism_of_fin (k: ℕ) (f : Fin k → Fin k) :=
    Function.Bijective f ∧ ∀ x y, f x + f y = f (x + y)

/-- "Rigid" abbreviates: the only automorphism is the identity. -/
def is_rigid (k : ℕ) := ∀ g, (automorphism_of_fin k g) → (g = id)

/-- (Fin 2, +) is rigid. -/
lemma fin2_rigid : is_rigid 2 := by
  intro (f : Fin 2 → Fin 2) (hf : automorphism_of_fin 2 f)
  apply funext
  intro x
  simp
  have fxalt: f x = 0 ∨ f x = 1 := fin2 _
  cases fin2 x with
  |inl hl =>
    let Q₀₀ := hf.2 0 0
    simp at Q₀₀
    subst hl
    exact Q₀₀
  |inr hr =>
    subst hr
    have Q₀₁ := hf.2 0 1
    simp at Q₀₁
    by_contra
    exact Fin.zero_ne_one <| hf.1.1 <| Eq.trans Q₀₁ (by tauto)


/-- 1 ≠ -1 when the characteristic is at least 3. -/
lemma one_not_neg_one_fin (k:ℕ) : (1 : Fin (k+3)) ≠ -1 := by
  intro h
  have : (1: Fin (k+3)) + 1 = -1 + 1 := by nth_rewrite 1 [h];simp
  have : (2: Fin (k+3)) = 0 := by
    ring_nf at this
    tauto
  revert this
  exact ne_of_beq_false rfl

/-- `(Fin n, +)`, `n ≥ 3` are not rigid. -/
lemma fin_not_rigid {k:ℕ} : ¬ is_rigid (k+3) := by
  unfold is_rigid
  push_neg
  use (fun x => -x)
  constructor
  · constructor
    · constructor
      · intro x y h;simp_all
      · intro x;use -x;simp
    · intro x y;simp only [neg_add_rev];simp_rw [add_comm]
  · intro h
    have : (1 : Fin (k+3)) ≠ -1 := by
      let Q := @one_not_neg_one_fin k
      tauto
    apply this
    exact calc (1:Fin (k+3)) = (fun x => -x) 1 := .symm <| congrFun h 1
               _         = -1 := by simp

/-- (Fin k, +) is rigid iff k ≥ 2. -/
theorem fin_rigid_characterize (k: ℕ) :
  is_rigid k ↔ k ≤ 2 := by
    constructor
    · intro h
      by_contra hc
      exact fin_not_rigid <| ((Nat.sub_eq_iff_eq_add <| Nat.gt_of_not_le hc).mp rfl) ▸ h
    · intro h
      cases (Nat.eq_or_lt_of_le h).symm with
      | inl h => cases (Nat.lt_succ_iff_lt_or_eq.mp h) with
        | inl h => exact (Nat.lt_one_iff.mp h) ▸
          (by unfold is_rigid; intros; ext x; have := x.2;simp at this)
        | inr h => exact h ▸ (by unfold is_rigid; intros; ext; simp)
      | inr h => exact h ▸ fin2_rigid
