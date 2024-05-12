/-
Copyright (c) 2020 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/
import Archive.MiuLanguage.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

#align_import miu_language.decision_nec from "leanprover-community/mathlib"@"3813d4ea1c6a34dbb472de66e73b8c6855b03964"

/-!
# Decision procedure: necessary condition

We introduce a condition `Decstr` and show that if a string `en` is `Derivable`, then `Decstr en`
holds.

Using this, we give a negative answer to the question: is `"MU"` derivable?

## Tags

miu, decision procedure
-/


namespace Miu

open MiuAtom Nat List

/-!
### Numerical condition on the `I` count

Suppose `st : Miustr`. Then `count I st` is the number of `I`s in `st`. We'll show, if
`Derivable st`, then `count I st` must be 1 or 2 modulo 3. To do this, it suffices to show that if
the `en : Miustr` is derived from `st`, then `count I en` moudulo 3 is either equal to or is twice
`count I st`, modulo 3.
-/


/-- Given `st en : Miustr`, the relation `CountEquivOrEquivTwoMulMod3 st en` holds if `st` and
`en` either have equal `count I`, modulo 3, or `count I en` is twice `count I st`, modulo 3.
-/
def CountEquivOrEquivTwoMulMod3 (st en : Miustr) : Prop :=
  let a := count I st
  let b := count I en
  b ≡ a [MOD 3] ∨ b ≡ 2 * a [MOD 3]
#align miu.count_equiv_or_equiv_two_mul_mod3 Miu.CountEquivOrEquivTwoMulMod3

example : CountEquivOrEquivTwoMulMod3 "II" "MIUI" :=
  Or.inl rfl

example : CountEquivOrEquivTwoMulMod3 "IUIM" "MI" :=
  Or.inr rfl

/-- If `a` is 1 or 2 mod 3 and if `b` is `a` or twice `a` mod 3, then `b` is 1 or 2 mod 3.
-/
theorem mod3_eq_1_or_mod3_eq_2 {a b : ℕ} (h1 : a % 3 = 1 ∨ a % 3 = 2)
    (h2 : b % 3 = a % 3 ∨ b % 3 = 2 * a % 3) : b % 3 = 1 ∨ b % 3 = 2 := by
  cases' h2 with h2 h2
  · rw [h2]; exact h1
  · cases' h1 with h1 h1
    · right; simp [h2, mul_mod, h1, Nat.succ_lt_succ]
    · left; simp only [h2, mul_mod, h1, mod_mod]
#align miu.mod3_eq_1_or_mod3_eq_2 Miu.mod3_eq_1_or_mod3_eq_2

/-- `count_equiv_one_or_two_mod3_of_derivable` shows any derivable string must have a `count I` that
is 1 or 2 modulo 3.
-/
theorem count_equiv_one_or_two_mod3_of_derivable (en : Miustr) :
    Derivable en → count I en % 3 = 1 ∨ count I en % 3 = 2 := by
  intro h
  induction' h with _ _ h_ih _ _ h_ih _ _ _ h_ih _ _ _ h_ih
  · left; rfl
  any_goals apply mod3_eq_1_or_mod3_eq_2 h_ih
  -- Porting note: `simp_rw [count_append]` usually doesn't work
  · left; rw [count_append, count_append]; rfl
  · right; simp_rw [count_append, count_cons, if_false, two_mul]; simp
  · left; rw [count_append, count_append, count_append]
    simp_rw [count_cons_self, count_nil, count_cons, ite_false, add_right_comm, add_mod_right]
    simp
  · left; rw [count_append, count_append, count_append]
    simp only [ne_eq, not_false_eq_true, count_cons_of_ne, count_nil, add_zero]
#align miu.count_equiv_one_or_two_mod3_of_derivable Miu.count_equiv_one_or_two_mod3_of_derivable

/-- Using the above theorem, we solve the MU puzzle, showing that `"MU"` is not derivable.
Once we have proved that `Derivable` is an instance of `DecidablePred`, this will follow
immediately from `dec_trivial`.
-/
theorem not_derivable_mu : ¬Derivable "MU" := by
  intro h
  cases count_equiv_one_or_two_mod3_of_derivable _ h <;> contradiction
#align miu.not_derivable_mu Miu.not_derivable_mu

/-!
### Condition on `M`

That solves the MU puzzle, but we'll proceed by demonstrating the other necessary condition for a
string to be derivable, namely that the string must start with an M and contain no M in its tail.
-/


/-- `Goodm xs` holds if `xs : Miustr` begins with `M` and has no `M` in its tail.
-/
def Goodm (xs : Miustr) : Prop :=
  List.headI xs = M ∧ ¬M ∈ List.tail xs
#align miu.goodm Miu.Goodm

instance : DecidablePred Goodm := by unfold Goodm; infer_instance

/-- Demonstration that `"MI"` starts with `M` and has no `M` in its tail.
-/
theorem goodmi : Goodm [M, I] := by
  constructor
  · rfl
  · rw [tail, mem_singleton]; trivial
#align miu.goodmi Miu.goodmi

/-!
We'll show, for each `i` from 1 to 4, that if `en` follows by Rule `i` from `st` and if
`Goodm st` holds, then so does `Goodm en`.
-/


theorem goodm_of_rule1 (xs : Miustr) (h₁ : Derivable (xs ++ ↑[I])) (h₂ : Goodm (xs ++ ↑[I])) :
    Goodm (xs ++ ↑[I, U]) := by
  cases' h₂ with mhead nmtail
  have : xs ≠ nil := by rintro rfl; contradiction
  constructor
  · -- Porting note: Original proof was `rwa [head_append] at * <;> exact this`.
    -- However, there is no `headI_append`
    cases xs
    · contradiction
    exact mhead
  · change ¬M ∈ tail (xs ++ ↑([I] ++ [U]))
    rw [← append_assoc, tail_append_singleton_of_ne_nil]
    · simp_rw [mem_append, mem_singleton, or_false]; exact nmtail
    · exact append_ne_nil_of_ne_nil_left _ _ this
#align miu.goodm_of_rule1 Miu.goodm_of_rule1

theorem goodm_of_rule2 (xs : Miustr) (_ : Derivable (M :: xs)) (h₂ : Goodm (M :: xs)) :
    Goodm (↑(M :: xs) ++ xs) := by
  constructor
  · rfl
  · cases' h₂ with mhead mtail
    contrapose! mtail
    rw [cons_append] at mtail
    exact or_self_iff.mp (mem_append.mp mtail)
#align miu.goodm_of_rule2 Miu.goodm_of_rule2

theorem goodm_of_rule3 (as bs : Miustr) (h₁ : Derivable (as ++ ↑[I, I, I] ++ bs))
    (h₂ : Goodm (as ++ ↑[I, I, I] ++ bs)) : Goodm (as ++ ↑(U :: bs)) := by
  cases' h₂ with mhead nmtail
  have k : as ≠ nil := by rintro rfl; contradiction
  constructor
  · cases as
    · contradiction
    exact mhead
  · contrapose! nmtail
    rcases exists_cons_of_ne_nil k with ⟨x, xs, rfl⟩
    -- Porting note: `simp_rw [cons_append]` didn't work
    rw [cons_append] at nmtail; rw [cons_append, cons_append]
    dsimp only [tail] at nmtail ⊢
    simpa using nmtail
#align miu.goodm_of_rule3 Miu.goodm_of_rule3

/-!
The proof of the next lemma is identical, on the tactic level, to the previous proof.
-/


theorem goodm_of_rule4 (as bs : Miustr) (h₁ : Derivable (as ++ ↑[U, U] ++ bs))
    (h₂ : Goodm (as ++ ↑[U, U] ++ bs)) : Goodm (as ++ bs) := by
  cases' h₂ with mhead nmtail
  have k : as ≠ nil := by rintro rfl; contradiction
  constructor
  · cases as
    · contradiction
    exact mhead
  · contrapose! nmtail
    rcases exists_cons_of_ne_nil k with ⟨x, xs, rfl⟩
    -- Porting note: `simp_rw [cons_append]` didn't work
    rw [cons_append] at nmtail; rw [cons_append, cons_append]
    dsimp only [tail] at nmtail ⊢
    simpa using nmtail
#align miu.goodm_of_rule4 Miu.goodm_of_rule4

/-- Any derivable string must begin with `M` and have no `M` in its tail.
-/
theorem goodm_of_derivable (en : Miustr) : Derivable en → Goodm en := by
  intro h
  induction h
  · exact goodmi
  · apply goodm_of_rule1 <;> assumption
  · apply goodm_of_rule2 <;> assumption
  · apply goodm_of_rule3 <;> assumption
  · apply goodm_of_rule4 <;> assumption
#align miu.goodm_of_derivable Miu.goodm_of_derivable

/-!
We put together our two conditions to give one necessary condition `Decstr` for an `Miustr` to be
derivable.
-/


/--
`Decstr en` is the condition that `count I en` is 1 or 2 modulo 3, that `en` starts with `M`, and
that `en` has no `M` in its tail. We automatically derive that this is a decidable predicate.
-/
def Decstr (en : Miustr) :=
  Goodm en ∧ (count I en % 3 = 1 ∨ count I en % 3 = 2)
#align miu.decstr Miu.Decstr

instance : DecidablePred Decstr := by unfold Decstr; infer_instance

/-- Suppose `en : Miustr`. If `en` is `Derivable`, then the condition `Decstr en` holds.
-/
theorem decstr_of_der {en : Miustr} : Derivable en → Decstr en := by
  intro h
  constructor
  · exact goodm_of_derivable en h
  · exact count_equiv_one_or_two_mod3_of_derivable en h
#align miu.decstr_of_der Miu.decstr_of_der

end Miu
