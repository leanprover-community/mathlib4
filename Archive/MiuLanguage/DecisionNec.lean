/-
Copyright (c) 2020 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/
import Archive.MiuLanguage.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.ModEq

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

example : CountEquivOrEquivTwoMulMod3 "II" "MIUI" :=
  Or.inl rfl

example : CountEquivOrEquivTwoMulMod3 "IUIM" "MI" :=
  Or.inr rfl

/-- If `a` is 1 or 2 mod 3 and if `b` is `a` or twice `a` mod 3, then `b` is 1 or 2 mod 3.
-/
theorem mod3_eq_1_or_mod3_eq_2 {a b : ℕ} (h1 : a % 3 = 1 ∨ a % 3 = 2)
    (h2 : b % 3 = a % 3 ∨ b % 3 = 2 * a % 3) : b % 3 = 1 ∨ b % 3 = 2 := by
  rcases h2 with h2 | h2
  · rw [h2]; exact h1
  · rcases h1 with h1 | h1
    · right; simp [h2, mul_mod, h1]
    · left; simp only [h2, mul_mod, h1, mod_mod]

/-- `count_equiv_one_or_two_mod3_of_derivable` shows any derivable string must have a `count I` that
is 1 or 2 modulo 3.
-/
theorem count_equiv_one_or_two_mod3_of_derivable (en : Miustr) :
    Derivable en → count I en % 3 = 1 ∨ count I en % 3 = 2 := by
  intro h
  induction h with
  | mk => left; rfl
  | r1 _ h_ih =>
    apply mod3_eq_1_or_mod3_eq_2 h_ih; left
    rw [count_append, count_append]; rfl
  | r2 _ h_ih =>
    apply mod3_eq_1_or_mod3_eq_2 h_ih; right
    simp_rw [count_append, count_cons, beq_iff_eq, reduceCtorEq, ite_false, add_zero, two_mul]
  | r3 _ h_ih =>
    apply mod3_eq_1_or_mod3_eq_2 h_ih; left
    rw [count_append, count_append, count_append]
    simp_rw [count_cons_self, count_nil, count_cons, beq_iff_eq, reduceCtorEq, ite_false,
      add_right_comm, add_mod_right]
    simp
  | r4 _ h_ih =>
    apply mod3_eq_1_or_mod3_eq_2 h_ih; left
    rw [count_append, count_append, count_append]
    simp only [ne_eq, not_false_eq_true, count_cons_of_ne, count_nil, add_zero, reduceCtorEq]

/-- Using the above theorem, we solve the MU puzzle, showing that `"MU"` is not derivable.
Once we have proved that `Derivable` is an instance of `DecidablePred`, this will follow
immediately from `dec_trivial`.
-/
theorem not_derivable_mu : ¬Derivable "MU" := by
  intro h
  cases count_equiv_one_or_two_mod3_of_derivable _ h <;> contradiction

/-!
### Condition on `M`

That solves the MU puzzle, but we'll proceed by demonstrating the other necessary condition for a
string to be derivable, namely that the string must start with an M and contain no M in its tail.
-/


/-- `Goodm xs` holds if `xs : Miustr` begins with `M` and has no `M` in its tail.
-/
def Goodm (xs : Miustr) : Prop :=
  List.headI xs = M ∧ M ∉ List.tail xs

instance : DecidablePred Goodm := by unfold Goodm; infer_instance

/-- Demonstration that `"MI"` starts with `M` and has no `M` in its tail.
-/
theorem goodmi : Goodm [M, I] := by
  constructor
  · rfl
  · rw [tail, mem_singleton]; trivial

/-!
We'll show, for each `i` from 1 to 4, that if `en` follows by Rule `i` from `st` and if
`Goodm st` holds, then so does `Goodm en`.
-/


theorem goodm_of_rule1 (xs : Miustr) (h₁ : Derivable (xs ++ [I])) (h₂ : Goodm (xs ++ [I])) :
    Goodm (xs ++ [I, U]) := by
  obtain ⟨mhead, nmtail⟩ := h₂
  constructor
  · cases xs <;> simp_all
  · change M ∉ tail (xs ++ ([I] ++ [U]))
    rw [← append_assoc, tail_append_singleton_of_ne_nil]
    · simp_rw [mem_append, mem_singleton, reduceCtorEq, or_false]; exact nmtail
    · simp

theorem goodm_of_rule2 (xs : Miustr) (_ : Derivable (M :: xs)) (h₂ : Goodm (M :: xs)) :
    Goodm ((M :: xs) ++ xs) := by
  constructor
  · rfl
  · obtain ⟨mhead, mtail⟩ := h₂
    contrapose! mtail
    rw [cons_append] at mtail
    exact or_self_iff.mp (mem_append.mp mtail)

theorem goodm_of_rule3 (as bs : Miustr) (h₁ : Derivable (as ++ [I, I, I] ++ bs))
    (h₂ : Goodm (as ++ [I, I, I] ++ bs)) : Goodm (as ++ (U :: bs)) := by
  obtain ⟨mhead, nmtail⟩ := h₂
  have k : as ≠ nil := by rintro rfl; contradiction
  constructor
  · cases as
    · contradiction
    exact mhead
  · contrapose! nmtail
    rcases exists_cons_of_ne_nil k with ⟨x, xs, rfl⟩
    simp_rw [cons_append] at nmtail ⊢
    simpa using nmtail

/-!
The proof of the next lemma is identical, on the tactic level, to the previous proof.
-/


theorem goodm_of_rule4 (as bs : Miustr) (h₁ : Derivable (as ++ [U, U] ++ bs))
    (h₂ : Goodm (as ++ [U, U] ++ bs)) : Goodm (as ++ bs) := by
  obtain ⟨mhead, nmtail⟩ := h₂
  have k : as ≠ nil := by rintro rfl; contradiction
  constructor
  · cases as
    · contradiction
    exact mhead
  · contrapose! nmtail
    rcases exists_cons_of_ne_nil k with ⟨x, xs, rfl⟩
    simp_rw [cons_append] at nmtail ⊢
    simpa using nmtail

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

instance : DecidablePred Decstr := by unfold Decstr; infer_instance

/-- Suppose `en : Miustr`. If `en` is `Derivable`, then the condition `Decstr en` holds.
-/
theorem decstr_of_der {en : Miustr} : Derivable en → Decstr en := by
  intro h
  constructor
  · exact goodm_of_derivable en h
  · exact count_equiv_one_or_two_mod3_of_derivable en h

end Miu
