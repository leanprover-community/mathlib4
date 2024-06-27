/-
Copyright (c) 2020 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/
import Archive.MiuLanguage.DecisionNec
import Mathlib.Tactic.Linarith

#align_import miu_language.decision_suf from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# Decision procedure - sufficient condition and decidability

We give a sufficient condition for a string to be derivable in the MIU language. Together with the
necessary condition, we use this to prove that `Derivable` is an instance of `DecidablePred`.

Let `count I st` and `count U st` denote the number of `I`s (respectively `U`s) in `st : Miustr`.

We'll show that `st` is derivable if it has the form `M::x` where `x` is a string of `I`s and `U`s
for which `count I x` is congruent to 1 or 2 modulo 3.

To prove this, it suffices to show `Derivable M::y` where `y` is any `Miustr` consisting only of
`I`s such that the number of `I`s in `y` is `a+3b`, where `a = count I x` and `b = count U x`.
This suffices because Rule 3 permits us to change any string of three consecutive `I`s into a `U`.

As `count I y = (count I x) + 3*(count U x) ≡ (count I x) [MOD 3]`, it suffices to show
`Derivable M::z` where `z` is an `Miustr` of `I`s such that `count I z` is congruent to
1 or 2 modulo 3.

Let `z` be such an `Miustr` and let `c` denote `count I z`, so `c ≡ 1 or 2 [MOD 3]`.
To derive such an `Miustr`, it suffices to derive an `Miustr` `M::w`, where again `w` is an
`Miustr` of only `I`s with the additional conditions that `count I w` is a power of 2, that
`count I w ≥ c` and that `count I w ≡ c [MOD 3]`.

To see that this suffices, note that we can remove triples of `I`s from the end of `M::w`,
creating `U`s as we go along. Once the number of `I`s equals `m`, we remove `U`s two at a time
until we have no `U`s. The only issue is that we may begin the removal process with an odd number
of `U`s.

Writing `d = count I w`, we see that this happens if and only if `(d-c)/3` is odd.
In this case, we must apply Rule 1 to `z`, prior to removing triples of `I`s. We thereby
introduce an additional `U` and ensure that the final number of `U`s will be even.

## Tags

miu, decision procedure, decidability, decidable_pred, decidable
-/


namespace Miu

open MiuAtom List Nat

/-- We start by showing that an `Miustr` `M::w` can be derived, where `w` consists only of `I`s and
where `count I w` is a power of 2.
-/
private theorem der_cons_replicate (n : ℕ) : Derivable (M :: replicate (2 ^ n) I) := by
  induction' n with k hk
  · -- base case
    constructor
  · -- inductive step
    rw [pow_add, pow_one 2, mul_two, replicate_add]
    exact Derivable.r2 hk

/-!
## Converting `I`s to `U`s

For any given natural number `c ≡ 1 or 2 [MOD 3]`, we need to show that can derive an `Miustr`
`M::w` where `w` consists only of `I`s, where `d = count I w` is a power of 2, where `d ≥ c` and
where `d ≡ c [MOD 3]`.

Given the above lemmas, the desired result reduces to an arithmetic result, given in the file
`arithmetic.lean`.

We'll use this result to show we can derive an `Miustr` of the form `M::z` where `z` is a string
consisting only of `I`s such that `count I z ≡ 1 or 2 [MOD 3]`.

As an intermediate step, we show that derive `z` from `zt`, where `t` is an `Miustr` consisting of
an even number of `U`s and `z` is any `Miustr`.
-/


/--
Any number of successive occurrences of `"UU"` can be removed from the end of a `Derivable` `Miustr`
to produce another `Derivable` `Miustr`.
-/
theorem der_of_der_append_replicate_U_even {z : Miustr} {m : ℕ}
    (h : Derivable (z ++ ↑(replicate (m * 2) U))) : Derivable z := by
  induction' m with k hk
  · revert h
    rw [replicate, append_nil]; exact id
  · apply hk
    simp only [succ_mul, replicate_add] at h
    rw [← append_nil ↑(z ++ ↑(replicate (k * 2) U))]
    apply Derivable.r4
    rwa [append_nil, append_assoc]
set_option linter.uppercaseLean3 false in
#align miu.der_of_der_append_replicate_U_even Miu.der_of_der_append_replicate_U_even

/-!
In fine-tuning my application of `simp`, I issued the following commend to determine which lemmas
`simp` uses.

`set_option trace.simplify.rewrite true`
-/


/-- We may replace several consecutive occurrences of `"III"` with the same number of `"U"`s.
In application of the following lemma, `xs` will either be `[]` or `[U]`.
-/
theorem der_cons_replicate_I_replicate_U_append_of_der_cons_replicate_I_append (c k : ℕ)
    (_ : c % 3 = 1 ∨ c % 3 = 2) (xs : Miustr)
    (hder : Derivable (↑(M :: replicate (c + 3 * k) I) ++ xs)) :
    Derivable (↑(M :: (replicate c I ++ replicate k U)) ++ xs) := by
  revert xs
  induction' k with a ha
  · simp only [replicate, zero_eq, mul_zero, add_zero, append_nil, forall_true_iff, imp_self]
  · intro xs
    specialize ha (U :: xs)
    intro h₂
    -- We massage the goal into a form amenable to the application of `ha`.
    rw [replicate_add, ← append_assoc, ← cons_append, replicate_one, append_assoc,
      singleton_append]
    apply ha
    apply Derivable.r3
    change Derivable (↑(M :: replicate (c + 3 * a) I) ++ ↑(replicate 3 I) ++ xs)
    rwa [cons_append, ← replicate_add, add_assoc]
set_option linter.uppercaseLean3 false in
#align miu.der_cons_replicate_I_replicate_U_append_of_der_cons_replicate_I_append Miu.der_cons_replicate_I_replicate_U_append_of_der_cons_replicate_I_append

/-!
### Arithmetic

We collect purely arithmetic lemmas: `add_mod2` is used to ensure we have an even number of `U`s
while `le_pow2_and_pow2_eq_mod3` treats the congruence condition modulo 3.
-/


section Arithmetic

/-- For every `a`, the number `a + a % 2` is even.
-/
theorem add_mod2 (a : ℕ) : ∃ t, a + a % 2 = t * 2 := by
  simp only [mul_comm _ 2] -- write `t*2` as `2*t`
  apply dvd_of_mod_eq_zero -- it suffices to prove `(a + a % 2) % 2 = 0`
  rw [add_mod, mod_mod, ← two_mul, mul_mod_right]
#align miu.add_mod2 Miu.add_mod2

private theorem le_pow2_and_pow2_eq_mod3' (c : ℕ) (x : ℕ) (h : c = 1 ∨ c = 2) :
    ∃ m : ℕ, c + 3 * x ≤ 2 ^ m ∧ 2 ^ m % 3 = c % 3 := by
  induction' x with k hk
  · use c + 1
    cases' h with hc hc <;> · rw [hc]; norm_num
  rcases hk with ⟨g, hkg, hgmod⟩
  by_cases hp : c + 3 * (k + 1) ≤ 2 ^ g
  · use g, hp, hgmod
  refine ⟨g + 2, ?_, ?_⟩
  · rw [mul_succ, ← add_assoc, pow_add]
    change c + 3 * k + 3 ≤ 2 ^ g * (1 + 3); rw [mul_add (2 ^ g) 1 3, mul_one]
    linarith [hkg, @Nat.one_le_two_pow g]
  · rw [pow_add, ← mul_one c]
    exact ModEq.mul hgmod rfl

/-- If `a` is 1 or 2 modulo 3, then exists `k` a power of 2 for which `a ≤ k` and `a ≡ k [MOD 3]`.
-/
theorem le_pow2_and_pow2_eq_mod3 (a : ℕ) (h : a % 3 = 1 ∨ a % 3 = 2) :
    ∃ m : ℕ, a ≤ 2 ^ m ∧ 2 ^ m % 3 = a % 3 := by
  cases' le_pow2_and_pow2_eq_mod3' (a % 3) (a / 3) h with m hm
  use m
  constructor
  · convert hm.1; exact (mod_add_div a 3).symm
  · rw [hm.2, mod_mod _ 3]
#align miu.le_pow2_and_pow2_eq_mod3 Miu.le_pow2_and_pow2_eq_mod3

end Arithmetic

theorem replicate_pow_minus_append {m : ℕ} :
    M :: replicate (2 ^ m - 1) I ++ [I] = M :: replicate (2 ^ m) I := by
  change M :: replicate (2 ^ m - 1) I ++ replicate 1 I = M :: replicate (2 ^ m) I
  rw [cons_append, ← replicate_add, tsub_add_cancel_of_le (one_le_pow' m 1)]
#align miu.replicate_pow_minus_append Miu.replicate_pow_minus_append

/--
`der_replicate_I_of_mod3` states that `M::y` is `Derivable` if `y` is any `Miustr` consisiting just
of `I`s, where `count I y` is 1 or 2 modulo 3.
-/
theorem der_replicate_I_of_mod3 (c : ℕ) (h : c % 3 = 1 ∨ c % 3 = 2) :
    Derivable (M :: replicate c I) := by
  -- From `der_cons_replicate`, we can derive the `Miustr` `M::w` described in the introduction.
  cases' le_pow2_and_pow2_eq_mod3 c h with m hm -- `2^m` will be the number of `I`s in `M::w`
  have hw₂ : Derivable (M :: replicate (2 ^ m) I ++ replicate ((2 ^ m - c) / 3 % 2) U) := by
    cases' mod_two_eq_zero_or_one ((2 ^ m - c) / 3) with h_zero h_one
    · -- `(2^m - c)/3 ≡ 0 [MOD 2]`
      simp only [der_cons_replicate m, append_nil, List.replicate, h_zero]
    · -- case `(2^m - c)/3 ≡ 1 [MOD 2]`
      rw [h_one, ← replicate_pow_minus_append, append_assoc]
      apply Derivable.r1
      rw [replicate_pow_minus_append]
      exact der_cons_replicate m
  have hw₃ : Derivable (M :: replicate c I ++
      replicate ((2 ^ m - c) / 3) U ++ replicate ((2 ^ m - c) / 3 % 2) U) := by
    apply
      der_cons_replicate_I_replicate_U_append_of_der_cons_replicate_I_append c ((2 ^ m - c) / 3) h
    convert hw₂ using 4
    -- now we must show `c + 3 * ((2 ^ m - c) / 3) = 2 ^ m`
    rw [Nat.mul_div_cancel']
    · exact add_tsub_cancel_of_le hm.1
    · exact (modEq_iff_dvd' hm.1).mp hm.2.symm
  rw [append_assoc, ← replicate_add _ _] at hw₃
  cases' add_mod2 ((2 ^ m - c) / 3) with t ht
  rw [ht] at hw₃
  exact der_of_der_append_replicate_U_even hw₃
set_option linter.uppercaseLean3 false in
#align miu.der_replicate_I_of_mod3 Miu.der_replicate_I_of_mod3

example (c : ℕ) (h : c % 3 = 1 ∨ c % 3 = 2) : Derivable (M :: replicate c I) := by
  -- From `der_cons_replicate`, we can derive the `Miustr` `M::w` described in the introduction.
  cases' le_pow2_and_pow2_eq_mod3 c h with m hm -- `2^m` will be the number of `I`s in `M::w`
  have hw₂ : Derivable (M :: replicate (2 ^ m) I ++ replicate ((2 ^ m - c) / 3 % 2) U) := by
    cases' mod_two_eq_zero_or_one ((2 ^ m - c) / 3) with h_zero h_one
    · -- `(2^m - c)/3 ≡ 0 [MOD 2]`
      simp only [der_cons_replicate m, append_nil, List.replicate, h_zero]
    · -- case `(2^m - c)/3 ≡ 1 [MOD 2]`
      rw [h_one, ← replicate_pow_minus_append, append_assoc]
      apply Derivable.r1
      rw [replicate_pow_minus_append]
      exact der_cons_replicate m
  have hw₃ : Derivable (M :: replicate c I ++
      replicate ((2 ^ m - c) / 3) U ++ replicate ((2 ^ m - c) / 3 % 2) U) := by
    apply
      der_cons_replicate_I_replicate_U_append_of_der_cons_replicate_I_append c ((2 ^ m - c) / 3) h
    convert hw₂ using 4
    -- now we must show `c + 3 * ((2 ^ m - c) / 3) = 2 ^ m`
    rw [Nat.mul_div_cancel']
    · exact add_tsub_cancel_of_le hm.1
    · exact (modEq_iff_dvd' hm.1).mp hm.2.symm
  rw [append_assoc, ← replicate_add _ _] at hw₃
  cases' add_mod2 ((2 ^ m - c) / 3) with t ht
  rw [ht] at hw₃
  exact der_of_der_append_replicate_U_even hw₃

/-!
### `Decstr` is a sufficient condition

The remainder of this file sets up the proof that `Decstr en` is sufficent to ensure
`Derivable en`. Decidability of `Derivable en` is an easy consequence.

The proof proceeds by induction on the `count U` of `en`.

We tackle first the base case of the induction. This requires auxiliary results giving
conditions under which `count I ys = length ys`.
-/


/-- If an `Miustr` has a zero `count U` and contains no `M`, then its `count I` is its length.
-/
theorem count_I_eq_length_of_count_U_zero_and_neg_mem {ys : Miustr} (hu : count U ys = 0)
    (hm : M ∉ ys) : count I ys = length ys := by
  induction' ys with x xs hxs
  · rfl
  · cases x
    · -- case `x = M` gives a contradiction.
      exfalso; exact hm (mem_cons_self M xs)
    · -- case `x = I`
      rw [count_cons, if_pos rfl, length, succ_inj']
      apply hxs
      · simpa only [count]
      · rw [mem_cons, not_or] at hm; exact hm.2
    · -- case `x = U` gives a contradiction.
      exfalso; simp only [count, countP_cons_of_pos (· == U) _ (rfl : U == U)] at hu
set_option linter.uppercaseLean3 false in
#align miu.count_I_eq_length_of_count_U_zero_and_neg_mem Miu.count_I_eq_length_of_count_U_zero_and_neg_mem

/-- `base_case_suf` is the base case of the sufficiency result.
-/
theorem base_case_suf (en : Miustr) (h : Decstr en) (hu : count U en = 0) : Derivable en := by
  rcases h with ⟨⟨mhead, nmtail⟩, hi⟩
  have : en ≠ nil := by
    intro k
    simp only [k, count, countP, countP.go, if_false, zero_mod, zero_ne_one, false_or_iff] at hi
  rcases exists_cons_of_ne_nil this with ⟨y, ys, rfl⟩
  rcases mhead
  rsuffices ⟨c, rfl, hc⟩ : ∃ c, replicate c I = ys ∧ (c % 3 = 1 ∨ c % 3 = 2)
  · exact der_replicate_I_of_mod3 c hc
  · use count I ys
    refine And.intro ?_ hi
    apply replicate_count_eq_of_count_eq_length
    exact count_I_eq_length_of_count_U_zero_and_neg_mem hu nmtail
#align miu.base_case_suf Miu.base_case_suf

/-!
Before continuing to the proof of the induction step, we need other auxiliary results that
relate to `count U`.
-/


theorem mem_of_count_U_eq_succ {xs : Miustr} {k : ℕ} (h : count U xs = succ k) : U ∈ xs := by
  induction' xs with z zs hzs
  · exfalso; rw [count] at h; contradiction
  · rw [mem_cons]
    cases z <;> try exact Or.inl rfl
    all_goals right; simp only [count_cons, if_false] at h; exact hzs h
set_option linter.uppercaseLean3 false in
#align miu.mem_of_count_U_eq_succ Miu.mem_of_count_U_eq_succ

theorem eq_append_cons_U_of_count_U_pos {k : ℕ} {zs : Miustr} (h : count U zs = succ k) :
    ∃ as bs : Miustr, zs = as ++ ↑(U :: bs) :=
  append_of_mem (mem_of_count_U_eq_succ h)
set_option linter.uppercaseLean3 false in
#align miu.eq_append_cons_U_of_count_U_pos Miu.eq_append_cons_U_of_count_U_pos

/-- `ind_hyp_suf` is the inductive step of the sufficiency result.
-/
theorem ind_hyp_suf (k : ℕ) (ys : Miustr) (hu : count U ys = succ k) (hdec : Decstr ys) :
    ∃ as bs : Miustr,
      ys = M :: as ++ U :: bs ∧
      count U (↑(M :: as) ++ ↑[I, I, I] ++ bs : Miustr) = k ∧
      Decstr (↑(M :: as) ++ ↑[I, I, I] ++ bs) := by
  rcases hdec with ⟨⟨mhead, nmtail⟩, hic⟩
  have : ys ≠ nil := by rintro rfl; contradiction
  rcases exists_cons_of_ne_nil this with ⟨z, zs, rfl⟩
  rcases mhead
  simp only [count_cons, if_false] at hu
  rcases eq_append_cons_U_of_count_U_pos hu with ⟨as, bs, rfl⟩
  use as, bs
  refine ⟨rfl, ?_, ?_, ?_⟩
  · -- Porting note: `simp_rw [count_append]` didn't work
    rw [count_append] at hu; simp_rw [count_cons, if_true, add_succ, succ_inj'] at hu
    rwa [count_append, count_append]
  · apply And.intro rfl
    rw [cons_append, cons_append]
    dsimp [tail] at nmtail ⊢
    rw [mem_append] at nmtail
    simpa only [append_assoc, cons_append, nil_append, mem_append, mem_cons, false_or] using nmtail
  · rw [count_append, count_append]; rw [← cons_append, count_append] at hic
    simp only [count_cons_self, count_nil, count_cons, if_false] at hic ⊢
    rw [add_right_comm, add_mod_right]; exact hic
#align miu.ind_hyp_suf Miu.ind_hyp_suf

/-- `der_of_decstr` states that `Derivable en` follows from `Decstr en`.
-/
theorem der_of_decstr {en : Miustr} (h : Decstr en) : Derivable en := by
  /- The next three lines have the effect of introducing `count U en` as a variable that can be used
   for induction -/
  have hu : ∃ n, count U en = n := exists_eq'
  cases' hu with n hu
  revert en -- Crucially, we need the induction hypothesis to quantify over `en`
  induction' n with k hk
  · exact base_case_suf _
  · intro ys hdec hus
    rcases ind_hyp_suf k ys hus hdec with ⟨as, bs, hyab, habuc, hdecab⟩
    have h₂ : Derivable (↑(M :: as) ++ ↑[I, I, I] ++ bs) := hk hdecab habuc
    rw [hyab]
    exact Derivable.r3 h₂
#align miu.der_of_decstr Miu.der_of_decstr

/-!
### Decidability of `Derivable`
-/


/-- Finally, we have the main result, namely that `Derivable` is a decidable predicate.
-/
instance : DecidablePred Derivable := fun _ => decidable_of_iff _ ⟨der_of_decstr, decstr_of_der⟩

/-!
By decidability, we can automatically determine whether any given `Miustr` is `Derivable`.
-/


example : ¬Derivable "MU" := by decide

example : Derivable "MUIUIUIIIIIUUUIUII" := by decide

end Miu
