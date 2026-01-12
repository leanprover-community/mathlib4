/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Computability.Primrec.List
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Nat.GCD.Prime
public import Mathlib.NumberTheory.Divisors

/-!
# Natural number arithmetic functions that are primitive recursive

The file `Computability/Primrec/Basic.lean` gives the basic machinery for primitive recursive
constructions, such as pairing/unpairing, adding, multiplication etc. that are used to work with
many other types. This file, in contrast, gives particular results for certain natural number
functions that are might show up in math (but less likely to be needed in other contexts).

## Main Results

* `Primrec.factorial`: The factorial function is primitve recursive.
* `Primrec₂.gcd`: The gcd function is primitve recursive.
* `Primrec₂.lcm`: The lcm function is primitve recursive.
* `Primrec.prime`: The primality test is primitve recursive.
* `Primrec₂.pow`: The power function is primitve recursive.
* `Primrec₂.log`: The logarithm function is primitve recursive.

-/

@[expose] public section

open Primrec Primrec₂

/-- The square root function is primitve recursive. -/
theorem Primrec.nat_sqrt : Primrec Nat.sqrt :=
  Nat.Primrec'.prim_iff₁.1 Nat.Primrec'.sqrt

/-- The factorial function is primitve recursive. -/
theorem Primrec.factorial : Primrec Nat.factorial := by
  convert list_foldl (σ := ℕ) (h := fun n ⟨p, k⟩ ↦ p * (k + 1)) list_range (const 1) ?_
  · rw [← Finset.prod_range_add_one_eq_factorial, ← List.foldl_map, ← List.prod_eq_foldl]
    rw [← List.prod_toFinset _ List.nodup_range, ← List.toFinset_range]
  · exact comp₂ (nat_mul.comp₂ left (succ.comp₂ right)) right

theorem Primrec₂.descFactorial : Primrec₂ Nat.descFactorial := by
  change Primrec (fun (n : ℕ × ℕ) ↦ Nat.descFactorial n.1 n.2)
  have h_descFactorial (n k) : Nat.descFactorial n k = Nat.recOn k 1
      (fun k IH ↦ (n - k) * IH) := by
    induction k <;> simp +arith +decide [ *, Nat.descFactorial_succ ]
  simp_rw [h_descFactorial]
  apply (Primrec.const 1).nat_rec (g := fun n p ↦ (n - p.1) * p.2)
  exact Primrec.nat_mul.comp₂ (Primrec.nat_sub.comp .fst (Primrec.fst.comp .snd))
    (Primrec.snd.comp .snd)

theorem Primrec₂.gcd : Primrec₂ Nat.gcd := by
  -- We can compute the gcd using the Euclidean algorithm, then describe this as a
  -- primitive recursive function.
  let step : ℕ × ℕ → ℕ × ℕ := fun p ↦ if p.2 = 0 then (p.1, 0) else (p.2, p.1 % p.2)
  have h_gcd (a b) : Nat.gcd a b = (step^[a + b] (a, b)).fst := by
    -- The iteration preserves the gcd
    have h_euc : ∀ n ≤ a + b, (step^[n] (a, b)).fst.gcd (step^[n] (a, b)).snd = Nat.gcd a b := by
      intro n hn
      induction n
      · rfl
      · grind [Nat.gcd_comm, Nat.gcd_rec, Function.iterate_succ_apply']
    -- After `a + b` steps, the second component will be 0.
    suffices h_second_zero : ((a + b).iterate step (a, b)).snd = 0 by
      rw [← h_euc _ le_rfl, h_second_zero, Nat.gcd_zero_right]
    suffices h_euclidean_zero : ∀ n ≤ a + b, (step^[n] (a, b)).snd ≤ a + b - n by
      simpa using h_euclidean_zero (a + b) le_rfl
    intro n hn
    induction n; · simp
    simp_rw [step, Function.iterate_succ_apply']
    split_ifs with h; · simp
    exact Nat.le_sub_one_of_lt ((Nat.mod_lt _ (by positivity)).trans_le (by grind))
  eta_expand
  simp_rw [h_gcd, Primrec₂]
  refine fst.comp (nat_iterate (nat_add.comp fst snd) .id ?_)
  apply_rules [Primrec.ite, const, pair, Primrec.eq.comp,
    nat_mod.comp fst snd, comp, snd.comp snd, fst.comp snd]

theorem Primrec.coprime : PrimrecRel Nat.Coprime := by
  rw [primrecRel_iff_primrec_decide]
  exact Primrec.beq.comp (gcd.comp fst snd) (const 1)

theorem Primrec₂.lcm : Primrec₂ Nat.lcm :=
  nat_div.comp₂ nat_mul gcd

theorem PrimrecRel.dvd : PrimrecRel (· ∣ · : ℕ → ℕ → Prop) := by
  simp_rw [Nat.dvd_iff_mod_eq_zero]
  exact (Primrec.eq.primrecRel.comp nat_mod (.const 0)).comp (snd.pair fst)

theorem Primrec.prime : PrimrecPred Nat.Prime := by
  -- We use the characterization `Nat.Prime p ↔ 2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1`.
  have h_reachable : PrimrecRel (fun m p : ℕ ↦ if m ∣ p then m = 1 else true) := by
    -- The relation `R m p := m ∣ p → m = 1` can be rewritten as `R m p := ¬(m ∣ p ∧ m ≠ 1)`.
    suffices h_reachable : PrimrecPred (fun (p : ℕ × ℕ) => ¬(p.1 ∣ p.2 ∧ p.1 ≠ 1)) by
      simp [PrimrecRel]
      grind only
    apply_rules [PrimrecPred.not, PrimrecPred.and, PrimrecRel.dvd]
    exact Primrec.eq.comp fst (const 1)
  -- Then `∀ m < p, R m p` is primrec by `PrimrecRel.forall_lt`
  have h_forall_lt : PrimrecPred (fun p ↦ ∀ m < p, if m ∣ p then m = 1 else true) :=
    h_reachable.forall_lt.comp .id .id
  -- Finally, `2 ≤ p` is primitive recursive, and the conjunction of primitive recursive
  -- predicates is primitive recursive.
  have h_conj := (nat_le.comp (const 2) .id).and h_forall_lt
  simp_all [PrimrecPred, Nat.prime_def_lt]

theorem Primrec₂.pow : Primrec₂ Nat.pow := by
  have h_pow (x n : ℕ) : x ^ n = n.recOn 1 (fun _ y ↦ x * y) := by
    induction n <;> simp [*, pow_succ']
  simp_rw [Primrec₂, Nat.pow_eq, h_pow]
  exact (Primrec.const 1).nat_rec (g := (· * Prod.snd ·))
    (Primrec.nat_mul.comp .fst (Primrec.snd.comp .snd))

theorem Primrec₂.log : Primrec₂ Nat.log := by
  eta_expand
  simp_rw [Nat.log_eq_findGreatest]
  have h_cond : Primrec (decide <| 1 < ·) := by
    rw [← primrecPred_iff_primrec_decide]
    exact nat_lt.comp (.const 1) .id
  have h_find_greatest : Primrec (fun p : ℕ × ℕ ↦ p.2.findGreatest (p.1 ^ · ≤ p.2)) := by
    apply nat_findGreatest snd
    rw [primrecRel_iff_primrec_decide]
    apply Primrec.comp (f := fun x ↦ decide (x.1 ≤ x.2))
      (g := fun p : (ℕ × ℕ) × ℕ ↦ (p.1.1 ^ p.2, p.1.2))
    · rw [← primrecPred_iff_primrec_decide]
      exact nat_le
    · exact pair (pow.comp (fst.comp fst) snd) (snd.comp fst)
  rw [Primrec₂]
  convert cond (h_cond.comp fst) h_find_greatest (const 0)
  grind only

theorem Primrec.log2 : Primrec Nat.log2 := by
  eta_expand
  simp_rw [Nat.log2_eq_log_two]
  exact log.comp (const 2) .id

theorem Primrec₂.clog : Primrec₂ Nat.clog := by
  eta_expand
  simp_rw [Nat.clog_eq_log_pred]
  apply Primrec.ite
  · have h_gt : PrimrecPred (fun p : ℕ × ℕ ↦ 1 < p.1) :=
      nat_lt.comp (const 1) fst
    exact h_gt.and <| h_gt.comp <| pair snd fst
  · exact succ.comp <| log.comp fst <| pred.comp snd
  · exact const 0

proof_wanted Primrec₂.stirlingFirst : Primrec₂ Nat.stirlingFirst

proof_wanted Primrec₂.stirlingSecond : Primrec₂ Nat.stirlingSecond

proof_wanted Primrec.divisors : Primrec Nat.divisors

proof_wanted Primrec.properDivisors : Primrec Nat.properDivisors

proof_wanted Primrec.perfect : PrimrecPred Nat.Perfect
