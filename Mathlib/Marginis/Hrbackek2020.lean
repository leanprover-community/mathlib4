/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.PNat.Basic

/-!
We prove a special case of Dickson's Conjecture as stated in
`On factoring of unlimited integers` by KAREL HRBACEK.

n = gcd(a,b) > 1 implies n | f(k) = a+bk for all k,
violating the main hypothesis of Dickson's conjecture.

### Main results

* `dickson_case`: the case where `gcd(a,b)>1` or `b=1`.

Dickson's Conjecture is trivial for `ℓ = 0`
and we do not need Hrbacek's assumption that `ℓ ≥ 1`.
 -/

open Finset

/-
## Arithmetical preliminaries
-/

/-- If `b ∣ a`, `b > 1` then `(a, b) > 1`. -/
lemma gcd_gt_of_dvd {a b : ℕ} (ha : b ∣ a) (h_b : 1 < b): 1 < Nat.gcd a b := by
  have hb : 1 ≤ b := Nat.one_le_of_lt h_b
  unfold Nat.gcd
  by_cases Ha : a = 0
  · rw [if_pos Ha]
    exact h_b
  rw [if_neg Ha]
  obtain ⟨k,hk⟩ := ha
  have hbk: b ∣ b.gcd (b * k) := by
    refine Nat.dvd_gcd_iff.mpr ?_
    constructor
    · simp
    · exact Nat.dvd_mul_right b k
  rw [hk]
  by_cases Hab : a = b
  · subst Hab
    have : k = 1 := (Nat.mul_right_eq_self_iff hb).mp hk.symm
    subst this
    simp only [mul_one, Nat.mod_self, Nat.gcd_zero_left]
    exact h_b
  · have hk1: 1 < k := Nat.one_lt_iff_ne_zero_and_ne_one.mpr
      ⟨fun hc => Ha  <| mul_zero b ▸ hc ▸ hk, fun hc => Hab <| mul_one  b ▸ hc ▸ hk⟩
    have : b % (b * k) = b :=
      Nat.mod_eq_of_lt <| (Nat.lt_mul_iff_one_lt_right (hb)).mpr hk1
    rw [this]
    exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨
      Nat.gcd_ne_zero_left (fun hc => by
        rw [hc, nonpos_iff_eq_zero] at hb
        exact one_ne_zero hb
      ), fun hc => by
      have : b ∣ 1 :=
        (Nat.ModEq.dvd_iff (congrFun (congrArg HMod.hMod hc) (b.gcd (b * k))) hbk).mp hbk
      rw [Nat.dvd_one] at this
      subst this
      simp only [lt_self_iff_false] at h_b⟩




/-
## Proven cases of Dickson's Conjecture
-/


/-- The statement that Dickson's Conjecture holds for `ℓ, a, b`. -/
def dickson_conjecture_holds_for (ℓ : ℕ) (a : Fin ℓ → ℕ) (b : Fin ℓ → ℕ+) : Prop :=
    ¬ (∃ n, n > 1 ∧ ∀ k, n ∣ ∏ i, (a i + b i * k)) → ∀ (i : Fin ℓ) (n₀:ℕ),
    ∃ n ≥ n₀, (a i + b i * n).Prime

/-- A conjecture from
  L E Dickson, A new extension of Dirichlet’s theorem on prime numbers,
  Messenger of Mathematics 33 (1904), 155 – 161.-/
def DicksonConjecture : Prop := ∀ ℓ a b, dickson_conjecture_holds_for ℓ a b

/-- Some trivial cases of Dickson's Conjecture. -/
theorem dickson_case {ℓ : ℕ} {a : Fin ℓ → ℕ} {b : Fin ℓ → ℕ+}
    (ha : ∀ i, Nat.gcd (a i) (b i) > 1 ∨ b i = 1) :
    dickson_conjecture_holds_for ℓ a b := by
  intro hc i n₀
  by_cases h : ∀ i, b i = 1
  · obtain ⟨p,hp⟩ := Nat.exists_infinite_primes (a i + n₀)
    rw [h i]
    simp only [ge_iff_le, PNat.val_ofNat, one_mul]
    exact ⟨p - a i, Nat.le_sub_of_add_le (by linarith),
      (Nat.add_sub_of_le (by show a i ≤ p; linarith)).symm ▸ hp.2⟩
  · simp at h
    obtain ⟨i,hi⟩ := h
    exfalso
    apply hc
    exists Nat.gcd (a i) (b i)
    constructor
    · exact (ha i).elim id <| hi.elim
    · intro k
      let h₀ := prod_dvd_prod_of_subset {i} univ
        (λ j : Fin ℓ ↦ a j + b j * k) (subset_univ {i})
      rw [prod_singleton] at h₀
      exact Nat.dvd_trans ((Nat.dvd_add_iff_right <| Nat.gcd_dvd_left (a i) (b i)).mp
          <| Nat.dvd_trans (Nat.gcd_dvd_right (a i) (b i))
            <| Nat.dvd_mul_right (b i) k) h₀

/-- Dickson's conjecture holds when `b∣a`. -/
lemma dickson_dvd {ℓ : ℕ} {a : Fin ℓ → ℕ} {b : Fin ℓ → ℕ+} (ha : ∀ i, (b i).1 ∣ a i) :
    dickson_conjecture_holds_for ℓ a b :=
  dickson_case (λ i ↦ (em (b i =1)).elim (fun H => .inr H)
  (fun H => .inl <| gcd_gt_of_dvd (ha i) <| lt_of_le_of_ne (b i).2 <|by
    contrapose H;simp_all;symm at H;exact PNat.coe_eq_one_iff.mp H))

/-- Dickson's conjecture holds when `a=0`. -/
theorem dickson_linear {ℓ : ℕ} {a : Fin ℓ → ℕ} {b : Fin ℓ → ℕ+} (ha : ∀ i, a i = 0) :
    dickson_conjecture_holds_for ℓ a b :=
  dickson_dvd <| fun i => by rw [ha i];exact Nat.dvd_zero (b i)
