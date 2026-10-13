import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# The Jacobsthal function

The Jacobsthal function `j(n)` (Jacobsthal, 1961) is the maximal gap between consecutive
integers coprime to `n`. This file defines `Nat.jacobsthal` and proves its exact values on
the first primorials:

> **`jacobsthal 2 = 2`, `jacobsthal 6 = 4`, `jacobsthal 30 = 6`,
> `jacobsthal 210 = 10`, `jacobsthal 2310 = 14`, `jacobsthal 30030 = 22`.**
>
> For `2310 = 2·3·5·7·11`: every interval of length 14 contains an integer coprime to
> 2310, and the bound is attained (after `113` the next coprime is `127`).

## Main results
* `Nat.jacobsthal` — the Jacobsthal function.
* `Nat.jacobsthal_eq_of_window` — a reusable criterion: if every interval of length `j`
  contains an integer coprime to `m` and a gap of exactly `j` is attained, then
  `jacobsthal m = j`.
* `Nat.jacobsthal_2`, `Nat.jacobsthal_6`, `Nat.jacobsthal_30`, `Nat.jacobsthal_210`,
  `Nat.jacobsthal_2310_value`, `Nat.jacobsthal_30030` — the values on the first six primorials.

## Proof outline
1. periodicity of coprimality mod `m` (`coprime_add_mul`), from
   `Nat.coprime_self_add_left`;
2. `hwin` — reduce the window condition to a finite check of the `m` residue classes;
3. `jacobsthal_eq_of_window` — an `sSup` argument combining the window and the attained gap.
-/

namespace Nat

/-- The Jacobsthal function: the maximal gap between consecutive integers coprime to `m`. -/
noncomputable def jacobsthal (m : ℕ) : ℕ :=
  sSup {d : ℕ | ∃ n, n.Coprime m ∧ (n + d).Coprime m ∧ ∀ k, n < k → k < n + d → ¬ k.Coprime m}

/-- Coprimality to `m` is periodic with period `m`. -/
lemma coprime_add_mul {x m t : ℕ} : (x + m * t).Coprime m ↔ x.Coprime m := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ]
    rw [← add_assoc]
    rw [add_comm]
    rw [coprime_self_add_left]
    exact ih

/-- A reusable criterion for the value of the Jacobsthal function:
  a window of length `j` plus an attained gap of `j` give `jacobsthal m = j`. -/
theorem jacobsthal_eq_of_window {m j : ℕ}
    (hwin : ∀ n : ℕ, ∃ d : ℕ, d < j ∧ (n + d + 1).Coprime m)
    (hattain : ∃ n : ℕ, n.Coprime m ∧ (n + j).Coprime m ∧
      ∀ k : ℕ, n < k → k < n + j → ¬ k.Coprime m) :
    jacobsthal m = j := by
  unfold jacobsthal
  apply le_antisymm
  · apply csSup_le
    · rcases hattain with ⟨n, hn, hnj, hgap⟩
      exact ⟨j, n, hn, hnj, hgap⟩
    · intro d hd
      rcases hd with ⟨n, hn, hnd, hgap⟩
      by_contra hnot
      have hgt : j < d := lt_of_not_ge hnot
      rcases hwin n with ⟨e, he, hcop⟩
      exact hgap (n + e + 1) (by omega) (by omega) hcop
  · apply le_csSup
    · refine ⟨j, ?_⟩
      intro d hd
      rcases hd with ⟨n, hn, hnd, hgap⟩
      by_contra hnot
      have hgt : j < d := lt_of_not_ge hnot
      rcases hwin n with ⟨e, he, hcop⟩
      exact hgap (n + e + 1) (by omega) (by omega) hcop
    · rcases hattain with ⟨n, hn, hnj, hgap⟩
      exact ⟨n, hn, hnj, hgap⟩

/-- Reduce the window condition to a finite check of the `m` residue classes. -/
lemma hwin (m j : ℕ) (hm : 0 < m) :
    (∀ r : ℕ, r < m → ∃ d : ℕ, d < j ∧ (r + d + 1).Coprime m) →
      ∀ n : ℕ, ∃ d : ℕ, d < j ∧ (n + d + 1).Coprime m := by
  intro hres n
  let r := n % m
  have hr : r < m := Nat.mod_lt n hm
  rcases hres r hr with ⟨d, hd, hcop⟩
  refine ⟨d, hd, ?_⟩
  have hn := Nat.div_add_mod n m
  have hpath : n + d + 1 = r + d + 1 + m * (n / m) := by omega
  rw [hpath]
  rw [coprime_add_mul]
  exact hcop

/-- `jacobsthal 2 = 2`. -/
theorem jacobsthal_2 : jacobsthal 2 = 2 :=
  jacobsthal_eq_of_window (hwin 2 2 (by norm_num : 0 < 2) (by native_decide))
    (by
      refine ⟨1, ?_, ?_, ?_⟩
      · native_decide
      · native_decide
      · intro k hk1 hk2
        interval_cases k <;> norm_num)

/-- `jacobsthal 6 = 4`. -/
theorem jacobsthal_6 : jacobsthal 6 = 4 :=
  jacobsthal_eq_of_window (hwin 6 4 (by norm_num : 0 < 6) (by native_decide))
    (by
      refine ⟨1, ?_, ?_, ?_⟩
      · native_decide
      · native_decide
      · intro k hk1 hk2
        interval_cases k <;> norm_num)

/-- `jacobsthal 30 = 6`. -/
theorem jacobsthal_30 : jacobsthal 30 = 6 :=
  jacobsthal_eq_of_window (hwin 30 6 (by norm_num : 0 < 30) (by native_decide))
    (by
      refine ⟨1, ?_, ?_, ?_⟩
      · native_decide
      · native_decide
      · intro k hk1 hk2
        interval_cases k <;> norm_num)

/-- `jacobsthal 210 = 10`. -/
theorem jacobsthal_210 : jacobsthal 210 = 10 :=
  jacobsthal_eq_of_window (hwin 210 10 (by norm_num : 0 < 210) (by native_decide))
    (by
      refine ⟨1, ?_, ?_, ?_⟩
      · native_decide
      · native_decide
      · intro k hk1 hk2
        interval_cases k <;> norm_num)

/-- **`jacobsthal 2310 = 14`** for the primorial 2310 = 2·3·5·7·11.
  Attained after 113: the next coprime to 2310 is 127. -/
theorem jacobsthal_2310_value : jacobsthal 2310 = 14 :=
  jacobsthal_eq_of_window (hwin 2310 14 (by norm_num : 0 < 2310) (by native_decide))
    (by
      refine ⟨113, ?_, ?_, ?_⟩
      · native_decide
      · native_decide
      · intro k hk1 hk2
        interval_cases k <;> norm_num)


/-- **`jacobsthal 30030 = 22`** for the primorial 30030 = 2·3·5·7·11·13.
  Attained after 20569: the next coprime to 30030 is 20591. -/
theorem jacobsthal_30030 : jacobsthal 30030 = 22 :=
  jacobsthal_eq_of_window (hwin 30030 22 (by norm_num : 0 < 30030) (by native_decide))
    (by
      refine ⟨20569, ?_, ?_, ?_⟩
      · native_decide
      · native_decide
      · intro k hk1 hk2
        interval_cases k <;> norm_num)

end Nat