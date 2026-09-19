/-
Copyright (c) 2026 Will Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Blair
-/
module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Interval.Set.Defs

/-!
# Addition chains

An *addition chain* of length `r` is a strictly increasing sequence `1 = a₀ < a₁ < ⋯ < a_r` in
which every entry after the first is a sum of two (not necessarily distinct) earlier entries.
The *addition chain length* `ℓ n` of `n` is the least length of a chain with `a_r = n`.
Addition chains measure the cost of computing `x ^ n` by repeated multiplication.

## Implementation notes

The entries are stored as a function `ℕ → ℕ`; values past index `length` carry no meaning.
Using `ℕ` rather than `Fin (length + 1)` keeps index side conditions out of the way until they
are needed.

## Main definitions

* `AdditionChain`: an addition chain, with `AdditionChain.length` the number of additions and
  `AdditionChain.last` its final entry.
* `AdditionChain.trivial n`: the chain `1, 2, …, n + 1`.
* `Nat.additionChainLength n`: the least length of an addition chain ending at `n`, written
  `ℓ n` in the literature.

## Main results

* `AdditionChain.seq_le_two_pow`: an addition step at most doubles, so `aᵢ ≤ 2 ^ i`.
* `Nat.le_two_pow_additionChainLength`: `n ≤ 2 ^ ℓ n` for `0 < n`.
* `Nat.additionChainLength_le_sub_one`: `ℓ n ≤ n - 1`.

## References

* [D. E. Knuth, *The Art of Computer Programming, Vol. 2*][knuth1997], section 4.6.3.

## Tags

addition chain, addition chain length, Scholz conjecture
-/

@[expose] public section

/-- An *addition chain* of length `length`: a strictly increasing sequence
`1 = seq 0 < seq 1 < ⋯ < seq length` in which every entry after the first is the sum of two
(not necessarily distinct) earlier entries. Values of `seq` past `length` are ignored. -/
structure AdditionChain where
  /-- The number of additions in the chain; the chain has `length + 1` entries. -/
  length : ℕ
  /-- The entries of the chain, indexed from `0` to `length`. -/
  seq : ℕ → ℕ
  seq_zero : seq 0 = 1
  strictMonoOn : StrictMonoOn seq (Set.Iic length)
  exists_add : ∀ i ≤ length, 0 < i → ∃ j < i, ∃ k < i, seq i = seq j + seq k

namespace AdditionChain

attribute [simp] seq_zero

variable (c : AdditionChain) {i : ℕ}

/-- The final entry of an addition chain. -/
def last : ℕ := c.seq c.length

theorem one_le_seq (hi : i ≤ c.length) : 1 ≤ c.seq i := by
  rcases i.eq_zero_or_pos with rfl | hi₀
  · simp
  · exact c.seq_zero ▸ (c.strictMonoOn (Set.mem_Iic.2 (Nat.zero_le _)) hi hi₀).le

theorem one_le_last : 1 ≤ c.last := c.one_le_seq le_rfl

/-- An addition step at most doubles, so the `i`th entry of a chain is at most `2 ^ i`. -/
theorem seq_le_two_pow (hi : i ≤ c.length) : c.seq i ≤ 2 ^ i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rcases i with - | i
    · simp
    · obtain ⟨j, hj, k, hk, h⟩ := c.exists_add _ hi i.succ_pos
      have := ih j hj (by lia)
      have := ih k hk (by lia)
      have := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_lt_succ hj)
      have := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_lt_succ hk)
      rw [h, Nat.pow_succ]
      lia

theorem last_le_two_pow : c.last ≤ 2 ^ c.length := c.seq_le_two_pow le_rfl

/-- The chain `1, 2, …, n + 1` of length `n`, each entry obtained by adding `1`. -/
def trivial (n : ℕ) : AdditionChain where
  length := n
  seq := (· + 1)
  seq_zero := rfl
  strictMonoOn := fun _ _ _ _ h ↦ Nat.add_lt_add_right h 1
  exists_add i _ hi := ⟨i - 1, by lia, 0, hi, by simp; lia⟩

@[simp] theorem trivial_length (n : ℕ) : (trivial n).length = n := rfl

@[simp] theorem last_trivial (n : ℕ) : (trivial n).last = n + 1 := rfl

end AdditionChain

namespace Nat

/-- The *addition chain length* `ℓ n` of `n`: the least length of an addition chain ending at `n`.
It is `0` when `n = 0`, where there is no such chain. -/
noncomputable def additionChainLength (n : ℕ) : ℕ :=
  sInf {r | ∃ c : AdditionChain, c.length = r ∧ c.last = n}

theorem additionChainLength_le (c : AdditionChain) : additionChainLength c.last ≤ c.length :=
  Nat.sInf_le ⟨c, rfl, rfl⟩

@[simp] theorem additionChainLength_zero : additionChainLength 0 = 0 := by
  rw [additionChainLength, Nat.sInf_eq_zero]
  exact .inr <| Set.eq_empty_of_forall_notMem fun r ⟨c, _, h⟩ ↦ by
    have := c.one_le_last; lia

theorem additionChainLength_le_sub_one (n : ℕ) : additionChainLength n ≤ n - 1 := by
  rcases n with - | n
  · simp
  · simpa using additionChainLength_le (.trivial n)

/-- Every positive `n` has an addition chain of length `ℓ n` ending at `n`. -/
theorem exists_additionChain_length_eq {n : ℕ} (hn : 0 < n) :
    ∃ c : AdditionChain, c.length = additionChainLength n ∧ c.last = n :=
  Nat.sInf_mem (s := {r | ∃ c : AdditionChain, c.length = r ∧ c.last = n})
    ⟨n - 1, .trivial (n - 1), rfl, by simp; lia⟩

/-- Reaching `n` takes at least `log₂ n` additions. -/
theorem le_two_pow_additionChainLength {n : ℕ} (hn : 0 < n) :
    n ≤ 2 ^ additionChainLength n := by
  obtain ⟨c, hlen, rfl⟩ := exists_additionChain_length_eq hn
  exact hlen ▸ c.last_le_two_pow

theorem lt_additionChainLength_of_two_pow_lt {n r : ℕ} (h : 2 ^ r < n) :
    r < additionChainLength n := by
  by_contra! hcon
  have := le_two_pow_additionChainLength (n := n) (by lia)
  have := Nat.pow_le_pow_right Nat.zero_lt_two hcon
  lia

end Nat
