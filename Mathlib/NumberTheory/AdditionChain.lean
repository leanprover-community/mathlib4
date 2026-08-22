/-
Copyright (c) 2026 Will Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Blair
-/
module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.List.Pairwise

/-!
# Addition chains

An *addition chain* for `n` is a strictly increasing list `1 = a₀ < a₁ < ⋯ < a_r = n` in which
every entry after the first is a sum of two (not necessarily distinct) earlier entries. Its
*length* is `r`, the number of additions, and `ℓ n` is the least length over all chains ending
at `n`. Addition chains measure the cost of computing `x ^ n` by repeated multiplication.

## Main definitions

* `List.IsAdditionChain`: the predicate that a list of naturals is an addition chain.
* `Nat.additionChainSteps n`: the set of lengths of addition chains ending at `n`.
* `Nat.additionChainLength n`: the least such length, written `ℓ n` in the literature.

## Main results

* `Nat.additionChainSteps_nonempty`: every positive `n` has an addition chain, so
  `additionChainLength` is the minimum of a nonempty set.
* `List.IsAdditionChain.getLast_le_two_pow`: an addition step at most doubles, so a chain of
  `r` steps cannot reach past `2 ^ r`.
* `Nat.lt_additionChainLength_of_two_pow_lt`: the resulting lower bound on
  `additionChainLength`, which is what makes it computable in practice: an explicit chain
  bounds it above by `Nat.additionChainLength_le`, and this bounds it below.

## References

* [D. E. Knuth, *The Art of Computer Programming, Vol. 2*][knuth1997], section 4.6.3.

## Tags

addition chain, addition chain length, Scholz conjecture
-/

@[expose] public section


namespace List

/-- An *addition chain* is a strictly increasing list of naturals starting at `1` in which
every entry other than `1` is a sum of two (not necessarily distinct) entries of the list. -/
def IsAdditionChain (c : List ℕ) : Prop :=
  c.head? = some 1 ∧ c.Pairwise (· < ·) ∧ ∀ x ∈ c, x ≠ 1 → ∃ y ∈ c, ∃ z ∈ c, x = y + z

instance (c : List ℕ) : Decidable (IsAdditionChain c) := by
  unfold IsAdditionChain; infer_instance

variable {c ys : List ℕ} {x y : ℕ}

/-- Every entry of an addition chain is positive. -/
theorem IsAdditionChain.one_le_of_mem (h : IsAdditionChain c) (hx : x ∈ c) : 1 ≤ x := by
  obtain ⟨hhead, hsorted, -⟩ := h
  cases c with
  | nil => simp at hx
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_rfl
    · exact le_of_lt ((List.pairwise_cons.mp hsorted).1 _ hx)

/-- Dropping the last entry of an addition chain leaves an addition chain. The entries are
positive, so a summand of the last entry is never the last entry itself. -/
theorem IsAdditionChain.dropLast (h : IsAdditionChain (ys ++ [y])) (hys : ys ≠ []) :
    IsAdditionChain ys := by
  obtain ⟨hhead, hsorted, hsum⟩ := h
  refine ⟨?_, (List.pairwise_append.mp hsorted).1, ?_⟩
  · cases ys with
    | nil => simp at hys
    | cons a t => simpa using hhead
  · intro x hx hx1
    obtain ⟨a, ha, b, hb, rfl⟩ := hsum x (List.mem_append_left _ hx) hx1
    have hxy := (List.pairwise_append.mp hsorted).2.2 _ hx _ (List.mem_singleton_self y)
    have ha1 := IsAdditionChain.one_le_of_mem ⟨hhead, hsorted, hsum⟩ ha
    have hb1 := IsAdditionChain.one_le_of_mem ⟨hhead, hsorted, hsum⟩ hb
    refine ⟨a, ?_, b, ?_, rfl⟩
    · rcases List.mem_append.mp ha with h | h
      · exact h
      · exact absurd (List.mem_singleton.mp h) (by rintro rfl; omega)
    · rcases List.mem_append.mp hb with h | h
      · exact h
      · exact absurd (List.mem_singleton.mp h) (by rintro rfl; omega)

/-- An addition step at most doubles, so a chain of `r` steps cannot reach past `2 ^ r`. -/
theorem IsAdditionChain.getLast_le_two_pow (h : IsAdditionChain c) (hne : c ≠ []) :
    c.getLast hne ≤ 2 ^ (c.length - 1) := by
  induction c using List.reverseRecOn with
  | nil => simp at hne
  | append_singleton ys y ih =>
    rw [List.getLast_append_singleton]
    rcases eq_or_ne ys [] with rfl | hys
    · obtain ⟨hhead, -, -⟩ := h
      simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hhead
      simp [hhead]
    · have hchain := h.dropLast hys
      obtain ⟨hhead, hsorted, hsum⟩ := h
      have hy1 : y ≠ 1 := by
        rintro rfl
        obtain ⟨a, hays⟩ := List.exists_mem_of_ne_nil ys hys
        have := (List.pairwise_append.mp hsorted).2.2 _ hays _ (List.mem_singleton_self 1)
        have := IsAdditionChain.one_le_of_mem ⟨hhead, hsorted, hsum⟩ (List.mem_append_left _ hays)
        omega
      obtain ⟨a, ha, b, hb, hyab⟩ := hsum y (by simp) hy1
      have ha1 := IsAdditionChain.one_le_of_mem ⟨hhead, hsorted, hsum⟩ ha
      have hb1 := IsAdditionChain.one_le_of_mem ⟨hhead, hsorted, hsum⟩ hb
      have hays : a ∈ ys := by
        rcases List.mem_append.mp ha with h' | h'
        · exact h'
        · exact absurd (List.mem_singleton.mp h') (by rintro rfl; omega)
      have hbys : b ∈ ys := by
        rcases List.mem_append.mp hb with h' | h'
        · exact h'
        · exact absurd (List.mem_singleton.mp h') (by rintro rfl; omega)
      have hsub := (List.pairwise_append.mp hsorted).1
      have hla := (hsub.imp le_of_lt).rel_getLast hays
      have hlb := (hsub.imp le_of_lt).rel_getLast hbys
      have hih := ih hchain hys
      have hlen : (ys ++ [y]).length - 1 = ys.length := by simp
      rw [hlen]
      have hyl : ys.length = (ys.length - 1) + 1 := by
        cases ys with
        | nil => simp at hys
        | cons _ t => simp
      rw [hyl, pow_succ]
      omega

end List

namespace Nat

/-- The set of lengths of addition chains ending at `n`, where the length of a chain is its
number of entries minus one. -/
def additionChainSteps (n : ℕ) : Set ℕ :=
  {r | ∃ c : List ℕ, c.IsAdditionChain ∧ c.getLast? = some n ∧ c.length = r + 1}

/-- The *addition chain length* `ℓ n` of `n`: the least number of additions needed to reach `n`
from `1`. It is `0` when `n = 0`, where there is no chain to take the minimum over. -/
noncomputable def additionChainLength (n : ℕ) : ℕ := sInf (additionChainSteps n)

/-- `additionChainLength` unfolds to the infimum of `additionChainSteps`. -/
theorem additionChainLength_eq_sInf (n : ℕ) :
    additionChainLength n = sInf (additionChainSteps n) := rfl

/-- Exhibiting a chain bounds `ℓ` above. -/
theorem additionChainLength_le {n r : ℕ} (c : List ℕ) (hc : c.IsAdditionChain)
    (hlast : c.getLast? = some n) (hlen : c.length = r + 1) : additionChainLength n ≤ r :=
  Nat.sInf_le ⟨c, hc, hlast, hlen⟩

/-- A chain ending at `n` witnesses that `additionChainSteps n` is nonempty. -/
theorem additionChainSteps_nonempty_of {n r : ℕ} (c : List ℕ) (hc : c.IsAdditionChain)
    (hlast : c.getLast? = some n) (hlen : c.length = r + 1) : (additionChainSteps n).Nonempty :=
  ⟨r, c, hc, hlast, hlen⟩

/-- Every positive natural number is the last entry of some addition chain: double when the
target is even, and add `1` when it is odd. -/
theorem exists_isAdditionChain (n : ℕ) (hn : 0 < n) :
    ∃ c : List ℕ, c.IsAdditionChain ∧ c.getLast? = some n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n = 1
    · exact h1 ▸ ⟨[1], ⟨rfl, by simp, by simp⟩, rfl⟩
    have hn1 : 1 < n := by omega
    -- `m` is `n / 2` when `n` is even and `n - 1` when `n` is odd; either way `n = m + m'`
    -- for two entries `m` and `m'` of a chain ending at `m`.
    obtain ⟨m, hm0, hmn, hsum⟩ : ∃ m, 0 < m ∧ m < n ∧ (n = m + m ∨ n = m + 1) := by
      by_cases hpar : n % 2 = 0
      · exact ⟨n / 2, by omega, by omega, Or.inl (by omega)⟩
      · exact ⟨n - 1, by omega, by omega, Or.inr (by omega)⟩
    obtain ⟨c, hc, hlast⟩ := ih m hmn hm0
    have hcne : c ≠ [] := by rintro rfl; simp at hlast
    have hgl : c.getLast hcne = m := by
      rw [List.getLast?_eq_some_getLast (l := c) (h := hcne)] at hlast
      exact Option.some.inj hlast
    have hone : (1 : ℕ) ∈ c := by
      obtain ⟨hhead, -, -⟩ := hc
      cases c with
      | nil => simp at hcne
      | cons a t => simp only [List.head?_cons, Option.some.injEq] at hhead; simp [hhead]
    refine ⟨c ++ [n], ⟨?_, ?_, ?_⟩, by simp⟩
    · obtain ⟨hhead, -, -⟩ := hc
      cases c with
      | nil => simp at hcne
      | cons a t => simpa using hhead
    · refine List.pairwise_append.mpr ⟨hc.2.1, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      have := (hc.2.1.imp le_of_lt).rel_getLast ha
      rw [hgl] at this
      omega
    · intro x hx hx1
      rcases List.mem_append.mp hx with hx' | hx'
      · obtain ⟨y, hy, z, hz, hyz⟩ := hc.2.2 x hx' hx1
        exact ⟨y, List.mem_append_left _ hy, z, List.mem_append_left _ hz, hyz⟩
      · simp only [List.mem_singleton] at hx'
        subst hx'
        have hmem : c.getLast hcne ∈ c := List.getLast_mem hcne
        rw [hgl] at hmem
        rcases hsum with h | h
        · exact ⟨m, List.mem_append_left _ hmem, m, List.mem_append_left _ hmem, h⟩
        · exact ⟨m, List.mem_append_left _ hmem, 1, List.mem_append_left _ hone, h⟩

/-- Every positive `n` admits an addition chain, so `additionChainLength n` is a genuine
minimum rather than `sInf ∅`. -/
theorem additionChainSteps_nonempty {n : ℕ} (hn : 0 < n) : (additionChainSteps n).Nonempty := by
  obtain ⟨c, hc, hlast⟩ := exists_isAdditionChain n hn
  have hcne : c ≠ [] := by rintro rfl; simp at hlast
  exact ⟨c.length - 1, c, hc, hlast, by cases c with
    | nil => simp at hcne
    | cons _ t => simp⟩

/-- The doubling bound, transported to `ℓ`: reaching `n` takes at least `log₂ n` steps. -/
theorem le_two_pow_additionChainLength {n : ℕ} (hn : 0 < n) :
    n ≤ 2 ^ additionChainLength n := by
  obtain ⟨c, hc, hlast, hlen⟩ := Nat.sInf_mem (additionChainSteps_nonempty hn)
  have hcne : c ≠ [] := by rintro rfl; simp at hlast
  have hgl : c.getLast hcne = n := by
    rw [List.getLast?_eq_some_getLast (l := c) (h := hcne)] at hlast
    exact Option.some.inj hlast
  have := hc.getLast_le_two_pow hcne
  rw [hgl, hlen] at this
  simpa [additionChainLength_eq_sInf] using this

/-- The lower bound on `ℓ`: `r` addition steps cannot reach past `2 ^ r`. -/
theorem lt_additionChainLength_of_two_pow_lt {n r : ℕ} (h : 2 ^ r < n) :
    r < additionChainLength n := by
  by_contra hcon
  push Not at hcon
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) h
  have h1 := le_two_pow_additionChainLength hn
  have h2 : (2 : ℕ) ^ additionChainLength n ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hcon
  omega

end Nat
