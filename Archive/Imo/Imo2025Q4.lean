/-
Copyright (c) 2026 Jörn Tiggemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jörn Tiggemann
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Field
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Qify
import Mathlib.Data.Nat.Factorization.Defs

/-!
# IMO 2025 Q4

A proper divisor of a positive integer $N$ is a positive divisor of $N$ other than $N$ itself.
The infinite sequence $a_1,a_2,\dots$ consists of positive integers, each of which has at least
three proper divisors. For each $n\geq1$, the integer $a_{n+1}$ is the sum of the three largest
proper divisors of $a_n$. Determine all possible values of $a_1$.

## Solution

The solution presented here is similar to [this](https://web.evanchen.cc/exams/IMO-2025-notes.pdf)
one. We call a positive integer $n$ _magic_ if there is a sequence $a_1,a_2,\dots$ like described in
the problem such that $a_1=n$. Thus, the problem asks us to determine all magic numbers. We will
show that $n$ is magic if and only if $n$ is of the form $n=12^a\cdot6r$ with non-negative integers
$a,r$ such that $\gcd(r,10)=1$.

Let $\alpha(n)$ be the sum of the three largest proper divisors of $n$ (or the sum of all proper
divisors of $n$ if $n$ has less than three). It is easy to see that $n$ is magic if and only if $n$
has at least three proper divisors and $\alpha(n)$ is magic. Also, if $n$ has at least three proper
divisors and $\alpha(n)=n$, then $n$ is also magic. Furthermore, it is helpful to notice that the
three largest proper divisors of $n$ are exactly the reciprocals of $d_3,d_2,d_1$, where
$d_i(n)$ denotes the $i$-th smallest divisors of $n$ greater than $1$.

We will show via induction over $a$ that $12^a\cdot6r$ is magic for non-negative integers $a,r$ with
$\gcd(r,10)=1$. To show that inversely, every magic number is of this form, we first prove
$d_1(n)=2,d_2(n)=3$ for all magic numbers $n$ (by showing that in every other case, we would have
$\alpha(n)< n$ and $2\nmid\alpha(n)\vee3\nmid\alpha(n)$, yielding the desired result with strong
induction over $n$). Then, $d_3(n)$ can only have the values $6$, $5$ or $4$. In the first case, we
can directly show that $n$ is of the desired form, while in the second and third case, we need to
employ strong induction over the multiplicity of the prime factor $6$ in $n$ to either derive a
contradiction or follow that $n$ is of the form from $\alpha(n)$ being in the form.
-/

namespace Imo2025Q4

/-! ### Definitions for setting up the problem -/

/-- The sum of the three largest proper divisors of `n` (or all of them if `n` has less than three
proper divisors). -/
def α (n : ℕ) : ℕ := (n.properDivisors.sort (· ≥ ·) |>.take 3).sum

/-- Definition of magic numbers like in the proof sketch above. -/
def Magic (n : ℕ) : Prop :=
  ∃ seq : ℕ → ℕ, seq 0 = n ∧ ∀ i, 3 ≤ (seq i).properDivisors.card ∧ α (seq i) = seq (i + 1)

/-! ### General lemmas and definitions for both parts of the proof -/

variable {n i j d l : ℕ}

/-- `n` is magic if and only if `n` has at least three proper divisors and `α n` is `Magic`. Note
that `¬ Magic 0` since `(Nat.properDivisord 0).card = 0`. -/
lemma magic_iff : Magic n ↔ 3 ≤ n.properDivisors.card ∧ Magic (α n) := by
  constructor
  · intro ⟨seq, h0, hi⟩
    rw [← h0]
    refine ⟨hi 0 |>.left, ?_⟩
    use fun i ↦ seq (i + 1)
    refine ⟨hi 0 |>.right.symm, ?_⟩
    intro i
    exact hi (i + 1)
  · intro ⟨h_card, seq, h0, hi⟩
    let seq' : ℕ → ℕ
    | 0 => n
    | i + 1 => seq i
    use seq'
    refine ⟨rfl, ?_⟩
    intro i
    induction i with
    | zero =>
      exact ⟨h_card, h0.symm⟩
    | succ i =>
      exact hi i

/-- If `n` has at least three proper divisors and `α n = n`, then `n` is `Magic`. -/
lemma magic_of_eq_α (h_card : 3 ≤ n.properDivisors.card) (hα : α n = n) :
    Magic n := by
  use fun _ ↦ n; refine ⟨by simp, ?_⟩; intro _; exact ⟨h_card, hα⟩

lemma not_magic_zero : ¬Magic 0 := by rw [magic_iff]; simp

lemma ne_zero_of_magic : Magic n → n ≠ 0 := by contrapose; intro h; rw [h]; exact not_magic_zero

/-- A list of all divisors of `n` in increasing order. Thus, $d_i(n)$ from the proof sketch above
corresponds to `(divisorsList n)[i]`. By definition, `divisorsList 0 = []`. -/
def divisorsList (n : ℕ) : List ℕ := n.divisors.sort

lemma zero_lt_length_divisorsList_iff : 0 < (divisorsList n).length ↔ n ≠ 0 := by
  rw [divisorsList, Finset.length_sort, ← Nat.ne_zero_iff_zero_lt, ne_eq, Finset.card_eq_zero,
    Nat.divisors_eq_empty]

lemma exists_getElem_divisorsList_zero_iff :
    (∃ _ : 0 < (divisorsList n).length, (divisorsList n)[0] = 1) ↔ n ≠ 0 := by
  rw [← zero_lt_length_divisorsList_iff]
  apply exists_iff_of_forall
  intro h
  unfold divisorsList
  simp only [Finset.sorted_zero_eq_min']
  rw [Finset.min'_eq_iff]
  constructor
  · rwa [Nat.one_mem_divisors, ← zero_lt_length_divisorsList_iff]
  · intro d hd
    rw [Nat.add_one_le_iff, ← Nat.ne_zero_iff_zero_lt]
    by_contra h!
    simp [h!] at hd

@[simp]
lemma getElem_divisorsList_zero {h : 0 < (divisorsList n).length} :
    (divisorsList n)[0] = 1 :=
  have hn := zero_lt_length_divisorsList_iff.mp h
  exists_getElem_divisorsList_zero_iff.mpr hn |>.choose_spec

@[simp]
lemma zero_lt_getElem_divisorsList {h : i < (divisorsList n).length} :
    0 < (divisorsList n)[i] := by
  have h' : (divisorsList n)[i] ∈ divisorsList n := by simp
  conv at h' => arg 1; unfold divisorsList
  by_contra! h!
  simp at h!
  simp [h!] at h'

@[simp]
lemma getElem_divisorsList_lt_iff {hi : i < (divisorsList n).length}
    {hj : j < (divisorsList n).length} :
    (divisorsList n)[i] < (divisorsList n)[j] ↔ i < j := by
  apply List.SortedLT.getElem_lt_getElem_iff
  apply Finset.sortedLT_sort

@[simp]
lemma getElem_divisorsList_dvd {h : i < (divisorsList n).length} : (divisorsList n)[i] ∣ n := by
  apply Nat.dvd_of_mem_divisors
  rw [← Finset.mem_sort (· ≤ ·)]
  apply List.getElem_mem

lemma ne_zero_of_lt_length_divisorsList (h : l < (divisorsList n).length) :
    n ≠ 0 := by
  rw [← zero_lt_length_divisorsList_iff]
  exact lt_of_le_of_lt (by simp) h

lemma dvd_iff_exists_getElem_divisorsList (h : n ≠ 0) :
    d ∣ n ↔ ∃ i, ∃ _ : i < (divisorsList n).length, (divisorsList n)[i] = d := by
  rw [← List.mem_iff_getElem, divisorsList, Finset.mem_sort, Nat.mem_divisors, and_iff_left h]

lemma not_dvd_of_between_divisorsList {hi : i + 1 < (divisorsList n).length}
    (lt_d : (divisorsList n)[i] < d) (d_lt : d < (divisorsList n)[i + 1]) : ¬d ∣ n := by
  have hn := ne_zero_of_lt_length_divisorsList hi
  by_contra h!
  have ⟨j, j_lt, hj⟩ := dvd_iff_exists_getElem_divisorsList hn |>.mp h!
  simp only [← hj, getElem_divisorsList_lt_iff, Order.lt_add_one_iff] at lt_d d_lt
  absurd lt_d
  simpa

lemma exists_getElem_divisorsList_α (h_length : i < (divisorsList n).length)
    (lt_d : (divisorsList n)[i] < d) (d_dvd : d ∣ n)
    (hd' : ∀ d', (divisorsList n)[i] < d' → d' < d → ¬d' ∣ n) :
    ∃ _ : i + 1 < (divisorsList n).length, (divisorsList n)[i + 1] = d := by
  have hn := ne_zero_of_lt_length_divisorsList h_length
  have ⟨j, j_lt, hj⟩ := dvd_iff_exists_getElem_divisorsList hn |>.mp d_dvd
  have j_eq_i_succ : j = i + 1 := by
    apply eq_of_le_of_ge
    · by_contra! h!
      absurd show (divisorsList n)[i + 1] ∣ n by simp
      apply hd'
      · simp
      · simpa [← hj]
    · rw [Nat.add_one_le_iff]
      simp only [← hj, getElem_divisorsList_lt_iff] at lt_d
      exact lt_d
  use (by rw [← j_eq_i_succ]; exact j_lt)
  simp only [← j_eq_i_succ]
  exact hj

lemma sort_divisors_ge_eq (h : n ≠ 0) : n.divisors.sort (· ≥ ·) = (divisorsList n).map (n / ·) := by
  apply List.SortedGT.eq_of_mem_iff
  · apply Finset.sortedGT_sort
  · rw [List.sortedGT_iff_getElem_gt_getElem_of_lt]
    intro i j hi hj hij
    repeat rw [List.getElem_map]
    rw [Nat.div_lt_div_left h (by simp) (by simp)]
    simpa
  · intro d
    unfold divisorsList
    suffices d ∣ n ∧ ¬n = 0 ↔ ∃ a, (a ∣ n ∧ ¬n = 0) ∧ n / a = d by simpa
    constructor
    · intro ⟨hd, hn⟩
      use n / d
      exact ⟨⟨Nat.div_dvd_of_dvd hd, hn⟩, Nat.div_div_self hd hn⟩
    · intro ⟨d', ⟨hd', hn⟩, hdd'⟩
      rw [← hdd']
      exact ⟨Nat.div_dvd_of_dvd hd', hn⟩

lemma cons_sort_properDivisors_ge_eq (h : n ≠ 0) :
    n :: n.properDivisors.sort (· ≥ ·) = (divisorsList n).map (n / ·) := by
  rw [← Finset.sort_cons (· ≥ ·)
    (fun d hd ↦ Nat.divisor_le <| Nat.properDivisors_subset_divisors hd) (by simp),
    Nat.cons_self_properDivisors h]
  exact sort_divisors_ge_eq h

lemma le_card_properDivisors_iff (h : n ≠ 0) :
    l ≤ n.properDivisors.card ↔ l < (divisorsList n).length := by
  have h' := congr_arg List.length <| cons_sort_properDivisors_ge_eq h
  simp at h'
  simp [← h']

/-- `α n` is the sum of the reciprocals of `(divisorsList n)[i]` for `i ∈ {1, 2, 3}`. -/
lemma α_eq_add_add (h_length : 3 < (divisorsList n).length) :
    α n = n / (divisorsList n)[1] + n / (divisorsList n)[2] + n / (divisorsList n)[3] := by
  have h_card : 3 ≤ n.properDivisors.card :=
    le_card_properDivisors_iff (ne_zero_of_lt_length_divisorsList h_length) |>.mpr h_length
  have hn : n ≠ 0 := by rw [← zero_lt_length_divisorsList_iff]; exact lt_trans (by simp) h_length
  unfold α
  repeat
    rw [List.take_succ_eq_append_getElem <|
        by rw [Finset.length_sort]; exact lt_of_lt_of_le (by simp) h_card,
      List.sum_append, List.sum_singleton, ← List.getElem_cons_succ n _ _
        (by rw [List.length_cons, Finset.length_sort, Nat.add_one_lt_add_one_iff];
              exact le_trans (by simp) h_card)]
    simp only [cons_sort_properDivisors_ge_eq hn, List.getElem_map]
    first | rw [Nat.add_left_inj] | rw [Nat.add_eq_right]
  simp

/-! ### Every number of the form is magic -/

variable {a r : ℕ}

/-- Auxillary lemma in the proof that every number of the form is `Magic`. -/
lemma d₁_d₂_eq_of_is_of_form (a : ℕ) (hr : r.Coprime 10) :
    ∃ _ : 2 < (divisorsList (12 ^ a * 6 * r)).length,
    (divisorsList (12 ^ a * 6 * r))[1] = 2 ∧ (divisorsList (12 ^ a * 6 * r))[2] = 3 := by
  have ⟨h_length₀, hd₀⟩ :
      ∃ _ : 0 < (divisorsList (12 ^ a * 6 * r)).length, (divisorsList (12 ^ a * 6 * r))[0] = 1 := by
    rw [exists_getElem_divisorsList_zero_iff]
    suffices r ≠ 0 by simpa
    by_contra h!
    simp [h!] at hr
  have ⟨h_length₁, hd₁⟩ :
      ∃ _ : 1 < (divisorsList (12 ^ a * 6 * r)).length, (divisorsList (12 ^ a * 6 * r))[1] = 2 := by
    apply exists_getElem_divisorsList_α h_length₀ (by simp) (by use 12 ^ a * 3 * r; ring)
    intro d' hd'_gt hd'_lt
    simp at hd'_gt
    interval_cases d'
  have ⟨h_length₂, hd₂⟩ :
      ∃ _ : 2 < (divisorsList (12 ^ a * 6 * r)).length, (divisorsList (12 ^ a * 6 * r))[2] = 3 := by
    apply exists_getElem_divisorsList_α h_length₁ (by simp [hd₁]) (by use 12 ^ a * 2 * r; ring)
    intro d' hd'_gt hd'_lt
    simp [hd₁] at hd'_gt
    interval_cases d'
  exact ⟨h_length₂, hd₁, hd₂⟩

/-- Base step in the proof that every number of the form is `Magic`. -/
lemma magic_of_is_of_form_ind_zero (hr : r.Coprime 10) : Magic (12 ^ 0 * 6 * r) := by
  have ⟨h_length₂, hd₁, hd₂⟩ := d₁_d₂_eq_of_is_of_form 0 hr
  simp only [pow_zero, one_mul] at ⊢ h_length₂ hd₁ hd₂
  have ⟨h_length₃, hd₃⟩ :
      ∃ _ : 3 < (divisorsList (6 * r)).length, (divisorsList (6 * r))[3] = 6 := by
    apply exists_getElem_divisorsList_α h_length₂ (by simp [hd₂]) (by simp)
    intro d' lt_d' d'_lt
    rw [hd₂] at lt_d'
    rw [Nat.coprime_comm, show 10 = 2 * 5 by rfl, Nat.coprime_mul_iff_left] at hr
    interval_cases d'
    · change ¬2 * 2 ∣ 2 * 3 * r
      rw [mul_assoc, mul_dvd_mul_iff_left (by simp), Nat.Coprime.dvd_mul_left (by decide)]
      rw [← Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      exact hr.left
    · have := hr.right
      simpa [Nat.Prime.dvd_mul Nat.prime_five, ← Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
  apply magic_of_eq_α
  · rw [le_card_properDivisors_iff <| ne_zero_of_lt_length_divisorsList h_length₂]
    exact h_length₃
  · rw [α_eq_add_add h_length₃]
    let k := 6 * r
    refold_let k
    qify [getElem_divisorsList_dvd]
    unfold k
    push_cast
    rw [hd₁, hd₂, hd₃]
    field

/-- Induction step in the proof that every number of the form is `Magic`. -/
lemma magic_of_is_of_form_ind_succ (hr : r.Coprime 10)
    (h_ind : ∀ {r : ℕ}, r.Coprime 10 → Magic (12 ^ a * 6 * r)) :
    Magic (12 ^ (a + 1) * 6 * r) := by
  have ⟨h_length₂, hd₁, hd₂⟩ := d₁_d₂_eq_of_is_of_form (a + 1) hr
  simp only [show 12 ^ (a + 1) * 6 * r = 12 ^ a * 72 * r by ring] at ⊢ h_length₂ hd₁ hd₂
  have ⟨h_length₃, hd₃⟩ : ∃ _ : 3 < (divisorsList (12 ^ a * 72 * r)).length,
      (divisorsList (12 ^ a * 72 * r))[3] = 4 := by
    apply exists_getElem_divisorsList_α h_length₂ (by simp [hd₂]) (by use 12 ^ a * 18 * r; ring)
    intro d' hd'_gt hd'_lt
    simp [hd₂] at hd'_gt
    interval_cases d'
  rw [magic_iff]
  refine ⟨by rw [le_card_properDivisors_iff <| ne_zero_of_lt_length_divisorsList h_length₂];
              exact h_length₃, ?_⟩
  have α_eq : α (12 ^ a * 72 * r) = 12 ^ a * 6 * (13 * r) := by
    rw [α_eq_add_add h_length₃]
    let k := 12 ^ a * 72 * r
    refold_let k
    qify [getElem_divisorsList_dvd]
    unfold k
    push_cast
    rw [hd₁, hd₂, hd₃]
    field
  rw [α_eq]
  apply h_ind
  rw [Nat.coprime_mul_iff_left]
  exact ⟨by decide, hr⟩

/-- If `n` is of the form, then it is `Magic`. -/
lemma magic_of_is_of_form (hr : r.Coprime 10) : Magic (12 ^ a * 6 * r) := by
  induction a generalizing r with
  | zero =>
    exact magic_of_is_of_form_ind_zero hr
  | succ a h_ind =>
    exact magic_of_is_of_form_ind_succ hr h_ind

/-! ### Every magic number is of the form -/

/-- An auxillary lemma for `α_lt_n_of_d₁` and `α_lt_n_of_d₁_d₂`. -/
lemma α_lt_n_aux {b₁ b₂ b₃ : ℕ} (h_length : 3 < (divisorsList n).length)
    (b₁_le : b₁ ≤ (divisorsList n)[1]) (b₂_le : b₂ ≤ (divisorsList n)[2])
    (b₃_lt : b₃ < (divisorsList n)[3])
    (h : 0 < b₁ ∧ 0 < b₂ ∧ 0 < b₃ ∧ b₂ * b₃ + b₁ * b₃ + b₁ * b₂ ≤ b₁ * b₂ * b₃) : α n < n := by
  obtain ⟨lt_b₁, lt_b₂, lt_b₃, h_sum⟩ := h
  qify at h_sum
  rw [← div_le_div_iff_of_pos_right <| show 0 < (b₁ : ℚ) by exact_mod_cast lt_b₁,
      ← div_le_div_iff_of_pos_right <| show 0 < (b₂ : ℚ) by exact_mod_cast lt_b₂,
      ← div_le_div_iff_of_pos_right <| show 0 < (b₃ : ℚ) by exact_mod_cast lt_b₃] at h_sum
  have h_sum' : (b₁ : ℚ)⁻¹ + (b₂ : ℚ)⁻¹ + (b₃ : ℚ)⁻¹ ≤ 1 := by
    apply le_of_eq_of_le (by field) <| le_of_le_of_eq h_sum (by field)
  rw [α_eq_add_add h_length]
  qify [getElem_divisorsList_dvd]
  repeat conv in (n : ℚ) / _ => rw [div_eq_mul_inv]
  rw [← left_distrib, ← left_distrib]
  conv => right; rw [← mul_one (n : ℚ)]
  apply mul_lt_mul_of_pos_left ?_
    (by norm_cast; rw [← Nat.ne_zero_iff_zero_lt, ← zero_lt_length_divisorsList_iff];
        exact lt_trans (by simp) h_length)
  refine lt_of_lt_of_le ?_ h_sum'
  refine add_lt_add_of_le_of_lt (add_le_add ?_ ?_) ?_
  · rw [inv_le_inv₀ (by simp) (by exact_mod_cast lt_b₁)]
    exact_mod_cast b₁_le
  · rw [inv_le_inv₀ (by simp) (by exact_mod_cast lt_b₂)]
    exact_mod_cast b₂_le
  · rw [inv_lt_inv₀ (by simp) (by exact_mod_cast lt_b₃)]
    exact_mod_cast b₃_lt

lemma α_lt_n_of_d₁ (h_length : 3 < (divisorsList n).length) (hd₁ : 3 ≤ (divisorsList n)[1]) :
    α n < n := by
  have hd₂ : 3 ≤ (divisorsList n)[2] := le_of_lt <| lt_of_le_of_lt hd₁ <| by simp
  have hd₃ : 3 < (divisorsList n)[3] := lt_of_le_of_lt hd₂ <| by simp
  exact α_lt_n_aux h_length hd₁ hd₂ hd₃ <| by simp

lemma α_lt_n_of_d₁_d₂ (h_length : 3 < (divisorsList n).length) (hd₁ : (divisorsList n)[1] = 2)
    (hd₂ : 4 ≤ (divisorsList n)[2]) : α n < n := by
  have hd₃ : 4 < (divisorsList n)[3] := lt_of_le_of_lt hd₂ <| by simp
  exact α_lt_n_aux h_length hd₁.symm.le hd₂ hd₃ <| by simp

lemma not_two_dvd_α_of_d₁ (h_length : 3 < (divisorsList n).length)
    (hd₁ : 3 ≤ (divisorsList n)[1]) : ¬2 ∣ α n := by
  have n_div_mod_two {i : ℕ} {hi : i < (divisorsList n).length} :
      n / (divisorsList n)[i] % 2 = 1 := by
    rw [← Nat.mod_two_not_eq_zero, ← Nat.dvd_iff_mod_eq_zero, Nat.dvd_div_iff_mul_dvd (by simp)]
    apply not_imp_not.mpr <| dvd_of_mul_left_dvd
    exact not_dvd_of_between_divisorsList (by simp) (lt_of_lt_of_le (by simp) hd₁)
  rw [Nat.dvd_iff_mod_eq_zero, α_eq_add_add h_length, Nat.add_mod,
    Nat.add_mod <| n / (divisorsList n)[1]]
  simp [n_div_mod_two]

lemma not_three_dvd_α_of_d₁_d₂ (h_length : 3 < (divisorsList n).length)
    (hd₁ : (divisorsList n)[1] = 2) (hd₂ : (divisorsList n)[2] = 4) : ¬3 ∣ α n := by
  have h : n / 2 + n / 4 = 3 * (n / 4) := by
    rw [← hd₁, ← hd₂]
    qify [getElem_divisorsList_dvd]
    rw [hd₁, hd₂]
    field
  rw [α_eq_add_add h_length, hd₁, hd₂, h, ← Nat.dvd_add_iff_right (by simp),
    Nat.dvd_div_iff_mul_dvd (by simp)]
  apply not_imp_not.mpr <| dvd_of_mul_left_dvd
  exact not_dvd_of_between_divisorsList (lt_of_eq_of_lt hd₁ (by simp))
    (lt_of_lt_of_eq (by simp) hd₂.symm)

lemma not_three_dvd_α_of_d₁_d₂_d₃ (h_length : 3 < (divisorsList n).length)
    (hd₁ : (divisorsList n)[1] = 2) (hd₂_gt : 4 < (divisorsList n)[2])
    (hd₃_even : Even (divisorsList n)[3]) : ¬3 ∣ α n := by
  have d₃_eq : (divisorsList n)[3] = 2 * (divisorsList n)[2] := by
    have ⟨l, hl⟩ := hd₃_even
    rw [ ← two_mul] at hl
    rw [hl, Nat.mul_right_inj (show 2 ≠ 0 by simp)]
    by_contra! h!
    rw [ne_iff_lt_or_gt] at h!
    absurd dvd_of_mul_left_dvd <| show 2 * l ∣ n by rw [← hl]; simp
    have hl' : 2 < l := Nat.mul_lt_mul_left (show 0 < 2 by simp) |>.mp
      <| lt_trans hd₂_gt <| lt_of_lt_of_eq (by simp) hl
    obtain h! | h! := h!
    · refine not_dvd_of_between_divisorsList ?_ h!
      exact lt_of_eq_of_lt hd₁ hl'
    · refine not_dvd_of_between_divisorsList h! (show l < (divisorsList n)[3] from ?_)
      rw [← one_mul l, hl, Nat.mul_lt_mul_right <| lt_trans (by simp) hl']
      simp
  have α_eq : α n = ((divisorsList n)[2] + 3) * (n / (divisorsList n)[3]) := by
    rw [α_eq_add_add h_length]
    qify [getElem_divisorsList_dvd]
    rw [hd₁, d₃_eq, Nat.cast_mul]
    field
  rw [α_eq, Nat.Prime.dvd_mul Nat.prime_three, not_or]
  have not_three_dvd_n : ¬3 ∣ n := by
    apply not_dvd_of_between_divisorsList ?_ (show 3 < (divisorsList n)[2] from ?_)
    · exact lt_of_eq_of_lt hd₁ (by simp)
    · exact lt_trans (by simp) hd₂_gt
  constructor
  · rw [Nat.dvd_add_self_right]
    apply not_imp_not.mpr <| flip dvd_trans (show (divisorsList n)[2] ∣ n by simp)
    exact not_three_dvd_n
  · rw [Nat.dvd_div_iff_mul_dvd (by simp)]
    apply not_imp_not.mpr <| dvd_of_mul_left_dvd
    exact not_three_dvd_n

lemma not_two_dvd_α_of_d₁_d₂_d₃ (h_length : 3 < (divisorsList n).length)
    (hd₁ : (divisorsList n)[1] = 2) (hd₂_gt : 4 < (divisorsList n)[2])
    (hd₃_odd : Odd (divisorsList n)[3]) : ¬2 ∣ α n := by
  have n_div_d₁ : n / (divisorsList n)[1] % 2 = 1 := by
    rw [← Nat.mod_two_ne_zero, ne_eq, ← Nat.dvd_iff_mod_eq_zero, Nat.dvd_div_iff_mul_dvd (by simp),
      hd₁]
    exact not_dvd_of_between_divisorsList (by rw [hd₁]; simp) hd₂_gt
  have n_div_d₂ : n / (divisorsList n)[2] % 2 = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero, Nat.dvd_div_iff_mul_dvd (by simp)]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (by simp) (by rw [← hd₁]; simp)
    rw [Nat.coprime_two_right, ← Nat.not_even_iff_odd, Nat.even_iff, ← Nat.dvd_iff_mod_eq_zero]
    by_contra ⟨l, hl⟩
    absurd dvd_of_mul_left_dvd <| show 2 * l ∣ n by rw [← hl]; simp
    have hl' : 2 < l := Nat.mul_lt_mul_left (show 0 < 2 by simp) |>.mp <| lt_of_lt_of_eq hd₂_gt hl
    apply not_dvd_of_between_divisorsList (by rwa [hd₁]) (show l < (divisorsList n)[2] from ?_)
    rw [← one_mul l, hl]
    exact Nat.mul_lt_mul_of_pos_right (by simp) <| lt_trans (by simp) hl'
  have n_div_d₃ : n / (divisorsList n)[3] % 2 = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero, Nat.dvd_div_iff_mul_dvd (by simp)]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (by simp) (by rw [← hd₁]; simp)
    rwa [Nat.coprime_two_right]
  rw [Nat.dvd_iff_mod_eq_zero, α_eq_add_add h_length, Nat.add_mod,
    Nat.add_mod <| n / (divisorsList n)[1], n_div_d₁, n_div_d₂, n_div_d₃]
  simp

/-- If `n` has at least three divisors greater than `1`, we either have `(divisorsList n)[1] = 2`
and `(divisorsList n)[2] = 3`, or we have `α n < n` and either `¬2 ∣ α n` or `¬3 ∣ α n`. -/
lemma d₁_d₂_eq_or_not_dvd_α_and_α_lt (h_length : 3 < (divisorsList n).length) :
    (divisorsList n)[1] = 2 ∧ (divisorsList n)[2] = 3 ∨
    (¬2 ∣ α n ∨ ¬3 ∣ α n) ∧ α n < n := by
  have two_le_d₁ : 2 ≤ (divisorsList n)[1] := by
    rw [Nat.add_one_le_iff]
    apply lt_of_eq_of_lt (show 1 = (divisorsList n)[0] by simp)
    simp [-getElem_divisorsList_zero]
  obtain two_lt_d₁ | d₁_eq_two := lt_or_eq_of_le two_le_d₁
  · exact .inr
      ⟨.inl <| not_two_dvd_α_of_d₁ h_length two_lt_d₁, α_lt_n_of_d₁ h_length two_lt_d₁⟩
  · rw [eq_comm] at d₁_eq_two
    simp only [d₁_eq_two, true_and]
    have three_le_d₂ : 3 ≤ (divisorsList n)[2] := by
      rw [Nat.add_one_le_iff]
      conv => left; rw [← d₁_eq_two]
      simp
    obtain d₂_eq_three | three_lt_d₂ := eq_or_lt_of_le three_le_d₂
    · exact .inl d₂_eq_three.symm
    · rw [← Nat.add_one_le_iff] at three_lt_d₂
      refine .inr ⟨?_, α_lt_n_of_d₁_d₂ h_length d₁_eq_two three_lt_d₂⟩
      obtain four_eq_d₂ | four_lt_d₂ := eq_or_lt_of_le three_lt_d₂
      · exact .inr <| not_three_dvd_α_of_d₁_d₂ h_length d₁_eq_two four_eq_d₂.symm
      · obtain even_d₃ | odd_d₃ := Nat.even_or_odd (divisorsList n)[3]
        · exact .inr <| not_three_dvd_α_of_d₁_d₂_d₃ h_length d₁_eq_two four_lt_d₂ even_d₃
        · exact .inl <| not_two_dvd_α_of_d₁_d₂_d₃ h_length d₁_eq_two four_lt_d₂ odd_d₃

/-- If `n` is Magic, `n` has at least three divisors greater than `1`. Furthermore, we can
inductively follow `(divisorsList n)[1] = 2` and `(divisorsList n)[2] = 3`. -/
lemma d₁_d₂_eq_of_magic (h_magic : Magic n) :
    ∃ _ : 3 < (divisorsList n).length, (divisorsList n)[1] = 2 ∧ (divisorsList n)[2] = 3 := by
  induction n using Nat.strongRec
  case ind n h_ind =>
  rw [magic_iff] at h_magic
  have h_length : 3 < (divisorsList n).length := by
    rw [← le_card_properDivisors_iff <| by by_contra h!; simp [h!] at h_magic]
    exact h_magic.left
  use h_length
  obtain d₁_d₂_eq | ⟨not_two_div_α | not_three_div_α, α_lt_n⟩ :=
      d₁_d₂_eq_or_not_dvd_α_and_α_lt h_length
  · exact d₁_d₂_eq
  · absurd not_two_div_α
    simp [← h_ind (α n) α_lt_n h_magic.right |>.choose_spec.left]
  · absurd not_three_div_α
    simp [← h_ind (α n) α_lt_n h_magic.right |>.choose_spec.right]

/-- An auxillary lemma for `is_of_form_of_d₃_eq_four` and `false_of_d₃_eq_five`. -/
lemma is_of_form_of_d₃_aux {c₁ c₂ : ℕ}
    (h : ¬2 ∣ c₁ ∧ c₁ ≠ 0 ∧ 2 ∣ c₂ ∧ c₂ ≠ 0)
    (h_n_α_n : c₁ * n = c₂ * α n) (h_length : 3 < (divisorsList n).length) (h_magic_α : Magic (α n))
    (h_ind : ∀ m < n.factorization 2, ∀ {n : ℕ}, Magic n → n.factorization 2 = m →
      ∃ a r, r.Coprime 10 ∧ n = 12 ^ a * 6 * r) : ∃ a r, r.Coprime 10 ∧ α n = 12 ^ a * 6 * r := by
  obtain ⟨not_two_dvd_c₁, c₁_ne_zero, two_dvd_c₂, c₂_ne_zero⟩ := h
  have fac_c₁_eq_zero : c₁.factorization 2 = 0 := by
    rw [Nat.factorization_eq_zero_iff]; right; left; exact not_two_dvd_c₁
  have zero_lt_fac_c₂ : 0 < c₂.factorization 2 := by
    rw [← Nat.ne_zero_iff_zero_lt, ne_eq, Nat.factorization_eq_zero_iff]
    push_neg
    exact ⟨Nat.prime_two, two_dvd_c₂, c₂_ne_zero⟩
  apply h_ind ((α n).factorization 2)
  · apply lt_of_lt_of_le <| Nat.lt_add_of_pos_left zero_lt_fac_c₂
    rw [← Finsupp.add_apply, ← Nat.factorization_mul c₂_ne_zero (ne_zero_of_magic h_magic_α),
      ← h_n_α_n, Nat.factorization_mul c₁_ne_zero (ne_zero_of_lt_length_divisorsList h_length)]
    simpa
  · exact h_magic_α
  · rfl

lemma prime_thirteen : Nat.Prime 13 := by decide

/-- If `n` is `Magic`, `(divisorsList n)[1] = 2`, `(divisorsList n)[2] = 3` and
`(divisorsList n)[3] = 4`, then we can follow that it is of the form from `α n` being of the form.
-/
lemma is_of_form_of_d₃_eq_four (h_magic_α : Magic (α n))
    {h_length : 3 < (divisorsList n).length} (hd₁ : (divisorsList n)[1] = 2)
    (hd₂ : (divisorsList n)[2] = 3) (hd₃ : (divisorsList n)[3] = 4)
    (h_ind : ∀ m < n.factorization 2, ∀ {n : ℕ}, Magic n → n.factorization 2 = m →
      ∃ a r, r.Coprime 10 ∧ n = 12 ^ a * 6 * r) : ∃ a r, r.Coprime 10 ∧ n = 12 ^ a * 6 * r := by
  have h_n_α_n : 13 * n = 12 * α n := by
    rw [α_eq_add_add h_length]
    qify [getElem_divisorsList_dvd]
    rw [hd₁, hd₂, hd₃]
    field
  have ⟨a', r', hr', α_n_eq⟩ :=
    is_of_form_of_d₃_aux (by simp) h_n_α_n h_length h_magic_α h_ind
  have thirteen_dvd_r' : 13 ∣ r' := by
    have h : 13 ∣ 12 * α n := ⟨n, h_n_α_n.symm⟩
    conv at h =>
      simp [Nat.Prime.dvd_mul prime_thirteen, α_n_eq, Nat.Prime.dvd_mul prime_thirteen,
        Nat.Prime.dvd_mul prime_thirteen]
      rw [or_iff_not_imp_left]
    apply h
    apply not_imp_not.mpr <| Nat.Prime.dvd_of_dvd_pow prime_thirteen
    simp
  use a' + 1, r' / 13
  constructor
  · exact Nat.Coprime.coprime_div_left hr' thirteen_dvd_r'
  · rw [← Nat.mul_right_inj (show 13 ≠ 0 by simp), h_n_α_n, α_n_eq]
    qify [show 13 ∣ (r' : ℤ) by apply Nat.cast_dvd_cast; exact thirteen_dvd_r']
    field

/-- If `n` is `Magic`, `(divisorsList n)[1] = 2`, `(divisorsList n)[2] = 3` and
`(divisorsList n)[3] = 5`, then we can follow a contradiction from `α n` being of the form. -/
lemma false_of_d₃_eq_five (h_magic_α : Magic (α n)) {h_length : 3 < (divisorsList n).length}
    (hd₁ : (divisorsList n)[1] = 2) (hd₂ : (divisorsList n)[2] = 3) (hd₃ : (divisorsList n)[3] = 5)
    (h_ind : ∀ m < n.factorization 2, ∀ {n : ℕ}, Magic n → n.factorization 2 = m →
      ∃ a r, r.Coprime 10 ∧ n = 12 ^ a * 6 * r) : False := by
  have h_n_α_n : 31 * n = 30 * α n := by
    rw [α_eq_add_add h_length]
    qify [getElem_divisorsList_dvd]
    rw [hd₁, hd₂, hd₃]
    field
  have ⟨a', r', hr', α_n_eq⟩ :=
    is_of_form_of_d₃_aux (by simp) h_n_α_n h_length h_magic_α h_ind
  rw [← Nat.mul_right_inj (show 30 ≠ 0 by simp), ← h_n_α_n] at α_n_eq
  absurd show ¬4 ∣ n from not_dvd_of_between_divisorsList (lt_of_eq_of_lt hd₂ (by simp))
    (lt_of_lt_of_eq (by simp) hd₃.symm)
  rw [← Nat.Coprime.dvd_mul_left (show Nat.Coprime 4 31 by decide), α_n_eq]
  use 12 ^ a' * 45 * r'
  ring

/-- If `n` is `Magic`, `(divisorsList n)[2] = 3` and `(divisorsList n)[3] = 6`, then we can directly
follow that is is of the form. -/
lemma is_of_form_of_d₃_eq_six {h_length : 3 < (divisorsList n).length}
    (hd₂ : (divisorsList n)[2] = 3) (hd₃ : (divisorsList n)[3] = 6) :
    ∃ a r, r.Coprime 10 ∧ n = 12 ^ a * 6 * r := by
  have six_dvd_n : 6 ∣ n := by simp [← hd₃]
  use 0, n / 6
  rw [Nat.coprime_comm, show 10 = 2 * 5 by rfl, Nat.coprime_mul_iff_left]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two, Nat.dvd_div_iff_mul_dvd six_dvd_n]
    change ¬4 * 3 ∣ n
    apply not_imp_not.mpr <| dvd_of_mul_right_dvd
    exact not_dvd_of_between_divisorsList (lt_of_eq_of_lt hd₂ (by simp))
      (lt_of_lt_of_eq (by simp) hd₃.symm)
  · rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_five, Nat.dvd_div_iff_mul_dvd six_dvd_n]
    apply not_imp_not.mpr <| dvd_of_mul_left_dvd
    exact not_dvd_of_between_divisorsList (lt_of_eq_of_lt hd₂ (by simp))
      (lt_of_lt_of_eq (by simp) hd₃.symm)
  · simp [Nat.mul_div_cancel' six_dvd_n]

/-- If `n` is `Magic`, then it is of the form. -/
lemma is_of_form_of_magic (h_magic : Magic n) : ∃ a r, r.Coprime 10 ∧ n = 12 ^ a * 6 * r := by
  induction hk : n.factorization 2 using Nat.strongRec generalizing n
  case ind k h_ind =>
  simp only [← hk] at h_ind
  have ⟨h_length, hd₁, hd₂⟩ := d₁_d₂_eq_of_magic h_magic
  rw [magic_iff] at h_magic
  have three_lt_d₃ : 3 < (divisorsList n)[3] := lt_of_eq_of_lt hd₂.symm (by simp)
  have d₃_le_six : (divisorsList n)[3] ≤ 6 := by
    by_contra! h!
    absurd show 2 * 3 ∣ n from
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) (by simp [← hd₁]) (by simp [← hd₂])
    exact not_dvd_of_between_divisorsList (lt_of_eq_of_lt hd₂ (by simp)) h!
  interval_cases hd₃_eq : (divisorsList n)[3]
  · exact is_of_form_of_d₃_eq_four h_magic.right hd₁ hd₂ hd₃_eq h_ind
  · exfalso
    exact false_of_d₃_eq_five h_magic.right hd₁ hd₂ hd₃_eq h_ind
  · exact is_of_form_of_d₃_eq_six hd₂ hd₃_eq

/-! ### Result -/

/-- The set of magic numbers. -/
def solutionSet : Set ℕ := {n | ∃ a r : ℕ, r.Coprime 10 ∧ n = 12 ^ a * 6 * r}

/-- `solutionSet` is in fact the set of all `Magic` numbers. -/
theorem result : ∀ n, n ∈ solutionSet ↔ Magic n := by
  intro n
  constructor
  · intro ⟨a, r, hr, hn⟩
    rw [hn]
    exact magic_of_is_of_form hr
  · exact is_of_form_of_magic

end Imo2025Q4
