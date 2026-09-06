/-
Copyright (c) 2026 Haoyu Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoyu Chen
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Kővári–Sós–Turán theorem

T. Kővári, V. T. Sós and P. Turán, *On a problem of K. Zarankiewicz*,
Colloq. Math. **3** (1954), 50–57.

If a bipartite graph with parts `A` (of size `m`) and `B` (of size `n`) contains no
complete bipartite subgraph `K_{s,t}` (with the `s`-side inside `A` and the `t`-side
inside `B`), then its number of edges `e` satisfies

`e ≤ (s - 1) * n + (t - 1) ^ (1/s) * m * n ^ (1 - 1/s)`.

Equivalently, and avoiding real exponents entirely,

`(e - (s - 1) * n) ^ s ≤ (t - 1) * m ^ s * n ^ (s - 1)`,

which is the form `KovariSosTuran.kovari_sos_turan` proved below (truncated subtraction
in `ℕ` makes the statement total).  This is the theorem that gives the classical bound
`ex(n; K_{s,t}) = O(n ^ (2 - 1/s))` for the Zarankiewicz problem.

Mathlib defines the Zarankiewicz function (`SimpleGraph.zarankiewicz`) but does not
contain this bound.

## Proof

Double count the "stars" `(S, b)` with `S ⊆ A`, `|S| = s`, and `b` adjacent to all of `S`.
Counting by `b` gives `∑_{b ∈ B} C(d b, s)`; counting by `S` and using `K_{s,t}`-freeness
gives at most `(t-1) * C(m, s)`.  The elementary inequalities
`(d + 1 - s)^s ≤ d.descFactorial s = s! * C(d, s)` and `m.descFactorial s ≤ m^s`, together
with the power-mean inequality `(∑ x)^s ≤ n^(s-1) * ∑ x^s`, turn this into the stated bound.

## Main results

* `KovariSosTuran.HasKst` : the bipartite graph contains a `K_{s,t}`.
* `KovariSosTuran.sum_choose_le` : the double-counting core,
  `∑_{b ∈ B} C(d b, s) ≤ (t - 1) * C(m, s)`.
* `KovariSosTuran.kovari_sos_turan` : **Kővári–Sós–Turán**, in `ℕ`.
* `KovariSosTuran.kovari_sos_turan_real` : the classical form with real exponents.
-/

@[expose] public section

open Finset

namespace KovariSosTuran

variable {α β : Type*} [DecidableEq α]
  (A : Finset α) (B : Finset β) (r : α → β → Prop) [∀ a b, Decidable (r a b)]

/-- The neighbourhood of `b : β` inside the part `A`. -/
def nbhd (b : β) : Finset α := A.filter fun a => r a b

/-- The degree of `b : β`, i.e. the number of its neighbours in `A`. -/
def deg (b : β) : ℕ := (nbhd A r b).card

/-- The number of edges of the bipartite graph between `A` and `B`. -/
def numEdges : ℕ := ∑ b ∈ B, deg A r b

/-- The bipartite graph given by `r` contains a complete bipartite subgraph `K_{s,t}`
with its `s`-side inside `A` and its `t`-side inside `B`. -/
def HasKst (s t : ℕ) : Prop :=
  ∃ S ⊆ A, ∃ T ⊆ B, S.card = s ∧ T.card = t ∧ ∀ a ∈ S, ∀ b ∈ T, r a b

variable {A B r} {s t : ℕ}

omit [DecidableEq α] in
lemma nbhd_subset (b : β) : nbhd A r b ⊆ A := Finset.filter_subset _ _

omit [DecidableEq α] in
lemma mem_nbhd {a : α} {b : β} : a ∈ nbhd A r b ↔ a ∈ A ∧ r a b := Finset.mem_filter

/-- If the graph is `K_{s,t}`-free then every `s`-subset of `A` has at most `t - 1`
common neighbours in `B`. -/
lemma card_common_le (h : ¬ HasKst A B r s t) (ht : 1 ≤ t)
    {S : Finset α} (hSA : S ⊆ A) (hS : S.card = s) :
    (B.filter fun b => S ⊆ nbhd A r b).card ≤ t - 1 := by
  by_contra hcon
  have htc : t ≤ (B.filter fun b => S ⊆ nbhd A r b).card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq htc
  refine h ⟨S, hSA, T, fun b hb => (Finset.mem_filter.mp (hT hb)).1, hS, hTcard, ?_⟩
  intro a ha b hb
  exact (mem_nbhd.mp ((Finset.mem_filter.mp (hT hb)).2 ha)).2

omit [DecidableEq α] in
/-- **The double-counting core of Kővári–Sós–Turán.**
If the bipartite graph is `K_{s,t}`-free then
`∑_{b ∈ B} C(deg b, s) ≤ (t - 1) * C(|A|, s)`. -/
theorem sum_choose_le (h : ¬ HasKst A B r s t) (ht : 1 ≤ t) :
    ∑ b ∈ B, (deg A r b).choose s ≤ (t - 1) * A.card.choose s := by
  classical
  have key : ∀ b ∈ B, (deg A r b).choose s
      = ((A.powersetCard s).filter fun S => S ⊆ nbhd A r b).card := by
    intro b _
    rw [deg, ← Finset.card_powersetCard]
    congr 1
    ext S
    simp only [Finset.mem_powersetCard, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1.trans (nbhd_subset (A := A) (r := r) b), h2⟩, h1⟩
    · rintro ⟨⟨-, h2⟩, h1⟩
      exact ⟨h1, h2⟩
  calc ∑ b ∈ B, (deg A r b).choose s
      = ∑ b ∈ B, ((A.powersetCard s).filter fun S => S ⊆ nbhd A r b).card :=
        Finset.sum_congr rfl key
    _ = ∑ b ∈ B, ∑ S ∈ A.powersetCard s, if S ⊆ nbhd A r b then 1 else 0 :=
        Finset.sum_congr rfl fun b _ => Finset.card_filter _ _
    _ = ∑ S ∈ A.powersetCard s, ∑ b ∈ B, if S ⊆ nbhd A r b then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ S ∈ A.powersetCard s, (B.filter fun b => S ⊆ nbhd A r b).card :=
        Finset.sum_congr rfl fun S _ => (Finset.card_filter _ _).symm
    _ ≤ ∑ _S ∈ A.powersetCard s, (t - 1) := by
        refine Finset.sum_le_sum fun S hS => ?_
        rw [Finset.mem_powersetCard] at hS
        exact card_common_le h ht hS.1 hS.2
    _ = (t - 1) * A.card.choose s := by
        rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul, mul_comm]

/-- The truncated degree `deg b + 1 - s`, whose `s`-th power is dominated by
`s! * C(deg b, s)`. -/
private def trunc (b : β) : ℕ := deg A r b + 1 - s

omit [DecidableEq α] in
private lemma trunc_pow_le (b : β) :
    (trunc (A := A) (r := r) (s := s) b) ^ s ≤ s.factorial * (deg A r b).choose s := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.pow_sub_le_descFactorial _ _

omit [DecidableEq α] in
/-- **The Kővári–Sós–Turán theorem.**

If the bipartite graph between `A` (of size `m`) and `B` (of size `n`) given by `r`
contains no `K_{s,t}`, then its number of edges `e` satisfies
`(e - (s-1) * n) ^ s ≤ (t - 1) * m ^ s * n ^ (s - 1)`.
(The subtraction is truncated subtraction in `ℕ`, so the statement is total.) -/
theorem kovari_sos_turan (hs : 1 ≤ s) (ht : 1 ≤ t) (h : ¬ HasKst A B r s t) :
    (numEdges A B r - (s - 1) * B.card) ^ s
      ≤ (t - 1) * A.card ^ s * B.card ^ (s - 1) := by
  classical
  obtain ⟨p, rfl⟩ : ∃ p, s = p + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  -- Step 1: the truncated degrees sum to at least `e - p * n`.
  have h1 : numEdges A B r - p * B.card ≤
      ∑ b ∈ B, trunc (A := A) (r := r) (s := p + 1) b := by
    have hconst : ∑ _b ∈ B, p = p * B.card := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have : numEdges A B r ≤
        (∑ b ∈ B, trunc (A := A) (r := r) (s := p + 1) b) + p * B.card := by
      rw [← hconst, ← Finset.sum_add_distrib, numEdges]
      refine Finset.sum_le_sum fun b _ => ?_
      simp only [trunc]
      omega
    omega
  -- Step 2: power-mean inequality.
  have h2 : (∑ b ∈ B, trunc (A := A) (r := r) (s := p + 1) b) ^ (p + 1)
      ≤ B.card ^ p * ∑ b ∈ B, (trunc (A := A) (r := r) (s := p + 1) b) ^ (p + 1) :=
    pow_sum_le_card_mul_sum_pow (fun _ _ => Nat.zero_le _) p
  -- Step 3: bound the sum of `(p+1)`-th powers using the double count.
  have h3 : ∑ b ∈ B, (trunc (A := A) (r := r) (s := p + 1) b) ^ (p + 1)
      ≤ (t - 1) * A.card ^ (p + 1) := by
    calc ∑ b ∈ B, (trunc (A := A) (r := r) (s := p + 1) b) ^ (p + 1)
        ≤ ∑ b ∈ B, (p + 1).factorial * (deg A r b).choose (p + 1) :=
          Finset.sum_le_sum fun b _ => trunc_pow_le b
      _ = (p + 1).factorial * ∑ b ∈ B, (deg A r b).choose (p + 1) := by
          rw [Finset.mul_sum]
      _ ≤ (p + 1).factorial * ((t - 1) * A.card.choose (p + 1)) := by
          exact Nat.mul_le_mul_left _ (sum_choose_le h ht)
      _ = (t - 1) * ((p + 1).factorial * A.card.choose (p + 1)) := by ring
      _ = (t - 1) * A.card.descFactorial (p + 1) := by
          rw [Nat.descFactorial_eq_factorial_mul_choose]
      _ ≤ (t - 1) * A.card ^ (p + 1) :=
          Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
  calc (numEdges A B r - p * B.card) ^ (p + 1)
      ≤ (∑ b ∈ B, trunc (A := A) (r := r) (s := p + 1) b) ^ (p + 1) :=
        Nat.pow_le_pow_left h1 _
    _ ≤ B.card ^ p * ∑ b ∈ B, (trunc (A := A) (r := r) (s := p + 1) b) ^ (p + 1) := h2
    _ ≤ B.card ^ p * ((t - 1) * A.card ^ (p + 1)) := Nat.mul_le_mul_left _ h3
    _ = (t - 1) * A.card ^ (p + 1) * B.card ^ p := by ring

omit [DecidableEq α] in
/-- **The Kővári–Sós–Turán theorem, classical form.**

If the bipartite graph between `A` (of size `m`) and `B` (of size `n`) given by `r` is
`K_{s,t}`-free, then its number of edges `e` satisfies

`e ≤ (s - 1) * n + (t - 1) ^ (1/s) * m * n ^ (1 - 1/s)`.

This is the bound that yields `ex(n; K_{s,t}) = O(n ^ (2 - 1/s))` for the Zarankiewicz
problem. -/
theorem kovari_sos_turan_real (hs : 1 ≤ s) (ht : 1 ≤ t) (h : ¬ HasKst A B r s t) :
    (numEdges A B r : ℝ)
      ≤ ((s - 1 : ℕ) : ℝ) * (B.card : ℝ)
        + ((t - 1 : ℕ) : ℝ) ^ ((s : ℝ)⁻¹) * (A.card : ℝ)
            * (B.card : ℝ) ^ (1 - (s : ℝ)⁻¹) := by
  classical
  have hs0 : s ≠ 0 := by omega
  have hsR : (0:ℝ) < (s : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs0
  have hsne : (s : ℝ) ≠ 0 := ne_of_gt hsR
  have hnat := kovari_sos_turan hs ht h
  obtain ⟨e, he⟩ : ∃ e, numEdges A B r = e := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, A.card = m := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, B.card = n := ⟨_, rfl⟩
  rw [he, hm, hn] at hnat ⊢
  have ht0 : (0:ℝ) ≤ ((t - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm0 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hmp : (0:ℝ) ≤ (m : ℝ) ^ s := by positivity
  have hnp : (0:ℝ) ≤ (n : ℝ) ^ (s - 1) := by positivity
  have hu0 : (0:ℝ) ≤ ((e - (s - 1) * n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcast : ((e - (s - 1) * n : ℕ) : ℝ) ^ s
      ≤ ((t - 1 : ℕ) : ℝ) * (m : ℝ) ^ s * (n : ℝ) ^ (s - 1) := by exact_mod_cast hnat
  have hexp : ((s - 1 : ℕ) : ℝ) * (s : ℝ)⁻¹ = 1 - (s : ℝ)⁻¹ := by
    have hcs : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by rw [Nat.cast_sub hs, Nat.cast_one]
    rw [hcs, sub_mul, mul_inv_cancel₀ hsne, one_mul]
  have hmain : ((e - (s - 1) * n : ℕ) : ℝ)
      ≤ ((t - 1 : ℕ) : ℝ) ^ ((s : ℝ)⁻¹) * (m : ℝ) *
          (n : ℝ) ^ (1 - (s : ℝ)⁻¹) := by
    calc ((e - (s - 1) * n : ℕ) : ℝ)
        = (((e - (s - 1) * n : ℕ) : ℝ) ^ s) ^ ((s : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast hu0 hs0).symm
      _ ≤ (((t - 1 : ℕ) : ℝ) * (m : ℝ) ^ s * (n : ℝ) ^ (s - 1)) ^ ((s : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hcast (by positivity)
      _ = ((t - 1 : ℕ) : ℝ) ^ ((s : ℝ)⁻¹) * ((m : ℝ) ^ s) ^ ((s : ℝ)⁻¹)
            * ((n : ℝ) ^ (s - 1)) ^ ((s : ℝ)⁻¹) := by
          rw [Real.mul_rpow (mul_nonneg ht0 hmp) hnp, Real.mul_rpow ht0 hmp]
      _ = ((t - 1 : ℕ) : ℝ) ^ ((s : ℝ)⁻¹) * (m : ℝ) *
          (n : ℝ) ^ (1 - (s : ℝ)⁻¹) := by
          rw [Real.pow_rpow_inv_natCast hm0 hs0,
            ← Real.rpow_natCast_mul hn0 (s - 1) ((s : ℝ)⁻¹), hexp]
  have hfin : (e : ℝ) ≤
      ((s - 1 : ℕ) : ℝ) * (n : ℝ) + ((e - (s - 1) * n : ℕ) : ℝ) := by
    have hle : e ≤ (s - 1) * n + (e - (s - 1) * n) := by omega
    calc (e : ℝ) ≤ (((s - 1) * n + (e - (s - 1) * n) : ℕ) : ℝ) := by exact_mod_cast hle
      _ = ((s - 1 : ℕ) : ℝ) * (n : ℝ) + ((e - (s - 1) * n : ℕ) : ℝ) := by push_cast; ring
  linarith

/-! ### Sanity check: the `K_{s,t}`-freeness hypothesis is satisfiable -/

/-- A one-vertex part cannot contain the `2`-side of a `K_{1,2}`, so the hypothesis of
`kovari_sos_turan` is not vacuous. -/
example : ¬ HasKst (Finset.univ : Finset (Fin 1)) (Finset.univ : Finset (Fin 1))
    (fun _ _ => True) 1 2 := by
  rintro ⟨S, -, T, -, -, hT, -⟩
  have h := Finset.card_le_univ T
  simp [hT] at h

/-! ### Axiom check -/


end KovariSosTuran
