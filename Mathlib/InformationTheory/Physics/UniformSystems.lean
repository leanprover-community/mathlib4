/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.Data.Sym.Card
public import Mathlib.InformationTheory.EntropyNumber.Basic
public import Mathlib.InformationTheory.Entropy.Uniqueness
public import Mathlib.InformationTheory.Entropy.Shannon
public import Mathlib.InformationTheory.Physics.Common



/-!
# Uniform Systems: State Spaces and Entropy

This file establishes the combinatorial equivalence between
occupancy-vector representations and multiset representations for
uniform distributions, and proves that any uniform physical system's
entropy equals `C * shannonEntropy`.

## Main definitions

* `OmegaUD` -- the uniform-distribution state space (occupancy
  vectors summing to M).
* `udStateEquivMultiset` -- the `Equiv` between `OmegaUD` and
  `SymFin`.
* `p_UD`, `p_UD_fin` -- uniform probability distributions.

## Main statements

* `H_physical_system_is_rota_uniform` -- physical entropy of a
  uniform dist equals `C * shannonEntropy`.
* `H_canonical_uniform_eq_C_shannon` -- canonical uniform dist
  entropy equals `C * shannonEntropy`.
* `H_physical_dist_eq_C_shannon_if_uniform_and_equiv` -- general
  uniform physical system entropy theorem.

## Tags

uniform distribution, combinatorics, entropy, statistical mechanics
-/

@[expose] public section

namespace InformationTheory.Physics.UniformSystems

open Multiset NNReal
open InformationTheory
open InformationTheory.Physics.Common

open Fin Real NNReal Nat Multiset Finset

/-! ## Helpers needed locally -/

private lemma nnreal_coe_nat_mul (n m : ℕ) :
    ((n : NNReal) * m) = (n * m : NNReal) := by
  apply NNReal.eq
  simp [NNReal.coe_mul, Nat.cast_mul]

private lemma nnreal_inv_mul_inv_eq_inv_mul
    {a b : NNReal} (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [mul_assoc]
  rw [mul_left_comm b⁻¹ a b]
  rw [←mul_assoc]
  rw [inv_mul_cancel₀ hb]
  rw [inv_mul_cancel₀ ha]
  ring

private lemma sum_count_eq_card {N : ℕ}
    (s : Multiset (Fin N)) :
    ∑ i : Fin N, Multiset.count i s =
      Multiset.card s := by
  have hms : ∀ a ∈ s,
      (a : Fin N) ∈ (Finset.univ : Finset (Fin N)) := by
    intro a _ha
    exact Finset.mem_univ _
  exact (Multiset.sum_count_eq_card
    (s := (Finset.univ : Finset (Fin N))) (m := s) hms)

private lemma replicate_count_zero_of_not_mem
    {α : Type*} [DecidableEq α] {s : Multiset α}
    {i : α} (hi_not_mem : i ∉ s) :
    Multiset.replicate (Multiset.count i s) i = 0 := by
  have h_count_eq_zero : Multiset.count i s = 0 :=
    Multiset.count_eq_zero.mpr hi_not_mem
  rw [h_count_eq_zero]
  rw [Multiset.replicate_zero]

private lemma count_cons_ne
    {α} [DecidableEq α] {a i : α} (h : i ≠ a)
    (s : Multiset α) :
  Multiset.count i (a ::ₘ s) = Multiset.count i s := by
  exact Multiset.count_cons_of_ne h s

private lemma replicate_split {α} (n : ℕ) (a : α) :
    Multiset.replicate (n + 1) a =
      Multiset.replicate 1 a +
        Multiset.replicate n a := by
  rw [Nat.add_comm]
  exact Multiset.replicate_add 1 n a

-- ================================================================
-- Core content
-- ================================================================

/--
Proof that `canonicalUniformDist k hk_pos` sums to 1.
This directly uses `sum_uniformDist` with the appropriate proof of
positivity for `Fintype.card (Fin k)`.
-/
lemma sum_canonicalUniformDist_eq_one (k : ℕ)
    (hk_pos : k > 0) :
    (∑ i, canonicalUniformDist k hk_pos i) = 1 := by
  simp only [canonicalUniformDist]
  exact sum_uniformDist (Fintype.card_fin_pos hk_pos)

/--
Symmetry of `shannonEntropy`:
`shannonEntropy (p ∘ e) = shannonEntropy p`
for an `Equiv e : α ≃ β` between two Fintypes `α` and `β`,
and a target distribution `p_target : β → NNReal`.
-/
theorem shannonEntropy_comp_equiv'
    {α β : Type*} [Fintype α] [Fintype β]
    (p_target : β → NNReal) (e : α ≃ β) :
    shannonEntropy (p_target ∘ e) =
      shannonEntropy p_target := by
  unfold shannonEntropy
  simp_rw [Function.comp_apply]
  exact Equiv.sum_comp e
    (fun (y : β) => Real.negMulLog ((p_target y) : ℝ))

/-- Any Rota-axiomatic entropy of the canonical uniform distribution equals
`rotaConstant * shannonEntropy`. -/
theorem H_canonical_uniform_eq_C_shannon'
    (H_func : ∀ {α_aux : Type} [Fintype α_aux],
      (α_aux → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyAxioms H_func)
    (k : ℕ) (hk_pos : k > 0) :
    (H_func (canonicalUniformDist k hk_pos) : ℝ) =
      (rotaConstant hH_axioms) *
        shannonEntropy
          (canonicalUniformDist k hk_pos) := by
  let p_unif_k := canonicalUniformDist k hk_pos
  have h_lhs_eq_f0_val :
      (H_func p_unif_k : ℝ) =
        (entropyUniform₀ hH_axioms k : ℝ) := by
    simp only [p_unif_k, canonicalUniformDist,
      uniformDist, Fintype.card_fin_pos,
      entropyUniform₀, entropyUniform,
      dif_pos hk_pos]
  rw [h_lhs_eq_f0_val]
  rw [(rota_uniqueness_formula hH_axioms).right k
    hk_pos]
  rw [shannonEntropy_canonicalUniform k hk_pos]

/--
Helper Lemma: Shows that a system distribution `p_sys`, if uniform
on `Ω_sys` with cardinality `k`, is equivalent to the canonical
uniform distribution on `Fin k` composed with the equivalence
`e_sys_to_fin_k : Ω_sys ≃ Fin k`.
-/
lemma p_sys_eq_canonical_comp_equiv
    {Ω_sys : Type} [Fintype Ω_sys]
    (p_sys : Ω_sys → NNReal)
    (k : ℕ) (hk_pos : k > 0)
    (hp_sys_is_uniform :
      p_sys = fun (_ : Ω_sys) => (k : NNReal)⁻¹)
    (e_sys_to_fin_k : Ω_sys ≃ Fin k) :
    p_sys =
      (canonicalUniformDist k hk_pos) ∘
        e_sys_to_fin_k := by
  let p_unif_k := canonicalUniformDist k hk_pos
  funext ω_sys
  rw [hp_sys_is_uniform]
  simp [p_unif_k, canonicalUniformDist, uniformDist,
    Function.comp_apply, Fintype.card_fin_pos, hk_pos]

/-- A system distribution composed with an equiv evaluates to the same entropy
as the canonical uniform distribution. -/
lemma H_sys_eq_H_canonical_nnreal_of_comp
    {Ω_sys : Type} [Fintype Ω_sys]
    (H_func : ∀ {α_aux : Type} [Fintype α_aux],
      (α_aux → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyAxioms H_func)
    (p_sys_arg : Ω_sys → NNReal)
    (k : ℕ) (hk_pos : k > 0)
    (e_sys_to_fin_k : Ω_sys ≃ Fin k)
    (h_p_sys_is_comp :
      p_sys_arg =
        (canonicalUniformDist k hk_pos) ∘
          e_sys_to_fin_k) :
    H_func p_sys_arg =
      H_func (canonicalUniformDist k hk_pos) := by
  let p_unif_k := canonicalUniformDist k hk_pos
  rw [h_p_sys_is_comp]
  exact hH_axioms.symmetry p_unif_k
    (sum_canonicalUniformDist_eq_one k hk_pos)
    e_sys_to_fin_k

/--
Helper Lemma: Shows that `shannonEntropy` of `p_sys`
is equal to `shannonEntropy` of
`canonicalUniformDist k hk_pos`, given that `p_sys` is the
composition of `canonicalUniformDist` with the equivalence
`e_sys_to_fin_k`.
-/
lemma shannon_sys_eq_shannon_canonical
    {Ω_sys : Type} [Fintype Ω_sys]
    (p_sys : Ω_sys → NNReal)
    (k : ℕ) (hk_pos : k > 0)
    (e_sys_to_fin_k : Ω_sys ≃ Fin k)
    (h_p_sys_is_comp :
      p_sys =
        (canonicalUniformDist k hk_pos) ∘
          e_sys_to_fin_k) :
    shannonEntropy p_sys =
      shannonEntropy
        (canonicalUniformDist k hk_pos) := by
  let p_unif_k := canonicalUniformDist k hk_pos
  rw [h_p_sys_is_comp]
  exact shannonEntropy_comp_equiv' p_unif_k
    e_sys_to_fin_k

/-- Any uniform physical system's entropy equals `rotaConstant * shannonEntropy`,
given an equivalence to `Fin k`. -/
theorem H_physical_dist_eq_C_shannon_if_uniform_and_equiv
    {Ω_sys : Type} [Fintype Ω_sys]
    (H_func : ∀ {α_aux : Type} [Fintype α_aux],
      (α_aux → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyAxioms H_func)
    (p_sys : Ω_sys → NNReal)
    (k : ℕ) (hk_pos : k > 0)
    (_h_card_Ω_eq_k : Fintype.card Ω_sys = k)
    (hp_sys_is_uniform :
      p_sys = fun (_ : Ω_sys) => (k : NNReal)⁻¹)
    (e_sys_to_fin_k : Ω_sys ≃ Fin k) :
    (H_func p_sys : ℝ) =
      (rotaConstant hH_axioms) *
        shannonEntropy p_sys := by
  let p_unif_k := canonicalUniformDist k hk_pos
  have h_psys_is_comp_val :
      p_sys = p_unif_k ∘ e_sys_to_fin_k :=
    p_sys_eq_canonical_comp_equiv p_sys k hk_pos
      hp_sys_is_uniform e_sys_to_fin_k
  have h_H_sys_eq_H_unif_k_real :
      (H_func p_sys : ℝ) = (H_func p_unif_k : ℝ) := by
    have h_nnreal_eq :
        H_func p_sys = H_func p_unif_k :=
      H_sys_eq_H_canonical_nnreal_of_comp H_func
        hH_axioms p_sys k hk_pos e_sys_to_fin_k
        h_psys_is_comp_val
    rw [h_nnreal_eq]
  rw [h_H_sys_eq_H_unif_k_real]
  rw [H_canonical_uniform_eq_C_shannon' H_func
    hH_axioms k hk_pos]
  have h_shannon_sys_eq_canon :
      shannonEntropy p_sys =
        shannonEntropy p_unif_k :=
    shannon_sys_eq_shannon_canonical p_sys k hk_pos
      e_sys_to_fin_k h_psys_is_comp_val
  rw [h_shannon_sys_eq_canon]

/-! # Multiset to Uniform Distribution State Space Mapping
by Vectorization -/
/-- The uniform-distribution state space: occupancy vectors summing to `M`. -/
@[reducible] def OmegaUD (N M : ℕ) := MBMacrostate N M

/-- Map an occupancy vector to the corresponding multiset of occupied states. -/
def udStateToMultiset {N M : ℕ}
    (q : OmegaUD N M) : Multiset (Fin N) :=
  Finset.univ.sum (fun i => replicate (q.val i) i)

/-- The cardinality of the multiset produced by `udStateToMultiset` equals `M`. -/
lemma card_udStateToMultiset {N M : ℕ}
    (q : OmegaUD N M) :
    Multiset.card (udStateToMultiset q) = M := by
  simp only [udStateToMultiset]
  rw [Multiset.card_sum]
  simp_rw [Multiset.card_replicate]
  exact q.property

/-- Map a multiset of states to an occupancy-count function. -/
def multisetToUDState {N : ℕ}
    (s : Multiset (Fin N)) : Fin N → ℕ :=
  fun i => Multiset.count i s

/-- Counting element `i` in `replicate (q j) j` yields zero when `i ≠ j`. -/
lemma count_replicate_term_zero {N : ℕ}
    {q : Fin N → ℕ} (i j : Fin N) (hij : i ≠ j) :
    Multiset.count i
      (Multiset.replicate (q j) j) = 0 := by
  simp [Multiset.count_replicate, Ne.symm hij]

/-- Counting element `i` in `replicate (q i) i` yields `q i`. -/
lemma count_replicate_term_eq {N : ℕ}
    {q : Fin N → ℕ} (i : Fin N) :
    Multiset.count i
      (Multiset.replicate (q i) i) = q i := by
  rw [Multiset.count_replicate_self]

/-- The sum of replicate-counts over all `j` simplifies to the single term `q i`. -/
lemma sum_count_replicate_eq_single_term {N : ℕ}
    {q : Fin N → ℕ} (i : Fin N) :
    ∑ j ∈ Finset.univ,
      Multiset.count i
        (Multiset.replicate (q j) j) = q i := by
  rw [Finset.sum_eq_single i]
  · exact count_replicate_term_eq i
  · intro j _ hij_ne
    exact count_replicate_term_zero i j
      (Ne.symm hij_ne)
  · intro h_not_mem
    simp only [Finset.mem_univ, not_true_eq_false]
      at h_not_mem

/-- `Multiset.count` distributes over the `Finset.sum` in `udStateToMultiset`. -/
lemma count_udStateToMultiset_eq_sum_count_replicate
    {N M : ℕ} (q : OmegaUD N M) (i : Fin N) :
    Multiset.count i (udStateToMultiset q) =
      ∑ j ∈ Finset.univ,
        Multiset.count i
          (Multiset.replicate (q.val j) j) := by
  simp only [udStateToMultiset]
  rw [Multiset.count_finset_sum]

/-- Bundle `multisetToUDState` with the proof that its components sum to `M`. -/
def multisetToUDStateSubtype {N M : ℕ}
    (s : SymFin N M) : OmegaUD N M :=
  ⟨ multisetToUDState s.val ,
    by
      have h_sum := sum_count_eq_card s.val
      simp only [multisetToUDState]
      rw [h_sum]
      exact s.property
  ⟩

/-- `multisetToUDStateSubtype ∘ udStateToMultiset` is the identity (left inverse). -/
lemma left_inv_udState_multiset {N M : ℕ}
    (q : OmegaUD N M) :
    multisetToUDStateSubtype
      ⟨udStateToMultiset q,
        card_udStateToMultiset q⟩ = q := by
  apply Subtype.ext
  dsimp [multisetToUDStateSubtype]
  funext i
  simp only [multisetToUDState]
  rw [count_udStateToMultiset_eq_sum_count_replicate]
  rw [sum_count_replicate_eq_single_term]

/-- Summing replicate-counts over `univ` equals summing over `s.toFinset`. -/
lemma sum_replicate_count_univ_eq_sum_toFinset
    {α : Type*} [DecidableEq α] (s : Multiset α)
    (univ : Finset α)
    (h_univ : ∀ x : α, x ∈ univ) :
    ∑ i ∈ univ,
      Multiset.replicate (Multiset.count i s) i =
    ∑ i ∈ s.toFinset,
      Multiset.replicate (Multiset.count i s) i := by
  apply Eq.symm
  apply Finset.sum_subset
  · intro x _hx_mem_toFinset
    exact h_univ x
  · intro x _hx_in_univ hx_not_in_s_toFinset
    have hx_not_mem_s : x ∉ s := by
      contrapose! hx_not_in_s_toFinset
      rwa [Multiset.mem_toFinset]
    exact replicate_count_zero_of_not_mem hx_not_mem_s

/-! ## Micro-micro lemmas for the "`a ∈ s`" branch -/

/-- Split the sum over `insert a t` into the part without `a`
plus the `i = a` summand. -/
private lemma sum_insert_split
    {α β} [DecidableEq α] [AddCommMonoid β]
    {a : α} {t : Finset α} (f : α → β)
    (ha : a ∈ insert a t) :
  (∑ i ∈ insert a t, f i)
    = (∑ i ∈ (insert a t).erase a, f i) + f a := by
  rw [Finset.sum_eq_sum_diff_singleton_add ha f]
  simp only [Finset.sdiff_singleton_eq_erase]

/-- `count` for every *other* element is unchanged after
consing `a`. -/
private lemma count_cons_ne'
    {α} [DecidableEq α] {a i : α} (h : i ≠ a)
    {s : Multiset α} :
  Multiset.count i (a ::ₘ s) =
    Multiset.count i s := by
  exact count_cons_ne h s

/-- `replicate` respects the count invariance. -/
private lemma replicate_cons_ne'
    {α} [DecidableEq α] {a i : α} (h : i ≠ a)
    {s : Multiset α} :
  Multiset.replicate
    (Multiset.count i (a ::ₘ s)) i =
    Multiset.replicate (Multiset.count i s) i := by
  simp [count_cons_ne' h]

/-- Rewrite the *tail* of the split sum using the count
invariance. -/
private lemma tail_sum_cons
    {α} [DecidableEq α] {a : α}
    {s : Multiset α} :
  (∑ i ∈ (insert a s.toFinset).erase a,
      Multiset.replicate
        (Multiset.count i (a ::ₘ s)) i) =
  (∑ i ∈ s.toFinset.erase a,
      Multiset.replicate
        (Multiset.count i s) i) := by
  rw [Finset.erase_insert_eq_erase]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_erase] at hi
  have hia : i ≠ a := hi.1
  simp [replicate_cons_ne' hia]

/-- The *head* replicate for `a`. -/
private lemma head_replicate_cons
    {α} [DecidableEq α] {a : α}
    {s : Multiset α} :
  Multiset.replicate
    (Multiset.count a (a ::ₘ s)) a =
    Multiset.replicate 1 a +
      Multiset.replicate
        (Multiset.count a s) a := by
  simp [Multiset.count_cons_self, replicate_split]

variable {α β : Type*} [DecidableEq α]
  [AddCommMonoid β]

private lemma sum_eq_add_sum_erase
    {s : Finset α} {a : α} (f : α → β)
    (h : a ∈ s) :
  ∑ x ∈ s, f x =
    f a + ∑ x ∈ s.erase a, f x := by
   rw [←Finset.sum_insert (Finset.notMem_erase a s)]
   congr
   exact Eq.symm (Finset.insert_erase h)

/-- Final streamlined version of the "`a ∈ s`" inductive
step. -/
private lemma step_mem
    {α} [DecidableEq α] {a : α}
    {s : Multiset α}
    (hmem : a ∈ s.toFinset)
    (IH : ∑ i ∈ s.toFinset,
      Multiset.replicate
        (Multiset.count i s) i = s) :
  ∑ i ∈ insert a s.toFinset,
    Multiset.replicate
      (Multiset.count i (a ::ₘ s)) i = a ::ₘ s := by
  have h_insert : insert a s.toFinset = s.toFinset :=
    Finset.insert_eq_of_mem hmem
  simp [h_insert] at IH ⊢
  have h_split :
      (∑ i ∈ s.toFinset,
        Multiset.replicate
          (Multiset.count i (a ::ₘ s)) i) =
        Multiset.replicate
          (Multiset.count a (a ::ₘ s)) a +
        ∑ i ∈ s.toFinset.erase a,
          Multiset.replicate
            (Multiset.count i (a ::ₘ s)) i := by
    exact sum_eq_add_sum_erase
      (fun i ↦ Multiset.replicate
        (Multiset.count i (a ::ₘ s)) i)
      hmem
  have h_tail :
      ∑ i ∈ s.toFinset.erase a,
        Multiset.replicate
          (Multiset.count i (a ::ₘ s)) i =
      ∑ i ∈ s.toFinset.erase a,
        Multiset.replicate
          (Multiset.count i s) i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_ne : i ≠ a :=
      (Finset.mem_erase.1 hi).1
    simp [Multiset.count_cons_of_ne hi_ne]
  have h_head :
      Multiset.replicate
        (Multiset.count a (a ::ₘ s)) a =
        {a} + Multiset.replicate
          (Multiset.count a s) a := by
    simp [Multiset.count_cons_self, replicate_split]
  calc
    (∑ i ∈ s.toFinset,
      Multiset.replicate
        (Multiset.count i (a ::ₘ s)) i)
        = {a} + ∑ i ∈ s.toFinset,
            Multiset.replicate
              (Multiset.count i s) i := by
          rw [h_split]
          rw [h_head]
          rw [h_tail]
          rw [Multiset.add_assoc]
          rw [←sum_eq_add_sum_erase
            (fun i ↦ Multiset.replicate
              (Multiset.count i s) i) hmem]
    _ = {a} + s := by
          simp only [IH]
    _ = a ::ₘ s := by
          simp only [Multiset.singleton_add]

/-! ## Micro-micro lemmas for the "`a ∉ s`" branch -/

/-- When `a ∉ s`, its count in `s` is zero. -/
private lemma count_not_mem_zero
    {α} [DecidableEq α] {a : α}
    {s : Multiset α} (h_not_mem : a ∉ s) :
  Multiset.count a s = 0 := by
  exact Multiset.count_eq_zero.mpr h_not_mem

/-- The head replicate collapses to `{a}` if `a ∉ s`. -/
private lemma head_replicate_not_mem
    {α} [DecidableEq α] {a : α}
    {s : Multiset α} (h_not_mem : a ∉ s) :
  Multiset.replicate
    (Multiset.count a (a ::ₘ s)) a = {a} := by
  rw [Multiset.count_cons_self]
  rw [count_not_mem_zero h_not_mem]
  simp only [Nat.zero_add]
  rw [Multiset.replicate_one]

/-- Tail sum unchanged when `a ∉ s`. -/
private lemma tail_sum_not_mem
    {α} [DecidableEq α] {a : α}
    {s : Multiset α} (h_not_mem : a ∉ s) :
  (∑ i ∈ s.toFinset,
      Multiset.replicate
        (Multiset.count i (a ::ₘ s)) i) =
  (∑ i ∈ s.toFinset,
      Multiset.replicate
        (Multiset.count i s) i) := by
  apply Finset.sum_congr rfl
  intro i hi_mem_finset
  have hi_ne_a : i ≠ a := by
    intro h_eq
    subst h_eq
    rw [Multiset.mem_toFinset] at hi_mem_finset
    exact h_not_mem hi_mem_finset
  rw [replicate_cons_ne' hi_ne_a]

/-- Assemble the pieces for `a ∉ s`. -/
private lemma step_not_mem
    {α} [DecidableEq α] {a : α}
    {s : Multiset α}
    (h_not_mem_finset : a ∉ s.toFinset)
    (IH : ∑ i ∈ s.toFinset,
      Multiset.replicate
        (Multiset.count i s) i = s) :
  ∑ i ∈ insert a s.toFinset,
    Multiset.replicate
      (Multiset.count i (a ::ₘ s)) i =
        a ::ₘ s := by
  have h_not_mem : a ∉ s := by
    contrapose! h_not_mem_finset
    rwa [Multiset.mem_toFinset]
  rw [Finset.sum_insert h_not_mem_finset]
  rw [head_replicate_not_mem h_not_mem]
  rw [tail_sum_not_mem h_not_mem]
  rw [IH]
  rw [Multiset.singleton_add]

/-- Summing `replicate (count i s) i` over `s.toFinset` reconstructs `s`. -/
@[simp]
theorem sum_replicate_count_toFinset_eq_self
    {α : Type*} [DecidableEq α]
    (s : Multiset α) :
    ∑ i ∈ s.toFinset,
      Multiset.replicate
        (Multiset.count i s) i = s := by
  induction s using Multiset.induction
  case empty =>
    simp
  case cons a s ih =>
    rw [Multiset.toFinset_cons]
    by_cases ha_mem_finset : a ∈ s.toFinset
    · exact step_mem ha_mem_finset ih
    · exact step_not_mem ha_mem_finset ih

/-- `udStateToMultiset ∘ multisetToUDStateSubtype` is the identity (right inverse). -/
lemma right_inv_beState_multiset {N M : ℕ}
    (s : SymFin N M) :
    udStateToMultiset
      (multisetToUDStateSubtype s) = s.val := by
  dsimp only [udStateToMultiset]
  simp only [multisetToUDStateSubtype]
  simp only [multisetToUDState]
  rw [sum_replicate_count_univ_eq_sum_toFinset s.val
    Finset.univ (Finset.mem_univ)]
  rw [sum_replicate_count_toFinset_eq_self s.val]

/-!
## Phase 1: Combinatorial Equivalence (Completed)
We have established the maps and proven they are inverses.
Now we bundle them into a formal `Equiv`.
-/

/--
Formal `Equiv` (bijection) between the `OmegaUD` representation
(occupancy vectors) and the `SymFin` representation (multisets of
a fixed size).
-/
def udStateEquivMultiset (N M : ℕ) :
    OmegaUD N M ≃ SymFin N M where
  toFun q :=
    ⟨udStateToMultiset q, card_udStateToMultiset q⟩
  invFun s := multisetToUDStateSubtype s
  left_inv q := left_inv_udState_multiset q
  right_inv s := by
    apply Subtype.eq
    exact right_inv_beState_multiset s

/--
`Fintype` instance for `OmegaUD N M`.
-/
instance fintypeOmegaUD (N M : ℕ) :
    Fintype (OmegaUD N M) :=
  Fintype.ofEquiv (SymFin N M)
    (udStateEquivMultiset N M).symm

/--
Defines the uniform probability distribution `p_UD` over the state
space `OmegaUD N M`.
-/
@[nolint unusedArguments]
noncomputable def p_UD (N M : ℕ) :
    OmegaUD N M → NNReal :=
  fun _q => uniformProb (Fintype.card (OmegaUD N M))

/-- The uniform distribution `p_UD` indexed by `Fin` of the state-space cardinality. -/
@[nolint unusedArguments]
noncomputable def p_UD_fin (N M : ℕ) :
    Fin (Fintype.card (OmegaUD N M)) → NNReal :=
  fun _i => uniformProb (Fintype.card (OmegaUD N M))

/-- The uniform distribution on `Fin n` sums to 1. -/
lemma sum_uniform_eq_one {n : ℕ} (hn : n > 0) :
  ∑ _i : Fin n, uniformProb n = 1 := by
  simp only [uniformProb, dif_pos hn]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [mul_inv_cancel₀]
  apply Nat.cast_ne_zero.mpr
  exact Nat.pos_iff_ne_zero.mp hn

/-- Product of two uniform distributions is uniform on the product
space. -/
lemma uniformProb_product_uniformProb_is_uniformProb
    {n m : ℕ} (hn : n > 0) (hm : m > 0) :
    productDist
        (fun _ : Fin n     => uniformProb n)
        (fun _ : Fin m     => uniformProb m)
      = (fun _ : Fin (n*m) => uniformProb (n * m)) := by
  funext k
  simp [productDist, uniformProb, mul_pos hn hm]
  have hn_ne_zero : n ≠ 0 :=
    (Nat.pos_iff_ne_zero).1 hn
  have hm_ne_zero : m ≠ 0 :=
    (Nat.pos_iff_ne_zero).1 hm
  have h_n : (n : NNReal) ≠ 0 := by
    exact_mod_cast hn_ne_zero
  have h_m : (m : NNReal) ≠ 0 := by
    exact_mod_cast hm_ne_zero
  rw [nnreal_inv_mul_inv_eq_inv_mul h_m h_n]
  rw [mul_comm]
  simp [hn, hm, mul_comm, nnreal_coe_nat_mul n m]

/-- Shannon entropy of `p_UD_fin` is zero when the state space has cardinality 1. -/
lemma shannonEntropy_of_p_UD_fin_when_k_is_1
    (N M : ℕ)
    (h_k_is_1 : Fintype.card (OmegaUD N M) = 1) :
    shannonEntropy (p_UD_fin N M) = 0 := by
  unfold shannonEntropy
  conv_lhs =>
    arg 1
    simp [h_k_is_1]
  simp [p_UD_fin, h_k_is_1, uniformProb, inv_one,
    NNReal.coe_one, Real.negMulLog_one]

/--
Calculates the cardinality of the Bose-Einstein state space
`OmegaUD N M`. This is the number of ways to distribute `M`
indistinguishable particles into `N` distinguishable energy
states, which is given by the multichoose function
`Nat.multichoose N M`.
-/
lemma card_omega_be (N M : ℕ) :
    Fintype.card (OmegaUD N M) =
      Nat.multichoose N M := by
  rw [Fintype.card_congr (udStateEquivMultiset N M)]
  rw [Sym.card_sym_eq_multichoose (Fin N) M]
  rw [Fintype.card_fin N]

/-- `Nat.multichoose` is positive exactly when we can really place
`k` indistinguishable balls into `n` labelled boxes -- i.e.
either we have at least one box (`n ≠ 0`) or there is nothing
to place (`k = 0`). -/
lemma multichoose_pos_iff (n k : ℕ) :
    0 < Nat.multichoose n k ↔ (n ≠ 0 ∨ k = 0) := by
  by_cases hk : k = 0
  · subst hk
    simp [Nat.multichoose_zero_right]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    cases n with
    | zero =>
        have h0 : Nat.multichoose 0 k = 0 := by
          have hlt : k - 1 < k :=
            Nat.pred_lt (Nat.ne_of_gt hkpos)
          rw [Nat.multichoose_eq]
          rw [Nat.zero_add]
          exact (Nat.choose_eq_zero_of_lt hlt)
        simp [h0, hk]
    | succ n' =>
        have hle : k ≤ n' + k := by
          simpa [add_comm] using Nat.le_add_left k n'
        have : 0 < (n' + k).choose k :=
          Nat.choose_pos hle
        simpa [Nat.multichoose_eq,
          Nat.succ_eq_add_one, add_comm,
          add_left_comm, add_assoc, hk] using this

/-- The Bose-Einstein state space has positive cardinality when `N ≠ 0 ∨ M = 0`. -/
lemma card_omega_BE_pos (N M : ℕ)
    (h : N ≠ 0 ∨ M = 0) :
    0 < Fintype.card (OmegaUD N M) := by
  simpa [card_omega_be, multichoose_pos_iff] using h

/-- `p_UD_fin` equals the canonical `uniformDist` on the Bose-Einstein state space. -/
lemma p_BE_fin_is_H_physical_system_uniform_input
    (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    p_UD_fin N M =
      uniformDist
        (α := Fin (Fintype.card (OmegaUD N M)))
        (by {
          simp only [Fintype.card_fin]
          exact card_omega_BE_pos N M h_domain_valid
        }) := by
  let k_card_ := Fintype.card (OmegaUD N M)
  have hk_card_pos_ : k_card_ > 0 :=
    card_omega_BE_pos N M h_domain_valid
  funext i
  simp [p_UD_fin, uniformProb, uniformDist,
    Fintype.card_fin, k_card_,
    if_pos hk_card_pos_]

/-- Evaluating `H_physical_system` on `p_UD_fin` reduces to
`H_physical_system_uniform_only_calc`. -/
lemma eval_H_physical_system_on_p_UD_fin (N M : ℕ)
    (h_domain_valid : N ≠ 0 ∨ M = 0) :
    H_physical_system (p_UD_fin N M) =
      H_physical_system_uniform_only_calc
        (Fintype.card (OmegaUD N M))
        (Nat.one_le_of_lt
          (card_omega_BE_pos N M h_domain_valid)) := by
  let k_card_ := Fintype.card (OmegaUD N M)
  have hk_card_pos_ : k_card_ > 0 :=
    card_omega_BE_pos N M h_domain_valid
  simp only [H_physical_system, Fintype.card_fin]
  rw [dif_neg (Nat.ne_of_gt hk_card_pos_)]
  simp only [p_BE_fin_is_H_physical_system_uniform_input
    N M h_domain_valid]
  rfl

/-- Physical entropy of a uniform distribution equals `C * shannonEntropy`. -/
theorem H_physical_system_is_rota_uniform (N M : ℕ)
    (h_domain_valid : N ≠ 0 ∨ M = 0) :
    (H_physical_system (p_UD_fin N M) : ℝ) =
      (C_physical_NNReal : ℝ) *
        shannonEntropy (p_UD_fin N M) := by
  let k_card_ := Fintype.card (OmegaUD N M)
  have hk_card_ge1_ : k_card_ ≥ 1 :=
    Nat.one_le_of_lt
      (card_omega_BE_pos N M h_domain_valid)
  rw [eval_H_physical_system_on_p_UD_fin N M
    h_domain_valid]
  rw [H_physical_system_uniform_only_calc]
  if hk_eq_1 : k_card_ = 1 then
    rw [dif_pos hk_eq_1]
    simp only [NNReal.coe_zero]
    rw [shannonEntropy_of_p_UD_fin_when_k_is_1 N M
      hk_eq_1]
    simp only [mul_zero]
  else
    rw [dif_neg hk_eq_1]
    simp only [RealLogNatToNNReal, NNReal.coe_mul,
      (Real.log_nonneg
        (Nat.one_le_cast.mpr hk_card_ge1_))]
    have h_shannon_eq_log_k :
        shannonEntropy (p_UD_fin N M) =
          Real.log (k_card_ : ℝ) := by
      rw [p_BE_fin_is_H_physical_system_uniform_input
        N M h_domain_valid]
      rw [shannonEntropy_uniformDist]
      simp only [Fintype.card_fin]
      rfl
    rw [h_shannon_eq_log_k]
    rfl

end InformationTheory.Physics.UniformSystems
