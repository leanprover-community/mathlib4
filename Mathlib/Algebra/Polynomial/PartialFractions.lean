/-
Copyright (c) 2023 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Sidharth Hariharan
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Logic.Function.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!

# Partial fractions

These results were formalised by the Xena Project, at the suggestion
of Patrick Massot.


# The main theorem

* `div_eq_quo_add_sum_rem_div`: General partial fraction decomposition theorem for polynomials over
  an integral domain R :
  If f, g₁, g₂, ..., gₙ ∈ R[X] and the gᵢs are all monic and pairwise coprime, then ∃ q, r₁, ..., rₙ
  ∈ R[X] such that f / g₁g₂...gₙ = q + r₁/g₁ + ... + rₙ/gₙ and for all i, deg(rᵢ) < deg(gᵢ).

* The result is formalized here in slightly more generality, using finsets. That is, if ι is an
  arbitrary index type, g denotes a map from ι to R[X], and if s is an arbitrary finite subset of ι,
  with g i monic for all i ∈ s and for all i,j ∈ s, i ≠ j → g i is coprime to g j, then we have
  ∃ q ∈ R[X] , r : ι → R[X] such that ∀ i ∈ s, deg(r i) < deg(g i) and
  f / ∏ g i = q + ∑ (r i) / (g i), where the product and sum are over s.

* The proof is done by proving the two-denominator case and then performing finset induction for an
  arbitrary (finite) number of denominators.

## Scope for Expansion

* Proving uniqueness of the decomposition

-/


variable (R : Type) [CommRing R] [IsDomain R]

open Polynomial

variable (K : Type) [Field K] [Algebra R[X] K] [IsFractionRing R[X] K]

section TwoDenominators

open scoped algebraMap

/-- Let R be an integral domain and f, g₁, g₂ ∈ R[X]. Let g₁ and g₂ be monic and coprime.
Then, ∃ q, r₁, r₂ ∈ R[X] such that f / g₁g₂ = q + r₁/g₁ + r₂/g₂ and deg(r₁) < deg(g₁) and
deg(r₂) < deg(g₂).
-/
theorem div_eq_quo_add_rem_div_add_rem_div (f : R[X]) {g₁ g₂ : R[X]} (hg₁ : g₁.Monic)
    (hg₂ : g₂.Monic) (hcoprime : IsCoprime g₁ g₂) :
    ∃ q r₁ r₂ : R[X],
      r₁.degree < g₁.degree ∧
        r₂.degree < g₂.degree ∧ (f : K) / (↑g₁ * ↑g₂) = ↑q + ↑r₁ / ↑g₁ + ↑r₂ / ↑g₂ := by
  rcases hcoprime with ⟨c, d, hcd⟩
  refine
    ⟨f * d /ₘ g₁ + f * c /ₘ g₂, f * d %ₘ g₁, f * c %ₘ g₂, degree_modByMonic_lt _ hg₁,
      degree_modByMonic_lt _ hg₂, ?_⟩
  have hg₁' : (↑g₁ : K) ≠ 0 := by
    norm_cast
    exact hg₁.ne_zero
  have hg₂' : (↑g₂ : K) ≠ 0 := by
    norm_cast
    exact hg₂.ne_zero
  have hfc := modByMonic_add_div (f * c) hg₂
  have hfd := modByMonic_add_div (f * d) hg₁
  field_simp
  norm_cast
  linear_combination -1 * f * hcd + -1 * g₁ * hfc + -1 * g₂ * hfd

end TwoDenominators

section NDenominators

open algebraMap

/-- Let R be an integral domain and f ∈ R[X]. Let s be a finite index set.
Then, a fraction of the form f / ∏ (g i) can be rewritten as q + ∑ (r i) / (g i), where
deg(r i) < deg(g i), provided that the g i are monic and pairwise coprime.
-/
theorem div_eq_quo_add_sum_rem_div (f : R[X]) {ι : Type*} {g : ι → R[X]} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).Monic) (hcop : Set.Pairwise ↑s fun i j => IsCoprime (g i) (g j)) :
    ∃ (q : R[X]) (r : ι → R[X]),
      (∀ i ∈ s, (r i).degree < (g i).degree) ∧
        ((↑f : K) / ∏ i ∈ s, ↑(g i)) = ↑q + ∑ i ∈ s, (r i : K) / (g i : K) := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
    refine ⟨f, fun _ : ι => (0 : R[X]), fun i => ?_, by simp⟩
    rintro ⟨⟩
  | insert a b hab Hind => ?_
  obtain ⟨q₀, r₁, r₂, hdeg₁, _, hf : (↑f : K) / _ = _⟩ :=
    div_eq_quo_add_rem_div_add_rem_div R K f
      (hg a (b.mem_insert_self a) : Monic (g a))
      (monic_prod_of_monic _ _ fun i hi => hg i (Finset.mem_insert_of_mem hi) :
        Monic (∏ i ∈ b, g i))
      (IsCoprime.prod_right fun i hi =>
        hcop (Finset.mem_coe.2 (b.mem_insert_self a))
          (Finset.mem_coe.2 (Finset.mem_insert_of_mem hi)) (by rintro rfl; exact hab hi))
  obtain ⟨q, r, hrdeg, IH⟩ :=
    Hind _ (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (Set.Pairwise.mono (Finset.coe_subset.2 fun i hi => Finset.mem_insert_of_mem hi) hcop)
  refine ⟨q₀ + q, fun i => if i = a then r₁ else r i, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs with h1
    · cases h1
      intro
      exact hdeg₁
    · intro hi
      exact hrdeg i (Finset.mem_of_mem_insert_of_ne hi h1)
  norm_cast at hf IH ⊢
  rw [Finset.prod_insert hab, hf, IH, Finset.sum_insert hab, if_pos rfl]
  trans (↑(q₀ + q : R[X]) : K) + (↑r₁ / ↑(g a) + ∑ i ∈ b, (r i : K) / (g i : K))
  · push_cast
    ring
  congr 2
  refine Finset.sum_congr rfl fun x hxb => ?_
  rw [if_neg]
  rintro rfl
  exact hab hxb

end NDenominators
