/-
Copyright (c) 2023 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Sidharth Hariharan, Aaron Liu
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Coprime.Lemmas

/-!

# Partial fractions

For `f, g : R[X]`, if `g` is expressed as a product `g₁ ^ n₁ * g₂ ^ n₂ * ... * gₙ ^ nₙ`,
where the `gᵢ` are monic and pairwise coprime, then there is a quotient `q` and
for each `i` from 1 to n and for each `0 ≤ j < nᵢ` there is a remainder `rᵢⱼ`
with degree less than the degree of `gᵢ`, such that the fraction `f / g`
decomposes as `q + ∑ i j, rᵢⱼ / gᵢ ^ (j + 1)`.

Since polynomials do not have a division, the main theorem
`mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` is stated in an `R[X]`-algebra `K`
containing inverses `giᵢ` for each polynomial `gᵢ` occuring in the denominator.


These results were formalised by the Xena Project, at the suggestion
of Patrick Massot.


## Main results

* `mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`: Partial fraction decomposition for
  polynomials over a commutative ring `R`, the denomiator is a product of powers of
  monic pairwise coprime polynomials. Division is done in an `R[X]`-algebra `K`
  containing inverses `gi i` for each `g i` occuring in the denomiator.
* `eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow`: Partial fraction decomposition for
  polynomials over a commutative ring `R`, the denomiator is a product of powers of
  monic pairwise coprime polynomials. The denominators are multiplied out on both sides
  and formally cancelled.
* `eq_quo_mul_prod_add_sum_rem_mul_prod`: Partial fraction decomposition for
  polynomials over a commutative ring `R`, the denomiator is a product of monic
  pairwise coprime polynomials. The denominators are multiplied out on both sides
  and formally cancelled.
* `div_prod_eq_quo_add_sum_rem_div`: Partial fraction decomposition for polynomials over an
  integral domain `R`, the denominator is a product of monic pairwise coprime polynomials.
  Division is done in a field `K` containing `R[X]`.
* `div_eq_quo_add_rem_div_add_rem_div`: Partial fraction decomposition for polynomials over an
  integral domain `R`, the denominator is a product of two monic coprime polynomials.
  Division is done in a field `K` containing `R[X]`.

## Naming

The lemmas in this file proving existence of partial fraction decomposition all have
conclusions of the form `∃ q r, degree r < degree g ∧ f / g = q + ∑ r / g`.
The names of these lemmas depict only the final equality `f / g = q + ∑ r / g`.
They are named structurally, except the bound variable `q` is called `quo` (for quotient)
and the bound variable `r` is called `rem` (for remainder), since they are the quotient
and remainder of the division `f / g`.
For example, `div_prod_eq_quo_add_sum_rem_div` has the conclusion
```
∃ q r, (∀ i ∈ s, (r i).degree < (g i).degree) ∧
  ↑f / ∏ i ∈ s, ↑(g i) = ↑q + ∑ i ∈ s, ↑(r i) / ↑(g i)
```
The name of the lemma only shows the final equality, and in order we have
`/` (`div`), `∏` (`prod`), `=` (`eq`), `q` (`quo`),
`+` (`add`), `∑` (`sum`), `r i` (`rem`), `/` (`div`).

## Scope for Expansion

* Proving uniqueness of the decomposition

-/

public section


variable {R : Type*} [CommRing R] [Nontrivial R]

namespace Polynomial

section Mul

section OneDenominator

/-- Let `R` be a commutative ring and `f g : R[X]`. Let `n` be a natural number.
Then `f` can be written in the form `g i ^ n * (q + ∑ i : Fin n, r i / g i ^ (i + 1))`, where
`degree (r i) < degree (g i)` and the denominator cancels formally. -/
theorem eq_quo_mul_pow_add_sum_rem_mul_pow (f : R[X]) {g : R[X]} (hg : g.Monic)
    (n : ℕ) : ∃ (q : R[X]) (r : Fin n → R[X]), (∀ i, (r i).degree < g.degree) ∧
      f = q * g ^ n + ∑ i, r i * g ^ i.1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨q, r, hr, hf⟩ := ih
    refine ⟨q /ₘ g, Fin.snoc r (q %ₘ g), fun i => ?_, hf.trans ?_⟩
    · cases i using Fin.lastCases with
      | cast i => simpa using hr i
      | last => simpa using degree_modByMonic_lt q hg
    · rw [Fin.sum_univ_castSucc, ← add_rotate', Fin.snoc_last, Fin.val_last,
        ← add_assoc, pow_succ', ← mul_assoc, ← add_mul, mul_comm (q /ₘ g) g,
        modByMonic_add_div q hg]
      simp

end OneDenominator

section ManyDenominators

/-- Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `s`.
Then `f` can be written in the form `(∏ i ∈ s, g i) * (q + ∑ i ∈ s, r i / g i)`, where
`degree (r i) < degree (g i)` and the denominator cancels formally. -/
theorem eq_quo_mul_prod_add_sum_rem_mul_prod {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (f : R[X]) {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j)) :
    ∃ (q : R[X]) (r : ι → R[X]),
      (∀ i ∈ s, (r i).degree < (g i).degree) ∧
      f = q * (∏ i ∈ s, g i) + ∑ i ∈ s, r i * ∏ k ∈ s.erase i, g k := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.forall_mem_cons] at hg
    rw [Finset.coe_cons, Set.pairwise_insert] at hgg
    obtain ⟨q, r, -, hf⟩ := ih hg.2 hgg.1
    have hjs {j : ι} (hj : j ∈ s) : i ≠ j := fun hij => hi (hij ▸ hj)
    have hc (j : ι) : ∃ a b, j ∈ s → a * g i + b * g j = 1 :=
      if h : j ∈ s ∧ i ≠ j then
        (hgg.2 j h.1 h.2).1.elim fun a h => h.elim fun b h => ⟨a, b, fun _ => h⟩
      else
        ⟨0, 0, fun hj => (h ⟨hj, hjs hj⟩).elim⟩
    choose a b hab using hc
    refine ⟨(q + ∑ j ∈ s, r j * b j %ₘ g i) /ₘ g i + ∑ j ∈ s, (r j * b j /ₘ g i + r j * a j /ₘ g j),
      Function.update (fun j => r j * a j %ₘ g j) i ((q + ∑ j ∈ s, r j * b j %ₘ g i) %ₘ g i),
      ?_, hf.trans ?_⟩
    · rw [Finset.forall_mem_cons, Function.update_self]
      refine ⟨degree_modByMonic_lt _ hg.1, fun j hj => ?_⟩
      rw [Function.update_of_ne (hjs hj).symm]
      exact degree_modByMonic_lt _ (hg.2 j hj)
    · rw [Finset.prod_cons, Finset.sum_cons, Function.update_self, Finset.erase_cons, add_mul,
        add_add_add_comm, ← mul_assoc, ← add_mul, add_comm (_ * g i), ← mul_comm (g i),
        modByMonic_add_div _ hg.1, add_mul, add_assoc, add_right_inj, Finset.sum_mul,
        Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (hjs hj).symm, Finset.erase_cons_of_ne _ (hjs hj),
        Finset.prod_cons, ← Finset.mul_prod_erase s g hj]
      simp_rw [← mul_assoc, ← add_mul]
      refine congrArg (· * _) ?_
      rw [add_mul, add_mul, ← add_assoc, ← add_assoc, ← add_mul, ← mul_comm (g i),
        modByMonic_add_div _ hg.1, add_assoc, mul_right_comm (_ /ₘ g j),
        ← add_mul, add_comm (_ * g j) (_ %ₘ g j), mul_comm (_ /ₘ g j),
        modByMonic_add_div _ (hg.2 j hj), mul_assoc, mul_assoc, ← mul_add,
        add_comm, hab j hj, mul_one]

/-- Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `s`,
and for each `g i` let `n i` be a natural number. Then `f` can be written in the form
`(∏ i ∈ s, g i ^ n i) * (q + ∑ i ∈ s, ∑ j : Fin (n i), r i j / g i ^ (j + 1))`, where
`degree (r i j) < degree (g i)` and the denominator cancels formally. -/
theorem eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (f : R[X]) {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j)) (n : ι → ℕ) :
    ∃ (q : R[X]) (r : (i : ι) → Fin (n i) → R[X]),
      (∀ i ∈ s, ∀ j, (r i j).degree < (g i).degree) ∧
      f = q * (∏ i ∈ s, g i ^ n i) +
        ∑ i ∈ s, ∑ j, r i j * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ n k := by
  obtain ⟨q, r, -, hf⟩ := eq_quo_mul_prod_add_sum_rem_mul_prod f
    (fun i hi => (hg i hi).pow (n i))
    (hgg.mono' fun i j hij => hij.pow)
  have hc (i : ι) : ∃ (q' : R[X]) (r' : Fin (n i) → R[X]), i ∈ s →
      (∀ j, (r' j).degree < (g i).degree) ∧
      r i = q' * g i ^ (n i) + ∑ j, r' j * g i ^ j.1 :=
    if hi : i ∈ s then
      (eq_quo_mul_pow_add_sum_rem_mul_pow (r i) (hg i hi) (n i)).elim
        fun q' h => h.elim fun r' h => ⟨q', r', fun _ => h⟩
    else
      ⟨0, fun _ => 0, hi.elim⟩
  choose q' r' hr' hr using hc
  refine ⟨q + ∑ i ∈ s, q' i, r', hr', hf.trans ?_⟩
  rw [add_mul, add_assoc, add_right_inj, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.mul_prod_erase s _ hi, hr i hi, add_mul, Finset.sum_mul, mul_assoc]

end ManyDenominators

end Mul

section Div
variable {K : Type*} [CommRing K] [Algebra R[X] K]

/-- Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `s`,
and for each `g i` let `n i` be a natural number.
Let `K` be an algebra over `R[X]` containing inverses `gi i` for each `g i`.
Then a fraction of the form `f * ∏ i ∈ s, gi i ^ n i` can be rewritten as
`q + ∑ i ∈ s, ∑ j : Fin (n i), r i j * gi i ^ (j + 1)`, where
`degree (r i j) < degree (g i)`. -/
theorem mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse {ι : Type*} {s : Finset ι}
    (f : R[X]) {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j))
    (n : ι → ℕ) {gi : ι → K} (hgi : ∀ i ∈ s, gi i * algebraMap R[X] K (g i) = 1) :
    ∃ (q : R[X]) (r : (i : ι) → Fin (n i) → R[X]),
      (∀ i ∈ s, ∀ j, (r i j).degree < (g i).degree) ∧
      algebraMap R[X] K f * ∏ i ∈ s, gi i ^ n i =
        algebraMap R[X] K q + ∑ i ∈ s, ∑ j,
          algebraMap R[X] K (r i j) * gi i ^ (j.1 + 1) := by
  classical
  obtain ⟨q, r, hr, hf⟩ := eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow f hg hgg n
  refine ⟨q, fun i j => r i j.rev, fun i hi j => hr i hi j.rev, ?_⟩
  rw [hf, map_add, map_mul, map_prod, add_mul, mul_assoc, ← Finset.prod_mul_distrib]
  have hc (x : ι) (hx : x ∈ s) : (algebraMap R[X] K) (g x ^ n x) * gi x ^ n x = 1 := by
    rw [map_pow, ← mul_pow, mul_comm, hgi x hx, one_pow]
  rw [Finset.prod_congr rfl hc, Finset.prod_const_one,
    mul_one, add_right_inj, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_sum, Finset.sum_mul, ← Equiv.sum_comp Fin.revPerm]
  refine Fintype.sum_congr _ _ fun j => ?_
  rw [Fin.revPerm_apply, map_mul, map_prod, ← Finset.prod_erase_mul s _ hi,
    ← mul_rotate', mul_assoc, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun x hx => hc x (Finset.mem_of_mem_erase hx),
    Finset.prod_const_one, mul_one, map_mul, map_pow, mul_left_comm]
  refine congrArg (_ * ·) ?_
  rw [← mul_one (gi i ^ (j.1 + 1)), ← @one_pow K _ j.rev, ← hgi i hi,
    mul_pow, ← mul_assoc, ← pow_add, Fin.val_rev, Nat.add_sub_cancel' (by lia)]

end Div

section Field

variable (K : Type*) [Field K] [Algebra R[X] K] [FaithfulSMul R[X] K]

section NDenominators

open algebraMap

/-- Let `R` be an integral domain and `f : R[X]`. Let `s` be a finite index set.
Then a fraction of the form `f / ∏ i ∈ s, g i` evaluated in a field `K` containing `R[X]`
can be rewritten as `q + ∑ i ∈ s, r i / g i`, where
`degree (r i) < degree (g i)`, provided that the `g i` are monic and pairwise coprime. -/
theorem div_prod_eq_quo_add_sum_rem_div (f : R[X]) {ι : Type*} {g : ι → R[X]} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).Monic) (hcop : Set.Pairwise ↑s fun i j => IsCoprime (g i) (g j)) :
    ∃ (q : R[X]) (r : ι → R[X]),
      (∀ i ∈ s, (r i).degree < (g i).degree) ∧
        ((↑f : K) / ∏ i ∈ s, ↑(g i)) = ↑q + ∑ i ∈ s, (r i : K) / (g i : K) := by
  have hgi (i : ι) (hi : i ∈ s) : (algebraMap R[X] K (g i))⁻¹ * algebraMap R[X] K (g i) = 1 :=
    inv_mul_cancel₀ (by simpa using (hg i hi).ne_zero)
  obtain ⟨q, r, hr, hf⟩ := mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    f hg hcop (fun _ => 1) hgi
  refine ⟨q, fun i => r i 0, fun i hi => hr i hi 0, ?_⟩
  simp_rw [Fin.sum_univ_one, Fin.val_zero, zero_add, pow_one, Finset.prod_inv_distrib] at hf
  simp_rw [Algebra.cast, div_eq_mul_inv]
  exact hf

@[deprecated (since := "2026-02-08")]
alias _root_.div_eq_quo_add_sum_rem_div := div_prod_eq_quo_add_sum_rem_div

end NDenominators

section TwoDenominators

open scoped algebraMap

/-- Let `R` be an integral domain and `f, g₁, g₂ : R[X]`. Let `g₁` and `g₂` be monic and coprime.
Then `∃ q, r₁, r₂ : R[X]` such that `f / (g₁ * g₂) = q + r₁ / g₁ + r₂ / g₂` and
`degree rᵢ < degree gᵢ`, where the equality is taken in a field `K` containing `R[X]`. -/
theorem div_eq_quo_add_rem_div_add_rem_div (f : R[X]) {g₁ g₂ : R[X]} (hg₁ : g₁.Monic)
    (hg₂ : g₂.Monic) (hcoprime : IsCoprime g₁ g₂) :
    ∃ q r₁ r₂ : R[X],
      r₁.degree < g₁.degree ∧
        r₂.degree < g₂.degree ∧ (f : K) / (↑g₁ * ↑g₂) = ↑q + ↑r₁ / ↑g₁ + ↑r₂ / ↑g₂ := by
  let g : Bool → R[X] := Bool.rec g₂ g₁
  have hg (i : Bool) (_ : i ∈ Finset.univ) : (g i).Monic := Bool.rec hg₂ hg₁ i
  have hcoprime : Set.Pairwise (Finset.univ : Finset Bool) fun i j => IsCoprime (g i) (g j) := by
    simp [g, Set.pairwise_insert, hcoprime, hcoprime.symm]
  obtain ⟨q, r, hr, hf⟩ := div_prod_eq_quo_add_sum_rem_div K f hg hcoprime
  refine ⟨q, r true, r false, hr true (Finset.mem_univ true), hr false (Finset.mem_univ false), ?_⟩
  simpa [g, add_assoc] using hf

@[deprecated (since := "2026-02-08")]
alias _root_.div_eq_quo_add_rem_div_add_rem_div := div_eq_quo_add_rem_div_add_rem_div

end TwoDenominators

end Field

end Polynomial
