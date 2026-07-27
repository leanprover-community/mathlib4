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
containing inverses `giᵢ` for each polynomial `gᵢ` occurring in the denominator.


These results were formalised by the Xena Project, at the suggestion
of Patrick Massot.


## Main results

* `mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`: Partial fraction decomposition for
  polynomials over a commutative ring `R`, the denominator is a product of powers of
  monic pairwise coprime polynomials. Division is done in an `R[X]`-algebra `K`
  containing inverses `gi i` for each `g i` occurring in the denominator.
* `eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow`: Partial fraction decomposition for
  polynomials over a commutative ring `R`, the denominator is a product of powers of
  monic pairwise coprime polynomials. The denominators are multiplied out on both sides
  and formally cancelled.
* `eq_quo_mul_prod_add_sum_rem_mul_prod`: Partial fraction decomposition for
  polynomials over a commutative ring `R`, the denominator is a product of monic
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

The lemmas in this file proving uniqueness of partial fraction decomposition all have
conclusions of the form `q₁ + ∑ r₁ / g = q₂ + ∑ r₂ / g → q₁ = q₂ ∧ r₁ = r₂`.
The names of these lemmas show a side of the equality hypothesis `q₁ + ∑ r₁ / g = q₂ + ∑ r₂ / g`,
and are suffixed by `_unique`.
In analogy with the existence lemmas, the variables `qᵢ` are called quotients
and referred to as `quo` in the name of the lemma and the variables `rᵢ` are called remainders
and referred to as `rem` in the name of the lemma.
For example, `quo_add_sum_rem_div_unique` has the conclusion
```
↑q₁ + ∑ i ∈ s, ↑(r₁ i) / ↑(g i) = ↑q₂ + ∑ i ∈ s, ↑(r₂ i) / ↑(g i)) →
  q₁ = q₂ ∧ ∀ i ∈ s, r₁ i = r₂ i
```
The name of the lemmas shows one side of the equality hypothesis (the other is the same),
and in order we have
`q` (`quo`), `+` (`add`), `∑` (`sum`), `r i` (`rem`), `/` (`div`).

-/

public section


variable {R : Type*} [CommRing R]

namespace Polynomial

section Mul

section OneDenominator

/-- Let `R` be a commutative ring and `f g : R[X]`. Let `n` be a natural number.
Then `f` can be written in the form `g ^ n * (q + ∑ i : Fin n, r i / g ^ (i + 1))`, where
`degree (r i) < degree g` and the denominator cancels formally.
See `quo_mul_pow_add_sum_rem_mul_pow_unique` for the uniqueness of this representation. -/
theorem eq_quo_mul_pow_add_sum_rem_mul_pow [Nontrivial R] (f : R[X]) {g : R[X]} (hg : g.Monic)
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
        modByMonic_add_div q]
      simp

/-- Let `R` be a commutative ring and `f g : R[X]`. Let `n` be a natural number.
Then `f` can be written in the form `g ^ n * (q + ∑ i : Fin n, r i / g ^ (i + 1))`
in at most one way, where `degree (r i) < degree g` and the denominator cancels formally.
See `eq_quo_mul_pow_add_sum_rem_mul_pow` for the existence of such a representation. -/
theorem quo_mul_pow_add_sum_rem_mul_pow_unique {g : R[X]} (hg : g.Monic) {n : ℕ}
    {q₁ q₂ : R[X]} {r₁ r₂ : Fin n → R[X]}
    (hr₁ : ∀ i, (r₁ i).degree < g.degree) (hr₂ : ∀ i, (r₂ i).degree < g.degree)
    (hf : q₁ * g ^ n + ∑ i, r₁ i * g ^ i.1 = q₂ * g ^ n + ∑ i, r₂ i * g ^ i.1) :
    q₁ = q₂ ∧ r₁ = r₂ := by
  induction n generalizing q₁ q₂ with
  | zero => exact ⟨by simpa using hf, funext Fin.rec0⟩
  | succ n ih =>
    cases r₁ using Fin.snocCases with | snoc rs₁ r₁
    cases r₂ using Fin.snocCases with | snoc rs₂ r₂
    simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.val_castSucc, Fin.snoc_last, Fin.val_last] at hf
    rw [← add_rotate' (r₁ * g ^ n), ← add_rotate' (r₂ * g ^ n), pow_succ', ← mul_assoc, ← mul_assoc,
      ← add_assoc, ← add_assoc, ← add_mul, ← add_mul, ← mul_comm g, ← mul_comm g] at hf
    obtain ⟨hqr, hrs⟩ := ih
      (fun i => by simpa using hr₁ i.castSucc)
      (fun i => by simpa using hr₂ i.castSucc) hf
    obtain ⟨hq₁, hrr₁⟩ := div_modByMonic_unique q₁ r₁ hg ⟨rfl, by simpa using hr₁ (Fin.last n)⟩
    obtain ⟨hq₂, hrr₂⟩ := div_modByMonic_unique q₂ r₂ hg ⟨rfl, by simpa using hr₂ (Fin.last n)⟩
    exact ⟨hq₁.symm.trans (hqr ▸ hq₂), congrArg₂ Fin.snoc hrs (hrr₁.symm.trans (hqr ▸ hrr₂))⟩

end OneDenominator

section ManyDenominators

/-- Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `s`.
Then `f` can be written in the form `(∏ i ∈ s, g i) * (q + ∑ i ∈ s, r i / g i)`, where
`degree (r i) < degree (g i)` and the denominator cancels formally.
See `quo_mul_prod_add_sum_rem_mul_prod_unique` for the uniqueness of this representation. -/
theorem eq_quo_mul_prod_add_sum_rem_mul_prod [Nontrivial R] {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (f : R[X]) {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
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
        modByMonic_add_div, add_mul, add_assoc, add_right_inj, Finset.sum_mul,
        Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (hjs hj).symm, Finset.erase_cons_of_ne _ (hjs hj),
        Finset.prod_cons, ← Finset.mul_prod_erase s g hj]
      simp_rw [← mul_assoc, ← add_mul]
      refine congrArg (· * _) ?_
      rw [add_mul, add_mul, ← add_assoc, ← add_assoc, ← add_mul, ← mul_comm (g i),
        modByMonic_add_div, add_assoc, mul_right_comm (_ /ₘ g j),
        ← add_mul, add_comm (_ * g j) (_ %ₘ g j), mul_comm (_ /ₘ g j),
        modByMonic_add_div, mul_assoc, mul_assoc, ← mul_add,
        add_comm, hab j hj, mul_one]

/-- Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `s`.
Then `f` can be written in the form `(∏ i ∈ s, g i) * (q + ∑ i ∈ s, r i / g i)`
in at most one way, where `degree (r i) < degree (g i)` and the denominator cancels formally.
See `eq_quo_mul_prod_add_sum_rem_mul_prod` for the existence of such a representation. -/
theorem quo_mul_prod_add_sum_rem_mul_prod_unique {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j))
    {q₁ q₂ : R[X]} {r₁ r₂ : ι → R[X]}
    (hr₁ : ∀ i ∈ s, (r₁ i).degree < (g i).degree) (hr₂ : ∀ i ∈ s, (r₂ i).degree < (g i).degree)
    (hf : q₁ * (∏ i ∈ s, g i) + ∑ i ∈ s, r₁ i * (∏ k ∈ s.erase i, g k) =
      q₂ * (∏ i ∈ s, g i) + ∑ i ∈ s, r₂ i * (∏ k ∈ s.erase i, g k)) :
    q₁ = q₂ ∧ ∀ i ∈ s, r₁ i = r₂ i := by
  induction s using Finset.cons_induction with
  | empty => simpa using hf
  | cons i s hi ih =>
    rw [Finset.forall_mem_cons] at hg hr₁ hr₂
    have cop : IsCoprime (g i) (∏ i ∈ s, g i) := by
      clear *-hgg
      induction s using Finset.cons_induction with
      | empty => simp [isCoprime_one_right]
      | cons j s hj ih =>
        rw [Finset.prod_cons, IsCoprime.mul_right_iff]
        refine ⟨hgg (by simp) (by simp) fun hij => hi (by simp [hij]), ih ?_ ?_⟩
        · exact mt Finset.mem_cons_of_mem hi
        · exact hgg.mono (SetLike.coe_mono (Finset.cons_subset_cons.2 (Finset.subset_cons hj)))
    rw [Finset.prod_cons, Finset.sum_cons, Finset.sum_cons, Finset.erase_cons] at hf
    have hjs {j : ι} (hj : j ∈ s) : i ≠ j := fun hij => hi (hij ▸ hj)
    simp +contextual only [Finset.erase_cons_of_ne hi (hjs _),
      Finset.prod_cons, ← mul_left_comm (g i), ← Finset.mul_sum] at hf
    rw [add_left_comm, ← mul_add, add_left_comm, ← mul_add] at hf
    rw [← sub_eq_zero, add_sub_add_comm, ← sub_mul, ← mul_sub,
      ← neg_sub, neg_mul, neg_add_eq_sub, sub_eq_zero] at hf
    have hgid : g i ∣ r₂ i - r₁ i := cop.dvd_of_dvd_mul_right (hf ▸ dvd_mul_right _ _)
    rw [add_sub_add_comm, ← sub_mul, mul_add, ← mul_assoc,
      ← eq_sub_iff_add_eq', ← sub_mul, ← Finset.sum_sub_distrib] at hf
    simp only [← sub_mul] at hf
    have hpgd : ∏ i ∈ s, g i ∣ _ := cop.symm.dvd_of_dvd_mul_left (hf.symm ▸ dvd_mul_left _ _)
    have hdr : (r₂ i - r₁ i).degree < (g i).degree :=
      (degree_sub_le (r₂ i) (r₁ i)).trans_lt (max_lt hr₂.1 hr₁.1)
    have hr0 : r₂ i - r₁ i = 0 := (hg.1.not_dvd_of_degree_lt · hdr).mtr hgid
    have hpm : (∏ i ∈ s, g i).Monic := monic_prod_of_monic s g hg.2
    have hdp : (∑ i ∈ s, (r₁ i - r₂ i) * ∏ k ∈ s.erase i, g k).degree < (∏ i ∈ s, g i).degree := by
      refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff ?_).2 ?_)
      · rw [bot_lt_iff_ne_bot, degree_ne_bot]
        exact hpm.ne_zero_of_polynomial_ne fun h : r₂ i - r₁ i = g i => lt_irrefl _ (h ▸ hdr)
      · intro j hj
        rw [← Finset.mul_prod_erase s g hj, mul_comm (g j), (hg.2 j hj).degree_mul]
        refine (degree_mul_le (r₁ j - r₂ j) (∏ k ∈ s.erase j, g k)).trans_lt ?_
        have dnb : (∏ k ∈ s.erase j, g k).degree ≠ ⊥ := by
          rw [degree_ne_bot]
          exact (monic_prod_of_monic _ g
            fun j hj => hg.2 j (Finset.mem_of_mem_erase hj)).ne_zero_of_polynomial_ne
            fun h : r₂ i - r₁ i = g i => lt_irrefl _ (h ▸ hdr)
        rw [add_comm, WithBot.add_lt_add_iff_left dnb]
        exact (degree_sub_le (r₁ j) (r₂ j)).trans_lt (max_lt (hr₁.2 j hj) (hr₂.2 j hj))
    have hp0 : ∑ i ∈ s, (r₁ i - r₂ i) * ∏ k ∈ s.erase i, g k = 0 :=
      (hpm.not_dvd_of_degree_lt · hdp).mtr hpgd
    rw [hr0, hp0, mul_zero, zero_sub, neg_mul, eq_comm, neg_eq_zero,
      ← mul_rotate, (hpm.mul hg.1).mul_right_eq_zero_iff] at hf
    simp only [sub_mul, Finset.sum_sub_distrib] at hp0
    rw [sub_eq_zero] at hf hr0 hp0
    obtain ⟨-, hrr⟩ := ih hg.2 (hgg.mono (SetLike.coe_mono (Finset.subset_cons hi)))
      hr₁.2 hr₂.2 congr($hf * ∏ i ∈ s, g i + $hp0)
    exact ⟨hf, (Finset.forall_mem_cons hi (fun j => r₁ j = r₂ j)).2 ⟨hr0.symm, hrr⟩⟩

/-- Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `s`,
and for each `g i` let `n i` be a natural number. Then `f` can be written in the form
`(∏ i ∈ s, g i ^ n i) * (q + ∑ i ∈ s, ∑ j : Fin (n i), r i j / g i ^ (j + 1))`, where
`degree (r i j) < degree (g i)` and the denominator cancels formally.
See `quo_mul_prod_pow_add_sum_rem_mul_prod_pow_unique` for the uniqueness of this representation. -/
theorem eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow [Nontrivial R] {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (f : R[X]) {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
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

/-- Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `s`,
and for each `g i` let `n i` be a natural number. Then `f` can be written in the form
`(∏ i ∈ s, g i ^ n i) * (q + ∑ i ∈ s, ∑ j : Fin (n i), r i j / g i ^ (j + 1))`
in at most one way, where `degree (r i j) < degree (g i)` and the denominator cancels formally.
See `eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow` for the existence of such a representation. -/
theorem quo_mul_prod_pow_add_sum_rem_mul_prod_pow_unique {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j)) {n : ι → ℕ}
    {q₁ q₂ : R[X]} {r₁ r₂ : (i : ι) → Fin (n i) → R[X]}
    (hr₁ : ∀ i ∈ s, ∀ j, (r₁ i j).degree < (g i).degree)
    (hr₂ : ∀ i ∈ s, ∀ j, (r₂ i j).degree < (g i).degree)
    (hf : q₁ * (∏ i ∈ s, g i ^ n i) +
        ∑ i ∈ s, ∑ j, r₁ i j * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ n k =
      q₂ * (∏ i ∈ s, g i ^ n i) +
        ∑ i ∈ s, ∑ j, r₂ i j * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ n k) :
    q₁ = q₂ ∧ ∀ i ∈ s, r₁ i = r₂ i := by
  nontriviality R
  simp only [← Finset.sum_mul] at hf
  have hrd {r : (i : ι) → Fin (n i) → R[X]} (hr : ∀ i ∈ s, ∀ j, (r i j).degree < (g i).degree)
      (i : ι) (hi : i ∈ s) : (∑ j, r i j * g i ^ j.1).degree < (g i ^ n i).degree := by
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff ?_).2 fun j _ => ?_)
    · rw [bot_lt_iff_ne_bot, degree_ne_bot]
      exact ((hg i hi).pow (n i)).ne_zero
    · refine (degree_mul_le _ _).trans_lt ?_
      rw [degree_eq_natDegree ((hg i hi).pow j.1).ne_zero, (hg i hi).natDegree_pow,
        degree_eq_natDegree ((hg i hi).pow (n i)).ne_zero, (hg i hi).natDegree_pow]
      conv_rhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 j.neZero.ne)]
      rw [Nat.add_one_mul, Nat.add_comm, Nat.cast_add, ← degree_eq_natDegree (hg i hi).ne_zero]
      refine WithBot.add_lt_add_of_lt_of_le (WithBot.natCast_ne_bot _) (hr i hi j) ?_
      exact Nat.cast_le.2 (Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt j.isLt))
  obtain ⟨hq, hr⟩ := quo_mul_prod_add_sum_rem_mul_prod_unique
    (fun i hi => (hg i hi).pow (n i)) (hgg.imp fun i j hij => hij.pow) (hrd hr₁) (hrd hr₂) hf
  refine ⟨hq, fun i hi => ?_⟩
  exact (quo_mul_pow_add_sum_rem_mul_pow_unique (hg i hi) (hr₁ i hi) (hr₂ i hi)
    (congrArg (0 * g i ^ n i + ·) (hr i hi))).2

end ManyDenominators

end Mul

section Div
variable {K : Type*} [CommRing K] [Algebra R[X] K]

/-- Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `s`,
and for each `g i` let `n i` be a natural number.
Let `K` be an algebra over `R[X]` containing inverses `gi i` for each `g i`.
Then a fraction of the form `f * ∏ i ∈ s, gi i ^ n i` can be rewritten as
`q + ∑ i ∈ s, ∑ j : Fin (n i), r i j * gi i ^ (j + 1)`, where `degree (r i j) < degree (g i)`.
See `mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` for the
uniqueness of this representation. -/
theorem mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse [Nontrivial R] {ι : Type*}
    {s : Finset ι} (f : R[X]) {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
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

/-- Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `s`,
and for each `g i` let `n i` be a natural number.
Let `K` be an algebra over `R[X]` containing inverses `gi i` for each `g i`.
Then a fraction of the form `f * ∏ i ∈ s, gi i ^ n i` can be rewritten as
`q + ∑ i ∈ s, ∑ j : Fin (n i), r i j * gi i ^ (j + 1)`
in at most one way, where `degree (r i j) < degree (g i)`.
See `mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` for the
existence of such a representation. -/
theorem quo_add_sum_rem_mul_pow_inverse_unique [FaithfulSMul R[X] K] {ι : Type*}
    {s : Finset ι} {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j))
    {n : ι → ℕ} {gi : ι → K} (hgi : ∀ i ∈ s, gi i * algebraMap R[X] K (g i) = 1)
    {q₁ q₂ : R[X]} {r₁ r₂ : (i : ι) → Fin (n i) → R[X]}
    (hr₁ : ∀ i ∈ s, ∀ j, (r₁ i j).degree < (g i).degree)
    (hr₂ : ∀ i ∈ s, ∀ j, (r₂ i j).degree < (g i).degree)
    (hf : algebraMap R[X] K q₁ + ∑ i ∈ s, ∑ j, algebraMap R[X] K (r₁ i j) * gi i ^ (j.1 + 1) =
      algebraMap R[X] K q₂ + ∑ i ∈ s, ∑ j, algebraMap R[X] K (r₂ i j) * gi i ^ (j.1 + 1)) :
    q₁ = q₂ ∧ ∀ i ∈ s, r₁ i = r₂ i := by
  classical
  suffices hff : ∀ {q : R[X]} {r : (i : ι) → Fin (n i) → R[X]},
      (algebraMap R[X] K q + ∑ i ∈ s, ∑ j,
        algebraMap R[X] K (r i j) * gi i ^ (j.1 + 1)) * ∏ i ∈ s, algebraMap R[X] K (g i) ^ n i =
      algebraMap R[X] K (q * ∏ i ∈ s, g i ^ n i + ∑ i ∈ s,
        ∑ j : Fin (n i), r i j.rev * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ n k) by
    apply_fun (· * ∏ i ∈ s, algebraMap R[X] K (g i) ^ n i) at hf
    rw [hff, hff, (FaithfulSMul.algebraMap_injective R[X] K).eq_iff] at hf
    obtain ⟨hq, hr⟩ := quo_mul_prod_pow_add_sum_rem_mul_prod_pow_unique hg hgg
      (fun i hi j => hr₁ i hi j.rev) (fun i hi j => hr₂ i hi j.rev) hf
    exact ⟨hq, fun i hi => funext fun j => j.rev_rev ▸ congrFun (hr i hi) j.rev⟩
  intro q r
  simp_rw [add_mul, Finset.sum_mul, map_add, map_sum, map_mul, map_prod, map_pow]
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun i hi => ?_)
  refine (Equiv.sum_comp Fin.revPerm _).symm.trans (Fintype.sum_congr _ _ fun j => ?_)
  rw [Fin.revPerm_apply, ← Finset.mul_prod_erase s _ hi, ← mul_assoc,
    mul_assoc (algebraMap R[X] K (r i j.rev))]
  refine congrArg (algebraMap R[X] K (r i j.rev) * · * _) ?_
  rw [← mul_one (gi i ^ (j.rev.1 + 1)), ← @one_pow K _ j, ← hgi i hi,
    mul_pow, ← mul_assoc, ← pow_add, Fin.val_rev, Nat.add_right_comm, Nat.add_assoc,
    Nat.sub_add_cancel (by lia), mul_right_comm, ← mul_pow, hgi i hi, one_pow, one_mul]

end Div

section Field

variable (K : Type*) [Field K] [Algebra R[X] K] [FaithfulSMul R[X] K]

section NDenominators

open algebraMap

/-- Let `R` be an integral domain and `f : R[X]`. Let `s` be a finite index set.
Then a fraction of the form `f / ∏ i ∈ s, g i` evaluated in a field `K` containing `R[X]`
can be rewritten as `q + ∑ i ∈ s, r i / g i`, where
`degree (r i) < degree (g i)`, provided that the `g i` are monic and pairwise coprime.
See `quo_add_sum_rem_div_unique` for the uniqueness of this representation. -/
theorem div_prod_eq_quo_add_sum_rem_div (f : R[X]) {ι : Type*} {g : ι → R[X]} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).Monic) (hcop : Set.Pairwise ↑s fun i j => IsCoprime (g i) (g j)) :
    ∃ (q : R[X]) (r : ι → R[X]),
      (∀ i ∈ s, (r i).degree < (g i).degree) ∧
        ((↑f : K) / ∏ i ∈ s, ↑(g i)) = ↑q + ∑ i ∈ s, (r i : K) / (g i : K) := by
  have : Nontrivial R :=
    have : Nontrivial R[X] := Module.nontrivial R[X] K
    Module.nontrivial R R[X]
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

/-- Let `R` be an integral domain and `f : R[X]`. Let `s` be a finite index set.
Then a fraction of the form `f / ∏ i ∈ s, g i` evaluated in a field `K` containing `R[X]`
can be rewritten as `q + ∑ i ∈ s, r i / g i` in at most one way, where
`degree (r i) < degree (g i)`, provided that the `g i` are monic and pairwise coprime.
See `div_prod_eq_quo_add_sum_rem_div` for the existence of such a representation. -/
theorem quo_add_sum_rem_div_unique {ι : Type*} {g : ι → R[X]} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).Monic) (hcop : Set.Pairwise ↑s fun i j => IsCoprime (g i) (g j))
    {q₁ q₂ : R[X]} {r₁ r₂ : ι → R[X]}
    (hr₁ : ∀ i ∈ s, (r₁ i).degree < (g i).degree)
    (hr₂ : ∀ i ∈ s, (r₂ i).degree < (g i).degree)
    (hf : ↑q₁ + ∑ i ∈ s, (r₁ i : K) / (g i : K) = ↑q₂ + ∑ i ∈ s, (r₂ i : K) / (g i : K)) :
    q₁ = q₂ ∧ ∀ i ∈ s, r₁ i = r₂ i := by
  have : Nontrivial R :=
    have : Nontrivial R[X] := Module.nontrivial R[X] K
    Module.nontrivial R R[X]
  have hgi (i : ι) (hi : i ∈ s) : (algebraMap R[X] K (g i))⁻¹ * algebraMap R[X] K (g i) = 1 :=
    inv_mul_cancel₀ (by simpa using (hg i hi).ne_zero)
  refine (quo_add_sum_rem_mul_pow_inverse_unique (n := fun _ => 1)
      hg hcop hgi (fun i hi _ => hr₁ i hi) (fun i hi _ => hr₂ i hi) ?_).imp_right
      fun h i hi => congrFun (h i hi) 0
  simp_rw [Fin.sum_univ_one, Fin.val_zero, zero_add, pow_one, ← div_eq_mul_inv]
  exact hf

end NDenominators

section TwoDenominators

open scoped algebraMap

/-- Let `R` be an integral domain and `f, g₁, g₂ : R[X]`. Let `g₁` and `g₂` be monic and coprime.
Then `∃ q, r₁, r₂ : R[X]` such that `f / (g₁ * g₂) = q + r₁ / g₁ + r₂ / g₂` and
`degree rᵢ < degree gᵢ`, where the equality is taken in a field `K` containing `R[X]`.
See `quo_add_rem_div_add_rem_div_unique` for the uniqueness of this representation. -/
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

/-- Let `R` be an integral domain and `f, g₁, g₂ : R[X]`. Let `g₁` and `g₂` be monic and coprime.
Then the representation of `f / (g₁ * g₂)` as `q + r₁ / g₁ + r₂ / g₂` for `q r₁ r₂ : R[X]` and
`degree rᵢ < degree gᵢ` is unique, where the equality is taken in a field `K` containing `R[X]`.
See `div_eq_quo_add_rem_div_add_rem_div` for the existence of such a representation. -/
theorem quo_add_rem_div_add_rem_div_unique {g₁ g₂ : R[X]} (hg₁ : g₁.Monic)
    (hg₂ : g₂.Monic) (hcoprime : IsCoprime g₁ g₂)
    {q₁ q₂ r₁₁ r₁₂ r₂₁ r₂₂ : R[X]}
    (hr₁₁ : r₁₁.degree < g₁.degree) (hr₁₂ : r₁₂.degree < g₁.degree)
    (hr₂₁ : r₂₁.degree < g₂.degree) (hr₂₂ : r₂₂.degree < g₂.degree)
    (hf : (↑q₁ + ↑r₁₁ / ↑g₁ + ↑r₂₁ / ↑g₂ : K) = ↑q₂ + ↑r₁₂ / ↑g₁ + ↑r₂₂ / ↑g₂) :
    q₁ = q₂ ∧ r₁₁ = r₁₂ ∧ r₂₁ = r₂₂ := by
  let g : Bool → R[X] := Bool.rec g₂ g₁
  let r₁ : Bool → R[X] := Bool.rec r₂₁ r₁₁
  let r₂ : Bool → R[X] := Bool.rec r₂₂ r₁₂
  have hg (i : Bool) (_ : i ∈ Finset.univ) : (g i).Monic := Bool.rec hg₂ hg₁ i
  have hcoprime : Set.Pairwise (Finset.univ : Finset Bool) fun i j => IsCoprime (g i) (g j) := by
    simp [g, Set.pairwise_insert, hcoprime, hcoprime.symm]
  have hr₁ (i : Bool) (_ : i ∈ Finset.univ) : (r₁ i).degree < (g i).degree := Bool.rec hr₂₁ hr₁₁ i
  have hr₂ (i : Bool) (_ : i ∈ Finset.univ) : (r₂ i).degree < (g i).degree := Bool.rec hr₂₂ hr₁₂ i
  refine (quo_add_sum_rem_div_unique K hg hcoprime hr₁ hr₂ ?_).imp_right fun h =>
    ⟨h true (Finset.mem_univ true), h false (Finset.mem_univ false)⟩
  simpa [g, r₁, r₂, add_assoc] using hf

end TwoDenominators

end Field

end Polynomial
