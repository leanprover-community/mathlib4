/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.ConstantTermRelations
import Mathlib

set_option linter.minImports true

/-!
# Elementary single-character (two-charge) DvdK, DvdK-premise-free

The one-variable Duistermaat--van der Kallen input `DvdK1` is *elementary* on a
two-charge support: for `f = c₀ zᵖ + c₁ z⁻ⁿ` with `p,n > 0` the constant term of
`f^{p+n}` is a single, uncancellable multinomial term, hence nonzero.  This is
the coprime-pair seed (the balanced-face uniqueness seed): there is a UNIQUE balanced
composition `r = (n, p)` at `m = p+n`, so no cancellation can occur.
-/

open MvPolynomial Finset

namespace GMC2DvdKTwoCharge

/-- The pair charge vector. -/
def pairQ (p n : ℕ) : Fin 2 → ℤ := ![(p : ℤ), -(n : ℤ)]

/-- The unique balanced composition at `m = p+n`: `n` copies of the `+p` charge
and `p` copies of the `-n` charge. -/
def pairR (p n : ℕ) : Fin 2 → ℕ := ![n, p]

lemma pairR_mem (p n : ℕ) :
    pairR p n ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) (p + n) := by
  rw [Finset.mem_piAntidiag]
  refine ⟨?_, by intro i _; exact Finset.mem_univ i⟩
  simp [pairR, Fin.sum_univ_two, Nat.add_comm]

lemma pairR_balanced (p n : ℕ) :
    GMC2ConstantTermRelations.totalCharge (pairQ p n) (pairR p n) = 0 := by
  simp [GMC2ConstantTermRelations.totalCharge, pairQ, pairR, Fin.sum_univ_two]
  ring

/-- Uniqueness: the only balanced composition of size `p+n` is `pairR`. -/
lemma balanced_unique (p n : ℕ) (hp : 0 < p) (hn : 0 < n)
    (r : Fin 2 → ℕ)
    (hr : r ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) (p + n))
    (hbal : GMC2ConstantTermRelations.totalCharge (pairQ p n) r = 0) :
    r = pairR p n := by
  rw [Finset.mem_piAntidiag] at hr
  obtain ⟨hsum, -⟩ := hr
  simp only [Fin.sum_univ_two] at hsum
  simp only [GMC2ConstantTermRelations.totalCharge, pairQ, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hbal
  -- hsum : r 0 + r 1 = p + n ; hbal : r0*p - r1*n = 0
  have h0 : (r 0 : ℤ) * p = (r 1 : ℤ) * n := by linarith
  have hr0 : (r 0 : ℤ) = n := by
    have hcast : (r 0 : ℤ) + (r 1 : ℤ) = (p : ℤ) + n := by exact_mod_cast hsum
    nlinarith [h0, hcast, hp, hn]
  have hr1 : (r 1 : ℤ) = p := by
    have hcast : (r 0 : ℤ) + (r 1 : ℤ) = (p : ℤ) + n := by exact_mod_cast hsum
    linarith [hr0, hcast]
  funext i
  fin_cases i
  · simpa [pairR] using (by exact_mod_cast hr0 : r 0 = n)
  · simpa [pairR] using (by exact_mod_cast hr1 : r 1 = p)

/-- **Elementary two-charge DvdK.** For `p,n > 0` and nonzero coefficients, the
constant term of the `(p+n)`-th power of `c₀ zᵖ + c₁ z⁻ⁿ` is nonzero. -/
theorem exists_nonzero_ct_pair (p n : ℕ) (hp : 0 < p) (hn : 0 < n)
    (c : Fin 2 → ℂ) (hc : ∀ i, c i ≠ 0) :
    MvPolynomial.aeval c
      (GMC2ConstantTermRelations.constantTermRelation (pairQ p n) (p + n)) ≠ 0 := by
  rw [GMC2ConstantTermRelations.aeval_constantTermRelation]
  rw [Finset.sum_eq_single (pairR p n)]
  · rw [if_pos (pairR_balanced p n)]
    have hmult : (Nat.multinomial Finset.univ (pairR p n) : ℂ) ≠ 0 := by
      have : 0 < Nat.multinomial Finset.univ (pairR p n) := Nat.multinomial_pos _ _
      exact_mod_cast this.ne'
    have hprod : (∏ i, c i ^ (pairR p n) i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hc i))
    exact mul_ne_zero hmult hprod
  · intro r hr hne
    rw [if_neg]
    intro hbal
    exact hne (balanced_unique p n hp hn r hr hbal)
  · intro h; exact absurd (pairR_mem p n) h

/-- **Two-charge DvdK1 existential** (the coprime-pair seed, DvdK-premise-free):
the constant term is nonzero in the positive power `m = p+n`. -/
theorem dvdk1_pair (p n : ℕ) (hp : 0 < p) (hn : 0 < n)
    (c : Fin 2 → ℂ) (hc : ∀ i, c i ≠ 0) :
    ∃ m, 1 ≤ m ∧
      MvPolynomial.aeval c
        (GMC2ConstantTermRelations.constantTermRelation (pairQ p n) m) ≠ 0 :=
  ⟨p + n, by omega, exists_nonzero_ct_pair p n hp hn c hc⟩

/-- Swapped orientation: index 0 carries the NEGATIVE charge `-n`, index 1 the `+p`. -/
def pairQ' (p n : ℕ) : Fin 2 → ℤ := ![-(n : ℤ), (p : ℤ)]

/-- Unique balanced composition for the swapped pair: `p` copies of `-n`, `n` of `+p`. -/
def pairR' (p n : ℕ) : Fin 2 → ℕ := ![p, n]

lemma pairR'_mem (p n : ℕ) :
    pairR' p n ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) (p + n) := by
  rw [Finset.mem_piAntidiag]
  exact ⟨by simp [pairR', Fin.sum_univ_two], by intro i _; exact Finset.mem_univ i⟩

lemma pairR'_balanced (p n : ℕ) :
    GMC2ConstantTermRelations.totalCharge (pairQ' p n) (pairR' p n) = 0 := by
  simp [GMC2ConstantTermRelations.totalCharge, pairQ', pairR', Fin.sum_univ_two]; ring

lemma balanced_unique' (p n : ℕ) (hp : 0 < p) (hn : 0 < n)
    (r : Fin 2 → ℕ)
    (hr : r ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) (p + n))
    (hbal : GMC2ConstantTermRelations.totalCharge (pairQ' p n) r = 0) :
    r = pairR' p n := by
  rw [Finset.mem_piAntidiag] at hr
  obtain ⟨hsum, -⟩ := hr
  simp only [Fin.sum_univ_two] at hsum
  simp only [GMC2ConstantTermRelations.totalCharge, pairQ', Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hbal
  have h0 : (r 1 : ℤ) * p = (r 0 : ℤ) * n := by linarith
  have hcast : (r 0 : ℤ) + (r 1 : ℤ) = (p : ℤ) + n := by exact_mod_cast hsum
  have hr1 : (r 1 : ℤ) = n := by nlinarith [h0, hcast, hp, hn]
  have hr0 : (r 0 : ℤ) = p := by linarith [hr1, hcast]
  funext i; fin_cases i
  · simpa [pairR'] using (by exact_mod_cast hr0 : r 0 = p)
  · simpa [pairR'] using (by exact_mod_cast hr1 : r 1 = n)

/-- **Elementary two-charge DvdK, swapped orientation.** -/
theorem exists_nonzero_ct_pair' (p n : ℕ) (hp : 0 < p) (hn : 0 < n)
    (c : Fin 2 → ℂ) (hc : ∀ i, c i ≠ 0) :
    MvPolynomial.aeval c
      (GMC2ConstantTermRelations.constantTermRelation (pairQ' p n) (p + n)) ≠ 0 := by
  rw [GMC2ConstantTermRelations.aeval_constantTermRelation]
  rw [Finset.sum_eq_single (pairR' p n)]
  · rw [if_pos (pairR'_balanced p n)]
    have hmult : (Nat.multinomial Finset.univ (pairR' p n) : ℂ) ≠ 0 := by
      have : 0 < Nat.multinomial Finset.univ (pairR' p n) := Nat.multinomial_pos _ _
      exact_mod_cast this.ne'
    exact mul_ne_zero hmult (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hc i)))
  · intro r hr hne
    exact if_neg (fun hbal => hne (balanced_unique' p n hp hn r hr hbal))
  · intro h; exact absurd (pairR'_mem p n) h

end GMC2DvdKTwoCharge

