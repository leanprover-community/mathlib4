/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.LocalRing

#align_import data.polynomial.expand from "leanprover-community/mathlib"@"bbeb185db4ccee8ed07dc48449414ebfa39cb821"

/-!
# Expand a polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

## Main definitions

* `Polynomial.expand R p f`: expand the polynomial `f` with coefficients in a
  commutative semiring `R` by a factor of p, so `expand R p (∑ aₙ xⁿ)` is `∑ aₙ xⁿᵖ`.
* `Polynomial.contract p f`: the opposite of `expand`, so it sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`.

-/


universe u v w

open Polynomial

open Finset

namespace Polynomial

section CommSemiring

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`. -/
noncomputable def expand : R[X] →ₐ[R] R[X] :=
  { (eval₂RingHom C (X ^ p) : R[X] →+* R[X]) with commutes' := fun _ => eval₂_C _ _ }
#align polynomial.expand Polynomial.expand

theorem coe_expand : (expand R p : R[X] → R[X]) = eval₂ C (X ^ p) :=
  rfl
#align polynomial.coe_expand Polynomial.coe_expand

variable {R}

theorem expand_eq_comp_X_pow {f : R[X]} : expand R p f = f.comp (X ^ p) := rfl

theorem expand_eq_sum {f : R[X]} : expand R p f = f.sum fun e a => C a * (X ^ p) ^ e := by
  simp [expand, eval₂]
#align polynomial.expand_eq_sum Polynomial.expand_eq_sum

@[simp]
theorem expand_C (r : R) : expand R p (C r) = C r :=
  eval₂_C _ _
set_option linter.uppercaseLean3 false in
#align polynomial.expand_C Polynomial.expand_C

@[simp]
theorem expand_X : expand R p X = X ^ p :=
  eval₂_X _ _
set_option linter.uppercaseLean3 false in
#align polynomial.expand_X Polynomial.expand_X

@[simp]
theorem expand_monomial (r : R) : expand R p (monomial q r) = monomial (q * p) r := by
  simp_rw [← smul_X_eq_monomial, AlgHom.map_smul, AlgHom.map_pow, expand_X, mul_comm, pow_mul]
#align polynomial.expand_monomial Polynomial.expand_monomial

theorem expand_expand (f : R[X]) : expand R p (expand R q f) = expand R (p * q) f :=
  Polynomial.induction_on f (fun r => by simp_rw [expand_C])
    (fun f g ihf ihg => by simp_rw [AlgHom.map_add, ihf, ihg]) fun n r _ => by
    simp_rw [AlgHom.map_mul, expand_C, AlgHom.map_pow, expand_X, AlgHom.map_pow, expand_X, pow_mul]
#align polynomial.expand_expand Polynomial.expand_expand

theorem expand_mul (f : R[X]) : expand R (p * q) f = expand R p (expand R q f) :=
  (expand_expand p q f).symm
#align polynomial.expand_mul Polynomial.expand_mul

@[simp]
theorem expand_zero (f : R[X]) : expand R 0 f = C (eval 1 f) := by simp [expand]
#align polynomial.expand_zero Polynomial.expand_zero

@[simp]
theorem expand_one (f : R[X]) : expand R 1 f = f :=
  Polynomial.induction_on f (fun r => by rw [expand_C])
    (fun f g ihf ihg => by rw [AlgHom.map_add, ihf, ihg]) fun n r _ => by
    rw [AlgHom.map_mul, expand_C, AlgHom.map_pow, expand_X, pow_one]
#align polynomial.expand_one Polynomial.expand_one

theorem expand_pow (f : R[X]) : expand R (p ^ q) f = (expand R p)^[q] f :=
  Nat.recOn q (by rw [pow_zero, expand_one, Function.iterate_zero, id]) fun n ih => by
    rw [Function.iterate_succ_apply', pow_succ', expand_mul, ih]
#align polynomial.expand_pow Polynomial.expand_pow

theorem derivative_expand (f : R[X]) : Polynomial.derivative (expand R p f) =
    expand R p (Polynomial.derivative f) * (p * (X ^ (p - 1) : R[X])) := by
  rw [coe_expand, derivative_eval₂_C, derivative_pow, C_eq_natCast, derivative_X, mul_one]
#align polynomial.derivative_expand Polynomial.derivative_expand

theorem coeff_expand {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
    (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0 := by
  simp only [expand_eq_sum]
  simp_rw [coeff_sum, ← pow_mul, C_mul_X_pow_eq_monomial, coeff_monomial, sum]
  split_ifs with h
  · rw [Finset.sum_eq_single (n / p), Nat.mul_div_cancel' h, if_pos rfl]
    · intro b _ hb2
      rw [if_neg]
      intro hb3
      apply hb2
      rw [← hb3, Nat.mul_div_cancel_left b hp]
    · intro hn
      rw [not_mem_support_iff.1 hn]
      split_ifs <;> rfl
  · rw [Finset.sum_eq_zero]
    intro k _
    rw [if_neg]
    exact fun hkn => h ⟨k, hkn.symm⟩
#align polynomial.coeff_expand Polynomial.coeff_expand

@[simp]
theorem coeff_expand_mul {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
    (expand R p f).coeff (n * p) = f.coeff n := by
  rw [coeff_expand hp, if_pos (dvd_mul_left _ _), Nat.mul_div_cancel _ hp]
#align polynomial.coeff_expand_mul Polynomial.coeff_expand_mul

@[simp]
theorem coeff_expand_mul' {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
    (expand R p f).coeff (p * n) = f.coeff n := by rw [mul_comm, coeff_expand_mul hp]
#align polynomial.coeff_expand_mul' Polynomial.coeff_expand_mul'

/-- Expansion is injective. -/
theorem expand_injective {n : ℕ} (hn : 0 < n) : Function.Injective (expand R n) := fun g g' H =>
  ext fun k => by rw [← coeff_expand_mul hn, H, coeff_expand_mul hn]
#align polynomial.expand_injective Polynomial.expand_injective

theorem expand_inj {p : ℕ} (hp : 0 < p) {f g : R[X]} : expand R p f = expand R p g ↔ f = g :=
  (expand_injective hp).eq_iff
#align polynomial.expand_inj Polynomial.expand_inj

theorem expand_eq_zero {p : ℕ} (hp : 0 < p) {f : R[X]} : expand R p f = 0 ↔ f = 0 :=
  (expand_injective hp).eq_iff' (map_zero _)
#align polynomial.expand_eq_zero Polynomial.expand_eq_zero

theorem expand_ne_zero {p : ℕ} (hp : 0 < p) {f : R[X]} : expand R p f ≠ 0 ↔ f ≠ 0 :=
  (expand_eq_zero hp).not
#align polynomial.expand_ne_zero Polynomial.expand_ne_zero

theorem expand_eq_C {p : ℕ} (hp : 0 < p) {f : R[X]} {r : R} : expand R p f = C r ↔ f = C r := by
  rw [← expand_C, expand_inj hp, expand_C]
set_option linter.uppercaseLean3 false in
#align polynomial.expand_eq_C Polynomial.expand_eq_C

theorem natDegree_expand (p : ℕ) (f : R[X]) : (expand R p f).natDegree = f.natDegree * p := by
  rcases p.eq_zero_or_pos with hp | hp
  · rw [hp, coe_expand, pow_zero, mul_zero, ← C_1, eval₂_hom, natDegree_C]
  by_cases hf : f = 0
  · rw [hf, AlgHom.map_zero, natDegree_zero, zero_mul]
  have hf1 : expand R p f ≠ 0 := mt (expand_eq_zero hp).1 hf
  rw [← WithBot.coe_eq_coe]
  convert (degree_eq_natDegree hf1).symm -- Porting note: was `rw [degree_eq_natDegree hf1]`
  symm
  refine le_antisymm ((degree_le_iff_coeff_zero _ _).2 fun n hn => ?_) ?_
  · rw [coeff_expand hp]
    split_ifs with hpn
    · rw [coeff_eq_zero_of_natDegree_lt]
      contrapose! hn
      erw [WithBot.coe_le_coe, ← Nat.div_mul_cancel hpn]
      exact Nat.mul_le_mul_right p hn
    · rfl
  · refine le_degree_of_ne_zero ?_
    erw [coeff_expand_mul hp, ← leadingCoeff]
    exact mt leadingCoeff_eq_zero.1 hf
#align polynomial.nat_degree_expand Polynomial.natDegree_expand

theorem leadingCoeff_expand {p : ℕ} {f : R[X]} (hp : 0 < p) :
    (expand R p f).leadingCoeff = f.leadingCoeff := by
  simp_rw [leadingCoeff, natDegree_expand, coeff_expand_mul hp]

theorem monic_expand_iff {p : ℕ} {f : R[X]} (hp : 0 < p) : (expand R p f).Monic ↔ f.Monic := by
  simp only [Monic, leadingCoeff_expand hp]

alias ⟨_, Monic.expand⟩ := monic_expand_iff
#align polynomial.monic.expand Polynomial.Monic.expand

theorem map_expand {p : ℕ} {f : R →+* S} {q : R[X]} :
    map f (expand R p q) = expand S p (map f q) := by
  by_cases hp : p = 0
  · simp [hp]
  ext
  rw [coeff_map, coeff_expand (Nat.pos_of_ne_zero hp), coeff_expand (Nat.pos_of_ne_zero hp)]
  split_ifs <;> simp_all
#align polynomial.map_expand Polynomial.map_expand

@[simp]
theorem expand_eval (p : ℕ) (P : R[X]) (r : R) : eval r (expand R p P) = eval (r ^ p) P := by
  refine Polynomial.induction_on P (fun a => by simp) (fun f g hf hg => ?_) fun n a _ => by simp
  rw [AlgHom.map_add, eval_add, eval_add, hf, hg]
#align polynomial.expand_eval Polynomial.expand_eval

@[simp]
theorem expand_aeval {A : Type*} [Semiring A] [Algebra R A] (p : ℕ) (P : R[X]) (r : A) :
    aeval r (expand R p P) = aeval (r ^ p) P := by
  refine Polynomial.induction_on P (fun a => by simp) (fun f g hf hg => ?_) fun n a _ => by simp
  rw [AlgHom.map_add, aeval_add, aeval_add, hf, hg]
#align polynomial.expand_aeval Polynomial.expand_aeval

/-- The opposite of `expand`: sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`. -/
noncomputable def contract (p : ℕ) (f : R[X]) : R[X] :=
  ∑ n ∈ range (f.natDegree + 1), monomial n (f.coeff (n * p))
#align polynomial.contract Polynomial.contract

theorem coeff_contract {p : ℕ} (hp : p ≠ 0) (f : R[X]) (n : ℕ) :
    (contract p f).coeff n = f.coeff (n * p) := by
  simp only [contract, coeff_monomial, sum_ite_eq', finset_sum_coeff, mem_range, not_lt,
    ite_eq_left_iff]
  intro hn
  apply (coeff_eq_zero_of_natDegree_lt _).symm
  calc
    f.natDegree < f.natDegree + 1 := Nat.lt_succ_self _
    _ ≤ n * 1 := by simpa only [mul_one] using hn
    _ ≤ n * p := mul_le_mul_of_nonneg_left (show 1 ≤ p from hp.bot_lt) (zero_le n)
#align polynomial.coeff_contract Polynomial.coeff_contract

theorem map_contract {p : ℕ} (hp : p ≠ 0) {f : R →+* S} {q : R[X]} :
    (q.contract p).map f = (q.map f).contract p := ext fun n ↦ by
  simp only [coeff_map, coeff_contract hp]

theorem contract_expand {f : R[X]} (hp : p ≠ 0) : contract p (expand R p f) = f := by
  ext
  simp [coeff_contract hp, coeff_expand hp.bot_lt, Nat.mul_div_cancel _ hp.bot_lt]
#align polynomial.contract_expand Polynomial.contract_expand

theorem contract_one {f : R[X]} : contract 1 f = f :=
  ext fun n ↦ by rw [coeff_contract one_ne_zero, mul_one]

section ExpChar

theorem expand_contract [CharP R p] [NoZeroDivisors R] {f : R[X]} (hf : Polynomial.derivative f = 0)
    (hp : p ≠ 0) : expand R p (contract p f) = f := by
  ext n
  rw [coeff_expand hp.bot_lt, coeff_contract hp]
  split_ifs with h
  · rw [Nat.div_mul_cancel h]
  · cases' n with n
    · exact absurd (dvd_zero p) h
    have := coeff_derivative f n
    rw [hf, coeff_zero, zero_eq_mul] at this
    cases' this with h'
    · rw [h']
    rename_i _ _ _ _ h'
    rw [← Nat.cast_succ, CharP.cast_eq_zero_iff R p] at h'
    exact absurd h' h
#align polynomial.expand_contract Polynomial.expand_contract

variable [ExpChar R p]

theorem expand_contract' [NoZeroDivisors R] {f : R[X]} (hf : Polynomial.derivative f = 0) :
    expand R p (contract p f) = f := by
  obtain _ | @⟨_, hprime, hchar⟩ := ‹ExpChar R p›
  · rw [expand_one, contract_one]
  · haveI := Fact.mk hchar; exact expand_contract p hf hprime.ne_zero

theorem expand_char (f : R[X]) : map (frobenius R p) (expand R p f) = f ^ p := by
  refine f.induction_on' (fun a b ha hb => ?_) fun n a => ?_
  · rw [AlgHom.map_add, Polynomial.map_add, ha, hb, add_pow_expChar]
  · rw [expand_monomial, map_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
      mul_pow, ← C.map_pow, frobenius_def]
    ring
#align polynomial.expand_char Polynomial.expand_char

theorem map_expand_pow_char (f : R[X]) (n : ℕ) :
    map (frobenius R p ^ n) (expand R (p ^ n) f) = f ^ p ^ n := by
  induction' n with _ n_ih
  · simp [RingHom.one_def]
  symm
  rw [pow_succ, pow_mul, ← n_ih, ← expand_char, pow_succ', RingHom.mul_def, ← map_map, mul_comm,
    expand_mul, ← map_expand]
#align polynomial.map_expand_pow_char Polynomial.map_expand_pow_char

end ExpChar

end CommSemiring

section rootMultiplicity

variable {R : Type u} [CommRing R] {p n : ℕ} [ExpChar R p] {f : R[X]} {r : R}

theorem rootMultiplicity_expand_pow :
    (expand R (p ^ n) f).rootMultiplicity r = p ^ n * f.rootMultiplicity (r ^ p ^ n) := by
  obtain rfl | h0 := eq_or_ne f 0; · simp
  obtain ⟨g, hg, ndvd⟩ := f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h0 (r ^ p ^ n)
  rw [dvd_iff_isRoot, ← eval_X (x := r), ← eval_pow, ← isRoot_comp, ← expand_eq_comp_X_pow] at ndvd
  conv_lhs => rw [hg, map_mul, map_pow, map_sub, expand_X, expand_C, map_pow, ← sub_pow_expChar_pow,
    ← pow_mul, mul_comm, rootMultiplicity_mul_X_sub_C_pow (expand_ne_zero (expChar_pow_pos R p n)
      |>.mpr <| right_ne_zero_of_mul <| hg ▸ h0), rootMultiplicity_eq_zero ndvd, zero_add]

theorem rootMultiplicity_expand :
    (expand R p f).rootMultiplicity r = p * f.rootMultiplicity (r ^ p) := by
  rw [← pow_one p, rootMultiplicity_expand_pow]

end rootMultiplicity

section IsDomain

variable (R : Type u) [CommRing R] [IsDomain R]

theorem isLocalRingHom_expand {p : ℕ} (hp : 0 < p) :
    IsLocalRingHom (↑(expand R p) : R[X] →+* R[X]) := by
  refine ⟨fun f hf1 => ?_⟩; norm_cast at hf1
  have hf2 := eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit hf1)
  rw [coeff_expand hp, if_pos (dvd_zero _), p.zero_div] at hf2
  rw [hf2, isUnit_C] at hf1; rw [expand_eq_C hp] at hf2; rwa [hf2, isUnit_C]
#align polynomial.is_local_ring_hom_expand Polynomial.isLocalRingHom_expand

variable {R}

theorem of_irreducible_expand {p : ℕ} (hp : p ≠ 0) {f : R[X]} (hf : Irreducible (expand R p f)) :
    Irreducible f :=
  let _ := isLocalRingHom_expand R hp.bot_lt
  of_irreducible_map (↑(expand R p)) hf
#align polynomial.of_irreducible_expand Polynomial.of_irreducible_expand

theorem of_irreducible_expand_pow {p : ℕ} (hp : p ≠ 0) {f : R[X]} {n : ℕ} :
    Irreducible (expand R (p ^ n) f) → Irreducible f :=
  Nat.recOn n (fun hf => by rwa [pow_zero, expand_one] at hf) fun n ih hf =>
    ih <| of_irreducible_expand hp <| by
      rw [pow_succ'] at hf
      rwa [expand_expand]
#align polynomial.of_irreducible_expand_pow Polynomial.of_irreducible_expand_pow

end IsDomain

end Polynomial
