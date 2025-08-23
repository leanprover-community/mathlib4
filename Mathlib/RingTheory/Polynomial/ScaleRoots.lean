/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Devon Tuma
-/
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.AdaptationNote

/-!
# Scaling the roots of a polynomial

This file defines `scaleRoots p s` for a polynomial `p` in one variable and a ring element `s` to
be the polynomial with root `r * s` for each root `r` of `p` and proves some basic results about it.
-/


variable {R S A K : Type*}

namespace Polynomial

section Semiring

variable [Semiring R] [Semiring S]

/-- `scaleRoots p s` is a polynomial with root `r * s` for each root `r` of `p`. -/
noncomputable def scaleRoots (p : R[X]) (s : R) : R[X] :=
  ∑ i ∈ p.support, monomial i (p.coeff i * s ^ (p.natDegree - i))

@[simp]
theorem coeff_scaleRoots (p : R[X]) (s : R) (i : ℕ) :
    (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i) := by
  simp +contextual [scaleRoots, coeff_monomial]

theorem coeff_scaleRoots_natDegree (p : R[X]) (s : R) :
    (scaleRoots p s).coeff p.natDegree = p.leadingCoeff := by
  rw [leadingCoeff, coeff_scaleRoots, tsub_self, pow_zero, mul_one]

@[simp]
theorem zero_scaleRoots (s : R) : scaleRoots 0 s = 0 := by
  ext
  simp

theorem scaleRoots_ne_zero {p : R[X]} (hp : p ≠ 0) (s : R) : scaleRoots p s ≠ 0 := by
  intro h
  have : p.coeff p.natDegree ≠ 0 := mt leadingCoeff_eq_zero.mp hp
  have : (scaleRoots p s).coeff p.natDegree = 0 :=
    congr_fun (congr_arg (coeff : R[X] → ℕ → R) h) p.natDegree
  rw [coeff_scaleRoots_natDegree] at this
  contradiction

theorem support_scaleRoots_le (p : R[X]) (s : R) : (scaleRoots p s).support ≤ p.support := by
  intro
  simpa using left_ne_zero_of_mul

theorem support_scaleRoots_eq (p : R[X]) {s : R} (hs : s ∈ nonZeroDivisors R) :
    (scaleRoots p s).support = p.support :=
  le_antisymm (support_scaleRoots_le p s)
    (by intro i
        simp only [coeff_scaleRoots, Polynomial.mem_support_iff]
        intro p_ne_zero ps_zero
        have := (pow_mem hs (p.natDegree - i)).2 _ ps_zero
        contradiction)

@[simp]
theorem degree_scaleRoots (p : R[X]) {s : R} : degree (scaleRoots p s) = degree p := by
  haveI := Classical.propDecidable
  by_cases hp : p = 0
  · rw [hp, zero_scaleRoots]
  refine le_antisymm (Finset.sup_mono (support_scaleRoots_le p s)) (degree_le_degree ?_)
  rw [coeff_scaleRoots_natDegree]
  intro h
  have := leadingCoeff_eq_zero.mp h
  contradiction

@[simp]
theorem natDegree_scaleRoots (p : R[X]) (s : R) : natDegree (scaleRoots p s) = natDegree p := by
  simp only [natDegree, degree_scaleRoots]

theorem monic_scaleRoots_iff {p : R[X]} (s : R) : Monic (scaleRoots p s) ↔ Monic p := by
  simp only [Monic, leadingCoeff, natDegree_scaleRoots, coeff_scaleRoots_natDegree]

theorem map_scaleRoots (p : R[X]) (x : R) (f : R →+* S) (h : f p.leadingCoeff ≠ 0) :
    (p.scaleRoots x).map f = (p.map f).scaleRoots (f x) := by
  ext
  simp [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ h]

@[simp]
lemma scaleRoots_C (r c : R) : (C c).scaleRoots r = C c := by
  ext; simp

@[simp]
lemma scaleRoots_one (p : R[X]) :
    p.scaleRoots 1 = p := by ext; simp

@[simp]
lemma scaleRoots_zero (p : R[X]) :
    p.scaleRoots 0 = p.leadingCoeff • X ^ p.natDegree := by
  ext n
  simp only [coeff_scaleRoots, tsub_eq_zero_iff_le, zero_pow_eq, mul_ite,
    mul_one, mul_zero, coeff_smul, coeff_X_pow, smul_eq_mul]
  split_ifs with h₁ h₂ h₂
  · subst h₂; rfl
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne h₁ (Ne.symm h₂))
  · exact (h₁ h₂.ge).elim
  · rfl

@[simp]
lemma one_scaleRoots (r : R) :
    (1 : R[X]).scaleRoots r = 1 := by ext; simp

end Semiring

section CommSemiring

variable [Semiring S] [CommSemiring R] [Semiring A] [Field K]

theorem scaleRoots_eval₂_mul_of_commute {p : S[X]} (f : S →+* A) (a : A) (s : S)
    (hsa : Commute (f s) a) (hf : ∀ s₁ s₂, Commute (f s₁) (f s₂)) :
    eval₂ f (f s * a) (scaleRoots p s) = f s ^ p.natDegree * eval₂ f a p := by
  calc
    _ = (scaleRoots p s).support.sum fun i =>
          f (coeff p i * s ^ (p.natDegree - i)) * (f s * a) ^ i := by
      simp [eval₂_eq_sum, sum_def]
    _ = p.support.sum fun i => f (coeff p i * s ^ (p.natDegree - i)) * (f s * a) ^ i :=
      (Finset.sum_subset (support_scaleRoots_le p s) fun i _hi hi' => by
        let this : coeff p i * s ^ (p.natDegree - i) = 0 := by simpa using hi'
        simp [this])
    _ = p.support.sum fun i : ℕ => f (p.coeff i) * f s ^ (p.natDegree - i + i) * a ^ i :=
      (Finset.sum_congr rfl fun i _hi => by
        simp_rw [f.map_mul, f.map_pow, pow_add, hsa.mul_pow, mul_assoc])
    _ = p.support.sum fun i : ℕ => f s ^ p.natDegree * (f (p.coeff i) * a ^ i) :=
      Finset.sum_congr rfl fun i hi => by
        rw [mul_assoc, ← map_pow, (hf _ _).left_comm, map_pow, tsub_add_cancel_of_le]
        exact le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)
    _ = f s ^ p.natDegree * eval₂ f a p := by simp [← Finset.mul_sum, eval₂_eq_sum, sum_def]

theorem scaleRoots_eval₂_mul {p : S[X]} (f : S →+* R) (r : R) (s : S) :
    eval₂ f (f s * r) (scaleRoots p s) = f s ^ p.natDegree * eval₂ f r p :=
  scaleRoots_eval₂_mul_of_commute f r s (mul_comm _ _) fun _ _ ↦ mul_comm _ _

theorem scaleRoots_eval₂_eq_zero {p : S[X]} (f : S →+* R) {r : R} {s : S} (hr : eval₂ f r p = 0) :
    eval₂ f (f s * r) (scaleRoots p s) = 0 := by rw [scaleRoots_eval₂_mul, hr, mul_zero]

theorem scaleRoots_aeval_eq_zero [Algebra R A] {p : R[X]} {a : A} {r : R} (ha : aeval a p = 0) :
    aeval (algebraMap R A r * a) (scaleRoots p r) = 0 := by
  rw [aeval_def, scaleRoots_eval₂_mul_of_commute, ← aeval_def, ha, mul_zero]
  · apply Algebra.commutes
  · intros; rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

theorem scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero {p : S[X]} {f : S →+* K}
    (hf : Function.Injective f) {r s : S} (hr : eval₂ f (f r / f s) p = 0)
    (hs : s ∈ nonZeroDivisors S) : eval₂ f (f r) (scaleRoots p s) = 0 := by
  -- if we don't specify the type with `(_ : S)`, the proof is much slower
  nontriviality S using Subsingleton.eq_zero (_ : S)
  convert @scaleRoots_eval₂_eq_zero _ _ _ _ p f _ s hr
  rw [← mul_div_assoc, mul_comm, mul_div_cancel_right₀]
  exact map_ne_zero_of_mem_nonZeroDivisors _ hf hs

theorem scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero [Algebra R K]
    (inj : Function.Injective (algebraMap R K)) {p : R[X]} {r s : R}
    (hr : aeval (algebraMap R K r / algebraMap R K s) p = 0) (hs : s ∈ nonZeroDivisors R) :
    aeval (algebraMap R K r) (scaleRoots p s) = 0 :=
  scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero inj hr hs

@[simp]
lemma scaleRoots_mul (p : R[X]) (r s) :
    p.scaleRoots (r * s) = (p.scaleRoots r).scaleRoots s := by
  ext; simp [mul_pow, mul_assoc]

/-- Multiplication and `scaleRoots` commute up to a power of `r`. The factor disappears if we
assume that the product of the leading coeffs does not vanish. See `Polynomial.mul_scaleRoots'`. -/
lemma mul_scaleRoots (p q : R[X]) (r : R) :
    r ^ (natDegree p + natDegree q - natDegree (p * q)) • (p * q).scaleRoots r =
      p.scaleRoots r * q.scaleRoots r := by
  ext n; simp only [coeff_scaleRoots, coeff_smul, smul_eq_mul]
  trans (∑ x ∈ Finset.antidiagonal n, coeff p x.1 * coeff q x.2) *
    r ^ (natDegree p + natDegree q - n)
  · rw [← coeff_mul]
    cases lt_or_ge (natDegree (p * q)) n with
    | inl h => simp only [coeff_eq_zero_of_natDegree_lt h, zero_mul, mul_zero]
    | inr h =>
      rw [mul_comm, mul_assoc, ← pow_add, add_comm, tsub_add_tsub_cancel natDegree_mul_le h]
  · rw [coeff_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    simp only [Finset.mem_antidiagonal, coeff_scaleRoots, Prod.forall]
    intro a b e
    cases lt_or_ge (natDegree p) a with
    | inl h => simp only [coeff_eq_zero_of_natDegree_lt h, zero_mul]
    | inr ha =>
      cases lt_or_ge (natDegree q) b with
      | inl h => simp only [coeff_eq_zero_of_natDegree_lt h, zero_mul, mul_zero]
      | inr hb =>
        simp only [← e, mul_assoc, mul_comm (r ^ (_ - a)), ← pow_add]
        rw [add_comm (_ - _), tsub_add_tsub_comm ha hb]

lemma mul_scaleRoots' (p q : R[X]) (r : R) (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    (p * q).scaleRoots r = p.scaleRoots r * q.scaleRoots r := by
  rw [← mul_scaleRoots, natDegree_mul' h, tsub_self, pow_zero, one_smul]

lemma mul_scaleRoots_of_noZeroDivisors (p q : R[X]) (r : R) [NoZeroDivisors R] :
    (p * q).scaleRoots r = p.scaleRoots r * q.scaleRoots r := by
  by_cases hp : p = 0; · simp [hp]
  by_cases hq : q = 0; · simp [hq]
  apply mul_scaleRoots'
  simp only [ne_eq, mul_eq_zero, leadingCoeff_eq_zero, hp, hq, or_self, not_false_eq_true]

lemma add_scaleRoots_of_natDegree_eq (p q : R[X]) (r : R) (h : natDegree p = natDegree q) :
    r ^ (natDegree p - natDegree (p + q)) • (p + q).scaleRoots r =
      p.scaleRoots r + q.scaleRoots r := by
  ext n; simp only [coeff_smul, coeff_scaleRoots, coeff_add, smul_eq_mul,
    mul_comm (r ^ _), ← h, ← add_mul]
  #adaptation_note /-- v4.7.0-rc1
  Previously `mul_assoc` was part of the `simp only` above, and this `rw` was not needed.
  but this now causes a max rec depth error. -/
  rw [mul_assoc, ← pow_add]
  cases lt_or_ge (natDegree (p + q)) n with
  | inl hn => simp only [← coeff_add, coeff_eq_zero_of_natDegree_lt hn, zero_mul]
  | inr hn =>
      rw [add_comm (_ - n), tsub_add_tsub_cancel (natDegree_add_le_of_degree_le le_rfl h.ge) hn]

lemma scaleRoots_dvd' (p q : R[X]) {r : R} (hr : IsUnit r)
    (hpq : p ∣ q) : p.scaleRoots r ∣ q.scaleRoots r := by
  obtain ⟨a, rfl⟩ := hpq
  rw [← ((hr.pow (natDegree p + natDegree a - natDegree (p * a))).map
    (algebraMap R R[X])).dvd_mul_left, ← Algebra.smul_def, mul_scaleRoots]
  exact dvd_mul_right (scaleRoots p r) (scaleRoots a r)

lemma scaleRoots_dvd (p q : R[X]) {r : R} [NoZeroDivisors R] (hpq : p ∣ q) :
    p.scaleRoots r ∣ q.scaleRoots r := by
  obtain ⟨a, rfl⟩ := hpq
  rw [mul_scaleRoots_of_noZeroDivisors]
  exact dvd_mul_right (scaleRoots p r) (scaleRoots a r)
alias _root_.Dvd.dvd.scaleRoots := scaleRoots_dvd

lemma scaleRoots_dvd_iff (p q : R[X]) {r : R} (hr : IsUnit r) :
    p.scaleRoots r ∣ q.scaleRoots r ↔ p ∣ q := by
  refine ⟨?_ ∘ scaleRoots_dvd' _ _ (hr.unit⁻¹).isUnit, scaleRoots_dvd' p q hr⟩
  simp [← scaleRoots_mul, scaleRoots_one]
alias _root_.IsUnit.scaleRoots_dvd_iff := scaleRoots_dvd_iff

lemma isCoprime_scaleRoots (p q : R[X]) (r : R) (hr : IsUnit r) (h : IsCoprime p q) :
    IsCoprime (p.scaleRoots r) (q.scaleRoots r) := by
  obtain ⟨a, b, e⟩ := h
  let s : R := ↑hr.unit⁻¹
  have : natDegree (a * p) = natDegree (b * q) := by
    apply natDegree_eq_of_natDegree_add_eq_zero
    rw [e, natDegree_one]
  use s ^ natDegree (a * p) • s ^ (natDegree a + natDegree p - natDegree (a * p)) • a.scaleRoots r
  use s ^ natDegree (a * p) • s ^ (natDegree b + natDegree q - natDegree (b * q)) • b.scaleRoots r
  simp only [s, smul_mul_assoc, ← mul_scaleRoots, smul_smul, mul_assoc,
    ← mul_pow, IsUnit.val_inv_mul, one_pow, mul_one, ← smul_add, one_smul, e, natDegree_one,
    one_scaleRoots, ← add_scaleRoots_of_natDegree_eq _ _ _ this, tsub_zero]
alias _root_.IsCoprime.scaleRoots := isCoprime_scaleRoots

end CommSemiring

end Polynomial
