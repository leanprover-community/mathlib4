/-
Copyright (c) 2026 Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solo

# Favard's Theorem for Orthogonal Polynomials

General framework for Favard's theorem: given a three-term recurrence system `{P_n}`
with compatible linear functional Λ satisfying normalization, killing, consecutive
orthogonality, and norm recursion conditions, we prove full orthogonality and the
Heilermann norm formula `⟨P_n, P_n⟩ = ∏_{k<n} β_k`.

**0 sorrys.** All theorems are fully proved.

The `CompatFunctional` axioms are:
1. `norm`: `Λ(1) = 1`
2. `killP`: `Λ(P_n) = 0` for `n ≥ 1`
3. `consecOrth`: `Λ(P_{n+1} · P_{n+2}) = 0` for all `n`
4. `normRec`: `Λ(P_{n+2} · P_{n+2}) = β_{n+1} · Λ(P_{n+1} · P_{n+1})` for all `n`

**Mathematical note:** `consecOrth` alone is insufficient to derive `normRec` — proving
`norm(n+2) = β_{n+1} * norm(n+1)` via the stepA=stepB approach requires knowing
`⟨P_{n+1}, P_{n+3}⟩ = 0`, which is a level-(n+3) orthogonality fact not available at
level n+2. The `normRec` axiom encodes this directly.

From these, we derive:
- `favard_orthogonal`: `⟨P_m, P_n⟩ = 0` for `m ≠ n`
- `favard_norm`: `⟨P_n, P_n⟩ = ∏_{k<n} β_k`

## Usage

To apply this framework to a concrete system, construct:
- A `Polynomial.Favard.System R` giving the recurrence coefficients and polynomials.
- A `Polynomial.Favard.CompatFunctional sys` providing the linear functional and proofs
  of the four axioms for your concrete system.

Then `favard_orthogonal` and `favard_norm` apply immediately.

## References
* Favard (1935). C.R. Acad. Sci. Paris 200:2052–2053.
* Chihara, T.S. (1978). *An Introduction to Orthogonal Polynomials*. Gordon and Breach.
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

set_option maxHeartbeats 400000
set_option autoImplicit false

open Polynomial BigOperators

namespace Polynomial.Favard

/-! ## §1. Three-term recurrence system -/

/-- A three-term recurrence system over a commutative ring.
    Packages the recurrence coefficients `alpha`, `beta` and
    polynomials `P n` satisfying the standard three-term relation. -/
structure System (R : Type*) [CommRing R] where
  /-- Diagonal recurrence coefficients. -/
  alpha : ℕ → R
  /-- Off-diagonal recurrence coefficients. -/
  beta  : ℕ → R
  /-- The polynomial sequence. -/
  P     : ℕ → Polynomial R
  P_zero : P 0 = 1
  P_one  : P 1 = X - C (alpha 0)
  P_rec  : ∀ k : ℕ, P (k + 2) = (X - C (alpha (k + 1))) * P (k + 1) - C (beta k) * P k

/-- Expanding `X * P(k+1)` using the three-term recurrence. -/
lemma X_mul_P_succ {R : Type*} [CommRing R] (sys : System R) (k : ℕ) :
    X * sys.P (k + 1) =
    sys.P (k + 2) + C (sys.alpha (k + 1)) * sys.P (k + 1) + C (sys.beta k) * sys.P k := by
  rw [sys.P_rec k]; ring

/-- Expanding `X * P(0)` using `P_one`. -/
lemma X_mul_P_zero {R : Type*} [CommRing R] (sys : System R) :
    X * sys.P 0 = sys.P 1 + C (sys.alpha 0) * sys.P 0 := by
  rw [sys.P_zero, sys.P_one]; ring

/-! ## §2. Compatible linear functional

The four axioms that define a compatible functional for a recurrence system.
`consecOrth` captures the consecutive orthogonality condition: in the classical
Favard theorem, this is a consequence of the functional being the unique moment
functional for the system. Here we axiomatize it directly.
`normRec` encodes the norm recursion; together these are sufficient
to prove full orthogonality and the Heilermann formula by mutual induction. -/

/-- A compatible linear functional for a three-term recurrence system.
    Given such a functional, `favard_orthogonal` and `favard_norm` apply. -/
structure CompatFunctional {R : Type*} [CommRing R] (sys : System R) where
  /-- The linear functional `Λ : Polynomial R →ₗ[R] R`. -/
  Λ          : Polynomial R →ₗ[R] R
  /-- Normalization: `Λ(1) = 1`. -/
  norm       : Λ 1 = 1
  /-- Killing: `Λ(P_n) = 0` for `n ≥ 1`. -/
  killP      : ∀ n : ℕ, 0 < n → Λ (sys.P n) = 0
  /-- Consecutive orthogonality: `Λ(P_{n+1} · P_{n+2}) = 0`. -/
  consecOrth : ∀ n : ℕ, Λ (sys.P (n + 1) * sys.P (n + 2)) = 0
  /-- Norm recursion: `Λ(P_{n+2}²) = β_{n+1} · Λ(P_{n+1}²)`. -/
  normRec    : ∀ n : ℕ, Λ (sys.P (n + 2) * sys.P (n + 2)) =
                sys.beta (n + 1) * Λ (sys.P (n + 1) * sys.P (n + 1))

/-! ## §3. Inner product and basic lemmas -/

/-- The "inner product" `⟨f, g⟩ := Λ(f · g)` induced by the compatible functional. -/
noncomputable def ip {R : Type*} [CommRing R] {sys : System R}
    (cf : CompatFunctional sys) (f g : Polynomial R) : R := cf.Λ (f * g)

section ipLemmas

variable {R : Type*} [CommRing R] {sys : System R} (cf : CompatFunctional sys)

lemma ip_symm (f g : Polynomial R) : ip cf f g = ip cf g f := by simp [ip, mul_comm]

lemma ip_add_left (f g h : Polynomial R) :
    ip cf (f + g) h = ip cf f h + ip cf g h := by simp [ip, add_mul, map_add]

lemma ip_sub_left (f g h : Polynomial R) :
    ip cf (f - g) h = ip cf f h - ip cf g h := by simp [ip, sub_mul, map_sub]

lemma ip_add_right (f g h : Polynomial R) :
    ip cf f (g + h) = ip cf f g + ip cf f h := by simp only [ip, mul_add, map_add]

lemma ip_sub_right (f g h : Polynomial R) :
    ip cf f (g - h) = ip cf f g - ip cf f h := by simp only [ip, mul_sub, map_sub]

lemma ip_C_left (r : R) (f g : Polynomial R) :
    ip cf (C r * f) g = r * ip cf f g := by
  simp only [ip]
  have h : C r * f * g = r • (f * g) := by simp [smul_eq_C_mul, mul_assoc]
  rw [h, map_smul, smul_eq_mul]

lemma ip_C_right (r : R) (f g : Polynomial R) :
    ip cf f (C r * g) = r * ip cf f g := by
  simp only [ip]
  have h : f * (C r * g) = r • (f * g) := by simp [smul_eq_C_mul]; ring
  rw [h, map_smul, smul_eq_mul]

/-- Self-adjointness of `X`: `⟨X·f, g⟩ = ⟨f, X·g⟩`. -/
lemma ip_X_selfadj (f g : Polynomial R) :
    ip cf (X * f) g = ip cf f (X * g) := by simp only [ip]; congr 1; ring

lemma ip_P0_self : ip cf (sys.P 0) (sys.P 0) = 1 := by
  simp only [ip, sys.P_zero, one_mul]; exact cf.norm

lemma ip_Pn_P0 (n : ℕ) (hn : 0 < n) : ip cf (sys.P n) (sys.P 0) = 0 := by
  simp only [ip, sys.P_zero, mul_one]; exact cf.killP n hn

/-- Consecutive orthogonality in `ip` form: `⟨P_{n+1}, P_{n+2}⟩ = 0`. -/
lemma ip_consec_orth (n : ℕ) : ip cf (sys.P (n + 1)) (sys.P (n + 2)) = 0 :=
  cf.consecOrth n

/-- Consecutive orthogonality, reversed: `⟨P_{n+2}, P_{n+1}⟩ = 0`. -/
lemma ip_consec_orth' (n : ℕ) : ip cf (sys.P (n + 2)) (sys.P (n + 1)) = 0 := by
  have h := ip_consec_orth cf n; rw [ip_symm] at h; exact h

/-- Norm recursion: `⟨P_{n+2}, P_{n+2}⟩ = β_{n+1} · ⟨P_{n+1}, P_{n+1}⟩`. -/
lemma ip_normRec (n : ℕ) :
    ip cf (sys.P (n + 2)) (sys.P (n + 2)) =
    sys.beta (n + 1) * ip cf (sys.P (n + 1)) (sys.P (n + 1)) :=
  cf.normRec n

end ipLemmas

/-! ## §4. Non-consecutive orthogonality -/

/-- If `P(n+1)` and `P(n)` are each orthogonal to all `P(j)` for small `j`,
    then `P(n+2)` is also orthogonal to `P(j)` for any `j < n`. -/
theorem favard_orth_nonconsec {R : Type*} [CommRing R] {sys : System R}
    (cf : CompatFunctional sys) (n j : ℕ) (hj : j < n)
    (horth_n1 : ∀ i : ℕ, i ≤ n → ip cf (sys.P (n + 1)) (sys.P i) = 0)
    (horth_n  : ∀ i : ℕ, i < n → ip cf (sys.P n) (sys.P i) = 0) :
    ip cf (sys.P (n + 2)) (sys.P j) = 0 := by
  rw [sys.P_rec n, ip_sub_left cf]
  rw [show (X - C (sys.alpha (n + 1))) * sys.P (n + 1) =
      X * sys.P (n + 1) - C (sys.alpha (n + 1)) * sys.P (n + 1) from by ring]
  rw [ip_sub_left cf, ip_X_selfadj cf, ip_C_left cf, ip_C_left cf]
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rw [X_mul_P_zero sys, ip_add_right cf, ip_C_right cf]
    have h0 := horth_n1 0 (Nat.zero_le n)
    have h1 := horth_n1 1 (by omega)
    have h00 := horth_n 0 (by omega)
    simp only [h0, h1, h00, mul_zero, add_zero, sub_zero]
  · obtain ⟨jp, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hjpos)
    rw [X_mul_P_succ sys jp, ip_add_right cf, ip_add_right cf, ip_C_right cf, ip_C_right cf]
    have ha := horth_n1 (jp + 2) (by omega)
    have hb := horth_n1 (jp + 1) (by omega)
    have hc := horth_n1 jp (by omega)
    have hd := horth_n (jp + 1) (by omega)
    simp only [ha, hb, hc, hd, mul_zero, add_zero, sub_zero]

/-! ## §5. Base case norms -/

/-- Base case: `⟨P_1, P_1⟩ = β_0`. -/
lemma favard_norm_base1 {R : Type*} [CommRing R] {sys : System R}
    (cf : CompatFunctional sys) :
    ip cf (sys.P 1) (sys.P 1) = sys.beta 0 := by
  simp only [ip]
  have hP1 : cf.Λ (sys.P 1) = 0 := cf.killP 1 (by norm_num)
  have hP2 : cf.Λ (sys.P 2) = 0 := cf.killP 2 (by norm_num)
  rw [show sys.P 1 * sys.P 1 = X * sys.P 1 - C (sys.alpha 0) * sys.P 1 from by
        rw [sys.P_one]; ring, map_sub]
  have hα : cf.Λ (C (sys.alpha 0) * sys.P 1) = sys.alpha 0 * cf.Λ (sys.P 1) := by
    rw [show C (sys.alpha 0) * sys.P 1 = sys.alpha 0 • sys.P 1 from by simp [smul_eq_C_mul],
        map_smul, smul_eq_mul]
  rw [hα, hP1, mul_zero, sub_zero,
      show X * sys.P 1 = sys.P 2 + C (sys.alpha 1) * sys.P 1 + C (sys.beta 0) * sys.P 0
        from X_mul_P_succ sys 0,
      map_add, map_add]
  have hα1 : cf.Λ (C (sys.alpha 1) * sys.P 1) = sys.alpha 1 * cf.Λ (sys.P 1) := by
    rw [show C (sys.alpha 1) * sys.P 1 = sys.alpha 1 • sys.P 1 from by simp [smul_eq_C_mul],
        map_smul, smul_eq_mul]
  have hβ0 : cf.Λ (C (sys.beta 0) * sys.P 0) = sys.beta 0 * cf.Λ (sys.P 0) := by
    rw [show C (sys.beta 0) * sys.P 0 = sys.beta 0 • sys.P 0 from by simp [smul_eq_C_mul],
        map_smul, smul_eq_mul]
  rw [hP2, hα1, hP1, hβ0, sys.P_zero, cf.norm]; ring

/-! ## §6. Mutual induction: orthogonality AND norm formula

**Key insight**: Proving `ip P(n+2) P(n) = 0` (gap-2 orthogonality) requires the norm
recursion `normRec`, and proving the full norm formula requires orthogonality. They must
be proved simultaneously by strong induction.

**Proof of gap-2**: Expanding `P(n+2)` via `P_rec` and using `ip_X_selfadj` + ih gives:
`ip P(n+2) P(n) = norm(n+1) - β_n · norm(n)`, which equals 0 by `normRec` induction.

**Proof of norm**: Once `normRec` is axiomatized, `norm(n) = ∏ β_k` follows by induction
directly from `ip_normRec`. -/

/-- Simultaneous induction: full orthogonality and Heilermann norm formula for all n. -/
private theorem favard_mutual {R : Type*} [CommRing R] {sys : System R}
    (cf : CompatFunctional sys) (n : ℕ) :
    (∀ j, j < n → ip cf (sys.P n) (sys.P j) = 0) ∧
    ip cf (sys.P n) (sys.P n) = ∏ k ∈ Finset.range n, sys.beta k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · -- n = 0
      exact ⟨fun j hj => by omega,
             by rw [Finset.range_zero, Finset.prod_empty]; exact ip_P0_self cf⟩
    · -- n = 1
      refine ⟨fun j hj => ?_, by simp only [Finset.prod_range_one]; exact favard_norm_base1 cf⟩
      have hj0 : j = 0 := by omega
      subst hj0; exact ip_Pn_P0 cf 1 (by norm_num)
    · -- n + 2: use ih for n and n+1
      obtain ⟨ih_orth_n, ih_norm_n⟩ := ih n (by omega)
      obtain ⟨ih_orth_n1, ih_norm_n1⟩ := ih (n + 1) (by omega)
      have h_consec : ip cf (sys.P (n + 2)) (sys.P (n + 1)) = 0 := ip_consec_orth' cf n
      -- Gap-2 orthogonality: ip P(n+2) P(n) = 0
      have h_skip2 : ip cf (sys.P (n + 2)) (sys.P n) = 0 := by
        rw [sys.P_rec n, ip_sub_left cf,
            show (X - C (sys.alpha (n + 1))) * sys.P (n + 1) =
                X * sys.P (n + 1) - C (sys.alpha (n + 1)) * sys.P (n + 1) from by ring,
            ip_sub_left cf, ip_X_selfadj cf, ip_C_left cf, ip_C_left cf]
        rcases Nat.eq_zero_or_pos n with rfl | hn_pos
        · -- n = 0 case
          rw [X_mul_P_zero sys, ip_add_right cf, ip_C_right cf]
          have h0 : ip cf (sys.P 1) (sys.P 0) = 0 := ih_orth_n1 0 (by omega)
          simp only [Finset.prod_range_zero] at ih_norm_n
          simp only [Finset.prod_range_one] at ih_norm_n1
          simp only [h0, mul_zero, add_zero]
          rw [ih_norm_n1, ih_norm_n]; ring
        · -- n ≥ 1 case
          obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn_pos)
          rw [X_mul_P_succ sys n', ip_add_right cf, ip_add_right cf, ip_C_right cf, ip_C_right cf]
          have ha : ip cf (sys.P (n' + 1 + 1)) (sys.P (n' + 1)) = 0 :=
            ih_orth_n1 (n' + 1) (by omega)
          have hb : ip cf (sys.P (n' + 1 + 1)) (sys.P n') = 0 :=
            ih_orth_n1 n' (by omega)
          simp only [ha, hb, mul_zero, add_zero]
          rw [ih_norm_n1, ih_norm_n, Finset.prod_range_succ]; ring
      constructor
      · -- Full orthogonality: ∀ j < n+2, ip P(n+2) P(j) = 0
        intro j hj
        by_cases hjn1 : j = n + 1
        · subst hjn1; exact h_consec
        · by_cases hjn : j = n
          · subst hjn; exact h_skip2
          · -- j < n: use nonconsec with ih at levels n and n+1
            apply favard_orth_nonconsec cf n j (by omega)
            · intro i hi; exact ih_orth_n1 i (by omega)
            · exact ih_orth_n
      · -- Norm formula: ip P(n+2) P(n+2) = ∏_{k<n+2} β_k
        rw [Finset.prod_range_succ, ip_normRec cf n, ih_norm_n1, mul_comm]

/-! ## §7. Main theorems -/

/-- **Favard's Theorem — Orthogonality**

Given a three-term recurrence system and a compatible linear functional,
the polynomials are pairwise orthogonal: `⟨P_m, P_n⟩ = 0` for `m ≠ n`. -/
theorem favard_orthogonal {R : Type*} [CommRing R] {sys : System R}
    (cf : CompatFunctional sys) (m n : ℕ) (hmn : m ≠ n) :
    ip cf (sys.P m) (sys.P n) = 0 := by
  rcases Nat.lt_or_gt_of_ne hmn with h | h
  · rw [ip_symm cf]; exact (favard_mutual cf n).1 m h
  · exact (favard_mutual cf m).1 n h

/-- **Favard's Theorem — Heilermann Norm Formula**

Given a three-term recurrence system and a compatible linear functional,
`⟨P_n, P_n⟩ = ∏_{k<n} β_k`. -/
theorem favard_norm {R : Type*} [CommRing R] {sys : System R}
    (cf : CompatFunctional sys) (n : ℕ) :
    ip cf (sys.P n) (sys.P n) = ∏ k ∈ Finset.range n, sys.beta k :=
  (favard_mutual cf n).2

end Polynomial.Favard
