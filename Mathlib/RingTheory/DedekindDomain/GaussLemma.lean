/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Polynomial.ContentIdeal
public import Mathlib.RingTheory.Polynomial.GaussNorm

/-!
## Gauss's Lemma for Dedekind Domains

This file contains Gauss's Lemma for Dedekind Domains, which states that the content ideal of a
polynomial is the whole ring if and only if the `v`-adic Gauss norms of the polynomial are equal to
1 for all `v`.
-/

public section
namespace Polynomial

open IsDedekindDomain HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R) {b : NNReal}
  (hb : 1 < b) (p : R[X])

theorem gaussNorm_intAdicAbv_le_one : p.gaussNorm (v.intAdicAbv hb) 1 ≤ 1 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  simp [gaussNorm, hp0, intAdicAbv_le_one]

/-- Given a polynomial `p` in `R[X]`, the `v`-adic Gauss norm of `p` is smaller than 1 if and only
if the content ideal of `p` is contained in the prime ideal corresponding to `v`. -/
theorem gaussNorm_lt_one_iff_contentIdeal_le :
    p.gaussNorm (v.intAdicAbv hb) 1 < 1 ↔ p.contentIdeal ≤ v.asIdeal := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have hsupp_nonempty : p.support.Nonempty := by grind [support_nonempty]
  simp only [gaussNorm, hsupp_nonempty, ↓reduceDIte, one_pow, mul_one, contentIdeal, Ideal.span_le,
    Set.subset_def, SetLike.mem_coe, ← v.intAdicAbv_lt_one_iff hb]
  constructor
  · contrapose!
    simp only [mem_coeffs_iff, mem_support_iff, ↓existsAndEq, and_true, forall_exists_index,
      and_imp]
    intro _ h1 h2
    exact Finset.le_sup'_of_le (fun n ↦ (v.intAdicAbv hb) (p.coeff n)) (by simp [h1]) h2
  · intro h
    rw [Finset.sup'_lt_iff]
    intro n hn
    rw [mem_support_iff] at hn
    exact h _ <| p.coeff_mem_coeffs hn

/-- **Gauss's Lemma:** given a polynomial `p` in `R[X]`, the content ideal of `p` is the whole ring
if and only if the `v`-adic Gauss norms of `p` are equal to 1 for all `v`. -/
theorem contentIdeal_eq_top_iff_forall_gaussNorm_eq_one (hR : ¬IsField R) :
    p.contentIdeal = ⊤ ↔ ∀ v : HeightOneSpectrum R, p.gaussNorm (v.intAdicAbv hb) 1 = 1 := by
  convert_to _ ↔ ∀ (x : HeightOneSpectrum R), 1 ≤ gaussNorm (x.intAdicAbv hb) 1 p
  · grind [gaussNorm_intAdicAbv_le_one]
  simp [← not_iff_not, gaussNorm_lt_one_iff_contentIdeal_le, ideal_ne_top_iff_exists hR]

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (hR : ¬IsField R)
  {b : NNReal} (hb : 1 < b) (p : R[X])

include hR in
/-- In case `R` is PID, given a polynomial `p` in `R[X]`, `p` is primitive if and only if the
`v`-adic Gauss norms of `p` are equal to 1 for all `v`. -/
theorem isPrimitive_iff_forall_gaussNorm_eq_one :
    p.IsPrimitive ↔ ∀ v : HeightOneSpectrum R, p.gaussNorm (v.intAdicAbv hb) 1 = 1 := by
  rw [isPrimitive_iff_contentIdeal_eq_top, p.contentIdeal_eq_top_iff_forall_gaussNorm_eq_one hb hR]

end Polynomial
