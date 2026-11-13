/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.NumberField.DedekindZeta

import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The Dedekind zeta function of `ℚ`

We show that the Dedekind zeta function of `ℚ` is the Riemann zeta function on the half-plane
`1 < re s`. This is in a separate file so that `Mathlib.NumberTheory.NumberField.DedekindZeta`
does not import the Riemann zeta function.

## Main results

* `Rat.dedekindZeta_eq_riemannZeta`: for `1 < re s`, `dedekindZeta ℚ s = riemannZeta s`.
-/

public section

open NumberField Ideal

namespace Rat

-- For `n ≠ 0`, the only ideal of `𝓞 ℚ` of norm `n` is `(n)`.
private theorem card_absNorm_eq {n : ℕ} (hn : n ≠ 0) :
    Nat.card {I : Ideal (𝓞 ℚ) // absNorm I = n} = 1 := by
  have hn' : absNorm (span {(n : 𝓞 ℚ)}) = n := by
    rw [absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  -- an ideal `I` of norm `n` contains `(n)`, so `(n) = I * J` with `J` of norm `1`
  have h (I : Ideal (𝓞 ℚ)) (hI : absNorm I = n) : I = span {(n : 𝓞 ℚ)} := by
    have hle : span {(n : 𝓞 ℚ)} ≤ I := hI ▸ span_singleton_absNorm_le I
    obtain ⟨J, hJ⟩ := dvd_iff_le.mpr hle
    have hJ₁ : absNorm J = 1 := by
      have := congr_arg absNorm hJ
      rw [map_mul, hn', hI] at this
      exact (mul_eq_left₀ hn).mp this.symm
    rw [hJ, absNorm_eq_one_iff.mp hJ₁, mul_top]
  exact Nat.card_eq_one_iff_exists.mpr ⟨⟨_, hn'⟩, fun I ↦ Subtype.ext (h I I.2)⟩

/-- The Dedekind zeta function of `ℚ` is the Riemann zeta function on the half-plane
`1 < re s`. -/
theorem dedekindZeta_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta ℚ s = riemannZeta s :=
  (LSeries_congr (fun hn ↦ by simp [card_absNorm_eq hn]) s).trans (LSeries_one_eq_riemannZeta hs)

end Rat
