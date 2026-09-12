/-
Copyright (c) 2026 Junji Hashimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junji Hashimoto
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.Algebra.Octonion

/-!
# The number-theoretic transform

The number-theoretic transform (NTT) is the discrete Fourier transform of functions
`ZMod N → M`, where `M` is a module over a commutative domain `R` containing a primitive
`N`-th root of unity `ζ` — e.g. `R = ZMod p` with `N ∣ p - 1`:

`ntt hζ f k = ∑ j, ζ ^ (j * k) • f j`.

There is no norm or complex conjugation over a general `R`, so Plancherel's theorem takes
the form of the *bilinear* Parseval identity `sum_bilin_ntt_ntt_neg`, and the Fourier
inversion formula `nttInv_ntt` holds after multiplication by `N` (so the transform is
bijective whenever `N` is invertible in `R`; over `ZMod p` this is `p ∤ N`).

The module `M` can be any `R`-module: taking `M` to be a hypercomplex algebra over `R`
(for instance the octonions or sedenions over `ZMod p`, with the `R`-scalar action) yields
hypercomplex number-theoretic transforms; see the example at the end of the file.

## Main definitions

* `ZMod.ntt`: the number-theoretic transform.
* `ZMod.nttInv`: the inverse transform (up to the factor `N`).

## Main statements

* `ZMod.sum_zmodChar_mul`: orthogonality of the characters `j ↦ ζ ^ (s * j)`.
* `ZMod.nttInv_ntt`, `ZMod.ntt_nttInv`: the Fourier inversion formula.
* `ZMod.sum_bilin_ntt_ntt_neg`: the bilinear Parseval identity.

## References

* J. M. Pollard, *The fast Fourier transform in a finite field*, Math. Comp. 25 (1971)

-/

@[expose] public section

open Finset AddChar

namespace ZMod

variable {N : ℕ} [NeZero N] {R : Type*} [CommRing R] [IsDomain R] {ζ : R}
  {M : Type*} [AddCommGroup M] [Module R M]

/-- The number-theoretic transform of `f : ZMod N → M` with respect to an `N`-th root of
unity `ζ`: `ntt hζ f k = ∑ j, ζ ^ (j * k) • f j`. -/
def ntt (hζ : ζ ^ N = 1) (f : ZMod N → M) (k : ZMod N) : M :=
  ∑ j : ZMod N, zmodChar N hζ (j * k) • f j

/-- The inverse number-theoretic transform, up to the factor `N`:
`nttInv hζ f k = ∑ j, ζ ^ (-(j * k)) • f j`. -/
def nttInv (hζ : ζ ^ N = 1) (f : ZMod N → M) (k : ZMod N) : M :=
  ∑ j : ZMod N, zmodChar N hζ (-(j * k)) • f j

/-- Orthogonality of the characters of `ZMod N` obtained from a primitive `N`-th root of
unity. -/
theorem sum_zmodChar_mul (hζ : IsPrimitiveRoot ζ N) (s : ZMod N) :
    ∑ j : ZMod N, zmodChar N hζ.pow_eq_one (s * j) = if s = 0 then (N : R) else 0 := by
  classical
  split_ifs with hs
  · simp [hs, card_univ, ZMod.card]
  · have hprim := zmodChar_primitive_of_primitive_root N hζ
    have h := sum_eq_ite ((zmodChar N hζ.pow_eq_one).mulShift s)
    rw [if_neg (show (zmodChar N hζ.pow_eq_one).mulShift s ≠ 0 from fun h => hprim hs h)] at h
    simpa only [mulShift_apply] using h

/-- The **Fourier inversion formula** for the number-theoretic transform. -/
theorem nttInv_ntt (hζ : IsPrimitiveRoot ζ N) (f : ZMod N → M) (k : ZMod N) :
    nttInv hζ.pow_eq_one (ntt hζ.pow_eq_one f) k = (N : R) • f k := by
  classical
  simp only [nttInv, ntt, smul_sum, smul_smul, ← map_add_eq_mul]
  rw [sum_comm]
  simp only [show ∀ i j : ZMod N, -(j * k) + i * j = (i - k) * j from fun i j => by ring]
  have horth : ∀ i : ZMod N,
      (∑ j : ZMod N, zmodChar N hζ.pow_eq_one ((i - k) * j) • f i)
        = (if i - k = 0 then (N : R) else 0) • f i := fun i => by
    rw [← sum_smul, sum_zmodChar_mul hζ]
  simp only [horth, sub_eq_zero, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ k, if_pos (mem_univ k)]

/-- The **Fourier inversion formula** for the number-theoretic transform, the other
composition. -/
theorem ntt_nttInv (hζ : IsPrimitiveRoot ζ N) (f : ZMod N → M) (k : ZMod N) :
    ntt hζ.pow_eq_one (nttInv hζ.pow_eq_one f) k = (N : R) • f k := by
  classical
  simp only [ntt, nttInv, smul_sum, smul_smul, ← map_add_eq_mul]
  rw [sum_comm]
  simp only [show ∀ i j : ZMod N, j * k + -(i * j) = (k - i) * j from fun i j => by ring]
  have horth : ∀ i : ZMod N,
      (∑ j : ZMod N, zmodChar N hζ.pow_eq_one ((k - i) * j) • f i)
        = (if k - i = 0 then (N : R) else 0) • f i := fun i => by
    rw [← sum_smul, sum_zmodChar_mul hζ]
  simp only [horth, sub_eq_zero, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq Finset.univ k, if_pos (mem_univ k)]

/-- Summing the transform against the character recovers `N` times the original function:
a reformulation of the inversion formula used for the Parseval identity. -/
theorem sum_zmodChar_smul_ntt_neg (hζ : IsPrimitiveRoot ζ N) (g : ZMod N → M) (i : ZMod N) :
    (∑ k : ZMod N, zmodChar N hζ.pow_eq_one (i * k) • ntt hζ.pow_eq_one g (-k))
      = (N : R) • g i := by
  rw [← nttInv_ntt hζ g i, nttInv]
  exact Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun k => by
    rw [Equiv.neg_apply, show (-(-k * i) : ZMod N) = i * k from by ring]

/-- The **bilinear Parseval identity** for the number-theoretic transform: over a general
coefficient ring there is no norm or conjugation, and Plancherel's theorem takes this
bilinear form. -/
theorem sum_bilin_ntt_ntt_neg {M' P : Type*} [AddCommGroup M'] [Module R M']
    [AddCommGroup P] [Module R P] (hζ : IsPrimitiveRoot ζ N)
    (B : M →ₗ[R] M' →ₗ[R] P) (f : ZMod N → M) (g : ZMod N → M') :
    ∑ k : ZMod N, B (ntt hζ.pow_eq_one f k) (ntt hζ.pow_eq_one g (-k))
      = (N : R) • ∑ x : ZMod N, B (f x) (g x) := by
  classical
  have hexp : ∀ (k : ZMod N) (y : M'), B (ntt hζ.pow_eq_one f k) y
      = ∑ i : ZMod N, zmodChar N hζ.pow_eq_one (i * k) • (B (f i)) y := fun k y => by
    rw [ntt, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun d _ => by rw [B.map_smul, LinearMap.smul_apply]
  simp only [hexp]
  rw [sum_comm]
  have hinner : ∀ i : ZMod N,
      (∑ k : ZMod N,
          zmodChar N hζ.pow_eq_one (i * k) • (B (f i)) (ntt hζ.pow_eq_one g (-k)))
        = (N : R) • (B (f i)) (g i) := fun i => by
    have h1 : (B (f i)) (∑ k : ZMod N,
        zmodChar N hζ.pow_eq_one (i * k) • ntt hζ.pow_eq_one g (-k))
        = ∑ k : ZMod N,
            zmodChar N hζ.pow_eq_one (i * k) • (B (f i)) (ntt hζ.pow_eq_one g (-k)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => (B (f i)).map_smul _ _
    rw [← h1, sum_zmodChar_smul_ntt_neg hζ g i]
    exact (B (f i)).map_smul _ _
  simp only [hinner]
  rw [← smul_sum]

/-- A hypercomplex number-theoretic transform: the octonions over `ZMod p` are a module
over `ZMod p`, so the inversion formula applies to octonion-valued NTTs (and similarly at
every level of the Cayley–Dickson tower). -/
example {p : ℕ} [Fact p.Prime] {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ N)
    (f : ZMod N → CayleyDickson (Quaternion (ZMod p))) (k : ZMod N) :
    nttInv hζ.pow_eq_one (ntt hζ.pow_eq_one f) k = (N : ZMod p) • f k :=
  nttInv_ntt hζ f k

end ZMod
