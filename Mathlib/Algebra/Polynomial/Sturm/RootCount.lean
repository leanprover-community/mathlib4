/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.Polynomial.Sturm.Tarski

/-!
# Root-count certificates

`Polynomial.RootCountCert p L B n` is a certificate for `p : ℝ[X]` that certifies:

1. `L` is the Sturm sequence of `p` and its derivative.
2. `B` is positive and every real root of `p` lies in `(-B, B)`.
3. The sign variations of `L` drop by `n` from `-B` to `B`.

## Main results

- `Polynomial.RootCountCert.card_rootSet`: given such a certificate, `p` has `n` distinct real
  roots.
-/

@[expose] public section

open SignType

namespace Polynomial

/-- A Sturm certificate for `p` -/
structure RootCountCert (p : ℝ[X]) (L : List ℝ[X]) (B : ℝ) (n : ℕ) : Prop where
  sturmSeq_eq : sturmSeq p (derivative p) = L
  pos : 0 < B
  root_bound : ∀ x, p.IsRoot x → |x| < B
  variations :
    (L.map (sign ∘ eval (-B))).signVariations = (L.map (sign ∘ eval B)).signVariations + n

/-- Given a certificate `c` for `p = f.map (algebraMap R ℝ)`, `f` has `n` distinct real roots. -/
theorem RootCountCert.card_rootSet {R : Type*} [CommRing R] [Algebra R ℝ] {f : R[X]} {p : ℝ[X]}
    {L : List ℝ[X]} {B : ℝ} {n : ℕ} (hf : f.map (algebraMap R ℝ) = p)
    (c : RootCountCert p L B n) : Fintype.card (f.rootSet ℝ) = n := by
  -- Prove using `sturm_tarski p 1` on `(-B, B)`, which contains every real root of `p`.
  sorry

end Polynomial
