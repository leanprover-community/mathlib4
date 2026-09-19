/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.SOS

open SOS CPoly

/-! ## BBR Lemma 7.2

The degree-8 bivariate polynomial of Lemma 7.2 in
Blomer–Brumley–Radziwill (https://arxiv.org/abs/2603.05609,
https://github.com/maksym-radziwill/BBR), reported on
[Zulip](https://leanprover.zulipchat.com/#narrow/channel/423402-PrimeNumberTheorem.2B/topic/sum.20of.20squares.20tactic.3A.20seeking.20users/near/595692701)
by Maksym Radziwill on 2026-05-18. Integer coefficients up to
`~5.8 × 10¹²`.

`by sos` closes this via the **i=0 strict-refutation Positivstellensatz**
(`SOS.Search.runClosedRefutation`): a certificate
`−1 = σ₀ + σ₁·(−p)` with `σ₀, σ₁` SOS, which proves the stronger
`0 < p` (hence `0 ≤ p`) by contradiction — under `p ≤ 0` the RHS is
`≥ 0`, contradicting `= −1`. This is exactly Harrison's HOL Light
`REAL_SOS` mechanism (the `i = 0` branch of `REAL_NONLINEAR_PROVER`'s
`tryall` loop, target `−pol⁰ = −1`), reached here through the
multi-block reduced Schmüdgen encoder.

The `−1` target is what makes BBR tractable: it yields a
well-conditioned reduced SDP whose float Gram rounds cleanly to a
rational certificate. The earlier `p^{2k+1}` Artin form
(`maxArtinExponent`) targets a far worse-conditioned SDP and does not
close BBR at any depth/denominator we expose.

The proof is fully kernel-checked — `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound` (no `native_decide`). The
certificate's Gram pivots have large denominators, so it needs the
upper end of the rounding schedule — which is just Harrison's
`find_rounding` ceiling of `2^66`, the default, so plain `by sos`
closes it with no config. -/

set_option maxHeartbeats 4000000 in
example : ∀ x y : ℝ,
    0 ≤ 5217874549248 + 16623868928 * y - 3336250252672 * y ^ 2
      - 25477793408 * y ^ 3 + 655195946720 * y ^ 4 + 10587831584 * y ^ 5
      - 152613570520 * y ^ 6 - 1371845320 * y ^ 7 + 41790603610 * y ^ 8
      - 16640770048 * x + 5796896462336 * x * y + 2432177280 * x * y ^ 2
      - 2074067626368 * x * y ^ 3 - 167534816 * x * y ^ 4
      - 3336702739328 * x ^ 2 - 2399492480 * x ^ 2 * y
      + 5223381207392 * x ^ 2 * y ^ 2 + 2035437600 * x ^ 2 * y ^ 3
      - 1238781629424 * x ^ 2 * y ^ 4 + 25484108416 * x ^ 3
      - 2074041622592 * x ^ 3 * y - 2039508160 * x ^ 3 * y ^ 2
      + 914071084096 * x ^ 3 * y ^ 3 + 409594776 * x ^ 3 * y ^ 4
      + 655694115936 * x ^ 4 + 155563456 * x ^ 4 * y
      - 1238844857440 * x ^ 4 * y ^ 2 - 407914952 * x ^ 4 * y ^ 3
      + 359512561893 * x ^ 4 * y ^ 4 - 10586722304 * x ^ 5
      - 152799075816 * x ^ 6 + 1371693928 * x ^ 7
      + 41813434533 * x ^ 8 := by
  sos
