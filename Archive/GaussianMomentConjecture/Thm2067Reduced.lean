/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKAssembly
import Archive.GaussianMomentConjecture.PhiVieta
import Archive.GaussianMomentConjecture.Thm2067Concrete
import Mathlib

set_option linter.minImports true

/-!
# the orbit-product argument, concrete, reduced to the small-root product identity alone

`GMC2Thm2067Concrete.thm2067_contradiction_concrete` is the whole orbit-product argument for the
one-variable DvdK theorem, on an *abstract* irreducible `Φ` over `F(t)`, taking three inputs:

* `hΦ`  — `Φ` is irreducible over `F(t)`;
* `hΩ`  — Vieta: the full product of the (distinct) roots of `Φ` is a constant `d ∈ F`;
* `hS`/`hfix` — the small-root product identity: the small-root product equals `c·t` and is Galois-fixed.

For the *concrete* DvdK polynomial `Φ = Phi R M = Xᴹ − t·R`, two of these are now theorems in the repo:

* `hΦ` is `GMC2DvdKAssembly.irreducible_Phi` (degree-`(M+N)` irreducibility over `F(t)`, via
  the swap bridge to `PhiIrreducible`), and
* `hΩ` is `GMC2PhiVieta.prod_rootSet_Phi` (the root product is `RatFunc.C d` with
  `d = (−1)^{deg R}·(r₀/lc R)`, valuation `0`), given separability of `Φ` over its splitting field.

So the concrete the orbit-product argument contradiction reduces to **exactly** the deep analytic input `hS` (the small-root product identity):
the small-root product equals `c·t`, Galois-fixed.  That is the sole remaining gap for GMC(2).
-/

open scoped BigOperators
open Polynomial

set_option maxHeartbeats 1000000

namespace GMC2Thm2067Reduced

open GMC2PhiVieta

variable {F : Type*} [Field F]

/-- **The concrete the orbit-product argument contradiction, reduced to the small-root product identity.**  For `Φ = Phi R M` (`= Xᴹ − t·R`,
`1 ≤ M < deg R`, `R(0) ≠ 0`), separable over its splitting field, the irreducibility (`hΦ`) and Vieta
(`hΩ`) inputs of `GMC2Thm2067Concrete.thm2067_contradiction_concrete` are discharged in-repo.  What
remains is precisely the the small-root product identity data: a Galois-fixed small-root packet `S` whose product is `c·t`.
Given that, the orbit-product argument closes.  This isolates the one deep analytic gap. -/
theorem thm2067_reduced_to_thm1550
    (R : F[X]) (M : ℕ) (hM : 1 ≤ M) (hMd : M < R.natDegree) (hR0 : R.coeff 0 ≠ 0)
    (hsep : Separable ((Phi R M).map (algebraMap (RatFunc F) (Phi R M).SplittingField)))
    (S : Finset ((Phi R M).rootSet (Phi R M).SplittingField))
    (x0 : (Phi R M).rootSet (Phi R M).SplittingField)
    (c : F) (hc : c ≠ 0)
    (hfix : ∀ σ : (Phi R M).Gal,
      σ • (∏ β ∈ S, (β : (Phi R M).SplittingField)) = ∏ β ∈ S, (β : (Phi R M).SplittingField))
    (hS : (∏ β ∈ S, (β : (Phi R M).SplittingField))
        = algebraMap (RatFunc F) (Phi R M).SplittingField (RatFunc.C c * RatFunc.X)) :
    False := by
  refine GMC2Thm2067Concrete.thm2067_contradiction_concrete (Phi R M)
    (GMC2DvdKAssembly.irreducible_Phi R M hM hR0)
    S x0 c ((-1) ^ R.natDegree * (R.coeff 0 / R.leadingCoeff)) hc hfix hS ?_
  exact GMC2PhiVieta.prod_rootSet_Phi R M hM hMd hsep

end GMC2Thm2067Reduced

