/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.OrbitProductReduced
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The orbit-product argument reduced to `hS` alone (the small-root product `= c·t`)

`GMC2.OrbitProductReduced.orbit_product_contradiction_of_hS_and_fixed` still carried two auxiliary
hypotheses beyond the deep analytic input `hS` (the small-root product is `c·t`): separability
(`hsep`) of `Φ = Phi R M` over its splitting field, and Galois-fixedness (`hfix`) of the small-root
packet product. Over a characteristic-zero base field, **both are free**:

* `hsep` — `Phi R M` is irreducible over `F(t)` (`GMC2.DvdKAssembly.irreducible_Phi`), and `F(t)` is
  a characteristic-zero, hence perfect, field (`CharZero (RatFunc F)` → `PerfectField (RatFunc F)`
  by `PerfectField.ofCharZero`), so `Phi R M` is separable; separability is preserved under `map`.
* `hfix` — `hS` says the packet product *equals* an element of the base field `F(t)` (`C c · X`),
  and every `σ ∈ Gal` fixes the base field (`AlgEquiv.commutes`); so the product is automatically
  Galois-fixed. In other words `hfix` is a logical consequence of `hS`, not an independent input.

Hence the entire concrete orbit-product contradiction reduces to **exactly** `hS`. In the
Weierstrass frame `hS` is `Π = c·t`, i.e. `h(0,t) = 1` (via
`GMC2.DvdKWeierstrass.coeff_zero_smallRootFactor_mul_unit`): the single analytic identity is the
sole remaining input to GMC(2) on the multiplicative route.
-/

open Polynomial

namespace GMC2.OrbitProductFromSmallRoots

variable {F : Type*} [Field F] [CharZero F]

/-- **The concrete orbit-product contradiction, reduced to `hS` alone.** For
`Φ = Phi R M` (`= Xᴹ − t·R`, `1 ≤ M < deg R`, `R(0) ≠ 0`) over a characteristic-zero field `F`, *the
only* remaining input is `hS`: a small-root packet `S` whose product equals `c·t` (`c ≠ 0`).
Separability and Galois-fixedness are discharged internally. Given `hS`, a contradiction follows —
so, reading `hS` as "all constant terms vanish", some constant term is nonzero: DvdK. -/
theorem orbit_product_contradiction_of_hS
    (R : F[X]) (M : ℕ) (hM : 1 ≤ M) (hMd : M < R.natDegree) (hR0 : R.coeff 0 ≠ 0)
    (S : Finset ((GMC2.PhiVieta.Phi R M).rootSet (GMC2.PhiVieta.Phi R M).SplittingField))
    (x0 : (GMC2.PhiVieta.Phi R M).rootSet (GMC2.PhiVieta.Phi R M).SplittingField)
    (c : F) (hc : c ≠ 0)
    (hS : (∏ β ∈ S, (β : (GMC2.PhiVieta.Phi R M).SplittingField))
        = algebraMap (RatFunc F) (GMC2.PhiVieta.Phi R M).SplittingField (RatFunc.C c * RatFunc.X)) :
    False := by
  -- (1) separability of `Φ` over its splitting field, from irreducibility over the perfect
  -- field `F(t)`
  have hirr : Irreducible (GMC2.PhiVieta.Phi R M) := GMC2.DvdKAssembly.irreducible_Phi R M hM hR0
  have hsepΦ : (GMC2.PhiVieta.Phi R M).Separable := PerfectField.separable_of_irreducible hirr
  have hsep : Separable ((GMC2.PhiVieta.Phi R M).map
      (algebraMap (RatFunc F) (GMC2.PhiVieta.Phi R M).SplittingField)) := hsepΦ.map
  -- (2) Galois-fixedness of the packet product, a consequence of `hS` (a base-field element)
  have hfix : ∀ σ : (GMC2.PhiVieta.Phi R M).Gal,
      σ • (∏ β ∈ S, (β : (GMC2.PhiVieta.Phi R M).SplittingField))
        = ∏ β ∈ S, (β : (GMC2.PhiVieta.Phi R M).SplittingField) := by
    intro σ
    -- `σ • z` is defeq to `σ z` (`AlgEquiv.smul_def` is `rfl`); every `σ ∈ Gal` fixes the
    -- base field
    rw [hS]
    exact AlgHomClass.commutes σ (RatFunc.C c * RatFunc.X)
  exact GMC2.OrbitProductReduced.orbit_product_contradiction_of_hS_and_fixed
    R M hM hMd hR0 hsep S x0 c hc hfix hS

end GMC2.OrbitProductFromSmallRoots
