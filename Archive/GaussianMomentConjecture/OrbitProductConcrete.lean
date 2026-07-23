/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.GalRootAction
import Archive.GaussianMomentConjecture.OrbitProductWrapper
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The orbit-product contradiction for an irreducible `Φ` over `F(t)`

Instantiating the abstract wrapper (`GMC2.OrbitProductWrapper.orbit_product_contradiction_abstract`) at `Φ.Gal` acting
on `Φ.rootSet Φ.SplittingField` via the direct action (`GalRootAction`). Transitivity comes from
`Φ`'s irreducibility (`isPretransitive_rootAction`), equivariance is tautological (`coe_smul`), and
the two number-theoretic inputs — the small-root product identity (`hS`, `hfix`: the small-root
product is `c·t` and Galois-fixed) and Vieta (`hΩ`: the full product is a constant `d`) — remain as
hypotheses.
-/

open Polynomial

namespace GMC2.OrbitProductConcrete

variable {F : Type*} [Field F]

/-- **The orbit-product argument, concrete.** For an irreducible `Φ` over `F(t)` splitting in its
splitting field, if the small-root subset product is `c·t` (`c ≠ 0`) and Galois-fixed (the
small-root product identity) and the full root product is a constant `d` (Vieta), a contradiction
follows. So — reading the hypotheses as "all constant terms vanish" — some constant term is nonzero:
DvdK. -/
theorem orbit_product_contradiction_concrete
    (Φ : (RatFunc F)[X]) (hΦ : Irreducible Φ)
    (S : Finset (Φ.rootSet Φ.SplittingField))
    (x0 : Φ.rootSet Φ.SplittingField)
    (c d : F) (hc : c ≠ 0)
    (hfix : ∀ σ : Φ.Gal,
      σ • (∏ β ∈ S, (β : Φ.SplittingField)) = ∏ β ∈ S, (β : Φ.SplittingField))
    (hS : (∏ β ∈ S, (β : Φ.SplittingField))
        = algebraMap (RatFunc F) Φ.SplittingField (RatFunc.C c * RatFunc.X))
    (hΩ : (∏ α : Φ.rootSet Φ.SplittingField, (α : Φ.SplittingField))
        = algebraMap (RatFunc F) Φ.SplittingField (RatFunc.C d)) :
    False := by
  classical
  haveI : FiniteDimensional (RatFunc F) Φ.SplittingField :=
    Polynomial.IsSplittingField.finiteDimensional Φ.SplittingField Φ
  haveI : MulAction.IsPretransitive Φ.Gal (Φ.rootSet Φ.SplittingField) :=
    GMC2.GalRootAction.isPretransitive_rootAction Φ hΦ
  exact GMC2.OrbitProductWrapper.orbit_product_contradiction_abstract
    (E := Φ.SplittingField) (G := Φ.Gal)
    (Ω := (Φ.rootSet Φ.SplittingField : Set Φ.SplittingField))
    (f := fun β => (β : Φ.SplittingField)) (S := S) (x := x0)
    (hf := fun σ β => GMC2.GalRootAction.coe_smul Φ σ β) (hfix := hfix)
    (c := c) (d := d) (hc := hc) (hS := hS) (hΩ := hΩ)

end GMC2.OrbitProductConcrete

