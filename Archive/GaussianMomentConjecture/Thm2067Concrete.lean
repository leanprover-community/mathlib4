/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.GalRootAction
import Archive.GaussianMomentConjecture.Thm2067Wrapper
import Mathlib

set_option linter.minImports true

/-!
# the orbit-product argument made concrete: the orbit-product contradiction for an irreducible `Φ` over `F(t)`

Instantiating the abstract wrapper (`GMC2Thm2067Wrapper.thm2067_contradiction`) at `Φ.Gal` acting on
`Φ.rootSet Φ.SplittingField` via the direct action (`GalRootAction`).  Transitivity comes from
`Φ`'s irreducibility (`isPretransitive_rootAction`), equivariance is tautological (`coe_smul`), and
the two number-theoretic inputs — the small-root product identity (`hS`, `hfix`: the small-root product is `c·t` and
Galois-fixed) and Vieta (`hΩ`: the full product is a constant `d`) — remain as hypotheses.
-/

open Polynomial

namespace GMC2Thm2067Concrete

variable {F : Type*} [Field F]

/-- **the orbit-product argument, concrete.**  For an irreducible `Φ` over `F(t)` splitting in its splitting field, if
the small-root subset product is `c·t` (`c ≠ 0`) and Galois-fixed (the small-root product identity) and the full root product
is a constant `d` (Vieta), a contradiction follows.  So — reading the hypotheses as "all constant
terms vanish" — some constant term is nonzero: DvdK. -/
theorem thm2067_contradiction_concrete
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
    GMC2GalRootAction.isPretransitive_rootAction Φ hΦ
  exact GMC2Thm2067Wrapper.thm2067_contradiction
    (E := Φ.SplittingField) (G := Φ.Gal)
    (Ω := (Φ.rootSet Φ.SplittingField : Set Φ.SplittingField))
    (f := fun β => (β : Φ.SplittingField)) (S := S) (x := x0)
    (hf := fun σ β => GMC2GalRootAction.coe_smul Φ σ β) (hfix := hfix)
    (c := c) (d := d) (hc := hc) (hS := hS) (hΩ := hΩ)

end GMC2Thm2067Concrete

