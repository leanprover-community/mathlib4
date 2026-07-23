/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.FieldTheory.RatFunc.AsPolynomial

set_option linter.minImports true

/-!
# Frame-bridge pullback: transporting the small-root product identity to the splitting field

The orbit-product contradiction (`GMC2.Thm2067HSonly.thm2067_reduced_to_hS`) consumes `hS`, the
identity `∏_{β∈S} β = algebraMap (RatFunc F) SF (c·t)` in the **splitting field** of `Φ = Phi R M`
over `RatFunc F`. The Weierstrass small-root product `Π = (−1)ᴹ (smallRootFactor R M).coeff 0 = c·t`
lives in the **power-series/Laurent frame**. This module supplies the elementary but essential
*pullback*: any `RatFunc F`-algebra embedding `ψ` of the splitting field into a larger field `Ω` is
injective and fixes the base field, so an identity `ψ(∏_S β) = algebraMap v` proved in `Ω`
transports verbatim to the splitting field.

**Why this matters (the reframe):** `thm2067_reduced_to_hS`'s orbit-product equation
(`GMC2.Thm2067Wrapper.thm2067_contradiction` via `prod_pow_card_group_eq`) holds for an
**arbitrary** finset `S` — it needs only that `∏_{β∈S} β` be Galois-fixed, which `hS` (a base-field
value) supplies. So `S` need **not** be the valuation-positive packet; it may be defined
*algebraically* as the roots of the Weierstrass distinguished factor `P` (via `P ∣ Φ`), and its
product is `(−1)ᴹ P.coeff 0 = c·t` by Vieta. Hence the frame bridge needs **no** extension of the
Laurent valuation to the algebraic closure (the months-long `SpectralNorm`/Krasner prerequisite):
only an algebraic embedding of the splitting field, `Vieta`, and this pullback.
-/

open Polynomial

namespace GMC2.FrameBridge

variable {F : Type*} [Field F]

/-- **The frame-bridge pullback.** For any `RatFunc F`-algebra embedding `ψ` of the splitting field
of `Φ` into a field `Ω`, an identity between a root-product and a base-field value `v` that holds
after applying `ψ` (i.e. in the frame `Ω`) already holds in the splitting field. `ψ` is injective (a
ring hom out of a field) and fixes `RatFunc F` (`AlgHom.commutes`), so the identity pulls back. -/
theorem prod_eq_algebraMap_of_embedding (Φ : (RatFunc F)[X])
    {Ω : Type*} [Field Ω] [Algebra (RatFunc F) Ω]
    (ψ : Φ.SplittingField →ₐ[RatFunc F] Ω)
    (S : Finset (Φ.rootSet Φ.SplittingField)) (v : RatFunc F)
    (hψ : ψ (∏ β ∈ S, (β : Φ.SplittingField)) = algebraMap (RatFunc F) Ω v) :
    (∏ β ∈ S, (β : Φ.SplittingField)) = algebraMap (RatFunc F) Φ.SplittingField v := by
  have hinj : Function.Injective ψ := ψ.toRingHom.injective
  apply hinj
  rw [hψ, AlgHom.commutes]

/-- Specialisation to the `hS` shape (`v = C c · X`, i.e. the small-root product `c·t`): the exact
hypothesis `GMC2.Thm2067HSonly.thm2067_reduced_to_hS` consumes. Constructing the embedding `ψ` (into
the algebraic closure of `LaurentSeries F`) and proving the `Ω`-side identity `ψ(∏_S β) = c·t` (via
`P ∣ Φ` + Vieta on the Weierstrass distinguished factor) is the remaining algebraic bridge work. -/
theorem hS_of_embedding (Φ : (RatFunc F)[X])
    {Ω : Type*} [Field Ω] [Algebra (RatFunc F) Ω]
    (ψ : Φ.SplittingField →ₐ[RatFunc F] Ω)
    (S : Finset (Φ.rootSet Φ.SplittingField)) (c : F)
    (hψ : ψ (∏ β ∈ S, (β : Φ.SplittingField))
        = algebraMap (RatFunc F) Ω (RatFunc.C c * RatFunc.X)) :
    (∏ β ∈ S, (β : Φ.SplittingField))
      = algebraMap (RatFunc F) Φ.SplittingField (RatFunc.C c * RatFunc.X) :=
  prod_eq_algebraMap_of_embedding Φ ψ S (RatFunc.C c * RatFunc.X) hψ

/-- **The bridge, reduced to the frame-side identity.**  The embedding `ψ` is *free* — for any field
`Ω` over `RatFunc F` in which `Φ` splits, `Polynomial.IsSplittingField.lift` supplies the canonical
`RatFunc F`-embedding of the splitting field.  So `hS` follows from a single frame-side obligation:
that the packet product, mapped into `Ω`, equals `c·t`.  This is where the intended `Ω` is the
algebraic closure of `LaurentSeries F`, the packet `S` is the roots that land on the Weierstrass
distinguished factor `P` (via `P ∣ Φ`), and the value `c·t = (−1)ᴹ P.coeff 0` comes from Vieta — all
purely algebraic, no valuation on the splitting field. -/
theorem hS_of_splits (Φ : (RatFunc F)[X])
    {Ω : Type*} [Field Ω] [Algebra (RatFunc F) Ω]
    (hsplit : Splits (Φ.map (algebraMap (RatFunc F) Ω)))
    (S : Finset (Φ.rootSet Φ.SplittingField)) (c : F)
    (hψ : (Polynomial.IsSplittingField.lift Φ.SplittingField Φ hsplit)
            (∏ β ∈ S, (β : Φ.SplittingField))
        = algebraMap (RatFunc F) Ω (RatFunc.C c * RatFunc.X)) :
    (∏ β ∈ S, (β : Φ.SplittingField))
      = algebraMap (RatFunc F) Φ.SplittingField (RatFunc.C c * RatFunc.X) :=
  hS_of_embedding Φ (Polynomial.IsSplittingField.lift Φ.SplittingField Φ hsplit) S c hψ

end GMC2.FrameBridge

