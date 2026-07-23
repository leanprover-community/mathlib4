/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.OrbitProduct
import Archive.GaussianMomentConjecture.RatFuncClosing
import Mathlib.FieldTheory.RatFunc.AsPolynomial

set_option linter.minImports true

/-!
# The orbit-product wrapper: orbit-product ⇒ contradiction

This assembles the Galois orbit-product argument for the general one-variable DvdK theorem,
reducing it to the two number-theoretic inputs it genuinely needs:

* **the small-root product identity** (the unramified-Hensel small-root product): assuming all
  constant terms vanish, the small-root product `Π = ∏_{β∈S} (root β)` equals `c·t` (`t`-valuation
  1) and is Galois-fixed (lies in `F(t)`).
* **Vieta**: the full product `C_Φ = ∏_{α} (root α)` is a nonzero *constant* `d ∈ F` (`t`-valuation
  0).

Given these (plus transitivity from `GMC2.PhiIrreducible.phi_irreducible_ratfunc` and equivariance
of the root embedding), the orbit-product equation `Π^{|G|} = C_Φ^{|S|·|Stab|}` pulls back to `F(t)`
and becomes `(c·t)^{|G|} = d^{K}`, impossible for `|G| ≥ 1` (a monomial is never a constant,
`GMC2.RatFuncClosing.monomial_pow_ne_const`). So some constant term is nonzero — DvdK.

The Galois structure (`G`, the transitive action, the equivariant embedding `f`) is taken
abstractly; instantiating it at `Φ.Gal`/`Φ.rootSet` via `Polynomial.Gal.galAction_isPretransitive`
and `Gal.smul_def` is the remaining wiring. the small-root product identity is the one deep analytic
gap.
-/

open scoped BigOperators
open MulAction Finset

namespace GMC2.Thm2067Wrapper

variable {F : Type*} [Field F]

/-- **The `F(t)` closing.**  `(c·t)^N = d^K` is impossible for `c ≠ 0`, `N ≥ 1`: the left side is a
degree-`N` monomial, the right a constant. -/
theorem pow_monomial_eq_const_absurd
    (c d : F) (hc : c ≠ 0) (N K : ℕ) (hN : 1 ≤ N)
    (heq : (RatFunc.C c * RatFunc.X) ^ N = (RatFunc.C d) ^ K) : False := by
  have hL : (RatFunc.C c * RatFunc.X) ^ N = RatFunc.C (c ^ N) * RatFunc.X ^ N := by
    rw [mul_pow, ← map_pow]
  have hR : (RatFunc.C d) ^ K = RatFunc.C (d ^ K) := by rw [← map_pow]
  rw [hL, hR] at heq
  exact GMC2.RatFuncClosing.monomial_pow_ne_const (c ^ N) (d ^ K) (pow_ne_zero _ hc) N hN heq

/-- **The orbit-product wrapper (abstract Galois input).** With a transitive finite
Galois-type action on the roots (embedded `G`-equivariantly by `f` into a field `E` over `F(t)`),
the small-root product equal to `c·t` and Galois-fixed (the small-root product identity), and the
full product a nonzero constant `d` (Vieta), a contradiction follows. This is the complete the
orbit-product argument modulo those two inputs. -/
theorem thm2067_contradiction
    {E : Type*} [Field E] [Algebra (RatFunc F) E]
    {G Ω : Type*} [Group G] [Fintype G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]
    [IsPretransitive G Ω] [MulDistribMulAction G E]
    (f : Ω → E) (S : Finset Ω) (x : Ω)
    (hf : ∀ (g : G) (β : Ω), f (g • β) = g • f β)
    (hfix : ∀ g : G, g • (∏ β ∈ S, f β) = ∏ β ∈ S, f β)
    (c d : F) (hc : c ≠ 0)
    (hS : (∏ β ∈ S, f β)
        = algebraMap (RatFunc F) E (RatFunc.C c * RatFunc.X))
    (hΩ : (∏ α : Ω, f α) = algebraMap (RatFunc F) E (RatFunc.C d)) :
    False := by
  -- the orbit-product equation in E
  have heqE := GMC2.OrbitProduct.prod_pow_card_group_eq f S x hf hfix
  rw [hS, hΩ, ← map_pow, ← map_pow] at heqE
  -- pull back along the injective algebra map `F(t) → E`
  have hinj : Function.Injective (algebraMap (RatFunc F) E) :=
    (algebraMap (RatFunc F) E).injective
  have heq : (RatFunc.C c * RatFunc.X) ^ Fintype.card G
      = (RatFunc.C d) ^ (S.card * Fintype.card (stabilizer G x)) := hinj heqE
  -- `|G| ≥ 1`
  have hG : 1 ≤ Fintype.card G := Fintype.card_pos
  exact pow_monomial_eq_const_absurd c d hc _ _ hG heq

end GMC2.Thm2067Wrapper

