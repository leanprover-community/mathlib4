/-
Copyright (c) 2026 emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: emlis
-/
module

public import Mathlib.Algebra.ContinuedFractions.Basic

/-!
# Euler's continued fraction

This file formalizes an transformation on generalized continued fractions over a field `K`.
It defines a map sending a generalized continued fraction to an equivalent Euler's continued
fraction obtained by an explicit transformation of its coefficient stream.

## Main definitions

* `GenContFract.Euler` : constructs a generalized continued fraction from a head term `h`
  and a coefficient stream `ρ`.
* `GenContFract.toEuler` : transforms a generalized continued fraction to a Euler's continued
  fraction.

## Main results (planned)

* `euler_convs` : explicit formula for convergents of an Euler-transformed continued fraction.
* `convs_eq_toEuler_convs` : equivalence of convergents between a continued fraction and its
  Euler transform (under suitable non-degeneracy conditions).

## References

* https://en.wikipedia.org/wiki/Euler%27s_continued_fraction_formula
* [Wall, H.S., *Analytic Theory of Continued Fractions*][wall2018analytic]

-/

public section

namespace GenContFract

variable {K : Type*} [Field K]

/-- A *Euler's continued fraction* is a generalized continued fraction of the form
$$
  h + \cfrac{\rho_0}
            {1 - \cfrac{\rho_1}
                       {1 + \rho_1 - \cfrac{\rho_2}
                                           {1 + \rho_2 - \cfrac{\rho_3}
                                                               {1 + \rho_3 - \dots}}}}
$$
`Euler h ρ` constructs a Euler's continued fraction whose coefficients are obtained
from the stream `ρ` with head term `h`.
-/
def Euler (h : K) (ρ : Stream'.Seq K) : GenContFract K :=
  ⟨h, ⟨
    fun n => match n with
    | 0 => (ρ.get? n).map fun ρ => ⟨ρ, 1⟩
    | _ => (ρ.get? n).map fun ρ => ⟨-ρ, 1 + ρ⟩,
    fun {n} h => match n with
    | 0 => by simp_all
    | n + 1 => by simp at h; simpa using ρ.property h
  ⟩⟩

private def toEulerAux (g : GenContFract K) : Stream'.Seq K :=
  ⟨
    fun n => match n with
    | 0 => (g.s.get? n).map fun c => c.a / c.b
    | _ => (g.s.get? n).map fun c => - c.a * g.dens (n - 1) / g.dens (n + 1),
    fun {n} h => match n with
    | 0 => by simp_all
    | n + 1 => by simp at h; simpa using g.s.property h
  ⟩

/--
`toEuler g` is the Euler's continued fraction equivalent to `g`, where `ρ₀` = `a₀ / b₀` and
`ρₙ` = `- aₙ * Bₙ₋₁ / Bₙ₊₁` for `n > 0`.
-/
def toEuler (g : GenContFract K) : GenContFract K :=
  Euler g.h (toEulerAux g)

end GenContFract
