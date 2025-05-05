/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.RingTheory.LocalRing.Defs

/-!
# Subrings of local rings

We prove basic properties of subrings of local rings.
-/

namespace IsLocalRing

variable {R S} [Semiring R] [Semiring S]

open nonZeroDivisors

/-- If a (semi)ring `R` in which every element is either invertible or a zero divisor
embeds in a local (semi)ring `S`, then `R` is local. -/
theorem of_injective [IsLocalRing S] {f : R →+* S} (hf : Function.Injective f)
    (h : ∀ a, a ∈ R⁰ → IsUnit a) : IsLocalRing R := by
  haveI : Nontrivial R := f.domain_nontrivial
  refine .of_is_unit_or_is_unit_of_add_one fun {a b} hab ↦
    (IsLocalRing.isUnit_or_isUnit_of_add_one (map_add f .. ▸ map_one f ▸ congrArg f hab)).imp ?_ ?_
  <;> exact h _ ∘ mem_nonZeroDivisors_of_injective hf ∘ IsUnit.mem_nonZeroDivisors

/-- If in a sub(semi)ring `R` of a local (semi)ring `S` every element is either
invertible or a zero divisor, then `R` is local. -/
theorem of_subring [IsLocalRing S] {R : Subsemiring S} (h : ∀ a, a ∈ R⁰ → IsUnit a) :
    IsLocalRing R :=
  of_injective R.subtype_injective h

/-- If in a sub(semi)ring `R` of a local (semi)ring `R'` every element is either
invertible or a zero divisor, then `R` is local.
This version is for `R` and `R'` that are both sub(semi)rings of a (semi)ring `S`. -/
theorem of_subring' {R R' : Subsemiring S} [IsLocalRing R'] (inc : R ≤ R')
    (h : ∀ a, a ∈ R⁰ → IsUnit a) : IsLocalRing R :=
  of_injective (Subsemiring.inclusion_injective inc) h

end IsLocalRing
