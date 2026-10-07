/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Roots of unity in a quotient ring

For `I` an ideal of a commutative ring `R`, reduction modulo `I` sends the roots of unity of `R`
of order `n` to units of `R ⧸ I`.

## Main definitions

* `Ideal.rootsOfUnityMapQuot`: the group morphism from the group of roots of unity of `R` of
  order `n` to `(R ⧸ I)ˣ` induced by the quotient map.

-/

public section

variable {R : Type*} [CommRing R] (I : Ideal R)

/--
For `I` an ideal of `R`, the group morphism from the group of roots of unity of `R`
of order `n` to `(R ⧸ I)ˣ`.
-/
@[expose]
def Ideal.rootsOfUnityMapQuot (n : ℕ) : (rootsOfUnity n R) →* (R ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).domRestrict _

@[simp]
theorem Ideal.rootsOfUnityMapQuot_apply (n : ℕ) {x : Rˣ} (hx : x ∈ rootsOfUnity n R) :
    Ideal.rootsOfUnityMapQuot I n ⟨x, hx⟩ = Ideal.Quotient.mk I x := rfl
