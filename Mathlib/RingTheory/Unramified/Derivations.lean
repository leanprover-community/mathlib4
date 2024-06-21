/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Unramified.Basic

/-!

# Differential properties of formally unramified algebras

We show that `R`-algebra `A` is formally unramified iff the Kaehler differentials vanish.

-/

universe u

namespace Algebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

instance FormallyUnramified.subsingleton_kaehlerDifferential [FormallyUnramified R S] :
    Subsingleton (Ω[S⁄R]) := by
  rw [← not_nontrivial_iff_subsingleton]
  intro h
  obtain ⟨f₁, f₂, e⟩ := (KaehlerDifferential.endEquiv R S).injective.nontrivial
  apply e
  ext1
  apply FormallyUnramified.lift_unique' _ _ _ _ (f₁.2.trans f₂.2.symm)
  rw [← AlgHom.toRingHom_eq_coe, AlgHom.ker_kerSquareLift]
  exact ⟨_, Ideal.cotangentIdeal_square _⟩
#align algebra.formally_unramified.subsingleton_kaehler_differential Algebra.FormallyUnramified.subsingleton_kaehlerDifferential

theorem FormallyUnramified.iff_subsingleton_kaehlerDifferential :
    FormallyUnramified R S ↔ Subsingleton (Ω[S⁄R]) := by
  constructor
  · intros; infer_instance
  · intro H
    constructor
    intro B _ _ I hI f₁ f₂ e
    letI := f₁.toRingHom.toAlgebra
    haveI := IsScalarTower.of_algebraMap_eq' f₁.comp_algebraMap.symm
    have :=
      ((KaehlerDifferential.linearMapEquivDerivation R S).toEquiv.trans
            (derivationToSquareZeroEquivLift I hI)).surjective.subsingleton
    exact Subtype.ext_iff.mp (@Subsingleton.elim _ this ⟨f₁, rfl⟩ ⟨f₂, e.symm⟩)
#align algebra.formally_unramified.iff_subsingleton_kaehler_differential Algebra.FormallyUnramified.iff_subsingleton_kaehlerDifferential
