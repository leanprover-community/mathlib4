/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Integral ring homomorphisms over local rings are local -/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

instance [IsLocalRing R] [Algebra.IsIntegral R S] [Nontrivial S] :
    IsLocalHom (algebraMap R S) := by
  have : (algebraMap R S).kerLift.IsIntegral :=
    .tower_top (Ideal.Quotient.mk _) _
      (by have := algebraMap_isIntegral_iff.mpr ‹Algebra.IsIntegral R S›; exact this)
  have := this.isLocalHom (algebraMap R S).kerLift_injective
  have : Nontrivial (R ⧸ RingHom.ker (algebraMap R S)) :=
    Ideal.Quotient.nontrivial_iff.mpr (RingHom.ker_ne_top _)
  have : IsLocalHom (Ideal.Quotient.mk (RingHom.ker (algebraMap R S))) :=
    .of_surjective _ Ideal.Quotient.mk_surjective
  exact RingHom.isLocalHom_comp (algebraMap R S).kerLift (Ideal.Quotient.mk _)
