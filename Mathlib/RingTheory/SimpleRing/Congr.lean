/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Simpleness is preserved by ring isomorphism/surjective ring homomorphisms

If `R` is a simple (non-assoc) ring and there exists surjective `f : R →+* S` where `S` is
nontrivial, then `S` is also simple.
If `R` is a simple (non-unital non-assoc) ring then any ring isomorphic to `R` is also simple.
-/

namespace IsSimpleRing

lemma of_surjective {R S : Type*} [NonAssocRing R] [NonAssocRing S] [Nontrivial S]
    (f : R →+* S) (h : IsSimpleRing R) (hf : Function.Surjective f) : IsSimpleRing S where
  simple := OrderIso.isSimpleOrder (RingEquiv.ofBijective f
    ⟨RingHom.injective f, hf⟩).symm.mapTwoSidedIdeal

lemma of_ringEquiv {R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    (f : R ≃+* S) (h : IsSimpleRing R) : IsSimpleRing S where
  simple := OrderIso.isSimpleOrder f.symm.mapTwoSidedIdeal

end IsSimpleRing

open TwoSidedIdeal in
theorem isSimpleRing_iff_isTwoSided_imp {R : Type*} [Ring R] :
    IsSimpleRing R ↔ Nontrivial R ∧ ∀ I : Ideal R, I.IsTwoSided → I = ⊥ ∨ I = ⊤ := by
  let e := orderIsoIsTwoSided (R := R)
  simp_rw [isSimpleRing_iff, isSimpleOrder_iff, orderIsoRingCon.toEquiv.nontrivial_congr,
    RingCon.nontrivial_iff, e.forall_congr_left, Subtype.forall, ← e.injective.eq_iff]
  simp [e, Subtype.ext_iff]
