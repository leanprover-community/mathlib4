/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.NC2
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic

set_option linter.minImports true

/-!
# Discharging `HeightWitnessSupplier`: the clean `DvdK1 -> NC2` endpoint

`NC2` exposes the last internal composition boundary of the modular
GMC(2) descent as an explicit hypothesis, `HeightWitnessSupplier`: from the
exact rational lowest face plus a nonzero complex face seed, produce a
scale `A0` together with a `NormalizedHeightPackage`.  Both ingredients were
already kernel-checked -- the reference-channel extractor
(`GMC2.FaceReferenceChannel.exists_reference_channel_of_nonzero_face_seed`) and
the height-obligation theorem
(`GMC2.SupportFaceBridge.normalized_height_obligations_of_face_reference`) --
but their direct existential wrapper exceeded Lean's elaboration budget: a
pathological `whnf` explosion during unification of the seed hypothesis.

The explosion is caused by the elaborator repeatedly reducing `P.coeff`
(a `Finsupp` lookup) to weak head normal form while matching the supplied
coefficient function `fun s : F => P.coeff s` against the extractor's
parameter.  Sealing that coefficient behind an opaque local definition
(`set c := fun s => P.coeff s`) removes every occurrence available for `whnf`
to unfold, so unification succeeds structurally.  With that single change the
wrapper compiles inside the default heartbeat budget and is kernel-pure.

Consequently `HeightWitnessSupplier` is no longer a hypothesis, and the
GMC(2) descent endpoints depend only on the one published analytic input,
one-variable Duistermaat--van der Kallen (`GMC2.DvdKInterface.DvdK1`).
-/

open MvPolynomial Finset

namespace GMC2.NC2

noncomputable section

/-- The compact height-package supplier holds.  This is the "direct
existential wrapper" that `Formalization` records as exceeding the
elaboration budget; the opaque-coefficient reformulation below discharges it
kernel-purely inside the default heartbeat limit. -/
theorem heightWitnessSupplier_holds : HeightWitnessSupplier := by
  constructor
  intro P F lambda delta m0 hlower hface hseed
  -- Seal the coefficient so `whnf` cannot unfold `P.coeff` during unification.
  set c : ↥F → ℂ := fun s => P.coeff s with hc
  have hface_tilted : ∀ s ∈ F,
      GMC2.FrobeniusFace.tiltedHeight GMC2.FaceDictionary.exponentA
        GMC2.FaceDictionary.exponentB lambda s = delta := by
    intro s hs
    rw [GMC2.FaceDictionary.tiltedHeight_eq]
    exact ((hface s).mp hs).2
  obtain ⟨r0, A0, _hr0mem, hrefMass, _hrefTotCharge, hrefBalanced, _hA0eq, hrefHeight,
      _hrefFace, _htermNe⟩ :=
    GMC2.FaceReferenceChannel.exists_reference_channel_of_nonzero_face_seed
      F c lambda delta m0 hface_tilted hseed
  have hObl : GMC2.SupportFaceBridge.ReferenceHeightObligations P F m0 A0 :=
    GMC2.SupportFaceBridge.normalized_height_obligations_of_face_reference
      P F lambda delta m0 A0 r0 hlower hface hrefBalanced hrefMass hrefHeight
  exact ⟨A0, normalized_height_package_of_base P F m0 A0 hObl⟩

/-- Unconditional (given only the published one-variable DvdK input) two-variable
nullcone classification.  `HeightWitnessSupplier` is discharged by
`heightWitnessSupplier_holds`. -/
theorem nc2_of_dvdK1 (hDvdK : GMC2.DvdKInterface.DvdK1) : GMC2.NC2 :=
  nc2_of_dvdK1_of_heightWitnessSupplier hDvdK heightWitnessSupplier_holds

/-- The GMC(2) endpoint from the one-variable DvdK input alone. -/
theorem gmc2_of_dvdK1 (hDvdK : GMC2.DvdKInterface.DvdK1)
    (P Q : MvPolynomial (Fin 2) ℂ)
    (hnull : ∀ m : ℕ, 1 ≤ m → GMC2.E (P ^ m) = 0) :
    ∃ N : ℕ, ∀ m ≥ N, GMC2.E (Q * P ^ m) = 0 :=
  gmc2_of_dvdK1_of_heightWitnessSupplier hDvdK heightWitnessSupplier_holds P Q hnull

end

end GMC2.NC2

