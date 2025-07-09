/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

import Mathlib.RingTheory.CohenMacaulay.Catenary

/-!

# A Noetherian Ring is CM iff the Unmixed Theorem holds

-/

universe u

variable {R : Type u} [CommRing R]

class Ideal.IsUnmixed (I : Ideal R) : Prop where
  height_eq : ∀ {p : Ideal R}, p ∈ associatedPrimes R (R ⧸ I) → p.height = I.height

variable [IsNoetherianRing R]



theorem isCohenMacaulayLocalRing_iff_umixed : IsCohenMacaulayLocalRing R ↔
    ∀ (l : List R), (Ideal.ofList l).height = l.length → (Ideal.ofList l).IsUnmixed := by
  sorry
