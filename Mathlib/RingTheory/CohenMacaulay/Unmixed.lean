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

open RingTheory.Sequence

class Ideal.IsUnmixed (I : Ideal R) : Prop where
  height_eq : ∀ {p : Ideal R}, p ∈ associatedPrimes R (R ⧸ I) → p.height = I.height

variable [IsNoetherianRing R]

theorem isCohenMacaulayRing_of_unmixed
    (unmix : ∀ (l : List R), (Ideal.ofList l).height = l.length → (Ideal.ofList l).IsUnmixed) :
    IsCohenMacaulayRing R := by
  apply (isCohenMacaulayRing_def R).mpr (fun p hp ↦ ?_)
  have : p.height ≠ ⊤ := by
    have := p.finiteHeight_of_isNoetherianRing.1
    have := Ideal.IsPrime.ne_top hp
    tauto
  have (i : ℕ) : i ≤ p.height → ∃ rs : List R, ∀ r ∈ rs, r ∈ p ∧ IsWeaklyRegular R rs ∧
    rs.length = i := by
    induction' i with i hi
    · sorry
    · sorry
  sorry

theorem isCohenMacaulayRing_iff_unmixed : IsCohenMacaulayRing R ↔
    ∀ (l : List R), (Ideal.ofList l).height = l.length → (Ideal.ofList l).IsUnmixed := by
  sorry
