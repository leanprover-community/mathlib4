/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.RegularLocalRing.GlobalDimension
public import Mathlib.RingTheory.RegularLocalRing.RegularRing.Basic

/-!

# Global Dimension of Regular Ring is equal to Krull Dimension

-/

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]

open IsLocalRing CategoryTheory

variable (R) in
theorem IsRegularRing.globalDimension_eq_ringKrullDim [Small.{v} R] [IsRegularRing R] :
    globalDimension.{v} R = ringKrullDim R := by
  rcases subsingleton_or_nontrivial R with sub|ntr
  · rw [(globalDimension_eq_bot_iff R).mpr sub, ringKrullDim_eq_bot_of_subsingleton]
  · rw [globalDimension_eq_iSup_loclization_maximal]
    let _ : Nonempty ((Subtype (Ideal.IsMaximal (α := R)))) :=
      nonempty_subtype.mpr (Ideal.exists_maximal R)
    let f := fun (x : Subtype (Ideal.IsMaximal (α := R))) ↦ x.1.height
    have bdd : BddAbove (Set.range f) := by
      have : ringKrullDim R ≠ ⊥ :=
        ne_bot_of_le_ne_bot WithBot.zero_ne_bot ringKrullDim_nonneg_of_nontrivial
      use (ringKrullDim R).unbot this
      refine mem_upperBounds.mpr (fun x ⟨y, hy⟩ ↦ ?_)
      simpa [← hy, WithBot.le_unbot_iff] using
        Ideal.height_le_ringKrullDim_of_ne_top y.2.isPrime.ne_top
    rw [← Ideal.sup_height_of_maximal_eq_ringKrullDim, iSup_subtype', WithBot.coe_iSup bdd]
    apply le_antisymm
    · simp only [iSup_le_iff]
      intro p
      have := isRegularRing_iff.mp ‹_› p.1 (Ideal.IsMaximal.isPrime' p.1)
      have : Small.{v} (Localization.AtPrime p.1) :=
        small_of_surjective Localization.mkHom_surjective
      rw [IsRegularLocalRing.globalDimension_eq_ringKrullDim.{u, v} (Localization.AtPrime p.1),
        IsLocalization.AtPrime.ringKrullDim_eq_height p.1]
      exact le_iSup (fun i ↦ (f i : WithBot ℕ∞)) ⟨p.1, p.2⟩
    · simp only [iSup_le_iff]
      intro ⟨p, hp⟩
      have := isRegularRing_iff.mp ‹_› p (Ideal.IsMaximal.isPrime' p)
      have : Small.{v} (Localization.AtPrime p) :=
        small_of_surjective Localization.mkHom_surjective
      simp only [f, ← IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
        ← IsRegularLocalRing.globalDimension_eq_ringKrullDim.{u, v} (Localization.AtPrime p)]
      exact le_iSup (fun (p : MaximalSpectrum R) ↦ globalDimension (Localization.AtPrime p.1))
        ⟨p, hp⟩
