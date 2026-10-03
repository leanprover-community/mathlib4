/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.CohenMacaulay.Maximal
public import Mathlib.RingTheory.Depth.AuslanderBuchsbaum

/-!

# Global Dimension of Regular Local Ring is equal to Krull Dimension

-/

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]

open IsLocalRing CategoryTheory

lemma finite_projectiveDimension_of_isRegularLocalRing_aux [IsRegularLocalRing R] [Small.{v, u} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] (i : ℕ) : IsLocalRing.depth M + i ≥ ringKrullDim R →
    ∃ n, HasProjectiveDimensionLE M n := by
  induction i generalizing M with
  | zero =>
    simp only [CharP.cast_eq_zero, add_zero, ge_iff_le]
    intro le
    rcases subsingleton_or_nontrivial M with sub|ntr
    · exact ⟨0, inferInstance⟩
    · have := (isMaximalCohenMacaulay_def M).mpr (le_antisymm (depth_le_ringKrullDim M) le)
      have := free_of_isMaximalCohenMacaulay_of_isRegularLocalRing M
      exact ⟨0, inferInstance⟩
  | succ i ih =>
    rw [Nat.cast_add, Nat.cast_one, ge_iff_le, add_comm _ 1, ← add_assoc]
    intro le
    rcases subsingleton_or_nontrivial M with sub|ntr
    · exact ⟨0, inferInstance⟩
    · rcases Module.exists_finite_presentation R M with ⟨P, _, _, _, _, f, surjf⟩
      let S : ShortComplex (ModuleCat.{v} R) := f.shortComplexKer
      have S_exact : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
      have ge : IsLocalRing.depth S.X₁ ≥ IsLocalRing.depth S.X₂ ⊓ (IsLocalRing.depth M + 1) :=
        moduleDepth_ge_min_of_shortExact_fst_snd _ S S_exact
      have ge' : (depth S.X₁) + i ≥ ringKrullDim R := by
        apply le_trans _ (add_le_add_left (WithBot.coe_le_coe.mpr ge) i)
        have : IsLocalRing.depth S.X₂ = IsLocalRing.depth (ModuleCat.of R R) := by
          have : Nontrivial S.X₂ := surjf.nontrivial
          exact (free_depth_eq_ring_depth S.X₂ _).trans
            (ring_depth_shrink_eq (maximalIdeal R) Ideal.IsPrime.ne_top'.lt_top)
        simpa [← (isCohenMacaulayLocalRing_def R).mp isCohenMacaulayLocalRing_of_isRegularLocalRing,
          this, min_add] using ⟨WithBot.le_self_add (WithBot.natCast_ne_bot i) (ringKrullDim R), le⟩
      rcases ih S.X₁ ge' with ⟨m, hm⟩
      exact ⟨m + 1, (S_exact.hasProjectiveDimensionLT_X₃_iff m inferInstance).mpr hm⟩

lemma projectiveDimension_ne_top_of_isRegularLocalRing [IsRegularLocalRing R] [Small.{v, u} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] : projectiveDimension M ≠ ⊤ := by
  rcases FiniteRingKrullDim.ringKrullDim_eq_nat R with ⟨m, hm⟩
  obtain ⟨n, hn⟩ := finite_projectiveDimension_of_isRegularLocalRing_aux M m
    (by simpa [hm] using! WithBot.coe_le_coe.mpr le_add_self)
  exact ne_top_of_le_ne_top (WithBot.coe_inj.not.mpr (ENat.natCast_ne_top n))
    ((projectiveDimension_le_iff M n).mpr hn)
