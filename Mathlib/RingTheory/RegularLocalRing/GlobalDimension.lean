/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.CohenMacaulay.Maximal
import Mathlib.RingTheory.Regular.AuslanderBuchsbaum
/-!

# Global Dimension of Regular Local Ring is equal to Krull Dimension

-/

--set_option pp.universes true

universe u v

variable (R : Type u) [CommRing R]

open IsLocalRing CategoryTheory

lemma finite_projectiveDimension_of_isRegularLocalRing_aux [IsRegularLocalRing R] [Small.{v, u} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] (i : ℕ) : IsLocalRing.depth M + i ≥ ringKrullDim R →
    ∃ n, HasProjectiveDimensionLE M n := by
  induction i generalizing M
  · simp only [CharP.cast_eq_zero, add_zero, ge_iff_le]
    intro le
    by_cases ntr : Nontrivial M
    · let _ := (isMaximalCohenMacaulay_def M).mpr (le_antisymm (depth_le_ringKrullDim M) le)
      let _ := free_of_isMaximalCohenMacaulay_of_isRegularLocalRing M
      use 0
      exact instHasProjectiveDimensionLTOfNatNatOfProjective M
    · have := ModuleCat.isZero_iff_subsingleton.mpr (not_nontrivial_iff_subsingleton.mp ntr)
      have := CategoryTheory.Limits.IsZero.hasProjectiveDimensionLT_zero this
      use 0
      exact CategoryTheory.instHasProjectiveDimensionLTSucc M 0
  · rename_i i ih _
    rw [Nat.cast_add, Nat.cast_one, ge_iff_le, add_comm _ 1, ← add_assoc]
    intro le
    by_cases ntr : Nontrivial M
    · rcases Module.Finite.exists_fin' R M with ⟨n, f', hf'⟩
      let f := f'.comp ((Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)).trans
        (Finsupp.linearEquivFunOnFinite R R (Fin n))).1
      have surjf : Function.Surjective f := by simpa [f] using hf'
      let S : ShortComplex (ModuleCat.{v} R) := {
        f := ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
        g := ModuleCat.ofHom.{v} f
        zero := by
          ext x
          simp }
      have S_exact : S.ShortExact := {
        exact := by
          apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
          intro x
          simp [S]
        mono_f := (ModuleCat.mono_iff_injective S.f).mpr (LinearMap.ker f).injective_subtype
        epi_g := (ModuleCat.epi_iff_surjective S.g).mpr surjf}
      let _ : Module.Finite R S.X₂ := by
        simp [S, Module.Finite.equiv (Shrink.linearEquiv R R).symm, Finite.of_fintype (Fin n)]
      let _ : Module.Free R (Shrink.{v, u} R) :=  Module.Free.of_equiv (Shrink.linearEquiv R R).symm
      let _ : Module.Free R S.X₂ := Module.Free.finsupp R (Shrink.{v, u} R) _
      have proj := ModuleCat.projective_of_categoryTheory_projective S.X₂
      have ge : IsLocalRing.depth S.X₁ ≥ IsLocalRing.depth S.X₂ ⊓ (IsLocalRing.depth M + 1) :=
        moduleDepth_ge_min_of_shortExact_fst_snd _ S S_exact
      have ge' : (depth S.X₁) + i ≥ ringKrullDim R := by
        apply le_trans _ (add_le_add_right (WithBot.coe_le_coe.mpr ge) i)
        have : IsLocalRing.depth S.X₂ = IsLocalRing.depth (ModuleCat.of R R) := by
          let _ : Nontrivial S.X₂ := surjf.nontrivial
          exact (free_depth_eq_ring_depth S.X₂ _).trans
            (ring_depth_invariant (maximalIdeal R) Ideal.IsPrime.ne_top'.lt_top)
        simpa [← (isCohenMacaulayLocalRing_def R).mp isCohenMacaulayLocalRing_of_isRegularLocalRing,
          this, min_add] using ⟨WithBot.le_self_add (WithBot.natCast_ne_bot i) (ringKrullDim R), le⟩
      rcases ih S.X₁ ge' with ⟨m, hm⟩
      use m + 1
      exact (S_exact.hasProjectiveDimensionLT_X₃_iff m proj).mpr hm
    · have := ModuleCat.isZero_iff_subsingleton.mpr (not_nontrivial_iff_subsingleton.mp ntr)
      have := CategoryTheory.Limits.IsZero.hasProjectiveDimensionLT_zero this
      use 0
      exact CategoryTheory.instHasProjectiveDimensionLTSucc M 0

lemma finite_projectiveDimension_of_isRegularLocalRing [IsRegularLocalRing R] [Small.{v, u} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] : ∃ n, HasProjectiveDimensionLE M n := by
  rcases exist_nat_eq R with ⟨m, hm⟩
  apply finite_projectiveDimension_of_isRegularLocalRing_aux R M m
  simpa [hm] using WithBot.coe_le_coe.mpr le_add_self
