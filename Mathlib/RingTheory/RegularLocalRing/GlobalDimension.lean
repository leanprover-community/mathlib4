/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.RegularLocalRing.Basic
import Mathlib.RingTheory.GlobalDimension
import Mathlib.RingTheory.CohenMacaulay.Maximal
import Mathlib.RingTheory.Regular.AuslanderBuchsbaum
/-!

# Global Dimension of Regular Local Ring is equal to Krull Dimension

-/

--set_option pp.universes true

universe u v

variable {R : Type u} [CommRing R]

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

lemma projectiveDimension_ne_top_of_isRegularLocalRing [IsRegularLocalRing R] [Small.{v, u} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] : projectiveDimension M ≠ ⊤ := by
  rcases exist_nat_eq R with ⟨m, hm⟩
  obtain ⟨n, hn⟩ := finite_projectiveDimension_of_isRegularLocalRing_aux M m
    (by simpa [hm] using WithBot.coe_le_coe.mpr le_add_self)
  exact ne_top_of_le_ne_top (WithBot.coe_inj.not.mpr (ENat.coe_ne_top n))
    ((projectiveDimension_le_iff M n).mpr hn)

variable (R) in
theorem IsRegularLocalRing.globalDimension_eq_ringKrullDim [Small.{v} R] [IsRegularLocalRing R] :
    globalDimension.{v} R = ringKrullDim R := by
  classical
  rw [globalDimension_eq_sup_projectiveDimension_finite]
  have depth_eq : depth (ModuleCat.of R (Shrink.{v, u} R)) = ringKrullDim R := by
    rw [(isCohenMacaulayLocalRing_def R).mp isCohenMacaulayLocalRing_of_isRegularLocalRing]
    exact WithBot.coe_inj.mpr (ring_depth_invariant (maximalIdeal R) Ideal.IsPrime.ne_top'.lt_top)
  apply le_antisymm
  · simp only [iSup_le_iff]
    intro M hM
    by_cases ntr : Nontrivial M
    · have finM := projectiveDimension_ne_top_of_isRegularLocalRing M
      have nz : ¬Limits.IsZero M := ModuleCat.isZero_iff_subsingleton.not.mpr
        (not_subsingleton_iff_nontrivial.mpr ntr)
      have eq : projectiveDimension M + depth M = ringKrullDim R := by
        rw [← depth_eq, AuslanderBuchsbaum M finM]
      simpa [← eq] using WithBot.le_self_add WithBot.coe_ne_bot _
    · have : Subsingleton M := not_nontrivial_iff_subsingleton.mp ntr
      simp [(projectiveDimension_eq_bot_iff M).mpr (ModuleCat.isZero_iff_subsingleton.mpr this)]
  · let _ : Small.{v, u} (ResidueField R) := small_of_surjective IsLocalRing.residue_surjective
    let k := (ModuleCat.of R (Shrink.{v} (ResidueField R)))
    let _ : Module.Finite R k :=
      Module.Finite.equiv (Shrink.linearEquiv R (ResidueField R)).symm
    have fink := projectiveDimension_ne_top_of_isRegularLocalRing k
    have nz : ¬Limits.IsZero k := ModuleCat.isZero_iff_subsingleton.not.mpr
      (not_subsingleton_iff_nontrivial.mpr inferInstance)
    have eq : projectiveDimension k + depth k = ringKrullDim R := by
      rw [← depth_eq, AuslanderBuchsbaum k fink]
    have eq0 : depth k = 0 := by
      rw [IsLocalRing.depth_eq_sSup_length_regular, ← bot_eq_zero', sSup_eq_bot]
      simp only [exists_prop, Set.mem_setOf_eq, bot_eq_zero', forall_exists_index, and_imp]
      intro a rs reg mem len
      match rs with
      | [] => simp [← len]
      | a :: rs' =>
        simp only [RingTheory.Sequence.isRegular_cons_iff] at reg
        simp only [List.mem_cons, forall_eq_or_imp] at mem
        absurd reg.1
        simp only [isSMulRegular_iff_right_eq_zero_of_smul, not_forall]
        use 1
        simp only [one_ne_zero, not_false_eq_true, exists_prop, and_true]
        have : a • (1 : ResidueField R) = 0 := by simpa [Algebra.smul_def] using mem.1
        rw [← map_one (Shrink.algEquiv R (ResidueField R)).symm, ← map_smul, this, map_zero]
    simpa [← eq, eq0] using le_biSup projectiveDimension ‹_›
