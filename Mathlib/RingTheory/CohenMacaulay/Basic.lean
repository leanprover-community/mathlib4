/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.Regular.Ischebeck
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Definition of Cohen-Macaulay Ring

-/

universe v' v u' u

variable {R : Type u} [CommRing R]

open RingTheory.Sequence IsLocalRing ModuleCat

class ModuleCat.IsCohenMacaulay [IsLocalRing R] [Small.{v} R]
    [Small.{v} (R ⧸ (maximalIdeal R))] (M : ModuleCat.{v} R) : Prop where
  depth_eq_dim : Subsingleton M ∨ Module.supportDim R M = IsLocalRing.depth M

lemma ModuleCat.isCohenMacaulay_iff [IsLocalRing R] [Small.{v} R]
    [Small.{v} (R ⧸ (maximalIdeal R))] (M : ModuleCat.{v} R) :
    M.IsCohenMacaulay ↔ Subsingleton M ∨ Module.supportDim R M = IsLocalRing.depth M :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma ModuleCat.depth_eq_supportDim_of_cohenMacaulay [IsLocalRing R] [Small.{v} R]
    [Small.{v} (R ⧸ (maximalIdeal R))] (M : ModuleCat.{v} R) [cm : M.IsCohenMacaulay]
    [ntr : Nontrivial M] : Module.supportDim R M = IsLocalRing.depth M := by
  have : ¬ Subsingleton M := not_subsingleton_iff_nontrivial.mpr ntr
  have := M.isCohenMacaulay_iff.mp cm
  tauto

lemma ModuleCat.depth_eq_supportDim_unbot_of_cohenMacaulay [IsLocalRing R] [Small.{v} R]
    [Small.{v} (R ⧸ (maximalIdeal R))] (M : ModuleCat.{v} R) [cm : M.IsCohenMacaulay]
    [ntr : Nontrivial M] : (Module.supportDim R M).unbot
    (Module.supportDim_ne_bot_of_nontrivial R M) = IsLocalRing.depth M := by
  simp [M.depth_eq_supportDim_of_cohenMacaulay]

--isCohenMacaulay under iso

--isCohenMacaulay universe invariant

section IsLocalization

variable [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R)
  [Small.{v} R] [Small.{v} (R ⧸ (maximalIdeal R))]

lemma depth_eq_dim_quotient_associated_prime_of_isCohenMacaulay (M : ModuleCat.{v} R)
    [M.IsCohenMacaulay] [Module.Finite R M] [Nontrivial M] [Small.{v} (R ⧸ p)]
    (mem : p ∈ associatedPrimes R M) :
    IsLocalRing.depth M = (ringKrullDim (R ⧸ p)).unbot
    (quotient_prime_ringKrullDim_ne_bot mem.1) := by
  apply le_antisymm (depth_le_ringKrullDim_associatedPrime M p mem)
  rw [← M.depth_eq_supportDim_unbot_of_cohenMacaulay]
  rw [← WithBot.coe_le_coe, WithBot.coe_unbot, WithBot.coe_unbot,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective
    (le_of_eq_of_le Submodule.annihilator_top.symm (AssociatePrimes.mem_iff.mp mem).annihilator_le))

--will update the two sets are equal when done with works about `Ass(M)`
lemma associated_prime_minimal_of_isCohenMacaulay (M : ModuleCat.{v} R)
    [M.IsCohenMacaulay] [Module.Finite R M] [Nontrivial M] [Small.{v} (R ⧸ p)]
    (mem : p ∈ associatedPrimes R M) : p ∈ (Module.annihilator R M).minimalPrimes := by
  have eq := Eq.trans M.depth_eq_supportDim_unbot_of_cohenMacaulay
    (depth_eq_dim_quotient_associated_prime_of_isCohenMacaulay p M mem)
  rw [← WithBot.coe_inj, WithBot.coe_unbot, WithBot.coe_unbot, ringKrullDim_quotient,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator, ringKrullDim_quotient] at eq
  let _ : p.IsPrime := mem.1
  have ann_le : Module.annihilator R M ≤ p := (le_of_eq_of_le Submodule.annihilator_top.symm
    (AssociatePrimes.mem_iff.mp mem).annihilator_le)
  rcases Ideal.exists_minimalPrimes_le ann_le with ⟨p', hp', le⟩
  rcases lt_or_eq_of_le le with lt|eq
  · classical
    let f : WithBot (PrimeSpectrum.zeroLocus (p : Set R)) →
        (PrimeSpectrum.zeroLocus ((Module.annihilator R M) : Set R)):= fun I ↦ by
        by_cases eqbot : I = ⊥
        · exact ⟨⟨p', Ideal.minimalPrimes_isPrime hp'⟩, hp'.1.2⟩
        · exact ⟨(I.unbot eqbot).1, PrimeSpectrum.zeroLocus_anti_mono ann_le (I.unbot eqbot).2⟩
    have f_mono : StrictMono f := by
      intro a b alt
      by_cases eqbot : a = ⊥
      · simp only [eqbot, ↓reduceDIte, alt.ne_bot, Subtype.mk_lt_mk, f]
        apply lt_of_lt_of_le lt (b.unbot alt.ne_bot).2
      · simp only [eqbot, ↓reduceDIte, alt.ne_bot, Subtype.mk_lt_mk, Subtype.coe_lt_coe, f]
        rw [← WithBot.coe_lt_coe, WithBot.coe_unbot, WithBot.coe_unbot]
        exact alt
    have dim_le := Order.krullDim_le_of_strictMono f f_mono
    let _ : Nonempty (PrimeSpectrum.zeroLocus (p : Set R)) := Nonempty.intro ⟨⟨p, mem.1⟩, le_refl p⟩
    rw [Order.krullDim_withBot, eq, ← ringKrullDim_quotient] at dim_le
    have nebot : ringKrullDim (R ⧸ p) ≠ ⊥ := quotient_prime_ringKrullDim_ne_bot mem.1
    have netop : (ringKrullDim (R ⧸ p)).unbot nebot ≠ ⊤ := by
      have : FiniteRingKrullDim R := instFiniteRingKrullDimOfIsNoetherianRingOfIsLocalRing
      have : ringKrullDim (R ⧸ p) ≠ ⊤ :=
        ne_top_of_le_ne_top ringKrullDim_ne_top
         (ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) (Ideal.Quotient.mk_surjective))
      simpa [← WithBot.coe_inj.not]
    rcases ENat.ne_top_iff_exists.mp netop with ⟨m, hm⟩
    have : (ringKrullDim (R ⧸ p)).unbot nebot + 1 ≤ (ringKrullDim (R ⧸ p)).unbot nebot := by
      rw [← WithBot.coe_le_coe]
      simpa using dim_le
    absurd this
    rw [← hm, not_le, ← ENat.coe_one, ← ENat.coe_add, ENat.coe_lt_coe]
    exact lt_add_one m
  · simpa [← eq] using hp'

lemma ENat.add_right_cancel_iff (a b c : ℕ∞) (netop : c ≠ ⊤) : a + c = b + c ↔ a = b :=
  ⟨fun h ↦ ENat.add_left_injective_of_ne_top netop h, fun h ↦ by rw [h]⟩

lemma withBotENat_add_coe_cancel (a b : WithBot ℕ∞) (c : ℕ) : a + c = b + c ↔ a = b := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  by_cases eqbot : a = ⊥
  · simp [eqbot, WithBot.bot_add] at h
    rw [WithBot.add_coe_eq_bot_iff.mp h.symm, eqbot]
  · by_cases eqbot' : b = ⊥
    · absurd eqbot
      simpa [eqbot'] using h
    · have : a.unbot eqbot + c = b.unbot eqbot' + c := by
        apply WithBot.coe_inj.mp
        convert h
        repeat simp;rfl
      rw [← WithBot.coe_unbot a eqbot, ← WithBot.coe_unbot b eqbot', WithBot.coe_inj]
      simpa [ENat.add_right_cancel_iff _ _ _ (ENat.coe_ne_top c)] using this

lemma quotient_regular_isCohenMacaulay_iff_isCohenMacaulay
    (M : ModuleCat.{v} R) [Module.Finite R M] (rs : List R) (reg : IsRegular M rs) :
    M.IsCohenMacaulay ↔
    (ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))).IsCohenMacaulay := by
  have ntr2 : Nontrivial (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) :=
    (IsRegular.quot_ofList_smul_nontrivial reg ⊤)
  have ntr1 : Nontrivial M := Function.Surjective.nontrivial (Submodule.mkQ_surjective
    (Ideal.ofList rs • (⊤ : Submodule R M)))
  simp only [isCohenMacaulay_iff, ← not_nontrivial_iff_subsingleton, ntr1, not_true_eq_false,
    false_or, ntr2]
  rw [← Module.supportDim_regular_sequence_add_length_eq_supportDim rs reg,
    ← depth_quotient_regular_sequence_add_length_eq_depth M rs reg, WithBot.coe_add]
  exact withBotENat_add_coe_cancel _ _ rs.length

variable [p.IsPrime] {Rₚ : Type u'} [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
  [IsLocalRing Rₚ]
  -- This can be deduced from `IsLocalization.AtPrime Rₚ p`, but cannot be an
  -- `instance`, so we need to manually add this condition.
  [Small.{v'} Rₚ] [Small.{v'} (Rₚ ⧸ (maximalIdeal Rₚ))] [IsNoetherianRing Rₚ]

variable (M : ModuleCat.{v} R) (Mₚ : ModuleCat.{v'} Rₚ)
  [Module R Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]

include p f

open Pointwise in
lemma isLocaliation_map_is_weakly_regular_of_is_weakly_regular (rs : List R)
    (M : Type*) [AddCommGroup M] [Module R M] (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]
    (reg : IsWeaklyRegular M rs) : IsWeaklyRegular Mₚ (rs.map (algebraMap R Rₚ)) := by
  generalize len : rs.length = n
  induction' n with n ih generalizing M Mₚ rs
  · simp [List.length_eq_zero_iff.mp len]
  · match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [isWeaklyRegular_cons_iff, List.map_cons] at reg ⊢
      constructor
      · rw [isSMulRegular_algebraMap_iff x, isSMulRegular_iff_ker_lsmul_eq_bot Mₚ x,
          LinearMap.ker_eq_bot']
        intro m hm
        rcases IsLocalizedModule.mk'_surjective p.primeCompl f m with ⟨a, ha⟩
        simp only [← ha, LinearMap.lsmul_apply] at hm ⊢
        have : x • IsLocalizedModule.mk' f a.1 a.2 = 0 := hm
        rw [← IsLocalizedModule.mk'_smul, IsLocalizedModule.mk'_eq_zero'] at this
        simp only [Subtype.exists, Submonoid.mk_smul, exists_prop] at this
        rcases this with ⟨s, mem, hs⟩
        rw [smul_smul, mul_comm, ← smul_smul] at hs
        apply (IsLocalizedModule.mk'_eq_zero' f a.2).mpr ⟨⟨s, mem⟩, ?_⟩
        simp only [Submonoid.mk_smul, ← Submodule.mem_bot (R := R),
          ← (isSMulRegular_iff_ker_lsmul_eq_bot M x).mp reg.1]
        exact hs
      · let f : QuotSMulTop x M →ₗ[R] QuotSMulTop ((algebraMap R Rₚ) x) Mₚ :=
          sorry
        have : IsLocalizedModule.AtPrime p f := sorry
        exact ih rs' (QuotSMulTop x M) (QuotSMulTop ((algebraMap R Rₚ) x) Mₚ) f reg.2 len

lemma isLocalization_at_prime_prime_depth_le_depth [Small.{v} (R ⧸ p)] [Module.Finite R M]
    [Nontrivial M] [Nontrivial Mₚ] : p.depth M ≤ IsLocalRing.depth Mₚ := by
  let _ : Module.Finite Rₚ Mₚ := sorry
  simp only [IsLocalRing.depth_eq_sSup_length_regular, Ideal.depth]
  let _ : Module.Finite R (ModuleCat.of R (Shrink.{v, u} (R ⧸ p))) := sorry
  have smul_lt : p • (⊤ : Submodule R M) < ⊤ :=
    Ne.lt_top' (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      ((IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top')).trans
      (IsLocalRing.maximalIdeal_le_jacobson _)))
  have h_supp : Module.support R (of R (Shrink.{v, u} (R ⧸ p))) = PrimeSpectrum.zeroLocus p := by
    rw [(Shrink.linearEquiv (R ⧸ p) R).support_eq, Module.support_eq_zeroLocus,
      Ideal.annihilator_quotient]
  rw [moduleDepth_eq_sSup_length_regular p _ _ smul_lt h_supp]
  apply sSup_le (fun n hn ↦ le_sSup ?_)
  rcases hn with ⟨rs, reg, mem, len⟩

  sorry

lemma isLocalize_at_prime_dim_eq_prime_depth_of_isCohenMacaulay [Small.{v} (R ⧸ p)]
    [M.IsCohenMacaulay] : Module.supportDim Rₚ Mₚ = p.depth M := by
  have : p.depth M ≠ ⊤ := sorry
  rcases ENat.ne_top_iff_exists.mp this with ⟨n, hn⟩
  induction' n with n ih generalizing M Mₚ
  · sorry
  · sorry

lemma isLocalize_at_prime_isCohenMacaulay_of_isCohenMacaulay [M.IsCohenMacaulay] :
    Mₚ.IsCohenMacaulay := by
  sorry

lemma isLocalize_at_prime_depth_eq_of_isCohenMacaulay [Small.{v} (R ⧸ p)] [M.IsCohenMacaulay] :
    p.depth M = IsLocalRing.depth Mₚ := sorry

end IsLocalization

--have some universe problem may have better statement using `IsLocalizedModule`
lemma localize_at_prime_isCohenMacaulay_of_isCohenMacaulay [IsLocalRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [Small.{v} R] [Small.{v} (R ⧸ (maximalIdeal R))]
    (M : ModuleCat.{v} R) [M.IsCohenMacaulay] :
    (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).IsCohenMacaulay :=
  isLocalize_at_prime_isCohenMacaulay_of_isCohenMacaulay p M _
    (LocalizedModule.mkLinearMap p.primeCompl M)

--have some universe problem may have better statement using `IsLocalizedModule`
lemma localize_at_prime_depth_eq_of_isCohenMacaulay [IsLocalRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [Small.{v} R] [Small.{v} (R ⧸ (maximalIdeal R))] [Small.{v} (R ⧸ p)]
    (M : ModuleCat.{v} R) [M.IsCohenMacaulay] : p.depth M =
    IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M)) :=
  isLocalize_at_prime_depth_eq_of_isCohenMacaulay p M _
    (LocalizedModule.mkLinearMap p.primeCompl M)

variable (R)

class IsCohenMacaulayLocalRing : Prop extends IsLocalRing R where
  depth_eq_dim : ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R)

class IsCohenMacaulayRing : Prop where
  CM_localize : ∀ p : Ideal R, ∀ (_ : p.IsPrime), IsCohenMacaulayLocalRing (Localization.AtPrime p)

lemma isCohenMacaulayRing_iff : IsCohenMacaulayRing R ↔
    ∀ m : Ideal R, ∀ (_ : m.IsMaximal), IsCohenMacaulayLocalRing (Localization.AtPrime m) := by
  sorry

--unmixedness theorem

--polynomial ring over CM ring is CM
