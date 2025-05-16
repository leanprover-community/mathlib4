/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.Regular.Depth
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.Algebra.Module.LocalizedModule.AtPrime

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

--isCohenMacaulay under iso

--isCohenMacaulay universe invariant

section IsLocalization

variable [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
  [Small.{v} R] [Small.{v} (R ⧸ (maximalIdeal R))]

lemma depth_eq_dim_quotient_associated_prime_of_isCohenMacaulay (M : ModuleCat.{v} R)
    [M.IsCohenMacaulay] (mem : p ∈ associatedPrimes R M) :
    IsLocalRing.depth M = ringKrullDim (R ⧸ p) := by
  sorry

--will update the two sets are equal when done with works about `Ass(M)`
lemma associated_prime_minimal_of_isCohenMacaulay (M : ModuleCat.{v} R)
    [M.IsCohenMacaulay] (mem : p ∈ associatedPrimes R M) :
    p ∈ (Module.annihilator R M).minimalPrimes := by
  sorry

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

variable {Rₚ : Type u'} [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
  [IsLocalRing Rₚ]
  -- This can be deduced from `IsLocalization.AtPrime Rₚ p`, but cannot be an
  -- `instance`, so we need to manually add this condition.
  [Small.{v'} Rₚ] [Small.{v'} (Rₚ ⧸ (maximalIdeal Rₚ))]

variable (M : ModuleCat.{v} R) (Mₚ : ModuleCat.{v'} Rₚ)
  [Module R Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]

include p f

lemma isLocalize_at_prime_prime_depth_le_depth [Small.{v} (R ⧸ p)] :
    p.depth M ≤ IsLocalRing.depth Mₚ := by
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
