/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Hausdorff-ness for Noetherian rings
-/

@[expose] public section

open IsLocalRing Module

variable {R : Type*} [CommRing R] (I : Ideal R)

section

variable (M : Type*) [AddCommGroup M] [Module R M]

variable [IsNoetherianRing R] [Module.Finite R M]

lemma IsHausdorff.of_le_jacobson (h : I ≤ Ideal.jacobson ⊥) : IsHausdorff I M :=
  ⟨fun x hx ↦ (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I h).le (by simpa [SModEq.zero] using hx)⟩

theorem IsHausdorff.of_isLocalRing [IsLocalRing R] (h : I ≠ ⊤) : IsHausdorff I M :=
  of_le_jacobson I M ((le_maximalIdeal h).trans (maximalIdeal_le_jacobson _))

instance [IsLocalRing R] : IsHausdorff (maximalIdeal R) M :=
  .of_le_jacobson _ _ (maximalIdeal_le_jacobson _)

lemma IsHausdorff.of_isTorsionFree [IsDomain R] [IsTorsionFree R M] (h : I ≠ ⊤) : IsHausdorff I M :=
  ⟨fun x hx ↦ (I.iInf_pow_smul_eq_bot_of_isTorsionFree h).le (by simpa [SModEq.zero] using hx)⟩

theorem IsHausdorff.of_isDomain [IsDomain R] (h : I ≠ ⊤) : IsHausdorff I R :=
  .of_isTorsionFree I R h

end

lemma AdicCompletion.isNoetherianRing_of_fg [IsNoetherianRing (R ⧸ I)] (fg : I.FG) :
    IsNoetherianRing (AdicCompletion I R) := by
  sorry

instance [IsNoetherianRing R] : IsNoetherianRing (AdicCompletion I R) :=
  AdicCompletion.isNoetherianRing_of_fg I I.fg_of_isNoetherianRing

lemma AdicCompletion.ringKrullDim_eq [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R := by
  --!!!
  sorry
