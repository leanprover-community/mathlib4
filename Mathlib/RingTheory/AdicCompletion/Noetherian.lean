/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Filtration

/-!
# Hausdorff-ness for noetherian rings
-/

open IsLocalRing

variable {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [Module.Finite R M]

lemma IsHausdorff.of_le_jacobson (h : I ≤ Ideal.jacobson ⊥) : IsHausdorff I M :=
  ⟨fun x hx ↦ (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I h).le (by simpa [SModEq.zero] using hx)⟩

theorem IsHausdorff.of_isLocalRing [IsLocalRing R] (h : I ≠ ⊤) : IsHausdorff I M :=
  of_le_jacobson I M ((le_maximalIdeal h).trans (maximalIdeal_le_jacobson _))

instance [IsLocalRing R] : IsHausdorff (maximalIdeal R) M :=
  .of_le_jacobson _ _ (maximalIdeal_le_jacobson _)

theorem IsHausdorff.of_noZeroSMulDivisors [NoZeroSMulDivisors R M] (h : I ≠ ⊤) : IsHausdorff I M :=
  ⟨fun x hx ↦ (I.iInf_pow_smul_eq_bot_of_noZeroSMulDivisors h).le (by simpa [SModEq.zero] using hx)⟩

theorem IsHausdorff.of_isDomain [IsDomain R] (h : I ≠ ⊤) : IsHausdorff I R :=
  .of_noZeroSMulDivisors I R h
