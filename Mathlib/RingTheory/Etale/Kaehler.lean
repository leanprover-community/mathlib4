/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Smooth.Kaehler

/-!
# The differential module and etale algebras

## Main results
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`:
The canonical isomorphism `T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]` for `T` a formally etale `S`-algebra.
-/

universe u

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

open TensorProduct

/--
The canonical isomorphism `T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]` for `T` a formally etale `S`-algebra.
Also see `S ⊗[R] Ω[A⁄R] ≃ₗ[S] Ω[S ⊗[R] A⁄S]` at `KaehlerDifferential.tensorKaehlerEquiv`.
-/
@[simps! apply] noncomputable
def KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale [Algebra.FormallyEtale S T] :
    T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R] := by
  refine LinearEquiv.ofBijective (mapBaseChange R S T)
    ⟨?_, fun x ↦ (KaehlerDifferential.exact_mapBaseChange_map R S T x).mp (Subsingleton.elim _ _)⟩
  rw [injective_iff_map_eq_zero]
  intros x hx
  obtain ⟨x, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx
  rw [Subsingleton.elim x 0, map_zero]

lemma KaehlerDifferential.isBaseChange_of_formallyEtale [Algebra.FormallyEtale S T] :
    IsBaseChange T (map R R S T) := by
  show Function.Bijective _
  convert (tensorKaehlerEquivOfFormallyEtale R S T).bijective using 1
  show _ = ((tensorKaehlerEquivOfFormallyEtale
    R S T).toLinearMap.restrictScalars S : T ⊗[S] Ω[S⁄R] → _)
  congr!
  ext
  simp

instance KaehlerDifferential.isLocalizedModule_map (M : Submonoid S) [IsLocalization M T] :
    IsLocalizedModule M (map R R S T) :=
  have := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  (isLocalizedModule_iff_isBaseChange M T _).mpr (isBaseChange_of_formallyEtale R S T)
