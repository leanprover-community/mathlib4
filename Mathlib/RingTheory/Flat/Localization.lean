/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Flatness and localization

In this file we show that localizations are flat, and flatness is a local property.

## Main result
* `IsLocalization.flat`: a localization of a commutative ring is flat over it.
* `Module.flat_iff_of_isLocalization` : Let `Rₚ` a localization of a commutative ring `R`
  and `M` be a module over `Rₚ`. Then `M` is flat over `R` if and only if `M` is flat over `Rₚ`.
* `Module.flat_of_isLocalized_maximal` : Let `M` be a module over a commutative ring `R`.
  If the localization of `M` at each maximal ideal `P` is flat over `Rₚ`, then `M` is flat over `R`.
* `Module.flat_of_isLocalized_span` : Let `M` be a module over a commutative ring `R`
  and `S` be a set that spans `R`. If the localization of `M` at each `s : S` is flat
  over `Localization.Away s`, then `M` is flat over `R`.
-/

open IsLocalizedModule LocalizedModule LinearMap TensorProduct

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable (p : Submonoid R) [IsLocalization p S]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

include p in
theorem IsLocalization.flat : Module.Flat R S :=
  (Module.Flat.iff_lTensor_injective' _ _).mpr fun I ↦ by
    have h := (I.isLocalizedModule S p (Algebra.linearMap R S)).isBaseChange _ S _
    have : I.subtype.lTensor S = (TensorProduct.rid R S).symm.comp
        ((Submodule.subtype _ ∘ₗ h.equiv.toLinearMap).restrictScalars R) := by
      rw [LinearEquiv.eq_toLinearMap_symm_comp]; ext
      simp [h.equiv_tmul, Algebra.smul_def, mul_comm, Algebra.ofId_apply]
    simpa [this, - Subtype.val_injective] using Subtype.val_injective

instance Localization.flat : Module.Flat R (Localization p) := IsLocalization.flat _ p

namespace Module

include p in
theorem flat_iff_of_isLocalization : Flat S M ↔ Flat R M :=
  have := isLocalizedModule_id p M S
  have := IsLocalization.flat S p
  ⟨fun _ ↦ .trans R S M, fun _ ↦ .of_isLocalizedModule S p .id⟩

private lemma aux (I : Ideal R) (s : Submonoid R) :
    have hM := isBaseChange s (Localization s) (mkLinearMap s M)
    have hIM := isBaseChange s (Localization s) (mkLinearMap s (I ⊗[R] M))
    let e := (hIM.equiv.restrictScalars R).symm ≪≫ₗ
      leftComm _ _ _ _ ≪≫ₗ (hM.equiv.restrictScalars R).lTensor I
    LocalizedModule.map s (TensorProduct.lift <| lsmul R M ∘ₗ I.subtype) =
      TensorProduct.lift (lsmul R (LocalizedModule s M) ∘ₗ I.subtype) ∘ₗ e.toLinearMap := by
  refine linearMap_ext s (mkLinearMap s _) (mkLinearMap s _) ?_
  ext m i
  rw [AlgebraTensorModule.curry_apply, curry_apply, restrictScalars_apply, LinearMap.comp_apply,
    restrictScalars_apply, mkLinearMap_apply, AlgebraTensorModule.curry_apply, curry_apply,
    restrictScalars_apply]
  simpa [-mkLinearMap_apply, IsBaseChange.equiv_symm_apply, IsBaseChange.equiv_tmul] using
    (mkLinearMap_apply _ _ _).symm.trans (map_smul (mkLinearMap s M) _ _)

variable (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]

theorem flat_of_localized_maximal
    (h : ∀ (J : Ideal R) [J.IsMaximal], Flat R (LocalizedModule J.primeCompl M)) :
    Flat R M :=
  (flat_iff _ _).mpr fun I fg ↦ injective_of_localized_maximal _ fun J hJ ↦ by
    rw [← LinearMap.coe_restrictScalars R, aux]
    simpa using (flat_iff _ _).mp (h J) fg

include f in
theorem flat_of_isLocalized_maixmal (H : ∀ (P : Ideal R) [P.IsMaximal], Flat R (Mₚ P)) :
    Module.Flat R M :=
  flat_of_localized_maximal M fun P _ ↦ .of_linearEquiv _ _ _ (iso _ (f P))

variable (s : Set R) (spn : Ideal.span s = ⊤)
  (Mₛ : ∀ _ : s, Type*)
  [∀ r : s, AddCommGroup (Mₛ r)]
  [∀ r : s, Module R (Mₛ r)]
  (g : ∀ r : s, M →ₗ[R] Mₛ r)
  [∀ r : s, IsLocalizedModule (.powers r.1) (g r)]
include spn

theorem flat_of_localized_span
    (h : ∀ r : s, Flat R (LocalizedModule (.powers r.1) M)) :
    Flat R M :=
  (Module.flat_iff _ _).mpr fun I fg ↦ injective_of_localized_span s spn _ fun r ↦ by
    rw [← LinearMap.coe_restrictScalars R, aux]
    simpa using (Module.flat_iff _ _).mp (h r) fg

include g in
theorem flat_of_isLocalized_span (H : ∀ r : s, Module.Flat R (Mₛ r)) :
    Module.Flat R M :=
  flat_of_localized_span M s spn fun r ↦ .of_linearEquiv _ _ _ (iso _ (g r))

end Module
