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
* `flat_iff_localization` : Let `Rₚ` a localization of `CommRing R` and `M` be a module over `R_p`.
  Then `M` is flat over `R` if and only if `M` is flat over `Rₚ`.
* `Flat_of_isLocalized_maximal` : Let `M` be a module over `CommRing R`. If the localization
  of `M` at each maximal ideal `P` is flat over `Rₚ`, then `M` is flat over `R`.
* `Flat_of_isLocalized_span` : Let `M` be a module over `CommRing R` and `S` be a set that
  spans `R`. If the localization of `M` at each `s : S` is flat over `Localization.Away s`,
  then `M` is flat over `R`.
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

include p in
theorem flat_iff_localization : Module.Flat S M ↔ Module.Flat R M := by
  letI := isLocalizedModule_id p M S
  letI := IsLocalization.flat S p
  exact ⟨fun h ↦ Module.Flat.trans R S M,
    fun h ↦ Module.Flat.of_isLocalizedModule S p LinearMap.id⟩

variable (S : Submonoid R) (N P Q : Type*) [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
  [Module R N] [Module R P] [Module R Q]

variable {M N P Q} in
lemma IsLocalizedModule.linearMap_ext (f : M →ₗ[R] N) [IsLocalizedModule S f]
    (f' : P →ₗ[R] Q) [IsLocalizedModule S f'] ⦃g g' : N →ₗ[R] Q⦄
    (h : g ∘ₗ f = g' ∘ₗ f) : g = g' := ext fun x ↦ by
  have ⟨⟨m, s⟩, (eq : s.1 • x = f m)⟩ := surj S f x
  apply ((Module.End_isUnit_iff _).mp (map_units f' s)).1
  simpa only [Module.algebraMap_end_apply, ← g.map_smul, ← g'.map_smul, eq] using congr($h m)

private lemma aux (I : Ideal R) (s : Submonoid R) :
    have hM := isBaseChange s (Localization s) (mkLinearMap s M)
    have hIM := isBaseChange s (Localization s) (mkLinearMap s (I ⊗[R] M))
    let e := (hIM.equiv.restrictScalars R).symm ≪≫ₗ
      leftComm _ _ _ _ ≪≫ₗ (hM.equiv.restrictScalars R).lTensor I
    LocalizedModule.map s (TensorProduct.lift <| lsmul R M ∘ₗ I.subtype) =
      TensorProduct.lift (lsmul R (LocalizedModule s M) ∘ₗ I.subtype) ∘ₗ e.toLinearMap := by
  refine linearMap_ext s (mkLinearMap s _) (mkLinearMap s _) ?_
  ext m i
  show LocalizedModule.map s _ _ = _
  rw [mkLinearMap_apply]
  simpa [-mkLinearMap_apply, IsBaseChange.equiv_symm_apply, IsBaseChange.equiv_tmul] using
    (mkLinearMap_apply _ _ _).symm.trans (map_smul (mkLinearMap s M) _ _)

variable (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]

theorem Flat_of_localized_maximal
    (h : ∀ (J : Ideal R) [J.IsMaximal], Module.Flat R (LocalizedModule J.primeCompl M)) :
    Module.Flat R M :=
  (Module.flat_iff _ _).mpr fun I fg ↦ injective_of_localized_maximal _ fun J hJ ↦ by
    rw [← LinearMap.coe_restrictScalars R, aux]
    simpa using (Module.flat_iff _ _).mp (h J) fg

include f in
theorem Flat_of_isLocalized_maixmal (H : ∀ (P : Ideal R) [P.IsMaximal], Module.Flat R (Mₚ P)) :
    Module.Flat R M := Flat_of_localized_maximal M
  fun P _ ↦ Module.Flat.of_linearEquiv R (Mₚ P) (LocalizedModule _ M) (f := H P) (iso _ (f P))

variable (s : Set R) (spn : Ideal.span (s : Set R) = ⊤)
   (Mₛ : ∀ _ : s, Type*)
  [∀ r : s, AddCommGroup (Mₛ r)]
  [∀ r : s, Module R (Mₛ r)]
  (g : ∀ r : s, M →ₗ[R] Mₛ r)
  [∀ r : s, IsLocalizedModule (.powers r.1) (g r)]
include spn

theorem Flat_of_localized_span
    (h : ∀ r : s, Module.Flat R (LocalizedModule (Submonoid.powers r.1) M)) :
    Module.Flat R M :=
  (Module.flat_iff _ _).mpr fun I fg ↦ injective_of_localized_span s spn _ fun r ↦ by
    rw [← LinearMap.coe_restrictScalars R, aux]
    simpa using (Module.flat_iff _ _).mp (h r) fg

include g in
theorem Flat_of_isLocalized_span (H : ∀ r : s, Module.Flat R (Mₛ r)) :
    Module.Flat R M := Flat_of_localized_span M s spn
  fun r ↦ Module.Flat.of_linearEquiv R (Mₛ r) (LocalizedModule _ M) (f := H r) (iso _ (g r))
