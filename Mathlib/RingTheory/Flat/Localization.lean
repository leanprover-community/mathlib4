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

section

variable {R M₁ M₂ M : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M]
    [Module R M₁] [Module R M₂] [Module R M]

lemma IsTensorProduct.of_equiv {f : M₁ →ₗ[R] M₂ →ₗ[R] M} (e : M₁ ⊗[R] M₂ ≃ₗ[R] M)
    (he : ∀ x y, e (x ⊗ₜ y) = f x y) :
    IsTensorProduct f := by
  have : TensorProduct.lift f = e := by
    ext x y
    simp [he]
  simpa [IsTensorProduct, this] using e.bijective

end

section

variable {R M N : Type*} {S : Type*}
variable [AddCommMonoid M] [AddCommMonoid N]
variable [CommSemiring R] [CommSemiring S] [Algebra R S] [Module R M] [Module R N] [Module S N]
variable [IsScalarTower R S N]

lemma IsBaseChange.of_equiv {f : M →ₗ[R] N} (e : S ⊗[R] M ≃ₗ[S] N)
    (he : ∀ x, e (1 ⊗ₜ x) = f x) :
    IsBaseChange S f := by
  apply IsTensorProduct.of_equiv (e.restrictScalars R)
  intro x y
  simp [show x ⊗ₜ[R] y = x • (1 ⊗ₜ[R] y) by simp [smul_tmul'], he]

end

section

variable {R S M N P : Type*} (A : Type*)
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [CommSemiring R] [CommSemiring A] [CommSemiring S]
variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Module R M] [Module S M] [IsScalarTower R S M]
variable [Module R N] [Module S N] [IsScalarTower R S N]
variable [Module R P]
variable [Module A N] [IsScalarTower S A N] [IsScalarTower R A N]
  (f : M →ₗ[S] N)

lemma isBaseChange_tensorProduct_map (hf : IsBaseChange A f) :
    IsBaseChange A (AlgebraTensorModule.map f (LinearMap.id (R := R) (M := P))) := by
  let e : A ⊗[S] M ⊗[R] P ≃ₗ[A] N ⊗[R] P := (AlgebraTensorModule.assoc R S A A M P).symm.trans
    (AlgebraTensorModule.congr hf.equiv (LinearEquiv.refl R P))
  refine IsBaseChange.of_equiv e (fun x ↦ ?_)
  induction' x with m p _ _ h1 h2
  · simp
  · simp [e, IsBaseChange.equiv_tmul]
  · simp [tmul_add, h1, h2]

end

section

variable {R : Type*} [CommSemiring R]
variable (A : Type*) {M N : Type*} [Semiring A] [Algebra R A]
  [AddCommMonoid M] [AddCommMonoid N] [Module A M]

def _root_.AddEquiv.smul (e : M ≃+ N) : SMul A N where
  smul r n := e (r • e.symm n)

lemma _root_.AddEquiv.smul_def (e : M ≃+ N) (r : A) (n : N) :
    letI := e.smul A
    r • n = e (r • e.symm n) :=
  rfl

def _root_.AddEquiv.module (e : M ≃+ N) : Module A N where
  __ := e.smul A
  one_smul := by simp [AddEquiv.smul_def]
  mul_smul := by simp [AddEquiv.smul_def, mul_smul]
  smul_zero := by simp [AddEquiv.smul_def]
  smul_add := by simp [AddEquiv.smul_def]
  add_smul := by simp [AddEquiv.smul_def, add_smul]
  zero_smul := by simp [AddEquiv.smul_def]

variable [Module R M] [Module R N] [IsScalarTower R A M]

lemma _root_.LinearEquiv.isScalarTower (e : M ≃ₗ[R] N) :
    letI := e.toAddEquiv.module A
    IsScalarTower R A N := by
  letI := e.toAddEquiv.module A
  constructor
  intro x y z
  simp only [LinearEquiv.coe_toAddEquiv, AddEquiv.smul_def, smul_assoc]
  apply e.map_smul

end

section

variable {R A M Mₚ N : Type*} [CommSemiring R] [CommSemiring A] (S : Submonoid A)
variable [Algebra R A] [AddCommMonoid M] [AddCommMonoid Mₚ] [AddCommMonoid N]
variable [Module R M] [Module A M] [IsScalarTower R A M]
variable [Module A Mₚ] [Module R Mₚ] [IsScalarTower R A Mₚ]
variable [Module R N]

lemma isLocalizedModule_tensorProduct_map (g : M →ₗ[A] Mₚ) [h : IsLocalizedModule S g] :
    IsLocalizedModule S (AlgebraTensorModule.map g (LinearMap.id (R := R) (M := N))) := by
  let Aₚ := Localization S
  letI : Module Aₚ Mₚ := (IsLocalizedModule.iso S g).toAddEquiv.module Aₚ
  haveI : IsScalarTower A Aₚ Mₚ := (IsLocalizedModule.iso S g).isScalarTower Aₚ
  haveI : IsScalarTower R Aₚ Mₚ :=
    IsScalarTower.of_algebraMap_smul <| fun r x ↦ by simp [IsScalarTower.algebraMap_apply R A Aₚ]
  rw [isLocalizedModule_iff_isBaseChange (R := A) (S := S) (A := Aₚ)] at h
  rw [isLocalizedModule_iff_isBaseChange (R := A) (S := S) (A := Aₚ)]
  apply isBaseChange_tensorProduct_map
  exact h

end

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
theorem flat_of_isLocalized_maximal (H : ∀ (P : Ideal R) [P.IsMaximal], Flat R (Mₚ P)) :
    Module.Flat R M :=
  flat_of_localized_maximal M fun P _ ↦ .of_linearEquiv _ _ _ (iso _ (f P))

variable (s : Set S) (spn : Ideal.span s = ⊤)
  (Mₛ : ∀ _ : s, Type*)
  [∀ r : s, AddCommGroup (Mₛ r)]
  [∀ r : s, Module R (Mₛ r)]
  [∀ r : s, Module S (Mₛ r)]
  [∀ r : s, IsScalarTower R S (Mₛ r)]
  (g : ∀ r : s, M →ₗ[S] Mₛ r)
  [∀ r : s, IsLocalizedModule (.powers r.1) (g r)]
include spn

theorem flat_of_localized_span
    (h : ∀ r : s, Flat S (LocalizedModule (.powers r.1) M)) :
    Flat S M :=
  (Module.flat_iff _ _).mpr fun I fg ↦ injective_of_localized_span s spn _ fun r ↦ by
    rw [← LinearMap.coe_restrictScalars S, aux]
    simpa using (Module.flat_iff _ _).mp (h r) fg

include g in
theorem flat_of_isLocalized_span (h : ∀ r : s, Module.Flat R (Mₛ r)) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_injective]
  intro I fg
  let F : M ⊗[R] I →ₗ[S] M ⊗[R] R := AlgebraTensorModule.lTensor S M (Submodule.subtype I)
  let g' (r : s) : M ⊗[R] I →ₗ[S] Mₛ r ⊗[R] I := AlgebraTensorModule.map (g r) LinearMap.id
  haveI (r : s) : IsLocalizedModule (Submonoid.powers r.val) (g' r) :=
    isLocalizedModule_tensorProduct_map _ _
  let g'' (r : s) : M ⊗[R] R →ₗ[S] Mₛ r ⊗[R] R := AlgebraTensorModule.map (g r) LinearMap.id
  haveI (r : s) : IsLocalizedModule (Submonoid.powers r.val) (g'' r) :=
    isLocalizedModule_tensorProduct_map _ _
  apply injective_of_isLocalized_span s spn _ g' _ g'' F
  have (r : s) : (IsLocalizedModule.map (Submonoid.powers r.val) (g' r) (g'' r)) F =
      AlgebraTensorModule.lTensor S (Mₛ r) (Submodule.subtype I) := by
    apply IsLocalizedModule.ringHom_ext (Submonoid.powers r.val) (g' r) (map_units (g'' r))
    ext x y
    simp only [AlgebraTensorModule.curry_apply, curry_apply, coe_comp,
      coe_restrictScalars, Function.comp_apply, map_apply]
    simp [g', g'', F]
  intro r
  rw [this]
  apply Module.Flat.lTensor_preserves_injective_linearMap
  exact Submodule.injective_subtype I

end Module
