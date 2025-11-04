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

variable {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
variable (p : Submonoid R) [IsLocalization p S]
variable (M : Type*) [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]

include p in
theorem IsLocalization.flat : Module.Flat R S := by
  refine Module.Flat.iff_lTensor_injectiveₛ.mpr fun P _ _ N ↦ ?_
  have h := ((range N.subtype).isLocalizedModule S p (TensorProduct.mk R S P 1)).isBaseChange _ S
  let e := (LinearEquiv.ofInjective _ Subtype.val_injective).lTensor S ≪≫ₗ h.equiv.restrictScalars R
  have : N.subtype.lTensor S = Submodule.subtype _ ∘ₗ e.toLinearMap := by
    ext; change _ = (h.equiv _).1; simp [h.equiv_tmul, TensorProduct.smul_tmul']
  simpa [this] using e.injective

instance Localization.flat : Module.Flat R (Localization p) := IsLocalization.flat _ p

namespace Module

include p in
theorem flat_iff_of_isLocalization : Flat S M ↔ Flat R M :=
  have := isLocalizedModule_id p M S
  have := IsLocalization.flat S p
  ⟨fun _ ↦ .trans R S M, fun _ ↦ .of_isLocalizedModule S p .id⟩

variable (Mₚ : ∀ (P : Ideal S) [P.IsMaximal], Type*)
  [∀ (P : Ideal S) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [∀ (P : Ideal S) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal S) [P.IsMaximal], Module S (Mₚ P)]
  [∀ (P : Ideal S) [P.IsMaximal], IsScalarTower R S (Mₚ P)]
  (f : ∀ (P : Ideal S) [P.IsMaximal], M →ₗ[S] Mₚ P)
  [∀ (P : Ideal S) [P.IsMaximal], IsLocalizedModule.AtPrime P (f P)]

include f in
theorem flat_of_isLocalized_maximal (H : ∀ (P : Ideal S) [P.IsMaximal], Flat R (Mₚ P)) :
    Module.Flat R M := by
  simp_rw [Flat.iff_lTensor_injectiveₛ] at H ⊢
  simp_rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  refine fun _ _ _ N ↦ injective_of_isLocalized_maximal _
    (fun P ↦ AlgebraTensorModule.rTensor R _ (f P)) _
    (fun P ↦ AlgebraTensorModule.rTensor R _ (f P)) _ fun P hP ↦ ?_
  simpa [IsLocalizedModule.map_lTensor] using H P N

theorem flat_of_localized_maximal
    (h : ∀ (P : Ideal R) [P.IsMaximal], Flat R (LocalizedModule P.primeCompl M)) :
    Flat R M :=
  flat_of_isLocalized_maximal _ _ _ (fun _ _ ↦ mkLinearMap _ _) h

variable (s : Set S) (spn : Ideal.span s = ⊤)
  (Mₛ : ∀ _ : s, Type*)
  [∀ r : s, AddCommMonoid (Mₛ r)]
  [∀ r : s, Module R (Mₛ r)]
  [∀ r : s, Module S (Mₛ r)]
  [∀ r : s, IsScalarTower R S (Mₛ r)]
  (g : ∀ r : s, M →ₗ[S] Mₛ r)
  [∀ r : s, IsLocalizedModule.Away r.1 (g r)]
include spn

include g in
theorem flat_of_isLocalized_span (H : ∀ r : s, Module.Flat R (Mₛ r)) :
    Module.Flat R M := by
  simp_rw [Flat.iff_lTensor_injectiveₛ] at H ⊢
  simp_rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  refine fun _ _ _ N ↦ injective_of_isLocalized_span s spn _
    (fun r ↦ AlgebraTensorModule.rTensor R _ (g r)) _
    (fun r ↦ AlgebraTensorModule.rTensor R _ (g r)) _ fun r ↦ ?_
  simpa [IsLocalizedModule.map_lTensor] using H r N

theorem flat_of_localized_span
    (h : ∀ r : s, Flat S (LocalizedModule.Away r.1 M)) :
    Flat S M :=
  flat_of_isLocalized_span _ _ _ spn _ (fun _ ↦ mkLinearMap _ _) h

end Module

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

instance [Module.Flat A B] (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    Module.Flat (Localization.AtPrime p) (Localization.AtPrime P) := by
  rw [Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl]
  exact Module.Flat.trans A B (Localization.AtPrime P)

section IsSMulRegular

variable {M} in
theorem IsSMulRegular.of_isLocalizedModule {K : Type*} [AddCommMonoid K] [Module R K]
    (f : K →ₗ[R] M) [IsLocalizedModule p f] {x : R} (reg : IsSMulRegular K x) :
    IsSMulRegular M (algebraMap R S x) :=
  have : Module.Flat R S := IsLocalization.flat S p
  reg.of_flat_of_isBaseChange (IsLocalizedModule.isBaseChange p S f)

include p in
theorem IsSMulRegular.of_isLocalization {x : R} (reg : IsSMulRegular R x) :
    IsSMulRegular S (algebraMap R S x) :=
  reg.of_isLocalizedModule S p (Algebra.linearMap R S)

end IsSMulRegular
