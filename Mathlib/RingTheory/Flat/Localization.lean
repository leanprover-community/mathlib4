/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.LocalProperties.Exactness

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

public section

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
  simpa [this] using! e.injective

instance Localization.flat [Module.Flat R S] (p : Submonoid S) : Module.Flat R (Localization p) :=
  have : Module.Flat S (Localization p) := IsLocalization.flat _ p
  .trans R S _

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

/-- A module `N` over a commutative ring `R` is flat if and only if its localization at every
prime ideal is flat over `R`. -/
theorem Module.flat_iff_forall_localizedModule_prime (R : Type*) [CommRing R] (N : Type*)
    [AddCommGroup N] [Module R N] :
    Module.Flat R N ↔
      ∀ (p : Ideal R) [p.IsPrime], Module.Flat R (LocalizedModule p.primeCompl N) := by
  refine ⟨fun _ p _ ↦ ?_, fun h ↦ Module.flat_of_localized_maximal _ fun P hP ↦ ?_⟩
  · have : Module.Flat (Localization p.primeCompl) (LocalizedModule p.primeCompl N) :=
      Module.Flat.localizedModule _
    have : Module.Flat R (Localization p.primeCompl) := IsLocalization.flat _ p.primeCompl
    exact Module.Flat.trans R (Localization p.primeCompl) _
  · haveI := hP.isPrime
    exact h P

/-- Localising an `R`-flat module (which is also a module over an `R`-algebra `S`) at a submonoid
of `S` yields again an `R`-flat module. -/
theorem Module.Flat.localizedModule_base {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (q : Submonoid S) [Module.Flat R M] :
    Module.Flat R (LocalizedModule q M) := by
  have e : LocalizedModule q M ≃ₗ[R] (Localization q ⊗[S] M) :=
    (LocalizedModule.equivTensorProduct q M).restrictScalars R
  haveI : Module.Flat S (Localization q) := IsLocalization.flat (Localization q) q
  haveI : Module.Flat R (Localization q ⊗[S] M) := Module.Flat.tensor_tower (Localization q) M
  exact Module.Flat.of_linearEquiv e

/-- **Local–global flatness over a base, indexed by primes of `S`.** For an `R`-algebra `S` and an
`S`-module `M`, `M` is flat over `R` iff its localization at every prime of `S` is flat over `R`. -/
theorem Module.flat_iff_forall_localizedModule_prime_of_algebra {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (M : Type*) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] :
    Module.Flat R M ↔
      ∀ (q : Ideal S) [q.IsPrime], Module.Flat R (LocalizedModule q.primeCompl M) := by
  refine ⟨fun _ q _ ↦ Module.Flat.localizedModule_base M q.primeCompl, fun h ↦ ?_⟩
  refine Module.flat_of_isLocalized_maximal S M (fun P _ ↦ LocalizedModule P.primeCompl M)
    (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M) fun P hP ↦ ?_
  haveI := hP.isPrime
  exact h P

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

instance [Module.Flat A B] (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
    [Localization.AtPrime.IsLiesOverAlgebra p P] :
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
