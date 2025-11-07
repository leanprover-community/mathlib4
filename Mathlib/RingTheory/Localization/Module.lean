/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Anne Baanen
-/
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-!
# Modules / vector spaces over localizations / fraction fields

This file contains some results about vector spaces over the field of fractions of a ring.

## Main results

* `LinearIndependent.localization`: `b` is linear independent over a localization of `R`
  if it is linear independent over `R` itself
* `Basis.ofIsLocalizedModule` / `Basis.localizationLocalization`: promote an `R`-basis `b` of `A`
  to an `Rₛ`-basis of `Aₛ`, where `Rₛ` and `Aₛ` are localizations of `R` and `A` at `s`
  respectively
* `LinearIndependent.iff_fractionRing`: `b` is linear independent over `R` iff it is
  linear independent over `Frac(R)`
-/


open nonZeroDivisors

section Localization
variable {R : Type*} (Rₛ : Type*)

section IsLocalizedModule

open Submodule

variable [CommSemiring R] (S : Submonoid R) [CommSemiring Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
  {M Mₛ : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid Mₛ] [Module R Mₛ]
  [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f]

include S

theorem span_eq_top_of_isLocalizedModule {v : Set M} (hv : span R v = ⊤) :
    span Rₛ (f '' v) = ⊤ := top_unique fun x _ ↦ by
  obtain ⟨⟨m, s⟩, h⟩ := IsLocalizedModule.surj S f x
  rw [Submonoid.smul_def, ← algebraMap_smul Rₛ, ← Units.smul_isUnit (IsLocalization.map_units Rₛ s),
    eq_comm, ← inv_smul_eq_iff] at h
  refine h ▸ smul_mem _ _  (span_subset_span R Rₛ _ ?_)
  rw [← LinearMap.coe_restrictScalars R, ← LinearMap.map_span, hv]
  exact mem_map_of_mem mem_top

theorem LinearIndependent.of_isLocalizedModule {ι : Type*} {v : ι → M}
    (hv : LinearIndependent R v) : LinearIndependent Rₛ (f ∘ v) := by
  rw [linearIndependent_iff'ₛ] at hv ⊢
  intro t g₁ g₂ eq i hi
  choose! a fg hfg using IsLocalization.exist_integer_multiples S (t.disjSum t) (Sum.elim g₁ g₂)
  simp_rw [Sum.forall, Finset.inl_mem_disjSum, Sum.elim_inl, Finset.inr_mem_disjSum, Sum.elim_inr,
    Subtype.forall'] at hfg
  apply_fun ((a : R) • ·) at eq
  simp_rw [← t.sum_coe_sort, Finset.smul_sum, ← smul_assoc, ← hfg,
    algebraMap_smul, Function.comp_def, ← map_smul, ← map_sum,
    t.sum_coe_sort (f := fun x ↦ fg (Sum.inl x) • v x),
    t.sum_coe_sort (f := fun x ↦ fg (Sum.inr x) • v x)] at eq
  have ⟨s, eq⟩ := IsLocalizedModule.exists_of_eq (S := S) eq
  simp_rw [Finset.smul_sum, Submonoid.smul_def, smul_smul] at eq
  have := congr(algebraMap R Rₛ $(hv t _ _ eq i hi))
  simpa only [map_mul, (IsLocalization.map_units Rₛ s).mul_right_inj, hfg.1 ⟨i, hi⟩, hfg.2 ⟨i, hi⟩,
    Algebra.smul_def, (IsLocalization.map_units Rₛ a).mul_right_inj] using this

theorem LinearIndependent.of_isLocalizedModule_of_isRegular {ι : Type*} {v : ι → M}
    (hv : LinearIndependent R v) (h : ∀ s : S, IsRegular (s : R)) : LinearIndependent R (f ∘ v) :=
  hv.map_injOn _ <| by
    rw [← Finsupp.range_linearCombination]
    rintro _ ⟨_, r, rfl⟩ _ ⟨_, r', rfl⟩ eq
    congr; ext i
    have ⟨s, eq⟩ := IsLocalizedModule.exists_of_eq (S := S) eq
    simp_rw [Submonoid.smul_def, ← map_smul] at eq
    exact (h s).1 (DFunLike.congr_fun (hv eq) i)

theorem LinearIndependent.localization [Module Rₛ M] [IsScalarTower R Rₛ M]
    {ι : Type*} {b : ι → M} (hli : LinearIndependent R b) :
    LinearIndependent Rₛ b := by
  have := isLocalizedModule_id S M Rₛ
  exact hli.of_isLocalizedModule Rₛ S .id

include f in
lemma IsLocalizedModule.linearIndependent_lift {ι} {v : ι → Mₛ} (hf : LinearIndependent R v) :
    ∃ w : ι → M, LinearIndependent R w := by
  cases isEmpty_or_nonempty ι
  · exact ⟨isEmptyElim, linearIndependent_empty_type⟩
  have inj := hf.smul_left_injective (Classical.arbitrary ι)
  choose sec hsec using surj S f
  use fun i ↦ (sec (v i)).1
  rw [linearIndependent_iff'ₛ] at hf ⊢
  intro t g g' eq i hit
  refine (isRegular_of_smul_left_injective f inj (sec (v i)).2).2 <|
    hf t (fun i ↦ _ * (sec (v i)).2) (fun i ↦ _ * (sec (v i)).2) ?_ i hit
  simp_rw [mul_smul, ← Submonoid.smul_def, hsec, ← map_smul, ← map_sum, eq]

namespace Module.Basis

variable {ι : Type*} (b : Basis ι R M)

/-- If `M` has an `R`-basis, then localizing `M` at `S` has a basis over `R` localized at `S`. -/
noncomputable def ofIsLocalizedModule : Basis ι Rₛ Mₛ :=
  .mk (b.linearIndependent.of_isLocalizedModule Rₛ S f) <| by
    rw [Set.range_comp, span_eq_top_of_isLocalizedModule Rₛ S _ b.span_eq]

@[simp]
theorem ofIsLocalizedModule_apply (i : ι) : b.ofIsLocalizedModule Rₛ S f i = f (b i) := by
  rw [ofIsLocalizedModule, coe_mk, Function.comp_apply]

@[simp]
theorem ofIsLocalizedModule_repr_apply (m : M) (i : ι) :
    ((b.ofIsLocalizedModule Rₛ S f).repr (f m)) i = algebraMap R Rₛ (b.repr m i) := by
  suffices ((b.ofIsLocalizedModule Rₛ S f).repr.toLinearMap.restrictScalars R) ∘ₗ f =
      Finsupp.mapRange.linearMap (Algebra.linearMap R Rₛ) ∘ₗ b.repr.toLinearMap by
    exact DFunLike.congr_fun (LinearMap.congr_fun this m) i
  refine ext b fun i ↦ ?_
  rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, ← b.ofIsLocalizedModule_apply Rₛ S f, repr_self, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe, repr_self, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_single, Algebra.linearMap_apply, map_one]

theorem ofIsLocalizedModule_span :
    span R (Set.range (b.ofIsLocalizedModule Rₛ S f)) = LinearMap.range f := by
  calc span R (Set.range (b.ofIsLocalizedModule Rₛ S f))
    _ = span R (f '' (Set.range b)) := by congr; ext; simp
    _ = map f (span R (Set.range b)) := by rw [Submodule.map_span]
    _ = LinearMap.range f := by rw [b.span_eq, Submodule.map_top]

end Module.Basis

end IsLocalizedModule

section LocalizationLocalization

variable [CommSemiring R] (S : Submonoid R) [CommSemiring Rₛ] [Algebra R Rₛ]
variable [IsLocalization S Rₛ]
variable {A : Type*} [CommSemiring A] [Algebra R A]
variable (Aₛ : Type*) [CommSemiring Aₛ] [Algebra A Aₛ]
variable [Algebra Rₛ Aₛ] [Algebra R Aₛ] [IsScalarTower R Rₛ Aₛ] [IsScalarTower R A Aₛ]
variable [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ]

open Submodule

include S

theorem LinearIndependent.localization_localization {ι : Type*} {v : ι → A}
    (hv : LinearIndependent R v) : LinearIndependent Rₛ (algebraMap A Aₛ ∘ v) :=
  hv.of_isLocalizedModule Rₛ S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap

theorem span_eq_top_localization_localization {v : Set A} (hv : span R v = ⊤) :
    span Rₛ (algebraMap A Aₛ '' v) = ⊤ :=
  span_eq_top_of_isLocalizedModule Rₛ S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap hv

namespace Module.Basis

/-- If `A` has an `R`-basis, then localizing `A` at `S` has a basis over `R` localized at `S`.

A suitable instance for `[Algebra A Aₛ]` is `localizationAlgebra`.
-/
noncomputable def localizationLocalization {ι : Type*} (b : Basis ι R A) : Basis ι Rₛ Aₛ :=
  b.ofIsLocalizedModule Rₛ S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap

@[simp]
theorem localizationLocalization_apply {ι : Type*} (b : Basis ι R A) (i) :
    b.localizationLocalization Rₛ S Aₛ i = algebraMap A Aₛ (b i) :=
  b.ofIsLocalizedModule_apply Rₛ S _ i

@[simp]
theorem localizationLocalization_repr_algebraMap {ι : Type*} (b : Basis ι R A) (x i) :
    (b.localizationLocalization Rₛ S Aₛ).repr (algebraMap A Aₛ x) i =
      algebraMap R Rₛ (b.repr x i) := b.ofIsLocalizedModule_repr_apply Rₛ S _ _ i

theorem localizationLocalization_span {ι : Type*} (b : Basis ι R A) :
    Submodule.span R (Set.range (b.localizationLocalization Rₛ S Aₛ)) =
      LinearMap.range (IsScalarTower.toAlgHom R A Aₛ) := b.ofIsLocalizedModule_span Rₛ S _

end Module.Basis
end LocalizationLocalization


section FractionRing

variable (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

theorem LinearIndependent.iff_fractionRing {ι : Type*} {b : ι → V} :
    LinearIndependent R b ↔ LinearIndependent K b :=
  ⟨.localization K R⁰,
    .restrict_scalars <| (faithfulSMul_iff_injective_smul_one ..).mp inferInstance⟩

end FractionRing

section

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
variable {M N : Type*}
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N]

open IsLocalization

/-- An `R`-linear map between two `S⁻¹R`-modules is actually `S⁻¹R`-linear. -/
def LinearMap.extendScalarsOfIsLocalization (f : M →ₗ[R] N) : M →ₗ[A] N where
  toFun := f
  map_add' := f.map_add
  map_smul' := (IsLocalization.linearMap_compatibleSMul S A M N).map_smul _

@[simp] lemma LinearMap.restrictScalars_extendScalarsOfIsLocalization (f : M →ₗ[R] N) :
    (f.extendScalarsOfIsLocalization S A).restrictScalars R = f := rfl

@[simp] lemma LinearMap.extendScalarsOfIsLocalization_apply (f : M →ₗ[A] N) :
    f.extendScalarsOfIsLocalization S A = f := rfl

@[simp] lemma LinearMap.extendScalarsOfIsLocalization_apply' (f : M →ₗ[R] N) (x : M) :
    (f.extendScalarsOfIsLocalization S A) x = f x := rfl

/-- The `S⁻¹R`-linear maps between two `S⁻¹R`-modules are exactly the `R`-linear maps. -/
@[simps]
def LinearMap.extendScalarsOfIsLocalizationEquiv : (M →ₗ[R] N) ≃ₗ[A] (M →ₗ[A] N) where
  toFun := LinearMap.extendScalarsOfIsLocalization S A
  invFun := LinearMap.restrictScalars R
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp
  left_inv := by intro _; ext; simp
  right_inv := by intro _; ext; simp

/-- An `R`-linear isomorphism between `S⁻¹R`-modules is actually `S⁻¹R`-linear. -/
@[simps!]
def LinearEquiv.extendScalarsOfIsLocalization (f : M ≃ₗ[R] N) : M ≃ₗ[A] N :=
  .ofLinear (LinearMap.extendScalarsOfIsLocalization S A f)
    (LinearMap.extendScalarsOfIsLocalization S A f.symm)
    (by ext; simp) (by ext; simp)

/-- The `S⁻¹R`-linear isomorphisms between two `S⁻¹R`-modules are exactly the `R`-linear
isomorphisms. -/
@[simps]
def LinearEquiv.extendScalarsOfIsLocalizationEquiv : (M ≃ₗ[R] N) ≃ M ≃ₗ[A] N where
  toFun e := e.extendScalarsOfIsLocalization S A
  invFun e := e.restrictScalars R
  left_inv e := by ext; simp
  right_inv e := by ext; simp

end

end Localization

namespace IsLocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R M']
variable (f : M →ₗ[R] M') [IsLocalizedModule S f]
variable {N N'} [AddCommMonoid N] [AddCommMonoid N'] [Module R N] [Module R N']
variable (g : N →ₗ[R] N') [IsLocalizedModule S g]
variable (Rₛ) [CommSemiring Rₛ] [Algebra R Rₛ] [Module Rₛ M'] [Module Rₛ N']
variable [IsScalarTower R Rₛ M'] [IsScalarTower R Rₛ N'] [IsLocalization S Rₛ]

/-- A linear map `M →ₗ[R] N` gives a map between localized modules `Mₛ →ₗ[Rₛ] Nₛ`. -/
@[simps!]
noncomputable
def mapExtendScalars : (M →ₗ[R] N) →ₗ[R] (M' →ₗ[Rₛ] N') :=
  ((LinearMap.extendScalarsOfIsLocalizationEquiv S Rₛ).restrictScalars R).toLinearMap ∘ₗ map S f g

/-- An `R`-module isomorphism `M ≃ₗ[R] N` gives an `Rₛ`-module isomorphism `Mₛ ≃ₗ[Rₛ] Nₛ`. -/
@[simps!]
noncomputable
def mapEquiv (e : M ≃ₗ[R] N) : M' ≃ₗ[Rₛ] N' :=
  LinearEquiv.ofLinear
    (IsLocalizedModule.mapExtendScalars S f g Rₛ e)
    (IsLocalizedModule.mapExtendScalars S g f Rₛ e.symm)
    (by
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.linearMap_ext S g g
      ext; simp)
    (by
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.linearMap_ext S f f
      ext; simp)

end IsLocalizedModule

section LocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N} [AddCommMonoid N] [Module R N]

/-- A linear map `M →ₗ[R] N` gives a map between localized modules `Mₛ →ₗ[Rₛ] Nₛ`. -/
noncomputable
def LocalizedModule.map :
    (M →ₗ[R] N) →ₗ[R] (LocalizedModule S M →ₗ[Localization S] LocalizedModule S N) :=
  IsLocalizedModule.mapExtendScalars S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) (Localization S)

@[simp]
lemma LocalizedModule.map_mk (f : M →ₗ[R] N) (x y) :
    map S f (.mk x y) = LocalizedModule.mk (f x) y := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk']
  exact IsLocalizedModule.map_mk' _ _ _ _ _ _

@[simp]
lemma LocalizedModule.map_id :
    LocalizedModule.map S (.id (R := R) (M := M)) = LinearMap.id :=
  LinearMap.ext fun x ↦ LinearMap.congr_fun (IsLocalizedModule.map_id S (mkLinearMap S M)) x

lemma LocalizedModule.map_injective (l : M →ₗ[R] N) (hl : Function.Injective l) :
    Function.Injective (map S l) :=
  IsLocalizedModule.map_injective S (mkLinearMap S M) (mkLinearMap S N) l hl

lemma LocalizedModule.map_surjective (l : M →ₗ[R] N) (hl : Function.Surjective l) :
    Function.Surjective (map S l) :=
  IsLocalizedModule.map_surjective S (mkLinearMap S M) (mkLinearMap S N) l hl

lemma LocalizedModule.restrictScalars_map_eq {M' N' : Type*} [AddCommMonoid M'] [AddCommMonoid N']
    [Module R M'] [Module R N'] (g₁ : M →ₗ[R] M') (g₂ : N →ₗ[R] N')
    [IsLocalizedModule S g₁] [IsLocalizedModule S g₂]
    (l : M →ₗ[R] N) :
    (map S l).restrictScalars R = (IsLocalizedModule.iso S g₂).symm ∘ₗ
      IsLocalizedModule.map S g₁ g₂ l ∘ₗ IsLocalizedModule.iso S g₁ := by
  rw [LinearEquiv.eq_toLinearMap_symm_comp, ← LinearEquiv.comp_toLinearMap_symm_eq]
  apply IsLocalizedModule.linearMap_ext S g₁ g₂
  rw [LinearMap.comp_assoc, IsLocalizedModule.iso_symm_comp]
  ext
  simp

end LocalizedModule
