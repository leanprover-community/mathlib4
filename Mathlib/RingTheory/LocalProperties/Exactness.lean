/-
Copyright (c) 2024 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sihan Su, Yongle Hu, Yi Song
-/
import Mathlib.Algebra.Exact
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Away

/-!
# Local properties about linear maps

In this file, we show that
injectivity, surjectivity, bijectivity and exactness of linear maps are local properties.
More precisely, we show that these can be checked at maximal ideals and on standard covers.
-/

open Submodule LocalizedModule Ideal LinearMap

section isLocalized_maximal

open IsLocalizedModule

variable {R M N L : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid L] [Module R L]

variable
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule.AtPrime P (f P)]
  (Nₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Nₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Nₚ P)]
  (g : ∀ (P : Ideal R) [P.IsMaximal], N →ₗ[R] Nₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule.AtPrime P (g P)]
  (Lₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Lₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Lₚ P)]
  (h : ∀ (P : Ideal R) [P.IsMaximal], L →ₗ[R] Lₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule.AtPrime P (h P)]
  (F : M →ₗ[R] N) (G : N →ₗ[R] L)

theorem injective_of_isLocalized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal], Function.Injective (map P.primeCompl (f P) (g P) F)) :
    Function.Injective F :=
  fun x y eq ↦ Module.eq_of_localization_maximal _ f _ _ fun P _ ↦ H P <| by simp [eq]

theorem surjective_of_isLocalized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal], Function.Surjective (map P.primeCompl (f P) (g P) F)) :
    Function.Surjective F :=
  range_eq_top.mp <| eq_top_of_localization₀_maximal Nₚ g _ <|
    fun P _ ↦ (range_localizedMap_eq_localized₀_range _ (f P) (g P) F).symm.trans <|
    range_eq_top.mpr <| H P

theorem bijective_of_isLocalized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal], Function.Bijective (map P.primeCompl (f P) (g P) F)) :
    Function.Bijective F :=
  ⟨injective_of_isLocalized_maximal Mₚ f Nₚ g F fun J _ ↦ (H J).1,
  surjective_of_isLocalized_maximal Mₚ f Nₚ g F fun J _ ↦ (H J).2⟩

theorem exact_of_isLocalized_maximal (H : ∀ (J : Ideal R) [J.IsMaximal],
    Function.Exact (map J.primeCompl (f J) (g J) F) (map J.primeCompl (g J) (h J) G)) :
    Function.Exact F G := by
  simp only [LinearMap.exact_iff] at H ⊢
  apply eq_of_localization₀_maximal Nₚ g
  intro J hJ
  rw [← LinearMap.range_localizedMap_eq_localized₀_range _ (f J) (g J) F,
    ← LinearMap.ker_localizedMap_eq_localized₀_ker J.primeCompl (g J) (h J) G]
  have := SetLike.ext_iff.mp <| H J
  ext x
  simp only [mem_range, mem_ker] at this ⊢
  exact this x

end isLocalized_maximal

section localized_maximal

variable {R M N L : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid L] [Module R L] (f : M →ₗ[R] N) (g : N →ₗ[R] L)

theorem injective_of_localized_maximal
    (h : ∀ (J : Ideal R) [J.IsMaximal], Function.Injective (map J.primeCompl f)) :
    Function.Injective f :=
  injective_of_isLocalized_maximal _ (fun _ _ ↦ mkLinearMap _ _) _ (fun _ _ ↦ mkLinearMap _ _) f h

theorem surjective_of_localized_maximal
    (h : ∀ (J : Ideal R) [J.IsMaximal], Function.Surjective (map J.primeCompl f)) :
    Function.Surjective f :=
  surjective_of_isLocalized_maximal _ (fun _ _ ↦ mkLinearMap _ _) _ (fun _ _ ↦ mkLinearMap _ _) f h

theorem bijective_of_localized_maximal
    (h : ∀ (J : Ideal R) [J.IsMaximal], Function.Bijective (map J.primeCompl f)) :
    Function.Bijective f :=
  ⟨injective_of_localized_maximal _ fun J _ ↦ (h J).1,
  surjective_of_localized_maximal _ fun J _ ↦ (h J).2⟩

theorem exact_of_localized_maximal
    (h : ∀ (J : Ideal R) [J.IsMaximal], Function.Exact (map J.primeCompl f) (map J.primeCompl g)) :
    Function.Exact f g :=
  exact_of_isLocalized_maximal _ (fun _ _ ↦ mkLinearMap _ _) _ (fun _ _ ↦ mkLinearMap _ _)
    _ (fun _ _ ↦ mkLinearMap _ _) f g h

end localized_maximal

section isLocalized_span

open IsLocalizedModule

variable {R M N L : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid L] [Module R L] (s : Set R) (spn : Ideal.span s = ⊤)
include spn

variable
  (Mₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommMonoid (Mₚ r)]
  [∀ r : s, Module R (Mₚ r)]
  (f : ∀ r : s, M →ₗ[R] Mₚ r)
  [∀ r : s, IsLocalizedModule.Away r.1 (f r)]
  (Nₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommMonoid (Nₚ r)]
  [∀ r : s, Module R (Nₚ r)]
  (g : ∀ r : s, N →ₗ[R] Nₚ r)
  [∀ r : s, IsLocalizedModule.Away r.1 (g r)]
  (Lₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommMonoid (Lₚ r)]
  [∀ r : s, Module R (Lₚ r)]
  (h : ∀ r : s, L →ₗ[R] Lₚ r)
  [∀ r : s, IsLocalizedModule.Away r.1 (h r)]
  (F : M →ₗ[R] N) (G : N →ₗ[R] L)

theorem injective_of_isLocalized_span
    (H : ∀ r : s, Function.Injective (map (.powers r.1) (f r) (g r) F)) :
    Function.Injective F :=
  fun x y eq ↦ Module.eq_of_isLocalized_span _ spn _ f _ _ fun P ↦ H P <| by simp [eq]

theorem surjective_of_isLocalized_span
    (H : ∀ r : s, Function.Surjective (map (.powers r.1) (f r) (g r) F)) :
    Function.Surjective F :=
  range_eq_top.mp <| eq_top_of_isLocalized₀_span s spn Nₚ g fun r ↦
    (range_localizedMap_eq_localized₀_range _ (f r) (g r) F).symm.trans <| range_eq_top.mpr <| H r

theorem bijective_of_isLocalized_span
    (H : ∀ r : s, Function.Bijective (map (.powers r.1) (f r) (g r) F)) :
    Function.Bijective F :=
  ⟨injective_of_isLocalized_span _ spn Mₚ f Nₚ g F fun r ↦ (H r).1,
  surjective_of_isLocalized_span _ spn Mₚ f Nₚ g F fun r ↦ (H r).2⟩

lemma exact_of_isLocalized_span (H : ∀ r : s, Function.Exact
    (map (.powers r.1) (f r) (g r) F) (map (.powers r.1) (g r) (h r) G)) :
    Function.Exact F G := by
  simp only [LinearMap.exact_iff] at H ⊢
  apply Submodule.eq_of_isLocalized₀_span s spn Nₚ g
  intro r
  rw [← LinearMap.range_localizedMap_eq_localized₀_range _ (f r) (g r) F]
  rw [← LinearMap.ker_localizedMap_eq_localized₀_ker (.powers r.1) (g r) (h r) G]
  have := SetLike.ext_iff.mp <| H r
  ext x
  simp only [mem_range, mem_ker] at this ⊢
  exact this x

end isLocalized_span

section localized_span

variable {R M N L : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid L] [Module R L]
  (s : Set R) (spn : span s = ⊤) (f : M →ₗ[R] N) (g : N →ₗ[R] L)
include spn

theorem injective_of_localized_span
    (h : ∀ r : s, Function.Injective (map (.powers r.1) f)) :
    Function.Injective f :=
  injective_of_isLocalized_span s spn _ (fun _ ↦ mkLinearMap _ _) _ (fun _ ↦ mkLinearMap _ _) f h

theorem surjective_of_localized_span
    (h : ∀ r : s, Function.Surjective (map (.powers r.1) f)) :
    Function.Surjective f :=
  surjective_of_isLocalized_span s spn _ (fun _ ↦ mkLinearMap _ _) _ (fun _ ↦ mkLinearMap _ _) f h

theorem bijective_of_localized_span
    (h : ∀ r : s, Function.Bijective (map (.powers r.1) f)) :
    Function.Bijective f :=
  ⟨injective_of_localized_span _ spn _ fun r ↦ (h r).1,
  surjective_of_localized_span _ spn _ fun r ↦ (h r).2⟩

lemma exact_of_localized_span
    (h : ∀ r : s, Function.Exact (map (.powers r.1) f) (map (.powers r.1) g)) :
    Function.Exact f g :=
  exact_of_isLocalized_span s spn _ (fun _ ↦ mkLinearMap _ _) _ (fun _ ↦ mkLinearMap _ _)
    _ (fun _ ↦ mkLinearMap _ _) f g h

end localized_span

section Algebra

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

variable
  (Rₚ : ∀ (p : Ideal R) [p.IsMaximal], Type*)
  [∀ (p : Ideal R) [p.IsMaximal], CommSemiring (Rₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], Algebra R (Rₚ p)]
  (Sₚ : ∀ (p : Ideal R) [p.IsMaximal], Type*)
  [∀ (p : Ideal R) [p.IsMaximal], CommSemiring (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], Algebra S (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], Algebra (Rₚ p) (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], Algebra R (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], IsScalarTower R (Rₚ p) (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], IsScalarTower R S (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], IsLocalization.AtPrime (Rₚ p) p]
  [∀ (p : Ideal R) [p.IsMaximal],
    IsLocalizedModule.AtPrime p (IsScalarTower.toAlgHom R S (Sₚ p) : S →ₗ[R] (Sₚ p))]

open TensorProduct

lemma IsLocalizedModule.map_linearMap_of_isLocalization (Rₚ Sₚ : Type*) [CommSemiring Rₚ]
    [Algebra R Rₚ] [CommSemiring Sₚ] [Algebra S Sₚ] [Algebra R Sₚ] [IsScalarTower R S Sₚ]
    [Algebra Rₚ Sₚ] [IsScalarTower R Rₚ Sₚ] (p : Ideal R) [p.IsPrime]
    [IsLocalization.AtPrime Rₚ p]
    [IsLocalizedModule.AtPrime p (IsScalarTower.toAlgHom R S Sₚ : S →ₗ[R] Sₚ)] :
    IsLocalizedModule.map p.primeCompl (Algebra.linearMap R Rₚ)
        (IsScalarTower.toAlgHom R S Sₚ : S →ₗ[R] Sₚ) (Algebra.linearMap R S) =
    (Algebra.linearMap Rₚ Sₚ).restrictScalars R := by
  apply IsLocalizedModule.linearMap_ext p.primeCompl (Algebra.linearMap _ _)
    (IsScalarTower.toAlgHom R S Sₚ : S →ₗ[R] Sₚ)
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, map_one,
    LinearMap.coe_restrictScalars]
  rw [show 1 = Algebra.linearMap R Rₚ 1 by simp, IsLocalizedModule.map_apply]
  simp

lemma injective_of_isLocalization_isMaximal
    (H : ∀ (p : Ideal R) [p.IsMaximal], Function.Injective (algebraMap (Rₚ p) (Sₚ p))) :
    Function.Injective (algebraMap R S) := by
  apply injective_of_isLocalized_maximal (fun P _ ↦ Rₚ P) (fun P _ ↦ Algebra.linearMap _ _)
    (fun P _ ↦ Sₚ P) (fun P _ ↦ IsScalarTower.toAlgHom R S (Sₚ P)) (Algebra.linearMap R S) _
  intro p hp
  convert_to Function.Injective ((Algebra.linearMap (Rₚ p) (Sₚ p)).restrictScalars R)
  · rw [DFunLike.coe_fn_eq]
    apply IsLocalizedModule.map_linearMap_of_isLocalization
  · exact H p

lemma surjective_of_isLocalization_isMaximal
    (H : ∀ (p : Ideal R) [p.IsMaximal], Function.Surjective (algebraMap (Rₚ p) (Sₚ p))) :
    Function.Surjective (algebraMap R S) := by
  apply surjective_of_isLocalized_maximal (fun P _ ↦ Rₚ P) (fun P _ ↦ Algebra.linearMap _ _)
    (fun P _ ↦ Sₚ P) (fun P _ ↦ IsScalarTower.toAlgHom R S (Sₚ P)) (Algebra.linearMap R S) _
  intro p hp
  convert_to Function.Surjective ((Algebra.linearMap (Rₚ p) (Sₚ p)).restrictScalars R)
  · rw [DFunLike.coe_fn_eq]
    apply IsLocalizedModule.map_linearMap_of_isLocalization
  · exact H p

lemma bijective_of_isLocalization_isMaximal
    (H : ∀ (p : Ideal R) [p.IsMaximal], Function.Bijective (algebraMap (Rₚ p) (Sₚ p))) :
    Function.Bijective (algebraMap R S) :=
  ⟨injective_of_isLocalization_isMaximal _ _ (fun p _ ↦ (H p).1),
    surjective_of_isLocalization_isMaximal _ _ (fun p _ ↦ (H p).2)⟩

end Algebra

section IsLocalization

variable {R S : Type*} [CommSemiring R] [CommSemiring S]
variable {s : Set R} (hs : span s = ⊤)
  (Rᵣ : s → Type*) [∀ r, CommSemiring (Rᵣ r)] [∀ r, Algebra R (Rᵣ r)]
  (Sᵣ : s → Type*) [∀ r, CommSemiring (Sᵣ r)] [∀ r, Algebra S (Sᵣ r)]
variable (f : R →+* S) [∀ r, IsLocalization.Away r.val (Rᵣ r)]
    [∀ r, IsLocalization.Away (f r.val) (Sᵣ r)]
include hs

lemma injective_of_isLocalization_of_span_eq_top
    (h : ∀ r : s, Function.Injective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) f r.1)) :
    Function.Injective f := by
  algebraize [f]
  letI (r : s) : Algebra R (Sᵣ r) := (algebraMap S (Sᵣ r)).comp f |>.toAlgebra
  have (r : s) : IsScalarTower R S (Sᵣ r) := IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ r, IsLocalization.Away (algebraMap R S r.val) (Sᵣ r) := ‹_›
  letI (r : s) : Algebra (Rᵣ r) (Sᵣ r) := localizationAlgebra (.powers r.val) S
  have (r : s) : IsScalarTower R (Rᵣ r) (Sᵣ r) :=
    .of_algebraMap_eq <| by simp [RingHom.algebraMap_toAlgebra]
  apply injective_of_isLocalized_span s hs Rᵣ (fun r : s ↦ Algebra.linearMap _ _) _
    (fun r : s ↦ ((IsScalarTower.toAlgHom R S (Sᵣ r)).toLinearMap)) (Algebra.linearMap R S)
  simpa [IsLocalization.map_linearMap_eq_toLinearMap_mapₐ] using h

lemma surjective_of_isLocalization_of_span_eq_top
    (h : ∀ r : s, Function.Surjective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) f r.1)) :
    Function.Surjective f := by
  algebraize [f]
  letI (r : s) : Algebra R (Sᵣ r) := (algebraMap S (Sᵣ r)).comp f |>.toAlgebra
  have (r : s) : IsScalarTower R S (Sᵣ r) := IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ r, IsLocalization.Away (algebraMap R S r.val) (Sᵣ r) := ‹_›
  letI (r : s) : Algebra (Rᵣ r) (Sᵣ r) := localizationAlgebra (.powers r.val) S
  have (r : s) : IsScalarTower R (Rᵣ r) (Sᵣ r) :=
    .of_algebraMap_eq <| by simp [RingHom.algebraMap_toAlgebra]
  apply surjective_of_isLocalized_span s hs Rᵣ (fun r : s ↦ Algebra.linearMap _ _) _
    (fun r : s ↦ ((IsScalarTower.toAlgHom R S (Sᵣ r)).toLinearMap)) (Algebra.linearMap R S)
  simpa [IsLocalization.map_linearMap_eq_toLinearMap_mapₐ] using h

lemma bijective_of_isLocalization_of_span_eq_top
    (h : ∀ r : s, Function.Bijective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) f r.1)) :
    Function.Bijective f :=
  ⟨injective_of_isLocalization_of_span_eq_top hs _ _ _ (fun r ↦ (h r).1),
    surjective_of_isLocalization_of_span_eq_top hs _ _ _ (fun r ↦ (h r).2)⟩

end IsLocalization
