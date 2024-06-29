/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.QuotientNilpotent
import Mathlib.RingTheory.TensorProduct.Basic

/-!

# Unramified morphisms

An `R`-algebra `A` is formally unramified if for every `R`-algebra,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
at most one lift `A →ₐ[R] B`.
It is unramified if it is formally unramified and of finite type.

Note that there are multiple definitions in the literature. The definition we give is equivalent to
the one in the Stacks Project https://stacks.math.columbia.edu/tag/00US. Note that in EGA unramified
is defined as formally unramified and of finite presentation.

We show that the property extends onto nilpotent ideals, and that it is stable
under `R`-algebra homomorphisms and compositions.

We show that unramified is stable under algebra isomorphisms, composition and
localization at an element.

-/

-- Porting note: added to make the syntax work below.
open scoped TensorProduct

universe u

namespace Algebra

section

variable (R : Type u) [CommSemiring R]
variable (A : Type u) [Semiring A] [Algebra R A]

/-- An `R`-algebra `A` is formally unramified if for every `R`-algebra, every square-zero ideal
`I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at most one lift `A →ₐ[R] B`. -/
@[mk_iff]
class FormallyUnramified : Prop where
  comp_injective :
    ∀ ⦃B : Type u⦄ [CommRing B],
      ∀ [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
        Function.Injective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)
#align algebra.formally_unramified Algebra.FormallyUnramified

end

namespace FormallyUnramified

section

variable {R : Type u} [CommSemiring R]
variable {A : Type u} [Semiring A] [Algebra R A]
variable {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B)

theorem lift_unique {B : Type u} [CommRing B] [_RB : Algebra R B]
    [FormallyUnramified R A] (I : Ideal B) (hI : IsNilpotent I) (g₁ g₂ : A →ₐ[R] B)
    (h : (Ideal.Quotient.mkₐ R I).comp g₁ = (Ideal.Quotient.mkₐ R I).comp g₂) : g₁ = g₂ := by
  revert g₁ g₂
  change Function.Injective (Ideal.Quotient.mkₐ R I).comp
  revert _RB
  apply Ideal.IsNilpotent.induction_on (R := B) I hI
  · intro B _ I hI _; exact FormallyUnramified.comp_injective I hI
  · intro B _ I J hIJ h₁ h₂ _ g₁ g₂ e
    apply h₁
    apply h₂
    ext x
    replace e := AlgHom.congr_fun e x
    dsimp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at e ⊢
    rwa [Ideal.Quotient.eq, ← map_sub, Ideal.mem_quotient_iff_mem hIJ, ← Ideal.Quotient.eq]
#align algebra.formally_unramified.lift_unique Algebra.FormallyUnramified.lift_unique

theorem ext [FormallyUnramified R A] (hI : IsNilpotent I) {g₁ g₂ : A →ₐ[R] B}
    (H : ∀ x, Ideal.Quotient.mk I (g₁ x) = Ideal.Quotient.mk I (g₂ x)) : g₁ = g₂ :=
  FormallyUnramified.lift_unique I hI g₁ g₂ (AlgHom.ext H)
#align algebra.formally_unramified.ext Algebra.FormallyUnramified.ext

theorem lift_unique_of_ringHom [FormallyUnramified R A] {C : Type u} [CommRing C]
    (f : B →+* C) (hf : IsNilpotent <| RingHom.ker f) (g₁ g₂ : A →ₐ[R] B)
    (h : f.comp ↑g₁ = f.comp (g₂ : A →+* B)) : g₁ = g₂ :=
  FormallyUnramified.lift_unique _ hf _ _
    (by
      ext x
      have := RingHom.congr_fun h x
      simpa only [Ideal.Quotient.eq, Function.comp_apply, AlgHom.coe_comp, Ideal.Quotient.mkₐ_eq_mk,
        RingHom.mem_ker, map_sub, sub_eq_zero])
#align algebra.formally_unramified.lift_unique_of_ring_hom Algebra.FormallyUnramified.lift_unique_of_ringHom

theorem ext' [FormallyUnramified R A] {C : Type u} [CommRing C] (f : B →+* C)
    (hf : IsNilpotent <| RingHom.ker f) (g₁ g₂ : A →ₐ[R] B) (h : ∀ x, f (g₁ x) = f (g₂ x)) :
    g₁ = g₂ :=
  FormallyUnramified.lift_unique_of_ringHom f hf g₁ g₂ (RingHom.ext h)
#align algebra.formally_unramified.ext' Algebra.FormallyUnramified.ext'

theorem lift_unique' [FormallyUnramified R A] {C : Type u} [CommRing C]
    [Algebra R C] (f : B →ₐ[R] C) (hf : IsNilpotent <| RingHom.ker (f : B →+* C))
    (g₁ g₂ : A →ₐ[R] B) (h : f.comp g₁ = f.comp g₂) : g₁ = g₂ :=
  FormallyUnramified.ext' _ hf g₁ g₂ (AlgHom.congr_fun h)
#align algebra.formally_unramified.lift_unique' Algebra.FormallyUnramified.lift_unique'

end

section OfEquiv

variable {R : Type u} [CommSemiring R]
variable {A B : Type u} [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem of_equiv [FormallyUnramified R A] (e : A ≃ₐ[R] B) :
    FormallyUnramified R B := by
  constructor
  intro C _ _ I hI f₁ f₂ e'
  rw [← f₁.comp_id, ← f₂.comp_id, ← e.comp_symm, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
  congr 1
  refine FormallyUnramified.comp_injective I hI ?_
  rw [← AlgHom.comp_assoc, e', AlgHom.comp_assoc]
#align algebra.formally_unramified.of_equiv Algebra.FormallyUnramified.of_equiv

end OfEquiv

section Comp

variable (R : Type u) [CommSemiring R]
variable (A : Type u) [CommSemiring A] [Algebra R A]
variable (B : Type u) [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem comp [FormallyUnramified R A] [FormallyUnramified A B] :
    FormallyUnramified R B := by
  constructor
  intro C _ _ I hI f₁ f₂ e
  have e' :=
    FormallyUnramified.lift_unique I ⟨2, hI⟩ (f₁.comp <| IsScalarTower.toAlgHom R A B)
      (f₂.comp <| IsScalarTower.toAlgHom R A B) (by rw [← AlgHom.comp_assoc, e, AlgHom.comp_assoc])
  letI := (f₁.comp (IsScalarTower.toAlgHom R A B)).toRingHom.toAlgebra
  let F₁ : B →ₐ[A] C := { f₁ with commutes' := fun r => rfl }
  let F₂ : B →ₐ[A] C := { f₂ with commutes' := AlgHom.congr_fun e'.symm }
  ext1 x
  change F₁ x = F₂ x
  congr
  exact FormallyUnramified.ext I ⟨2, hI⟩ (AlgHom.congr_fun e)
#align algebra.formally_unramified.comp Algebra.FormallyUnramified.comp

theorem of_comp [FormallyUnramified R B] : FormallyUnramified A B := by
  constructor
  intro Q _ _ I e f₁ f₂ e'
  letI := ((algebraMap A Q).comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A Q := IsScalarTower.of_algebraMap_eq' rfl
  refine AlgHom.restrictScalars_injective R ?_
  refine FormallyUnramified.ext I ⟨2, e⟩ ?_
  intro x
  exact AlgHom.congr_fun e' x
#align algebra.formally_unramified.of_comp Algebra.FormallyUnramified.of_comp

end Comp

section BaseChange

open scoped TensorProduct

variable {R : Type u} [CommSemiring R]
variable {A : Type u} [Semiring A] [Algebra R A]
variable (B : Type u) [CommSemiring B] [Algebra R B]

instance base_change [FormallyUnramified R A] :
    FormallyUnramified B (B ⊗[R] A) := by
  constructor
  intro C _ _ I hI f₁ f₂ e
  letI := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  ext : 1
  · exact Subsingleton.elim _ _
  · exact FormallyUnramified.ext I ⟨2, hI⟩ fun x => AlgHom.congr_fun e (1 ⊗ₜ x)
#align algebra.formally_unramified.base_change Algebra.FormallyUnramified.base_change

end BaseChange

section Localization

variable {R S Rₘ Sₘ : Type u} [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
variable (M : Submonoid R)
variable [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
variable [IsLocalization M Rₘ] [IsLocalization (M.map (algebraMap R S)) Sₘ]

-- Porting note: no longer supported
-- attribute [local elab_as_elim] Ideal.IsNilpotent.induction_on

/-- This holds in general for epimorphisms. -/
theorem of_isLocalization : FormallyUnramified R Rₘ := by
  constructor
  intro Q _ _ I _ f₁ f₂ _
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext M ?_
  ext
  simp
#align algebra.formally_unramified.of_is_localization Algebra.FormallyUnramified.of_isLocalization

/-- This actually does not need the localization instance, and is stated here again for
consistency. See `Algebra.FormallyUnramified.of_comp` instead.

 The intended use is for copying proofs between `Formally{Unramified, Smooth, Etale}`
 without the need to change anything (including removing redundant arguments). -/
-- @[nolint unusedArguments] -- Porting note: removed
theorem localization_base [FormallyUnramified R Sₘ] : FormallyUnramified Rₘ Sₘ :=
  -- Porting note: added
  let _ := M
  FormallyUnramified.of_comp R Rₘ Sₘ
#align algebra.formally_unramified.localization_base Algebra.FormallyUnramified.localization_base

theorem localization_map [FormallyUnramified R S] :
    FormallyUnramified Rₘ Sₘ := by
  haveI : FormallyUnramified S Sₘ :=
    FormallyUnramified.of_isLocalization (M.map (algebraMap R S))
  haveI : FormallyUnramified R Sₘ := FormallyUnramified.comp R S Sₘ
  exact FormallyUnramified.localization_base M
#align algebra.formally_unramified.localization_map Algebra.FormallyUnramified.localization_map

end Localization

end FormallyUnramified

section

variable (R : Type u) [CommSemiring R]
variable (A : Type u) [Semiring A] [Algebra R A]

/-- An `R`-algebra `A` is unramified if it is formally unramified and of finite type.
-/
class Unramified : Prop where
  formallyUnramified : FormallyUnramified R A := by infer_instance
  finiteType : FiniteType R A := by infer_instance

end

namespace Unramified

attribute [instance] formallyUnramified finiteType

variable {R : Type u} [CommRing R]
variable {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Being unramified is transported via algebra isomorphisms. -/
theorem of_equiv [Unramified R A] (e : A ≃ₐ[R] B) : Unramified R B where
  formallyUnramified := FormallyUnramified.of_equiv e
  finiteType := FiniteType.equiv Unramified.finiteType e

/-- Localization at an element is unramified. -/
theorem of_isLocalization_Away (r : R) [IsLocalization.Away r A] : Unramified R A where
  formallyUnramified := Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers r)
  finiteType :=
    haveI : FinitePresentation R A := IsLocalization.Away.finitePresentation r
    inferInstance

section Comp

variable (R A B)

/-- Unramified is stable under composition. -/
theorem comp [Algebra A B] [IsScalarTower R A B] [Unramified R A] [Unramified A B] :
    Unramified R B where
  formallyUnramified := FormallyUnramified.comp R A B
  finiteType := FiniteType.trans (S := A) Unramified.finiteType
    Unramified.finiteType

/-- Unramified is stable under base change. -/
instance baseChange [Unramified R A] : Unramified B (B ⊗[R] A) where

end Comp

end Unramified

end Algebra
