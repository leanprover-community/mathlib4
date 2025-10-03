/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!

# Unramified morphisms

An `R`-algebra `A` is formally unramified if `Ω[A⁄R]` is trivial.
This is equivalent to the standard definition "for every `R`-algebra,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
at most one lift `A →ₐ[R] B`".
It is unramified if it is formally unramified and of finite type.

Note that there are multiple definitions in the literature. The definition we give is equivalent to
the one in the Stacks Project https://stacks.math.columbia.edu/tag/00US. Note that in EGA unramified
is defined as formally unramified and of finite presentation.

We show that the property extends onto nilpotent ideals, and that it is stable
under `R`-algebra homomorphisms and compositions.

We show that unramified is stable under algebra isomorphisms, composition and
localization at an element.

-/

open scoped TensorProduct

universe u v w

namespace Algebra

section

variable (R : Type v) (A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/--
An `R`-algebra `A` is formally unramified if `Ω[A⁄R]` is trivial.

This is equivalent to "for every `R`-algebra, every square-zero ideal
`I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at most one lift `A →ₐ[R] B`".
See `Algebra.FormallyUnramified.iff_comp_injective`. -/
@[mk_iff, stacks 00UM]
class FormallyUnramified : Prop where
  subsingleton_kaehlerDifferential : Subsingleton Ω[A⁄R]

attribute [instance] FormallyUnramified.subsingleton_kaehlerDifferential

end

namespace FormallyUnramified

section

variable {R : Type v} [CommRing R]
variable {A : Type u} [CommRing A] [Algebra R A]
variable {B : Type w} [CommRing B] [Algebra R B] (I : Ideal B)

theorem comp_injective [FormallyUnramified R A] (hI : I ^ 2 = ⊥) :
    Function.Injective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) := by
  intro f₁ f₂ e
  letI := f₁.toRingHom.toAlgebra
  haveI := IsScalarTower.of_algebraMap_eq' f₁.comp_algebraMap.symm
  have :=
    ((KaehlerDifferential.linearMapEquivDerivation R A).toEquiv.trans
          (derivationToSquareZeroEquivLift I hI)).surjective.subsingleton
  exact Subtype.ext_iff.mp (@Subsingleton.elim _ this ⟨f₁, rfl⟩ ⟨f₂, e.symm⟩)

theorem iff_comp_injective :
    FormallyUnramified R A ↔
      ∀ ⦃B : Type u⦄ [CommRing B],
        ∀ [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
          Function.Injective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) := by
  constructor
  · intros; exact comp_injective _ ‹_›
  · intro H
    constructor
    by_contra! h
    obtain ⟨f₁, f₂, e⟩ := (KaehlerDifferential.endEquiv R A).injective.nontrivial
    apply e
    ext1
    refine H
      (RingHom.ker (TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom) ?_ ?_
    · rw [AlgHom.ker_kerSquareLift]
      exact Ideal.cotangentIdeal_square _
    · ext x
      apply RingHom.kerLift_injective (TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom
      simpa using DFunLike.congr_fun (f₁.2.trans f₂.2.symm) x

theorem lift_unique
    [FormallyUnramified R A] (I : Ideal B) (hI : IsNilpotent I) (g₁ g₂ : A →ₐ[R] B)
    (h : (Ideal.Quotient.mkₐ R I).comp g₁ = (Ideal.Quotient.mkₐ R I).comp g₂) : g₁ = g₂ := by
  revert g₁ g₂
  change Function.Injective (Ideal.Quotient.mkₐ R I).comp
  revert ‹Algebra R B›
  apply Ideal.IsNilpotent.induction_on (S := B) I hI
  · intro B _ I hI _; exact FormallyUnramified.comp_injective I hI
  · intro B _ I J hIJ h₁ h₂ _ g₁ g₂ e
    apply h₁
    apply h₂
    ext x
    replace e := AlgHom.congr_fun e x
    dsimp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at e ⊢
    rwa [Ideal.Quotient.eq, ← map_sub, Ideal.mem_quotient_iff_mem hIJ, ← Ideal.Quotient.eq]

theorem ext [FormallyUnramified R A] (hI : IsNilpotent I) {g₁ g₂ : A →ₐ[R] B}
    (H : ∀ x, Ideal.Quotient.mk I (g₁ x) = Ideal.Quotient.mk I (g₂ x)) : g₁ = g₂ :=
  FormallyUnramified.lift_unique I hI g₁ g₂ (AlgHom.ext H)

theorem lift_unique_of_ringHom [FormallyUnramified R A] {C : Type*} [Ring C]
    (f : B →+* C) (hf : IsNilpotent <| RingHom.ker f) (g₁ g₂ : A →ₐ[R] B)
    (h : f.comp ↑g₁ = f.comp (g₂ : A →+* B)) : g₁ = g₂ :=
  FormallyUnramified.lift_unique _ hf _ _
    (by
      ext x
      have := RingHom.congr_fun h x
      simpa only [Ideal.Quotient.eq, Function.comp_apply, AlgHom.coe_comp, Ideal.Quotient.mkₐ_eq_mk,
        RingHom.mem_ker, map_sub, sub_eq_zero])

theorem ext' [FormallyUnramified R A] {C : Type*} [Ring C] (f : B →+* C)
    (hf : IsNilpotent <| RingHom.ker f) (g₁ g₂ : A →ₐ[R] B) (h : ∀ x, f (g₁ x) = f (g₂ x)) :
    g₁ = g₂ :=
  FormallyUnramified.lift_unique_of_ringHom f hf g₁ g₂ (RingHom.ext h)

theorem lift_unique' [FormallyUnramified R A] {C : Type*} [Ring C]
    [Algebra R C] (f : B →ₐ[R] C) (hf : IsNilpotent <| RingHom.ker (f : B →+* C))
    (g₁ g₂ : A →ₐ[R] B) (h : f.comp g₁ = f.comp g₂) : g₁ = g₂ :=
  FormallyUnramified.ext' _ hf g₁ g₂ (AlgHom.congr_fun h)

theorem ext_of_iInf [FormallyUnramified R A] (hI : ⨅ i, I ^ i = ⊥) {g₁ g₂ : A →ₐ[R] B}
    (H : ∀ x, Ideal.Quotient.mk I (g₁ x) = Ideal.Quotient.mk I (g₂ x)) : g₁ = g₂ := by
  have (i : ℕ) :
      (Ideal.Quotient.mkₐ R (I ^ i)).comp g₁ = (Ideal.Quotient.mkₐ R (I ^ i)).comp g₂ := by
    by_cases hi : i = 0
    · ext x
      have : Subsingleton (B ⧸ I ^ i) := by
        rw [hi, pow_zero, Ideal.one_eq_top]
        infer_instance
      exact Subsingleton.elim _ _
    apply ext (I.map (algebraMap _ _)) ⟨i, by simp [← Ideal.map_pow]⟩
    intro x
    dsimp
    rw [Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap, Ideal.comap_map_of_surjective',
      sup_eq_left.mpr, ← Ideal.Quotient.eq]
    · exact H _
    · simpa using Ideal.pow_le_self hi
    · exact Ideal.Quotient.mk_surjective
  ext x
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← hI, Ideal.mem_iInf]
  intro i
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact DFunLike.congr_fun (this i) x

end

instance {R : Type*} [CommRing R] : FormallyUnramified R R := by
  rw [iff_comp_injective]
  intro B _ _ _ _ f₁ f₂ _
  exact Subsingleton.elim _ _

section OfEquiv

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

theorem of_equiv [FormallyUnramified R A] (e : A ≃ₐ[R] B) :
    FormallyUnramified R B := by
  rw [iff_comp_injective]
  intro C _ _ I hI f₁ f₂ e'
  rw [← f₁.comp_id, ← f₂.comp_id, ← e.comp_symm, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
  congr 1
  refine FormallyUnramified.comp_injective I hI ?_
  rw [← AlgHom.comp_assoc, e', AlgHom.comp_assoc]

end OfEquiv

section Comp

variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]
variable (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem comp [FormallyUnramified R A] [FormallyUnramified A B] :
    FormallyUnramified R B := by
  rw [iff_comp_injective]
  intro C _ _ I hI f₁ f₂ e
  have e' :=
    FormallyUnramified.lift_unique I ⟨2, hI⟩ (f₁.comp <| IsScalarTower.toAlgHom R A B)
      (f₂.comp <| IsScalarTower.toAlgHom R A B) (by rw [← AlgHom.comp_assoc, e, AlgHom.comp_assoc])
  letI := (f₁.restrictDomain A).toAlgebra
  let F₁ : B →ₐ[A] C := { f₁ with commutes' := fun r => rfl }
  let F₂ : B →ₐ[A] C := { f₂ with commutes' := AlgHom.congr_fun e'.symm }
  ext1 x
  change F₁ x = F₂ x
  congr
  exact FormallyUnramified.ext I ⟨2, hI⟩ (AlgHom.congr_fun e)

theorem of_comp [FormallyUnramified R B] : FormallyUnramified A B := by
  rw [iff_comp_injective]
  intro Q _ _ I e f₁ f₂ e'
  letI := ((algebraMap A Q).comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A Q := IsScalarTower.of_algebraMap_eq' rfl
  refine AlgHom.restrictScalars_injective R ?_
  refine FormallyUnramified.ext I ⟨2, e⟩ ?_
  intro x
  exact AlgHom.congr_fun e' x

end Comp

section of_surjective

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- This holds in general for epimorphisms. -/
theorem of_surjective [FormallyUnramified R A] (f : A →ₐ[R] B) (H : Function.Surjective f) :
    FormallyUnramified R B := by
  rw [iff_comp_injective]
  intro Q _ _ I hI f₁ f₂ e
  ext x
  obtain ⟨x, rfl⟩ := H x
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply FormallyUnramified.comp_injective I hI
  ext x; exact DFunLike.congr_fun e (f x)

instance quotient {A} [CommRing A] [Algebra R A] [FormallyUnramified R A] (I : Ideal A) :
    FormallyUnramified R (A ⧸ I) :=
  FormallyUnramified.of_surjective (IsScalarTower.toAlgHom R A (A ⧸ I)) Ideal.Quotient.mk_surjective

theorem iff_of_equiv (e : A ≃ₐ[R] B) : FormallyUnramified R A ↔ FormallyUnramified R B :=
  ⟨fun _ ↦ of_equiv e, fun _ ↦ of_equiv e.symm⟩

end of_surjective

section BaseChange

open scoped TensorProduct

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable (B : Type*) [CommRing B] [Algebra R B]

instance base_change [FormallyUnramified R A] :
    FormallyUnramified B (B ⊗[R] A) := by
  rw [iff_comp_injective]
  intro C _ _ I hI f₁ f₂ e
  letI := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  ext : 1
  · subsingleton
  · exact FormallyUnramified.ext I ⟨2, hI⟩ fun x => AlgHom.congr_fun e (1 ⊗ₜ x)

end BaseChange

section Localization

variable {R S Rₘ Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
variable (M : Submonoid R)
variable [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
variable [IsLocalization (M.map (algebraMap R S)) Sₘ]
include M

/-- This holds in general for epimorphisms. -/
theorem of_isLocalization [IsLocalization M Rₘ] : FormallyUnramified R Rₘ := by
  rw [iff_comp_injective]
  intro Q _ _ I _ f₁ f₂ _
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext M ?_
  ext
  simp

instance [FormallyUnramified R S] (M : Submonoid S) : FormallyUnramified R (Localization M) :=
  have := of_isLocalization (Rₘ := Localization M) M
  .comp _ S _

set_option linter.unusedSectionVars false in
/-- This actually does not need the localization instance, and is stated here again for
consistency. See `Algebra.FormallyUnramified.of_comp` instead.

The intended use is for copying proofs between `Formally{Unramified, Smooth, Etale}`
without the need to change anything (including removing redundant arguments). -/
@[nolint unusedArguments]
theorem localization_base [FormallyUnramified R Sₘ] : FormallyUnramified Rₘ Sₘ :=
  FormallyUnramified.of_comp R Rₘ Sₘ

theorem localization_map [FormallyUnramified R S] :
    FormallyUnramified Rₘ Sₘ := by
  haveI : FormallyUnramified S Sₘ :=
    FormallyUnramified.of_isLocalization (M.map (algebraMap R S))
  haveI : FormallyUnramified R Sₘ := FormallyUnramified.comp R S Sₘ
  exact FormallyUnramified.localization_base M

end Localization

end FormallyUnramified

section

variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]

/-- An `R`-algebra `A` is unramified if it is formally unramified and of finite type. -/
@[stacks 00UT "Note that the Stacks project has a different definition of unramified, and tag
<https://stacks.math.columbia.edu/tag/00UU> shows that their definition is the same as this one."]
class Unramified : Prop where
  formallyUnramified : FormallyUnramified R A := by infer_instance
  finiteType : FiniteType R A := by infer_instance

end

namespace Unramified

attribute [instance] formallyUnramified finiteType

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

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
