/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.QuotientNilpotent
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Unramified.Basic

#align_import ring_theory.etale from "leanprover-community/mathlib"@"73f96237417835f148a1f7bc1ff55f67119b7166"

/-!

# Etale morphisms

An `R`-algebra `A` is formally étale if for every `R`-algebra,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
exactly one lift `A →ₐ[R] B`.
It is étale if it is formally étale and of finite presentation.

We show that the property extends onto nilpotent ideals, and that these properties are stable
under `R`-algebra homomorphisms and compositions.

We show that étale is stable under algebra isomorphisms, composition and
localization at an element.

-/


-- Porting note: added to make the syntax work below.
open scoped TensorProduct

universe u

namespace Algebra

section

variable (R : Type u) [CommSemiring R]
variable (A : Type u) [Semiring A] [Algebra R A]

/-- An `R` algebra `A` is formally étale if for every `R`-algebra, every square-zero ideal
`I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists exactly one lift `A →ₐ[R] B`. -/
@[mk_iff]
class FormallyEtale : Prop where
  comp_bijective :
    ∀ ⦃B : Type u⦄ [CommRing B],
      ∀ [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
        Function.Bijective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)
#align algebra.formally_etale Algebra.FormallyEtale

end

namespace FormallyEtale

section

variable {R : Type u} [CommSemiring R]
variable {A : Type u} [Semiring A] [Algebra R A]
variable {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B)

theorem iff_unramified_and_smooth :
    FormallyEtale R A ↔ FormallyUnramified R A ∧ FormallySmooth R A := by
  rw [formallyUnramified_iff, formallySmooth_iff, formallyEtale_iff]
  simp_rw [← forall_and, Function.Bijective]
#align algebra.formally_etale.iff_unramified_and_smooth Algebra.FormallyEtale.iff_unramified_and_smooth

instance (priority := 100) to_unramified [h : FormallyEtale R A] :
    FormallyUnramified R A :=
  (FormallyEtale.iff_unramified_and_smooth.mp h).1
#align algebra.formally_etale.to_unramified Algebra.FormallyEtale.to_unramified

instance (priority := 100) to_smooth [h : FormallyEtale R A] : FormallySmooth R A :=
  (FormallyEtale.iff_unramified_and_smooth.mp h).2
#align algebra.formally_etale.to_smooth Algebra.FormallyEtale.to_smooth

theorem of_unramified_and_smooth [h₁ : FormallyUnramified R A]
    [h₂ : FormallySmooth R A] : FormallyEtale R A :=
  FormallyEtale.iff_unramified_and_smooth.mpr ⟨h₁, h₂⟩
#align algebra.formally_etale.of_unramified_and_smooth Algebra.FormallyEtale.of_unramified_and_smooth

end

section OfEquiv

variable {R : Type u} [CommSemiring R]
variable {A B : Type u} [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem of_equiv [FormallyEtale R A] (e : A ≃ₐ[R] B) : FormallyEtale R B :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.of_equiv e, FormallySmooth.of_equiv e⟩
#align algebra.formally_etale.of_equiv Algebra.FormallyEtale.of_equiv

end OfEquiv

section Comp

variable (R : Type u) [CommSemiring R]
variable (A : Type u) [CommSemiring A] [Algebra R A]
variable (B : Type u) [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem comp [FormallyEtale R A] [FormallyEtale A B] : FormallyEtale R B :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.comp R A B, FormallySmooth.comp R A B⟩
#align algebra.formally_etale.comp Algebra.FormallyEtale.comp

end Comp

section BaseChange

open scoped TensorProduct

variable {R : Type u} [CommSemiring R]
variable {A : Type u} [Semiring A] [Algebra R A]
variable (B : Type u) [CommSemiring B] [Algebra R B]

instance base_change [FormallyEtale R A] : FormallyEtale B (B ⊗[R] A) :=
  FormallyEtale.iff_unramified_and_smooth.mpr ⟨inferInstance, inferInstance⟩
#align algebra.formally_etale.base_change Algebra.FormallyEtale.base_change

end BaseChange

section Localization

variable {R S Rₘ Sₘ : Type u} [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
variable (M : Submonoid R)
variable [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
variable [IsLocalization M Rₘ] [IsLocalization (M.map (algebraMap R S)) Sₘ]

-- Porting note: no longer supported
-- attribute [local elab_as_elim] Ideal.IsNilpotent.induction_on

theorem of_isLocalization : FormallyEtale R Rₘ :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.of_isLocalization M, FormallySmooth.of_isLocalization M⟩
#align algebra.formally_etale.of_is_localization Algebra.FormallyEtale.of_isLocalization

theorem localization_base [FormallyEtale R Sₘ] : FormallyEtale Rₘ Sₘ :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.localization_base M, FormallySmooth.localization_base M⟩
#align algebra.formally_etale.localization_base Algebra.FormallyEtale.localization_base

theorem localization_map [FormallyEtale R S] : FormallyEtale Rₘ Sₘ := by
  haveI : FormallyEtale S Sₘ := FormallyEtale.of_isLocalization (M.map (algebraMap R S))
  haveI : FormallyEtale R Sₘ := FormallyEtale.comp R S Sₘ
  exact FormallyEtale.localization_base M
#align algebra.formally_etale.localization_map Algebra.FormallyEtale.localization_map

end Localization

end FormallyEtale

section

variable (R : Type u) [CommSemiring R]
variable (A : Type u) [Semiring A] [Algebra R A]

/-- An `R`-algebra `A` is étale if it is formally étale and of finite presentation. -/
class Etale : Prop where
  formallyEtale : FormallyEtale R A := by infer_instance
  finitePresentation : FinitePresentation R A := by infer_instance

end

namespace Etale

attribute [instance] formallyEtale finitePresentation

variable {R : Type u} [CommRing R]
variable {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Being étale is transported via algebra isomorphisms. -/
theorem of_equiv [Etale R A] (e : A ≃ₐ[R] B) : Etale R B where
  formallyEtale := FormallyEtale.of_equiv e
  finitePresentation := FinitePresentation.equiv e

section Comp

variable (R A B)

/-- Etale is stable under composition. -/
theorem comp [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale A B] : Etale R B where
  formallyEtale := FormallyEtale.comp R A B
  finitePresentation := FinitePresentation.trans R A B

/-- Etale is stable under base change. -/
instance baseChange [Etale R A] : Etale B (B ⊗[R] A) where

end Comp

/-- Localization at an element is étale. -/
theorem of_isLocalization_Away (r : R) [IsLocalization.Away r A] : Etale R A where
  formallyEtale := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  finitePresentation := IsLocalization.Away.finitePresentation r

end Etale

end Algebra
