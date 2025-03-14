/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Unramified.Basic

/-!

# Etale morphisms

An `R`-algebra `A` is formally étale if for every `R`-algebra `B`,
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

variable (R : Type u) [CommRing R]
variable (A : Type u) [CommRing A] [Algebra R A]

/-- An `R` algebra `A` is formally étale if for every `R`-algebra, every square-zero ideal
`I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists exactly one lift `A →ₐ[R] B`. -/
@[mk_iff, stacks 00UQ]
class FormallyEtale : Prop where
  comp_bijective :
    ∀ ⦃B : Type u⦄ [CommRing B],
      ∀ [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
        Function.Bijective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)

end

namespace FormallyEtale

section

variable {R : Type u} [CommRing R]
variable {A : Type u} [CommRing A] [Algebra R A]

theorem iff_unramified_and_smooth :
    FormallyEtale R A ↔ FormallyUnramified R A ∧ FormallySmooth R A := by
  rw [FormallyUnramified.iff_comp_injective, formallySmooth_iff, formallyEtale_iff]
  simp_rw [← forall_and, Function.Bijective]

instance (priority := 100) to_unramified [h : FormallyEtale R A] :
    FormallyUnramified R A :=
  (FormallyEtale.iff_unramified_and_smooth.mp h).1

instance (priority := 100) to_smooth [h : FormallyEtale R A] : FormallySmooth R A :=
  (FormallyEtale.iff_unramified_and_smooth.mp h).2

theorem of_unramified_and_smooth [h₁ : FormallyUnramified R A]
    [h₂ : FormallySmooth R A] : FormallyEtale R A :=
  FormallyEtale.iff_unramified_and_smooth.mpr ⟨h₁, h₂⟩

end

section OfEquiv

variable {R : Type u} [CommRing R]
variable {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

theorem of_equiv [FormallyEtale R A] (e : A ≃ₐ[R] B) : FormallyEtale R B :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.of_equiv e, FormallySmooth.of_equiv e⟩

theorem iff_of_equiv (e : A ≃ₐ[R] B) : FormallyEtale R A ↔ FormallyEtale R B :=
  ⟨fun _ ↦ of_equiv e, fun _ ↦ of_equiv e.symm⟩

end OfEquiv

section Comp

variable (R : Type u) [CommRing R]
variable (A : Type u) [CommRing A] [Algebra R A]
variable (B : Type u) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem comp [FormallyEtale R A] [FormallyEtale A B] : FormallyEtale R B :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.comp R A B, FormallySmooth.comp R A B⟩

end Comp

section BaseChange

open scoped TensorProduct

variable {R : Type u} [CommRing R]
variable {A : Type u} [CommRing A] [Algebra R A]
variable (B : Type u) [CommRing B] [Algebra R B]

instance base_change [FormallyEtale R A] : FormallyEtale B (B ⊗[R] A) :=
  FormallyEtale.iff_unramified_and_smooth.mpr ⟨inferInstance, inferInstance⟩

end BaseChange

section Localization

/-!

We now consider a commutative square of commutative rings

```
R -----> S
|        |
|        |
v        v
Rₘ ----> Sₘ
```

where `Rₘ` and `Sₘ` are the localisations of `R` and `S` at a multiplicatively closed
subset `M` of `R`.
-/

/-! Let R, S, Rₘ, Sₘ be commutative rings -/
variable {R S Rₘ Sₘ : Type u} [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
/-! Let M be a multiplicatively closed subset of `R` -/
variable (M : Submonoid R)
/-! Assume that the rings are in a commutative diagram as above. -/
variable [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
/-! and that Rₘ and Sₘ are localizations of R and S at M. -/
variable [IsLocalization M Rₘ] [IsLocalization (M.map (algebraMap R S)) Sₘ]
include M

-- Porting note: no longer supported
-- attribute [local elab_as_elim] Ideal.IsNilpotent.induction_on

theorem of_isLocalization : FormallyEtale R Rₘ :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.of_isLocalization M, FormallySmooth.of_isLocalization M⟩

theorem localization_base [FormallyEtale R Sₘ] : FormallyEtale Rₘ Sₘ :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.localization_base M, FormallySmooth.localization_base M⟩

/-- The localization of a formally étale map is formally étale. -/
theorem localization_map [FormallyEtale R S] : FormallyEtale Rₘ Sₘ := by
  haveI : FormallyEtale S Sₘ := FormallyEtale.of_isLocalization (M.map (algebraMap R S))
  haveI : FormallyEtale R Sₘ := FormallyEtale.comp R S Sₘ
  exact FormallyEtale.localization_base M

end Localization

end FormallyEtale

section

variable (R : Type u) [CommRing R]
variable (A : Type u) [CommRing A] [Algebra R A]

/-- An `R`-algebra `A` is étale if it is formally étale and of finite presentation. -/
@[stacks 00U1 "Note that this is a different definition from this Stacks entry, but
<https://stacks.math.columbia.edu/tag/00UR> shows that it is equivalent to the definition here."]
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

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S]

/--
A ring homomorphism `R →+* A` is formally etale if it is formally unramified and formally smooth.
See `Algebra.FormallyEtale`.
-/
@[algebraize Algebra.FormallyEtale]
def FormallyEtale (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.FormallyEtale R S

lemma formallyEtale_algebraMap [Algebra R S] :
    (algebraMap R S).FormallyEtale ↔ Algebra.FormallyEtale R S := by
  delta FormallyEtale
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

end RingHom
