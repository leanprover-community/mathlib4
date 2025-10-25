/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Unramified.Basic

/-!

# Étale morphisms

An `R`-algebra `A` is formally etale if `Ω[A⁄R]` and `H¹(L_{S/R})` both vanish.
This is equivalent to the standard definition that "for every `R`-algebra `B`,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
exactly one lift `A →ₐ[R] B`".
An `R`-algebra `A` is étale if it is formally étale and of finite presentation.

We show that the property extends onto nilpotent ideals, and that these properties are stable
under `R`-algebra homomorphisms and compositions.

We show that étale is stable under algebra isomorphisms, composition and
localization at an element.

-/

open scoped TensorProduct

universe u v

namespace Algebra

variable {R : Type u} {A : Type v} {B : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]

section

variable (R A) in
/-- An `R`-algebra `A` is formally etale if both `Ω[A⁄R]` and `H¹(L_{S/R})` are zero.
For the infinitesimal lifting definition, see `FormallyEtale.iff_comp_bijective`. -/
@[mk_iff, stacks 00UQ]
class FormallyEtale : Prop where
  subsingleton_kaehlerDifferential : Subsingleton Ω[A⁄R]
  subsingleton_h1Cotangent : Subsingleton (H1Cotangent R A)

attribute [instance]
  FormallyEtale.subsingleton_kaehlerDifferential FormallyEtale.subsingleton_h1Cotangent

end

namespace FormallyEtale

section

instance (priority := 100) to_unramified [FormallyEtale R A] :
    FormallyUnramified R A := ⟨subsingleton_kaehlerDifferential⟩

instance (priority := 100) to_smooth [FormallyEtale R A] : FormallySmooth R A :=
  ⟨inferInstance, inferInstance⟩

theorem iff_unramified_and_smooth :
    FormallyEtale R A ↔ FormallyUnramified R A ∧ FormallySmooth R A :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ⟨inferInstance, inferInstance⟩⟩

theorem of_unramified_and_smooth [FormallyUnramified R A]
    [FormallySmooth R A] : FormallyEtale R A :=
  FormallyEtale.iff_unramified_and_smooth.mpr ⟨‹_›, ‹_›⟩

variable (R A) in
lemma comp_bijective [FormallyEtale R A] (I : Ideal B) (hI : I ^ 2 = ⊥) :
    Function.Bijective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) :=
  ⟨FormallyUnramified.comp_injective I hI, FormallySmooth.comp_surjective R A I hI⟩

/--
An `R`-algebra `A` is formally etale iff "for every `R`-algebra `B`,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
a unique lift `A →ₐ[R] B`".
-/
theorem iff_comp_bijective :
   FormallyEtale R A ↔ ∀ ⦃B : Type max u v⦄ [CommRing B] [Algebra R B] (I : Ideal B), I ^ 2 = ⊥ →
      Function.Bijective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) :=
  ⟨fun _ _ ↦ comp_bijective R A, fun H ↦
    have : FormallyUnramified R A := FormallyUnramified.iff_comp_injective'.mpr
      (by aesop (add safe Function.Bijective.injective))
    have : FormallySmooth R A := FormallySmooth.of_comp_surjective
      (by aesop (add safe Function.Bijective.surjective))
   FormallyEtale.of_unramified_and_smooth⟩

end

section OfEquiv

theorem of_equiv [FormallyEtale R A] (e : A ≃ₐ[R] B) : FormallyEtale R B :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.of_equiv e, FormallySmooth.of_equiv e⟩

theorem iff_of_equiv (e : A ≃ₐ[R] B) : FormallyEtale R A ↔ FormallyEtale R B :=
  ⟨fun _ ↦ of_equiv e, fun _ ↦ of_equiv e.symm⟩

end OfEquiv

section Comp

variable (R A B) in
theorem comp [Algebra A B] [IsScalarTower R A B] [FormallyEtale R A] [FormallyEtale A B] :
    FormallyEtale R B :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.comp R A B, FormallySmooth.comp R A B⟩

end Comp

section BaseChange

open scoped TensorProduct

variable (B) in
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
variable {R S Rₘ Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
/-! Let M be a multiplicatively closed subset of `R` -/
variable (M : Submonoid R)
/-! Assume that the rings are in a commutative diagram as above. -/
variable [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
/-! and that Rₘ and Sₘ are localizations of R and S at M. -/
variable [IsLocalization M Rₘ] [IsLocalization (M.map (algebraMap R S)) Sₘ]
include M

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

variable (R A) in
/-- An `R`-algebra `A` is étale if it is formally étale and of finite presentation. -/
@[stacks 00U1 "Note that this is a different definition from this Stacks entry, but
<https://stacks.math.columbia.edu/tag/00UR> shows that it is equivalent to the definition here."]
class Etale : Prop where
  formallyEtale : FormallyEtale R A := by infer_instance
  finitePresentation : FinitePresentation R A := by infer_instance

end

namespace Etale

attribute [instance] formallyEtale finitePresentation

/-- Being étale is transported via algebra isomorphisms. -/
theorem of_equiv [Etale R A] (e : A ≃ₐ[R] B) : Etale R B where
  formallyEtale := FormallyEtale.of_equiv e
  finitePresentation := FinitePresentation.equiv e

section Comp

variable (R A B)

/-- Étale is stable under composition. -/
theorem comp [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale A B] : Etale R B where
  formallyEtale := FormallyEtale.comp R A B
  finitePresentation := FinitePresentation.trans R A B

/-- Étale is stable under base change. -/
instance baseChange [Etale R A] : Etale B (B ⊗[R] A) where

end Comp

/-- Localization at an element is étale. -/
theorem of_isLocalization_Away (r : R) [IsLocalization.Away r A] : Etale R A where
  formallyEtale := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  finitePresentation := IsLocalization.Away.finitePresentation r

end Etale

end Algebra

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/--
A ring homomorphism `R →+* A` is formally étale if it is formally unramified and formally smooth.
See `Algebra.FormallyEtale`.
-/
@[algebraize Algebra.FormallyEtale]
def FormallyEtale (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.FormallyEtale R S

lemma formallyEtale_algebraMap [Algebra R S] :
    (algebraMap R S).FormallyEtale ↔ Algebra.FormallyEtale R S := by
  rw [FormallyEtale, toAlgebra_algebraMap]

end RingHom
