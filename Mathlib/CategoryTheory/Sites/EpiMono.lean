/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.MorphismProperty.Concrete
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Morphisms of sheaves factor as a locally surjective followed by a locally injective morphism

When morphisms in a concrete category `A` factor in a functorial manner as a surjective map
followed by an injective map, we obtain that any morphism of sheaves in `Sheaf J A`
factors in a functorial manner as a locally surjective morphism (which is epi) followed by
a locally injective morphism (which is mono).

Moreover, if we assume that the category of sheaves `Sheaf J A` is balanced
(see `Sites.LeftExact`), then epimorphisms are exactly locally surjective morphisms.

-/

universe w v' u' v u

namespace CategoryTheory

open Category ConcreteCategory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A] [ConcreteCategory.{w} A]
  [HasFunctorialSurjectiveInjectiveFactorization A]
  [J.WEqualsLocallyBijective A]

namespace Presheaf

end Presheaf

namespace Sheaf

/-- The class of locally injective morphisms of sheaves, see `Sheaf.IsLocallyInjective`. -/
def locallyInjective : MorphismProperty (Sheaf J A) :=
  fun _ _  f => IsLocallyInjective f

/-- The class of locally surjective morphisms of sheaves, see `Sheaf.IsLocallySurjective`. -/
def locallySurjective : MorphismProperty (Sheaf J A) :=
  fun _ _  f => IsLocallySurjective f

section

variable {A}
variable (data : FunctorialSurjectiveInjectiveFactorizationData A) [HasWeakSheafify J A]

/-- Given a functorial surjective/injective factorizations of morphisms in a concrete
category `A`, this is the induced functorial locally surjective/locally injective
factorization of morphisms in the category `Sheaf J A`. -/
noncomputable def functorialLocallySurjectiveInjectiveFactorization :
    (locallySurjective J A).FunctorialFactorizationData (locallyInjective J A) where
  Z := (sheafToPresheaf J A).mapArrow ⋙ (data.functorCategory Cᵒᵖ).Z ⋙ presheafToSheaf J A
  i := whiskerLeft Arrow.leftFunc (inv (sheafificationAdjunction J A).counit) ≫
        whiskerLeft (sheafToPresheaf J A).mapArrow
          (whiskerRight (data.functorCategory Cᵒᵖ).i (presheafToSheaf J A))
  p := whiskerLeft (sheafToPresheaf J A).mapArrow
        (whiskerRight (data.functorCategory Cᵒᵖ).p (presheafToSheaf J A)) ≫
          whiskerLeft Arrow.rightFunc (sheafificationAdjunction J A).counit
  fac := by
    ext f : 2
    dsimp
    simp only [assoc, ← Functor.map_comp_assoc,
      MorphismProperty.FunctorialFactorizationData.fac_app,
      NatIso.isIso_inv_app, IsIso.inv_comp_eq]
    exact (sheafificationAdjunction J A).counit.naturality f.hom
  hi _ := by
    dsimp [locallySurjective]
    rw [← isLocallySurjective_sheafToPresheaf_map_iff, Functor.map_comp,
      Presheaf.comp_isLocallySurjective_iff, isLocallySurjective_sheafToPresheaf_map_iff,
      Presheaf.isLocallySurjective_presheafToSheaf_map_iff]
    apply Presheaf.isLocallySurjective_of_surjective
    apply (data.functorCategory Cᵒᵖ).hi
  hp _ := by
    dsimp [locallyInjective]
    rw [← isLocallyInjective_sheafToPresheaf_map_iff, Functor.map_comp,
      Presheaf.isLocallyInjective_comp_iff, isLocallyInjective_sheafToPresheaf_map_iff,
      Presheaf.isLocallyInjective_presheafToSheaf_map_iff]
    apply Presheaf.isLocallyInjective_of_injective
    apply (data.functorCategory Cᵒᵖ).hp

section

variable (f : Arrow (Sheaf J A))

instance : IsLocallySurjective
            ((functorialLocallySurjectiveInjectiveFactorization J data).i.app f) := by
  apply (functorialLocallySurjectiveInjectiveFactorization J data).hi

instance : IsLocallyInjective
            ((functorialLocallySurjectiveInjectiveFactorization J data).p.app f) := by
  apply (functorialLocallySurjectiveInjectiveFactorization J data).hp

variable [J.HasSheafCompose (forget A)]

instance : Epi ((functorialLocallySurjectiveInjectiveFactorization J data).i.app f) := by
  apply epi_of_isLocallySurjective

instance : Mono ((functorialLocallySurjectiveInjectiveFactorization J data).p.app f) := by
  apply mono_of_isLocallyInjective

end

instance : (locallySurjective J A).HasFunctorialFactorization (locallyInjective J A) where
  nonempty_functorialFactorizationData :=
    ⟨functorialLocallySurjectiveInjectiveFactorization J
      (MorphismProperty.functorialFactorizationData _ _)⟩

end

section

variable {J}
variable [HasSheafify J A] [J.HasSheafCompose (forget A)] [Balanced (Sheaf J A)]
variable {F G : Sheaf J A} (φ : F ⟶ G)

lemma isLocallySurjective_iff_epi' :
    IsLocallySurjective φ ↔ Epi φ := by
  constructor
  · intro
    infer_instance
  · intro
    let data := (locallySurjective J A).factorizationData (locallyInjective J A) φ
    have : IsLocallySurjective data.i := data.hi
    have : IsLocallyInjective data.p := data.hp
    have : Epi data.p := epi_of_epi_fac data.fac
    have := mono_of_isLocallyInjective data.p
    have := isIso_of_mono_of_epi data.p
    rw [← data.fac]
    infer_instance

end

end Sheaf

end CategoryTheory
