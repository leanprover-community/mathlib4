/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Refinements
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Lemmas about images

-- Verdier, Des catégories dérivées des catégories abéliennes, II 4.2.7

-/

namespace CategoryTheory

open Category Limits

variable {C : Type _} [Category C] [Abelian C]

namespace Abelian

noncomputable def image.lift {X Y : C} (f : X ⟶ Y) {A : C} (g : A ⟶ Y)
    (hg : g ≫ cokernel.π f = 0) : A ⟶ Abelian.image f :=
  kernel.lift _ g hg

@[reassoc (attr := simp)]
lemma image.lift_ι {X Y : C} (f : X ⟶ Y) {A : C} (g : A ⟶ Y)
    (hg : g ≫ cokernel.π f = 0 ) :
    Abelian.image.lift f g hg ≫ Abelian.image.ι f = g :=
  kernel.lift_ι _ _ _

section

variable {X Y : C} (f : X ⟶ Y) {Z : C} (p : X ⟶ Z) (i : Z ⟶ Y)
    (fac : p ≫ i = f) [Epi p]

noncomputable def toImageOfFac : Z ⟶ Abelian.image f :=
  image.lift f i
    (by rw [← cancel_epi p, reassoc_of% fac, cokernel.condition, comp_zero])

@[simp]
lemma toImageOfFac_ι : toImageOfFac f p i fac ≫ Abelian.image.ι f = i := by
  dsimp [toImageOfFac]
  simp only [image.lift_ι]

lemma toImageOfFac_fac :
    p ≫ toImageOfFac f p i fac = Abelian.factorThruImage f := by
  rw [← cancel_mono (Abelian.image.ι f), assoc, toImageOfFac_ι, kernel.lift_ι, fac]

instance [Mono i] : Mono (toImageOfFac f p i fac) :=
  mono_of_mono_fac (toImageOfFac_ι f p i fac)

instance : Epi (toImageOfFac f p i fac) :=
  epi_of_epi_fac (toImageOfFac_fac f p i fac)

instance [Mono i] : IsIso (toImageOfFac f p i fac) := by
  apply isIso_of_mono_of_epi

@[simps! hom]
noncomputable def isoImageOfFac [Mono i] :
    Z ≅ Abelian.image f :=
  asIso (toImageOfFac f p i fac)

end

variable (C)

structure ImagesLemmaInput where
  Y : C
  S : ShortComplex C
  hS : S.Exact
  f₁ : S.X₁ ⟶ Y
  f₂ : Y ⟶ S.X₂
  f₃ : Y ⟶ S.X₃
  fac₁ : f₁ ≫ f₂ = S.f := by aesop_cat
  fac₂ : f₂ ≫ S.g = f₃ := by aesop_cat

variable {C}

namespace ImagesLemmaInput

attribute [reassoc] fac₁ fac₂

variable (I : ImagesLemmaInput C)

@[simps]
noncomputable def shortComplex : ShortComplex C where
  X₁ := Abelian.image I.S.f
  X₂ := Abelian.image I.f₂
  X₃ := Abelian.image I.f₃
  f := image.lift I.f₂ (image.ι I.S.f) (by
    rw [← cancel_epi (Abelian.factorThruImage I.S.f), kernel.lift_ι_assoc,
      comp_zero, ← I.fac₁, assoc, cokernel.condition, comp_zero])
  g := image.lift I.f₃ (image.ι I.f₂ ≫ I.S.g) (by
    rw [assoc, ← cancel_epi (Abelian.factorThruImage I.f₂), kernel.lift_ι_assoc,
      comp_zero, I.fac₂_assoc, cokernel.condition])
  zero := by
    rw [← cancel_mono (image.ι I.f₃), zero_comp, assoc, image.lift_ι,
      image.lift_ι_assoc, ← cancel_epi (Abelian.factorThruImage I.S.f), comp_zero,
      kernel.lift_ι_assoc, I.S.zero]

lemma shortComplex_f_fac :
    I.shortComplex.f ≫ image.ι I.f₂ = image.ι I.S.f := by simp

lemma shortComplex_g_fac :
    Abelian.factorThruImage I.f₂ ≫ I.shortComplex.g = Abelian.factorThruImage I.f₃ := by
  rw [← cancel_mono (image.ι I.f₃), assoc, shortComplex_g, image.lift_ι,
    kernel.lift_ι_assoc, kernel.lift_ι, I.fac₂]

instance : Epi I.shortComplex.g := epi_of_epi_fac I.shortComplex_g_fac

lemma shortComplex_exact : I.shortComplex.Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A₀ x₂ hx₂
  dsimp
  obtain ⟨A₁, π₁, hπ₁, y, hy⟩ := surjective_up_to_refinements_of_epi
    (Abelian.factorThruImage I.f₂) x₂
  replace hy := hy =≫ (Abelian.image.ι I.f₂)
  have hx₂' := hx₂ =≫ (Abelian.image.ι I.f₃)
  rw [assoc, assoc, kernel.lift_ι] at hy
  rw [zero_comp, assoc, shortComplex_g, image.lift_ι] at hx₂'
  obtain ⟨A₂, π₂, hπ₂, x₁, hx₁⟩ := I.hS.exact_up_to_refinements (y ≫ I.f₂)
    (by rw [← hy, assoc, assoc, hx₂', comp_zero])
  refine ⟨A₂, π₂ ≫ π₁, epi_comp _ _, x₁ ≫ Abelian.factorThruImage I.S.f, ?_⟩
  simp only [← cancel_mono (Abelian.image.ι I.f₂), assoc, hy,
    image.lift_ι, kernel.lift_ι, hx₁]

instance : Mono (I.shortComplex.f) := mono_of_mono_fac I.shortComplex_f_fac

instance : Epi (I.shortComplex.g) := epi_of_epi_fac I.shortComplex_g_fac

lemma shortComplex_shortExact : I.shortComplex.ShortExact where
  exact := I.shortComplex_exact

end ImagesLemmaInput

end Abelian

end CategoryTheory
