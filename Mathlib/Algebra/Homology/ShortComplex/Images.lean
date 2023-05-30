import Mathlib.Algebra.Homology.ShortComplex.Refinements

-- Verdier, Des catégories dérivées des catégories abéliennes, II 4.2.7

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

variable (C)

structure ImagesLemmaInput where
  Y : C
  S : ShortComplex C
  hS : S.Exact
  f₁ : S.X₁ ⟶ Y
  f₂ : Y ⟶ S.X₂
  f₃ : Y ⟶ S.X₃
  fac₁ : f₁ ≫ f₂ = S.f
  fac₂ : f₂ ≫ S.g = f₃

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

lemma shortComplex_g_fac :
    Abelian.factorThruImage I.f₂ ≫ I.shortComplex.g = Abelian.factorThruImage I.f₃ := by
  rw [← cancel_mono (image.ι I.f₃), assoc, shortComplex_g, image.lift_ι,
    kernel.lift_ι_assoc, kernel.lift_ι, I.fac₂]

instance : Epi I.shortComplex.g := epi_of_epi_fac I.shortComplex_g_fac

lemma shortComplex_exact : I.shortComplex.Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A₀ x₂ hx₂
  dsimp
  obtain ⟨A₁, π₁, hπ₁, y, hy⟩ := surjective_up_to_refinements_of_epi (Abelian.factorThruImage I.f₂) x₂
  replace hy := hy =≫ (Abelian.image.ι I.f₂)
  have hx₂' := hx₂ =≫ (Abelian.image.ι I.f₃)
  rw [assoc, assoc, kernel.lift_ι] at hy
  rw [zero_comp, assoc, shortComplex_g, image.lift_ι] at hx₂'
  obtain ⟨A₂, π₂, hπ₂, x₁, hx₁⟩ := I.hS.exact_up_to_refinements (y ≫ I.f₂)
    (by rw [← hy, assoc, assoc, hx₂', comp_zero])
  refine' ⟨A₂, π₂ ≫ π₁, epi_comp _ _, x₁ ≫ Abelian.factorThruImage I.S.f, _⟩
  simp only [← cancel_mono (Abelian.image.ι I.f₂), assoc, hy,
    image.lift_ι, kernel.lift_ι, hx₁]

end ImagesLemmaInput

end Abelian

end CategoryTheory
