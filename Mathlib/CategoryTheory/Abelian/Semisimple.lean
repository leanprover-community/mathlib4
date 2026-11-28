/-
Copyright (c) 2026 mrb-eel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mrb-eel
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Semisimple abelian categories

An abelian category is semisimple if every short exact sequence splits. This is equivalent
to every object being injective and to every object being projective.
-/

@[expose] public section

namespace CategoryTheory.Abelian

open Category Limits

universe v u

variable {C : Type u} [Category.{v, u} C] [Abelian C]

/-- An abelian category is semisimple if every short exact sequence admits a splitting. -/
def IsSemisimple (C : Type u) [Category.{v, u} C] [Abelian C] : Prop :=
  ∀ (S : ShortComplex C), S.ShortExact → Nonempty S.Splitting

/-- Every object of a semisimple abelian category is injective. -/
lemma IsSemisimple.injective (hC : IsSemisimple C) (J : C) : Injective J where
  factors {X Y} g f := by
    intro
    let S := ShortComplex.cokernelSequence f
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact f
        mono_f := inferInstanceAs (Mono f) }
    obtain ⟨σ⟩ := hC S hS
    let r : Y ⟶ X := σ.r
    have h : f ≫ r = 𝟙 X := σ.f_r
    exact ⟨r ≫ g, by rw [← assoc, h, id_comp]⟩

/-- Every object of a semisimple abelian category is projective. -/
lemma IsSemisimple.projective (hC : IsSemisimple C) (P : C) : Projective P where
  factors {E X} f e := by
    intro
    let S := ShortComplex.kernelSequence e
    have hS : S.ShortExact :=
      { exact := ShortComplex.kernelSequence_exact e
        epi_g := inferInstanceAs (Epi e) }
    obtain ⟨σ⟩ := hC S hS
    let s : X ⟶ E := σ.s
    have h : s ≫ e = 𝟙 X := σ.s_g
    exact ⟨f ≫ s, by rw [assoc, h, comp_id]⟩

/-- An abelian category in which every object is injective is semisimple. -/
lemma isSemisimple_of_injective (h : ∀ X : C, Injective X) : IsSemisimple C := by
  intro S hS
  have := h S.X₁
  exact ⟨hS.splittingOfInjective⟩

/-- An abelian category in which every object is projective is semisimple. -/
lemma isSemisimple_of_projective (h : ∀ X : C, Projective X) : IsSemisimple C := by
  intro S hS
  have := h S.X₃
  exact ⟨hS.splittingOfProjective⟩

/-- An abelian category is semisimple if and only if every object is injective. -/
lemma isSemisimple_iff_injective : IsSemisimple C ↔ ∀ X : C, Injective X :=
  ⟨fun h ↦ h.injective, isSemisimple_of_injective⟩

/-- An abelian category is semisimple if and only if every object is projective. -/
lemma isSemisimple_iff_projective : IsSemisimple C ↔ ∀ X : C, Projective X :=
  ⟨fun h ↦ h.projective, isSemisimple_of_projective⟩

end CategoryTheory.Abelian
