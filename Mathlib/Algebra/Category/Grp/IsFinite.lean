/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.Data.Finite.Prod

/-!
# The Serre class of finite abelian groups

In this file, we define `isFinite : ObjectProperty AddCommGrpCat` and show
that it is a Serre class.

-/

universe u

open CategoryTheory Limits ZeroObject

namespace AddCommGrpCat

/-- The Serre class of finite abelian groups
in the category of abelian groups. -/
def isFinite : ObjectProperty AddCommGrpCat.{u} :=
  fun M ↦ Finite M

@[simp]
lemma prop_isFinite_iff (M : AddCommGrpCat.{u}) : isFinite M ↔ Finite M := Iff.rfl

instance : isFinite.{u}.IsSerreClass where
  exists_zero := ⟨.of PUnit, isZero_of_subsingleton _,
    by rw [prop_isFinite_iff]; infer_instance⟩
  prop_of_mono {M N} f hf hN := by
    rw [AddCommGrpCat.mono_iff_injective] at hf
    simp only [prop_isFinite_iff] at hN ⊢
    exact Finite.of_injective _ hf
  prop_of_epi {M N} f hf hM := by
    rw [AddCommGrpCat.epi_iff_surjective] at hf
    simp only [prop_isFinite_iff] at hM ⊢
    exact Finite.of_surjective _ hf
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    simp only [prop_isFinite_iff] at h₁ h₃ ⊢
    have hg := hS.epi_g
    rw [AddCommGrpCat.epi_iff_surjective] at hg
    obtain ⟨s, hs⟩ := hg.hasRightInverse
    have hφ : Function.Surjective (fun (x₁, x₃) ↦ S.f x₁ + s x₃) := fun x₂ ↦ by
      obtain ⟨x₁, hx₁⟩ := (ShortComplex.ab_exact_iff S).1 hS.exact (x₂ - s (S.g x₂))
        (by simp [hs (S.g x₂)])
      exact ⟨⟨x₁, S.g x₂⟩, by simp [hx₁]⟩
    exact Finite.of_surjective _ hφ

end AddCommGrpCat
