/-
Copyright (c) 2025 Klaus Gy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Klaus Gy
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Topos.Classifier
/-!
# Elementary Topos (in Elementary Form)

This ongoing work formalizes the elementary definition of a topos and the direct consequences.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
-/


universe u v

open CategoryTheory Category Functor Limits MonoidalCategory Opposite

variable {ℰ : Type u} [Category.{v} ℰ] [CartesianMonoidalCategory ℰ]

def WhiskeredHom (B C : ℰ) : ℰᵒᵖ ⥤ Type v :=
  ⟨ ⟨ fun A ↦ B ⊗ unop A ⟶ C, fun f g ↦ (B ◁ unop f) ≫ g ⟩,
    fun A ↦ by
      have : unop (𝟙 A) = 𝟙 (unop A) := by rfl
      ext; simp[this],
    fun f f' ↦ by
      have : B ◁ unop (f ≫ f') = B ◁ unop f' ≫ B ◁ unop f := by aesop_cat
      ext; simp[this] ⟩

def IsPowerObjectOf (hc : Classifier ℰ (𝟙_ ℰ)) (B P : ℰ) :=
  RepresentableBy (WhiskeredHom B P) hc.Ω

variable (ℰ) [HasPullbacks ℰ]

structure ElementaryTopos extends Classifier ℰ (𝟙_ ℰ) where
  P (B : ℰ) : ℰ
  is_power_object (B : ℰ) : IsPowerObjectOf _ B (P B)
