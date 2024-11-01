/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Module.Presentation.Cokernel
import Mathlib.Algebra.Module.Presentation.ExteriorProduct
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The algebraic De Rham complex

-/

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

open ExteriorAlgebra

namespace DeRhamComplex

variable (n : ℕ)

def presentation : Module.Presentation B (exteriorPower B n (KaehlerDifferential A B)) := sorry

def d (n : ℕ) : exteriorPower B n (KaehlerDifferential A B) →ₗ[A]
  exteriorPower B (n + 1) (KaehlerDifferential A B) := sorry

@[simp]
lemma d_d (n : ℕ) : d A B (n + 1) ∘ d A B n = 0 := sorry

@[simp]
lemma d_d_apply {n : ℕ} (x) : d A B (n + 1) (d A B n x) = 0 := congr_fun (d_d A B n) x

end DeRhamComplex

noncomputable def deRhamComplex : CochainComplex (ModuleCat A) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of A (exteriorPower B n (KaehlerDifferential A B)))
    (DeRhamComplex.d A B) (by intro; ext; apply DeRhamComplex.d_d_apply)
