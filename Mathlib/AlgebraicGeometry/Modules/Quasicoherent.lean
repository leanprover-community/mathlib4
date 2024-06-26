/-
Copyright (c) 2024 Nikolas Kuhn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Kuhn
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
--import Mathlib.Algebra.Category.ModuleCat.Basic
--import Mathlib.Algebra.Category.Ring.Basic

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Properties of quasi-coherent sheaves on schemes

In this file, we show basic properties of the category of the category of quasi-coherent
sheaves over a scheme `X`.
-/

universe v u

open CategoryTheory SheafOfModules ModuleCat Limits --Spec
--open CategoryTheory

variable (R: CommRingCat.{u}) (M: ModuleCat.{max u v} R)

#check ModuleCat.of R (M →₀ R) ⟶ M


namespace AlgebraicGeometry.Scheme

example (R : CommRingCat.{u}) : Type u := by
  exact (R : Type u)


/-- The quasi-coherent sheaf on `Spec R` associated to a module `M` over the ring `R`-/
def associated_sheaf (R : CommRingCat.{u}) (M : ModuleCat.{v} (R : Type u)) :  (Spec R).Modules :=
  sorry



variable (X : Scheme.{u})

--variable (M : X.Modules) [IsQuasicoherent M]

-- Move to Algebra.Category.ModuleCat.Presentation

variable (R: CommRingCat.{u}) (M: ModuleCat.{max u v} R)

#check  ModuleCat.of R (M →₀ R) ⟶ M

example (M : ModuleCat.{max u v} R) : Epi (Finsupp.total ↑M ↑M ↑R fun a ↦ a :(M →₀ R) →ₗ[R] (M)) := by
  exact

lemma has_presentation :
    ∃ (S : ShortComplex (ModuleCat.{max u v} R)) (h₁ : Module.Free R S.X₁) (h₂ : Module.Free R S.X₂)
    (hS : S.Exact) (hg: Epi S.g), (M = S.X₃)  := by
  let N₂ : ModuleCat.{max v u} R := ModuleCat.of R (M →₀ R)
  let g : (N₂ ⟶ M) := Finsupp.total ↑M ↑M ↑R fun a ↦ a

  sorry

variable (ι : Type v ) (i: ι → Type)
#check  Module R (ι →₀ R)

example (M : Type v) [AddCommMonoid M] [Module R M] : ModuleCat R := by
  sorry
