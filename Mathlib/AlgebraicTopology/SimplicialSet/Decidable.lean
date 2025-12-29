/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.CodiscreteCategory

/-!
# Decidable instances

-/

universe v u

namespace CategoryTheory

def Arrow.decidableEq
    (C : Type u) [Category.{v} C] [DecidableEq C] [∀ (X Y : C), DecidableEq (X ⟶ Y)] :
    DecidableEq (Arrow C) :=
  fun _ _ ↦ decidable_of_iff _ (Arrow.mk_eq_mk_iff _ _).symm

instance (C : Type u) {X Y : Codiscrete C} : Subsingleton (X ⟶ Y) where
  allEq _ _ := rfl

instance (C : Type u) [DecidableEq C] : DecidableEq (Arrow (Codiscrete C)) :=
  Arrow.decidableEq _

instance {C : Type u} [Category.{v} C] [DecidableEq (Arrow C)] (n : ℕ) :
    DecidableEq (ComposableArrows C n) := by
  intro D₁ D₂
  induction n with
  | zero =>
    have : D₁ = D₂ ↔ (Arrow.mk (𝟙 (D₁.obj 0)) = Arrow.mk ((𝟙 (D₂.obj 0)))) :=
      ⟨by rintro rfl; rfl, fun h ↦ ComposableArrows.ext₀ (congr_arg Arrow.leftFunc.obj h)⟩
    exact decidable_of_iff _ this.symm
  | succ n hn =>
    have : D₁ = D₂ ↔ Arrow.mk (D₁.map' 0 1) = Arrow.mk (D₂.map' 0 1) ∧ D₁.δ₀ = D₂.δ₀ :=
      ⟨by rintro rfl; tauto, fun ⟨h₁, h₂⟩ ↦ by
        rw [Arrow.mk_eq_mk_iff] at h₁
        obtain ⟨h₀, _, h⟩ := h₁
        exact ComposableArrows.ext_succ h₀ h₂ h⟩
    exact decidable_of_iff _ this.symm

end CategoryTheory

open CategoryTheory

namespace SSet

open Simplicial

instance {C : Type u} [Category.{v} C] [DecidableEq (Arrow C)] (n : SimplexCategoryᵒᵖ) :
    DecidableEq ((nerve C).obj n) :=
      inferInstanceAs (DecidableEq (ComposableArrows C _))

example {C : Type u} [Category.{v} C] [DecidableEq (Arrow C)] (n : ℕ) :
    DecidableEq (Δ[n] ⟶ nerve C) :=
  inferInstance

example : DecidableEq (Δ[1] ⟶ nerve (Codiscrete (Fin 2))) := inferInstance

abbrev coherentIso := nerve (Codiscrete (Fin 2))

noncomputable def coherentIso.hom : Δ[1] ⟶ coherentIso :=
  yonedaEquiv.symm (ComposableArrows.mk₁ (X₀ := ⟨0⟩) (X₁ := ⟨1⟩) ⟨⟩)

example : stdSimplex.δ 0 ≫ coherentIso.hom = SSet.const (ComposableArrows.mk₀ ⟨1⟩) := by
  decide

end SSet
