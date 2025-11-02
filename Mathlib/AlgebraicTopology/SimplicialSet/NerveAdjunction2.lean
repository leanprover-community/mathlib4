/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Presheaf

/-!

-/

universe u

open CategoryTheory Nerve Simplicial SimplicialObject.Truncated
  SimplexCategory.Truncated

namespace SSet

namespace Truncated

def Path.mk₂ {n : ℕ} {X : Truncated.{u} (n + 1)} (p q : X.Path 1)
    (h : p.vertex 1 = q.vertex 0) : X.Path 2 := sorry

section

variable {n : ℕ} {X Y : Truncated.{u} 2} (f₀ : X _⦋0⦌₂ → Y _⦋0⦌₂) (f₁ : X _⦋1⦌₂ → Y _⦋1⦌₂)
  (hδ₁ : ∀ (x : X _⦋1⦌₂), f₀ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op (f₁ x))
  (hδ₀ : ∀ (x : X _⦋1⦌₂), f₀ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op (f₁ x))
  (hσ : ∀ (x : X _⦋0⦌₂), f₁ (X.map (σ₂ 0).op x) = Y.map (σ₂ 0).op (f₀ x))
  (hY : Y.StrictSegal)

namespace liftOfIsStrictSegal

def app {n : (SimplexCategory.Truncated 2)ᵒᵖ} : X.obj n ⟶ Y.obj n := by
  obtain ⟨n, hn⟩ := n
  induction n using SimplexCategory.rec with | _ n
  match n with
  | 0 => exact f₀
  | 1 => exact f₁
  | 2 => exact fun x ↦ (hY.spineEquiv 2).symm
          (.mk₂ (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 2).op x)))
            (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 0).op x))) (by
              simp only [spine_vertex]
              rw [← δ₂_one_eq_const, ← δ₂_zero_eq_const, ← hδ₁, ← hδ₀]
              simp only [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_zero_comp_δ₂_two]))

end liftOfIsStrictSegal

def liftOfIsStrictSegal : X ⟶ Y := by
  have := f₀
  have := f₁
  have := hδ₁
  have := hδ₀
  have := hσ
  have := hY
  sorry

end

namespace HomotopyCategory

variable {X : Truncated.{u} 2} {C : Type u} [SmallCategory C]

def functorOfTruncation (φ : (X ⟶ (truncation 2).obj (nerve C))) :
    X.HomotopyCategory ⥤ C := by
  refine lift (fun x ↦ nerveEquiv (φ.app _ x)) (fun x y e ↦ nerveHomEquiv (e.map φ)) ?_ ?_
  · sorry
  · sorry

def functorEquiv :
    (X.HomotopyCategory ⥤ C) ≃ (X ⟶ (truncation 2).obj (nerve C)) where
  toFun F :=
    liftOfIsStrictSegal (fun x ↦ nerveEquiv.symm (F.obj (mk x))) (by
      sorry) sorry sorry sorry sorry
  invFun φ := functorOfTruncation φ
  left_inv := sorry
  right_inv := sorry

end HomotopyCategory

/-- The adjunction between the 2-truncated nerve functor and the 2-truncated homotopy category
functor. -/
def nerve₂Adj : hoFunctor₂.{u} ⊣ nerveFunctor₂ :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := HomotopyCategory.functorEquiv
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }


end Truncated

end SSet
