/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.SimplicialHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism

/-!
# Simplicial homotopies

-/

open CategoryTheory SimplicialObject MonoidalCategory Simplicial Opposite

universe u

namespace SSet

-- to be moved
namespace stdSimplex

@[simp]
lemma δ_objEquiv_symm_apply
    {n : ℕ} {m : SimplexCategory} (f : .mk (n + 1) ⟶ m) (i : Fin (n + 2)) :
    (stdSimplex.obj _).δ i (objEquiv.symm f) =
      (objEquiv (n := m) (m := (op ⦋n⦌))).symm (SimplexCategory.δ i ≫ f) := by
  rfl

@[simp]
lemma σ_objEquiv_symm_apply
    {n : ℕ} {m : SimplexCategory} (f : .mk n ⟶ m) (i : Fin (n + 1)) :
    (stdSimplex.obj _).σ i (objEquiv.symm f) =
      objEquiv.symm (SimplexCategory.σ i ≫ f) := by
  rfl

lemma yonedaEquiv_symm_app_objEquiv_symm {X : SSet.{u}} {n : SimplexCategory}
    (x : X.obj (op n)) {m : SimplexCategoryᵒᵖ} (f : unop m ⟶ n) :
    (yonedaEquiv.symm x).app _ (stdSimplex.objEquiv.symm f) =
      X.map f.op x :=
  rfl

end stdSimplex

variable {X Y : SSet.{u}}

namespace RelativeMorphism

@[simps]
def botEquiv :
    RelativeMorphism (⊥ : X.Subcomplex) (⊥ : Y.Subcomplex)
      (Subcomplex.isInitialBot.to _) ≃ (X ⟶ Y) where
  toFun f := f.map
  invFun f := { map := f }

end RelativeMorphism

/-- The type of homotopies between morphisms `X ⟶ Y` of simplicial sets.
The data consists of a morphism `h : X ⊗ Δ[1] ⟶ Y`. -/
def Homotopy (f g : X ⟶ Y) : Type u :=
  (RelativeMorphism.botEquiv.symm f).Homotopy (RelativeMorphism.botEquiv.symm g)

namespace Homotopy

variable {f g : X ⟶ Y}

section

variable (h : Homotopy f g)

@[reassoc (attr := simp)]
lemma h₀ : ι₀ ≫ h.h = f :=
  RelativeMorphism.Homotopy.h₀ h

@[reassoc (attr := simp)]
lemma h₁ : ι₁ ≫ h.h = g :=
  RelativeMorphism.Homotopy.h₁ h

end

namespace toSimplicialHomotopy

variable (H : Homotopy f g)

noncomputable def h {n : ℕ} (i : Fin (n + 1)) (x : X _⦋n⦌) : Y _⦋n + 1⦌ :=
  (yonedaEquiv.symm x ▷ Δ[1] ≫ H.h).app _ (prodStdSimplex.nonDegenerateEquiv₁ i).1
-- Which one of `prodStdSimplex.nonDegenerateEquiv₁ i` or
-- `prodStdSimplex.nonDegenerateEquiv₁ i.rev` will work?

end toSimplicialHomotopy

open toSimplicialHomotopy in
noncomputable def toSimplicialHomotopy (H : Homotopy f g) :
    SimplicialHomotopy g f where
  h := h H
  h_zero_comp_δ_zero n := by
    ext x
    simp only [types_comp_apply, h, ← SSet.δ_naturality_apply, ← H.h₁]
    dsimp
    apply congr_arg
    ext i : 2
    · have := SimplexCategory.δ_comp_σ_self (i := (0 : Fin (n + 1)))
      dsimp at this ⊢
      rw [stdSimplex.δ_objEquiv_symm_apply, this,
        stdSimplex.yonedaEquiv_symm_app_objEquiv_symm,
        op_id, FunctorToTypes.map_id_apply]
    · rw [stdSimplex.δ_objMk₁_of_lt _ _ (by tauto)]
      rfl
  h_last_comp_δ_last n := by
    ext x
    simp only [types_comp_apply, h, ← SSet.δ_naturality_apply, ← H.h₀]
    dsimp
    apply congr_arg
    ext i
    · simp
      sorry
    · simp
      sorry
  h_succ_comp_δ_castSucc_of_lt := sorry
  h_succ_comp_δ_castSucc_succ := sorry
  h_castSucc_comp_δ_succ_of_lt := sorry
  h_comp_σ_castSucc_of_le := sorry
  h_comp_σ_succ_of_lt := sorry

end Homotopy

end SSet
