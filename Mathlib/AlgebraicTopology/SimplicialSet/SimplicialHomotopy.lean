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

@[expose] public section

open CategoryTheory SimplicialObject MonoidalCategory Simplicial Opposite

universe u

namespace SSet

-- to be moved
namespace stdSimplex

@[simp]
lemma δ_objEquiv_symm_apply
    {n : ℕ} {m : SimplexCategory} (f : .mk (n + 1) ⟶ m) (i : Fin (n + 2)) :
    (stdSimplex.obj _).δ i (objEquiv.symm f) =
      (objEquiv (n := m) (m := op ⦋n⦌)).symm (SimplexCategory.δ i ≫ f) := by
  rfl

@[simp]
lemma σ_objEquiv_symm_apply
    {n : ℕ} {m : SimplexCategory} (f : .mk n ⟶ m) (i : Fin (n + 1)) :
    (stdSimplex.obj _).σ i (objEquiv.symm f) =
      (objEquiv (n := m) (m := op ⦋n + 1⦌)).symm (SimplexCategory.σ i ≫ f) := by
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

noncomputable def toSimplicialHomotopy (H : Homotopy f g) :
    SimplicialHomotopy f g where
  h {n} i x := (yonedaEquiv.symm x ▷ Δ[1] ≫ H.h).app _ (prodStdSimplex.nonDegenerateEquiv₁ i).1
  h_zero_comp_δ_zero n := by
    ext x
    simp only [types_comp_apply, ← SSet.δ_naturality_apply, ← H.h₁]
    dsimp
    apply congr_arg
    ext k : 2
    · have := SimplexCategory.δ_comp_σ_self (i := (0 : Fin (n + 1)))
      dsimp at this ⊢
      rw [stdSimplex.δ_objEquiv_symm_apply, this, stdSimplex.yonedaEquiv_symm_app_objEquiv_symm,
        op_id, FunctorToTypes.map_id_apply]
    · rw [stdSimplex.δ_objMk₁_of_lt _ _ (by tauto)]
      rfl
  h_last_comp_δ_last n := by
    ext x
    simp only [types_comp_apply, ← SSet.δ_naturality_apply, ← H.h₀]
    dsimp
    apply congr_arg
    ext k
    · dsimp
      have := SimplexCategory.δ_comp_σ_succ (i := Fin.last n)
      dsimp at this
      rw [stdSimplex.δ_objEquiv_symm_apply, this, stdSimplex.yonedaEquiv_symm_app_objEquiv_symm,
        op_id, FunctorToTypes.map_id_apply]
    · change _ = 0
      rw [stdSimplex.δ_objMk₁_of_le _ _ (by simp)]
      simp [stdSimplex.objMk₁_apply_eq_zero_iff]
  h_succ_comp_δ_castSucc_of_lt {n} i j hij := by
    ext x
    simp only [types_comp_apply, ← SSet.δ_naturality_apply]
    dsimp
    apply congr_arg
    ext k : 2
    · dsimp
      rw [stdSimplex.δ_objEquiv_symm_apply,
        stdSimplex.yonedaEquiv_symm_app_objEquiv_symm,
        stdSimplex.yonedaEquiv_symm_app_objEquiv_symm]
      erw [← FunctorToTypes.map_comp_apply]
      rw [← op_comp, SimplexCategory.δ_comp_σ_of_le hij, op_comp]
    · dsimp
      rw [stdSimplex.δ_objMk₁_of_lt, Fin.pred_succ]
      rw [Fin.castSucc_lt_succ_iff, ← Fin.castSucc_succ]
      simp only [Fin.castSucc_le_castSucc_iff]
      exact hij.trans (j.castSucc_le_succ)
  h_succ_comp_δ_castSucc_succ {n} i := by
    ext x
    simp only [types_comp_apply, ← SSet.δ_naturality_apply]
    dsimp
    apply congr_arg
    ext k : 2
    · dsimp
      rw [stdSimplex.δ_objEquiv_symm_apply, stdSimplex.yonedaEquiv_symm_app_objEquiv_symm,
        stdSimplex.δ_objEquiv_symm_apply, stdSimplex.yonedaEquiv_symm_app_objEquiv_symm,
        SimplexCategory.δ_comp_σ_succ (i := i.castSucc), ← Fin.castSucc_succ,
        SimplexCategory.δ_comp_σ_self (i := i.succ)]
    · dsimp
      rw [stdSimplex.δ_objMk₁_of_lt _ _ (by simp), stdSimplex.δ_objMk₁_of_le _ _ (by simp)]
      aesop
  h_castSucc_comp_δ_succ_of_lt {n} i j hij := by
    ext x
    simp only [types_comp_apply, ← SSet.δ_naturality_apply]
    dsimp
    apply congr_arg
    ext k : 2
    · dsimp
      rw [stdSimplex.δ_objEquiv_symm_apply, stdSimplex.yonedaEquiv_symm_app_objEquiv_symm,
        stdSimplex.yonedaEquiv_symm_app_objEquiv_symm]
      erw [← FunctorToTypes.map_comp_apply]
      rw [← op_comp, SimplexCategory.δ_comp_σ_of_gt hij, op_comp]
    · dsimp
      rw [stdSimplex.δ_objMk₁_of_le _ _ (by simpa using Fin.le_of_lt hij)]
      rfl
  h_comp_σ_castSucc_of_le {n} i j hij := by
    ext x
    simp only [types_comp_apply, ← SSet.σ_naturality_apply]
    dsimp
    apply congr_arg
    ext k : 2
    · dsimp
      rw [stdSimplex.σ_objEquiv_symm_apply, stdSimplex.yonedaEquiv_symm_app_objEquiv_symm,
        stdSimplex.yonedaEquiv_symm_app_objEquiv_symm]
      erw [← FunctorToTypes.map_comp_apply]
      rw [← op_comp, SimplexCategory.σ_comp_σ hij]
    · dsimp
      rw [stdSimplex.σ_objMk₁_of_lt _ _ (by simpa)]
  h_comp_σ_succ_of_lt {n} i j hij := by
    ext x
    simp only [types_comp_apply, ← SSet.σ_naturality_apply]
    dsimp
    apply congr_arg
    ext k : 2
    · dsimp
      rw [stdSimplex.σ_objEquiv_symm_apply, stdSimplex.yonedaEquiv_symm_app_objEquiv_symm,
        stdSimplex.yonedaEquiv_symm_app_objEquiv_symm]
      erw [← FunctorToTypes.map_comp_apply]
      rw [← op_comp, SimplexCategory.σ_comp_σ hij]
    · dsimp
      rw [stdSimplex.σ_objMk₁_of_le _ _ (by simpa)]
      rfl

end Homotopy

end SSet
