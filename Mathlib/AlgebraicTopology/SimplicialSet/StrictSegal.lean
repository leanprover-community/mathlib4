/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Path
import Mathlib.AlgebraicTopology.SimplicialSet.Quasicategory
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Strict Segal simplicial sets

A simplicial set `X` satisfies the `StrictSegal` condition if for all `n`, the map
`X.spine n : X _[n] → X.Path n` is an equivalence, with equivalence inverse
`spineToSimplex {n : ℕ} : Path X n → X _[n]`.

Examples of `StrictSegal` simplicial sets are given by nerves of categories.

TODO: Show that these are the only examples: that a `StrictSegal` simplicial set is isomorphic to
the nerve of its homotopy category.
-/

universe v u

open CategoryTheory

open Simplicial SimplicialObject SimplexCategory

namespace SSet

variable (X : SSet.{u})

/-- A simplicial set `X` satisfies the strict Segal condition if its simplices are uniquely
determined by their spine. -/
class StrictSegal where
  /-- The inverse to `X.spine n`.-/
  spineToSimplex {n : ℕ} : Path X n → X _[n]
  /-- `spineToSimplex` is a right inverse to `X.spine n`.-/
  spine_spineToSimplex {n : ℕ} (f : Path X n) : X.spine n (spineToSimplex f) = f
  /-- `spineToSimplex` is a left inverse to `X.spine n`.-/
  spineToSimplex_spine {n : ℕ} (Δ : X _[n]) : spineToSimplex (X.spine n Δ) = Δ

namespace StrictSegal
variable {X : SSet.{u}} [StrictSegal X] {n : ℕ}

/-- The fields of `StrictSegal` define an equivalence between `X _[n]` and `Path X n`.-/
def spineEquiv (n : ℕ) : X _[n] ≃ Path X n where
  toFun := spine X n
  invFun := spineToSimplex
  left_inv := spineToSimplex_spine
  right_inv := spine_spineToSimplex

theorem spineInjective {n : ℕ} : Function.Injective (spineEquiv (X := X) n) := Equiv.injective _

@[simp]
theorem spineToSimplex_vertex (i : Fin (n + 1)) (f : Path X n) :
    X.map (const [0] [n] i).op (spineToSimplex f) = f.vertex i := by
  rw [← spine_vertex, spine_spineToSimplex]

@[simp]
theorem spineToSimplex_arrow (i : Fin n) (f : Path X n) :
    X.map (mkOfSucc i).op (spineToSimplex f) = f.arrow i := by
  rw [← spine_arrow, spine_spineToSimplex]

/-- In the presence of the strict Segal condition, a path of length `n` can be "composed" by taking
the diagonal edge of the resulting `n`-simplex. -/
def spineToDiagonal (f : Path X n) : X _[1] := diagonal X (spineToSimplex f)

@[simp]
theorem spineToSimplex_interval (f : Path X n) (j l : ℕ) (hjl : j + l ≤  n)  :
    X.map (subinterval j l hjl).op (spineToSimplex f) =
      spineToSimplex (Path.interval f j l hjl) := by
  apply spineInjective
  unfold spineEquiv
  dsimp
  rw [spine_spineToSimplex]
  convert spine_map_subinterval X j l hjl (spineToSimplex f)
  exact Eq.symm (spine_spineToSimplex f)

theorem spineToSimplex_edge (f : Path X n) (j l : ℕ) (hjl : j + l ≤ n) :
    X.map (intervalEdge j l hjl).op (spineToSimplex f) =
      spineToDiagonal (Path.interval f j l hjl) := by
  unfold spineToDiagonal
  rw [← congrArg (diagonal X) (spineToSimplex_interval f j l hjl)]
  unfold diagonal
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp, diag_subinterval_eq]

/-- If we take the path along the spine of a face of a `spineToSimplex`, the
common vertices will still agree with those of the original path. -/
lemma spine_face_lt (f : Path X (n + 1)) (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : j.castSucc < i) :
    (X.spine n (X.δ i (spineToSimplex f))).vertex j = f.vertex j := by
  simp [SimplicialObject.δ]
  simp [← FunctorToTypes.map_comp_apply, ← op_comp]
  simp [Hom.toOrderHom, SimplexCategory.δ, Hom.mk]
  rw [Fin.succAbove_of_castSucc_lt]
  exact h

/-- If we take the path along the spine of a face of a `spineToSimplex`, the
common vertices will still agree with those of the original path. -/
lemma spine_face_ge (f : Path X (n + 1)) (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : i ≤ j.castSucc) :
    (X.spine n (X.δ i (spineToSimplex f))).vertex j = f.vertex j.succ := by
  simp [SimplicialObject.δ]
  simp [← FunctorToTypes.map_comp_apply, ← op_comp]
  simp [Hom.toOrderHom, SimplexCategory.δ, Hom.mk]
  rw [Fin.succAbove_of_le_castSucc]
  exact h

/-- If `i + 1 = j`, `mkOfSucc i ≫ δ j` is a composition of two arrows and
therefore not in the image of `mkOfSucc`. -/
lemma mkOfSucc_δ_lt {n : ℕ} {i : Fin n} {j : Fin (n + 2)}
    (h : i.succ.castSucc < j) :
    mkOfSucc i ≫ SimplexCategory.δ j = mkOfSucc i.castSucc := by
  ext x
  simp [SimplexCategory.δ]
  fin_cases x
  · simp
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · refine Nat.lt_trans ?_ h
      simp
  · simp
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · exact h

/-- If `i + 1 = j`, `mkOfSucc i ≫ δ j` is a composition of two arrows and
therefore not in the image of `mkOfSucc`. -/
lemma mkOfSucc_δ_gt {n : ℕ} {i : Fin n} {j : Fin (n + 2)}
    (h : j < i.succ.castSucc) :
    mkOfSucc i ≫ SimplexCategory.δ j = mkOfSucc i.succ := by
  ext x
  simp [SimplexCategory.δ]
  fin_cases x
  · simp
    rw [Fin.succAbove_of_le_castSucc]
    · rfl
    · exact Nat.le_of_lt_succ h
  · simp
    rw [Fin.succAbove_of_le_castSucc]
    · rfl
    · exact Nat.le_of_lt h

lemma mkOfSucc_δ_eq {n : ℕ} {i : Fin n} {j : Fin (n + 2)}
    (h : j = i.succ.castSucc) :
    mkOfSucc i ≫ SimplexCategory.δ j = intervalEdge i 2 (by omega) := by
  ext x
  simp [SimplexCategory.δ]
  fin_cases x
  · simp
    rw [Fin.succAbove_of_castSucc_lt]
    · simp
      simp [Hom.toOrderHom, intervalEdge, mkOfLe, Hom.mk]
    · rw [h]
      simp
  · simp
    rw [h]
    rw [Fin.succAbove_castSucc_self]
    simp [Hom.toOrderHom, intervalEdge, mkOfLe, Hom.mk, mkHom, ]

lemma spine_face_arrow_lt (f : Path X (n + 1)) (i : Fin (n + 2)) (j : Fin n)
    (h : j.succ.castSucc < i) :
    (X.spine n (X.δ i (spineToSimplex f))).arrow j = f.arrow j := by
  simp [SimplicialObject.δ]
  simp [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_lt h]
  rw [spineToSimplex_arrow]

lemma spine_face_arrow_gt (f : Path X (n + 1)) (i : Fin (n + 2)) (j : Fin n)
    (h : i < j.succ.castSucc) :
    (X.spine n (X.δ i (spineToSimplex f))).arrow j = f.arrow j.succ := by
  simp [SimplicialObject.δ]
  simp [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_gt h]
  rw [spineToSimplex_arrow]

lemma spine_face_arrow_eq (f : Path X (n + 1)) (i : Fin (n + 2)) (j : Fin n)
    (h : i = j.succ.castSucc) :
    (X.spine n (X.δ i (spineToSimplex f))).arrow j
      = spineToDiagonal (Path.interval f j 2 (by omega)) := by
  simp [SimplicialObject.δ]
  simp [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_eq h]
  rw [spineToSimplex_edge]

/- set_option pp.coercions false -/
open Opposite in
instance : Quasicategory X := by
  apply quasicategory_of_filler X
  intro n i σ₀ h₀ hₙ
  exists spineToSimplex ∘ mapPath σ₀ <| spineHorn n i h₀ hₙ
  intro j hj
  apply spineInjective
  ext k
  · simp only [spineEquiv, Function.comp_apply, Equiv.coe_fn_mk]
    have hkj : k.castSucc < j ∨ j ≤ k.castSucc := Nat.lt_or_ge k j
    rcases hkj with hcmp | hcmp
    · rw [spine_face_lt _ _ _ hcmp]
      simp only [mapPath, spine_vertex, Fin.coe_eq_castSucc]
      rw [← types_comp_apply (σ₀.app _) (X.map _)]
      rw [← σ₀.naturality]
      /- apply congr_arg -/
      /- simp [spineHorn, idSpine, horn, standardSimplex.idSimplex_objEquiv] -/
      /- simp [Hom.mk, standardSimplex.objEquiv, Equiv.ulift] -/
      /- simp [SimplexCategory.δ, Hom.mk] -/
      rw [← Fin.succAbove_of_castSucc_lt j k hcmp]
      rfl
    · rw [spine_face_ge _ _ _ hcmp]
      simp only [mapPath, spine_vertex, Fin.coe_eq_castSucc]
      rw [← types_comp_apply (σ₀.app _) (X.map _)]
      rw [← σ₀.naturality]
      rw [← Fin.succAbove_of_le_castSucc j k hcmp]
      rfl
  · simp only [spineEquiv, Function.comp_apply, Equiv.coe_fn_mk]
    have hkj : k.succ.castSucc < j ∨ j < k.succ.castSucc ∨ j = k.succ.castSucc := by omega
    rcases hkj with hcmp | hcmp | heq
    · rw [spine_face_arrow_lt _ _ _ hcmp]
      simp only [mapPath, spine_arrow, Fin.coe_eq_castSucc]
      rw [← types_comp_apply (σ₀.app _) (X.map _)]
      rw [← σ₀.naturality]
      apply congr_arg
      simp [spineHorn, idSpine, horn, standardSimplex.idSimplex_objEquiv]
      simp [Hom.mk, standardSimplex.objEquiv, Equiv.ulift]
      simp [standardSimplex, uliftFunctor]
      rw [mkOfSucc_δ_lt hcmp]
      rfl
    · rw [spine_face_arrow_gt _ _ _ hcmp]
      simp only [mapPath, spine_arrow, Fin.coe_eq_castSucc]
      rw [← types_comp_apply (σ₀.app _) (X.map _)]
      rw [← σ₀.naturality]
      apply congr_arg
      simp [spineHorn, idSpine, horn, standardSimplex.idSimplex_objEquiv]
      simp [Hom.mk, standardSimplex.objEquiv, Equiv.ulift]
      simp [standardSimplex, uliftFunctor]
      rw [mkOfSucc_δ_gt hcmp]
      rfl
    · rw [spine_face_arrow_eq _ _ _ heq]
      simp [spineToDiagonal, spine_arrow, Fin.coe_eq_castSucc, diagonal]
      rw [← spineToSimplex_interval]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      rw [diag_subinterval_eq]
      simp [horn.face, standardSimplex.objEquiv, Equiv.ulift]

      rw [← types_comp_apply (σ₀.app _) (X.map _)]
      rw [← σ₀.naturality]
      simp [horn, standardSimplex.idSimplex_objEquiv]

      simp [standardSimplex.objEquiv, Equiv.ulift, standardSimplex, uliftFunctor]
      rw [← mkOfSucc_δ_eq heq]
      /- simp [mapPath, spineHorn, idSpine, standardSimplex.idSimplex, yonedaEquiv, yonedaCompUliftFunctorEquiv] -/
      /- conv => -/ 
      /-   rhs -/
      /-   congr -/
      /-   rfl -/
      /-   left -/
      /-   rw [mkOfSucc_δ_eq heq] -/
      sorry

end StrictSegal

end SSet

namespace Nerve

open SSet

variable {C : Type*} [Category C] {n : ℕ}

/-- Simplices in the nerve of categories are uniquely determined by their spine. Indeed, this
property describes the essential image of the nerve functor.-/
noncomputable instance strictSegal (C : Type u) [Category.{v} C] : StrictSegal (nerve C) where
  spineToSimplex {n} F :=
    ComposableArrows.mkOfObjOfMapSucc (fun i ↦ (F.vertex i).obj 0)
      (fun i ↦ eqToHom (Functor.congr_obj (F.arrow_src i).symm 0) ≫
        (F.arrow i).map' 0 1 ≫ eqToHom (Functor.congr_obj (F.arrow_tgt i) 0))
  spine_spineToSimplex {n} F := by
    ext i
    · exact ComposableArrows.ext₀ rfl
    · refine ComposableArrows.ext₁ ?_ ?_ ?_
      · exact Functor.congr_obj (F.arrow_src i).symm 0
      · exact Functor.congr_obj (F.arrow_tgt i).symm 0
      · dsimp
        apply ComposableArrows.mkOfObjOfMapSucc_map_succ
  spineToSimplex_spine {n} F := by
    fapply ComposableArrows.ext
    · intro i
      rfl
    · intro i hi
      apply ComposableArrows.mkOfObjOfMapSucc_map_succ

instance : Quasicategory (nerve C) := inferInstance

end Nerve
