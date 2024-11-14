/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Path
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Strict Segal simplicial sets

A simplicial set `X` satisfies the `StrictSegal` condition if for all `n`, the map
`X.spine n : X _[n] → X.Path n` is a bijection.

Examples of `StrictSegal` simplicial sets are given by nerves of categories.

TODO: Show that these are the only examples: that a `StrictSegal` simplicial set is isomorphic to
the nerve of its homotopy category.

`StrictSegal` simplicial sets have an important property of being 2-coskeletal which is proven
in `Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal`.
-/

universe v u

open CategoryTheory

open Simplicial SimplicialObject SimplexCategory

namespace SSet

variable (X : SSet.{u})

/-- A simplicial set `X` satisfies the strict Segal condition if its simplices are uniquely
determined by their spine. -/
class StrictSegal : Prop where
  segal : ∀ (n : ℕ), Function.Bijective (X.spine n)

/-- In the presence of the strict Segal condition, a path of length `n` extends to an `n`-simplex
whose spine is that path. -/
noncomputable def spineToSimplex {X : SSet.{u}} [StrictSegal X] {n : ℕ} : Path X n → X _[n] :=
  (Equiv.ofBijective _ (StrictSegal.segal n)).invFun


namespace StrictSegal
variable {X : SSet.{u}} [StrictSegal X] {n : ℕ}

@[simp]
theorem spine_spineToSimplex (f : Path X n) :
    X.spine n (spineToSimplex f) = f :=
  (Equiv.ofBijective _ (segal n)).right_inv f

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
noncomputable def spineToDiagonal (f : Path X n) : X _[1] := diagonal X (spineToSimplex f)

@[simp]
theorem spineToSimplex_interval (f : Path X n) (j l : ℕ) (hjl : j + l ≤  n)  :
    X.map (subinterval j l hjl).op (spineToSimplex f) =
      spineToSimplex (Path.interval f j l hjl) := by
  apply (segal _).injective
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

end StrictSegal

end SSet

namespace Nerve

open SSet

variable {C : Type*} [Category C] {n : ℕ}

/-- Simplices in the nerve of categories are uniquely determined by their spine. Indeed, this
property describes the essential image of the nerve functor.-/
instance strictSegal (C : Type u) [Category.{v} C] : StrictSegal (nerve C) where
  segal n := by
    constructor
    · intro Δ Δ' h
      exact ComposableArrows.ext
        (fun i ↦ Functor.congr_obj (congr_fun (congr_arg Path.vertex h) i) 0)
        (fun i hi ↦
          Functor.congr_hom (congr_fun (congr_arg Path.arrow h) ⟨i, hi⟩) (show 0 ⟶ 1 by tauto))
    · intro F
      refine ⟨ComposableArrows.mkOfObjOfMapSucc (fun i ↦ (F.vertex i).obj 0)
        (fun i ↦ eqToHom (Functor.congr_obj (F.arrow_src i).symm 0) ≫
          (F.arrow i).map' 0 1 ≫ eqToHom (Functor.congr_obj (F.arrow_tgt i) 0)), ?_⟩
      ext i
      · exact ComposableArrows.ext₀ rfl
      · refine ComposableArrows.ext₁ ?_ ?_ ?_
        · exact Functor.congr_obj (F.arrow_src i).symm 0
        · exact Functor.congr_obj (F.arrow_tgt i).symm 0
        · dsimp
          apply ComposableArrows.mkOfObjOfMapSucc_map_succ

end Nerve
