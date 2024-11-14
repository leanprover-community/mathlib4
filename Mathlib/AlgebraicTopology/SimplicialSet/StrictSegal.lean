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

open Simplicial SimplexCategory

namespace SSet

variable (X : SSet.{u})

/-- A simplicial set `X` satisfies the strict Segal condition if its simplices are uniquely
determined by their spine. -/
class StrictSegal : Prop where
  segal : ∀ (n : ℕ), Function.Bijective (X.spine n)

variable {X} in
/-- The diagonal of a simplex is the long edge of the simplex.-/
def diagonal {n : ℕ} (Δ : X _[n]) : X _[1] := X.map ((diag n).op) Δ

namespace StrictSegal
variable {X : SSet.{u}} [StrictSegal X] {n : ℕ}

/-- In the presence of the strict Segal condition, a path of length `n` extends to an `n`-simplex
whose spine is that path. -/
noncomputable def spineToSimplex : Path X n → X _[n] :=
  (Equiv.ofBijective _ (segal n)).invFun

@[simp]
theorem spineToSimplex_spine (f : Path X n) :
    X.spine n (StrictSegal.spineToSimplex f) = f :=
  (Equiv.ofBijective _ (segal n)).right_inv f

@[simp]
theorem spineToSimplex_vertex (i : Fin (n + 1)) (f : Path X n) :
    X.map (const [0] [n] i).op (spineToSimplex f) = f.vertex i := by
  rw [← spine_vertex, spineToSimplex_spine]

@[simp]
theorem spineToSimplex_spine_edge (i : Fin n) (f : Path X n) :
    X.map (mkOfSucc i).op (spineToSimplex f) = f.arrow i := by
  rw [← spine_arrow, spineToSimplex_spine]

/-- In the presence of the strict Segal condition, a path of length `n` can be "composed" by taking
the diagonal edge of the resulting `n`-simplex. -/
noncomputable def spineToDiagonal (f : Path X n) : X _[1] := diagonal (spineToSimplex f)

@[simp]
theorem spineToSimplex_interval (f : Path X n) (j l : ℕ) (hjl : j + l ≤  n)  :
    X.map (subinterval j l hjl).op (spineToSimplex f) =
      spineToSimplex (Path.interval f j l hjl) := by
  apply (segal _).injective
  rw [StrictSegal.spineToSimplex_spine]
  convert spine_map_subinterval X j l hjl (spineToSimplex f)
  exact Eq.symm (spineToSimplex_spine f)

@[simp]
theorem spineToSimplex_edge (f : Path X n) (j l : ℕ) (hn : j + l ≤ n) :
    X.map
      (mkOfLe ⟨j, (by omega)⟩ ⟨j + l, (by omega)⟩ (Nat.le_add_right j l)).op
      (spineToSimplex f) = spineToDiagonal (Path.interval f j l hn) := by
  unfold spineToDiagonal
  rw [← congrArg diagonal (spineToSimplex_interval f j l hn)]
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
