/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism

/-!
# Pointed simplices

Given a simplicial set `X`, `n : ℕ` and `x : X _⦋0⦌`, we introduce the
type `X.PtSimplex n x` of morphisms `Δ[n] ⟶ X` which send `∂Δ[n]` to `x`.
We introduce structures `PtSimplex.RelStruct` and `PtSimplex.MulStruct`
which will be used in the definition of homotopy groups of Kan complexes.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial
namespace SSet

variable (X : SSet.{u})

/-- Given a simplicial set `X`, `n : ℕ` and `x : X _⦋0⦌`, this is the type
of morphisms `Δ[n] ⟶ X` which are constant with value `x` on the boundary. -/
abbrev PtSimplex (n : ℕ) (x : X _⦋0⦌) : Type u :=
  RelativeMorphism (boundary n) (Subcomplex.ofSimplex x)
    (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

namespace PtSimplex

variable {X} {n : ℕ} {x : X _⦋0⦌}

/-- For each `i : Fin (n + 1)`, this is a variant of the homotopy relation on
`n`-simplices that are constant on the boundary. Simplices `f` and `g` are related
if they appear respectively as the `i.castSucc` and `i.succ` faces of a
`n + 1`-simplex such that all the other faces are constant. -/
structure RelStruct (f g : X.PtSimplex n x) (i : Fin (n + 1)) where
  /-- A `n + 1`-simplex -/
  map : Δ[n + 1] ⟶ X
  δ_castSucc_map : stdSimplex.δ i.castSucc ≫ map = f.map := by cat_disch
  δ_succ_map : stdSimplex.δ i.succ ≫ map = g.map := by cat_disch
  δ_map_of_lt (j : Fin (n + 2)) (hj : j < i.castSucc) :
    stdSimplex.δ j ≫ map = const x := by cat_disch
  δ_map_of_gt (j : Fin (n + 2)) (hj : i.succ < j) :
    stdSimplex.δ j ≫ map = const x := by cat_disch

namespace RelStruct

attribute [reassoc (attr := simp)] δ_castSucc_map δ_succ_map

end RelStruct

/-- For each `i : Fin n`, this structure is a candidate for the relation saying
that `fg` is the product of `f` and `g` in the homotopy group (of a Kan complex).
It is so if `g`, `fg` and `f` are respectively the `i.castSucc.castSucc`,
`i.castSucc.succ` and `i.succ.succ` faces of a `n + 1`-simplex such that
all the other faces are constant. (The multiplication on homotopy groups will be
defined using `i := Fin.last _`, but in general, this structure is useful in
order to obtain properties of `RelStruct`.) -/
structure MulStruct (f g fg : X.PtSimplex n x) (i : Fin n) where
  /-- A `n + 1`-simplex -/
  map : Δ[n + 1] ⟶ X
  δ_castSucc_castSucc_map : stdSimplex.δ (i.castSucc.castSucc) ≫ map = g.map := by cat_disch
  δ_succ_castSucc_map : stdSimplex.δ (i.castSucc.succ) ≫ map = fg.map := by cat_disch
  δ_succ_succ_map : stdSimplex.δ (i.succ.succ) ≫ map = f.map := by cat_disch
  δ_map_of_lt (j : Fin (n + 2)) (hj : j < i.castSucc.castSucc) :
    stdSimplex.δ j ≫ map = const x := by cat_disch
  δ_map_of_gt (j : Fin (n + 2)) (hj : i.succ.succ < j) :
    stdSimplex.δ j ≫ map = const x := by cat_disch

namespace MulStruct

attribute [reassoc (attr := simp)] δ_castSucc_castSucc_map δ_succ_castSucc_map δ_succ_succ_map

end MulStruct

end PtSimplex

end SSet
