/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

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

@[reassoc]
lemma comp_map_eq_const
    (s : X.PtSimplex n x) {Y : SSet.{u}} (φ : Y ⟶ Δ[n]) [Y.HasDimensionLT n] :
    φ ≫ s.map = const x := by
  refine (Subcomplex.lift φ ?_) ≫= s.comm
  rw [stdSimplex.le_boundary_iff]
  intro h
  have : IsIso (Subcomplex.range φ).ι := by rw [h]; infer_instance
  exact stdSimplex.not_hasDimensionLT n
    ((hasDimensionLT_iff_of_iso (asIso (Subcomplex.range φ).ι) n).mp inferInstance)

@[reassoc (attr := simp)]
lemma δ_map (f : X.PtSimplex (n + 1) x) (i : Fin (n + 2)) :
    stdSimplex.δ i ≫ f.map = const x :=
  comp_map_eq_const _ _

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

/-- `RelStruct` is reflexive. -/
@[simps]
def refl (f : X.PtSimplex n x) (i : Fin (n + 1)) : RelStruct f f i where
  map := stdSimplex.σ i ≫ f.map
  δ_castSucc_map := by rw [CosimplicialObject.δ_comp_σ_self_assoc]
  δ_succ_map := by rw [CosimplicialObject.δ_comp_σ_succ_assoc]
  δ_map_of_lt j hj := by
    obtain ⟨i, rfl⟩ := i.eq_succ_of_ne_zero (by aesop)
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (by grind)
    obtain _ | n := n
    · fin_cases i
    · rw [stdSimplex.δ_comp_σ_of_le_assoc (by grind), δ_map, comp_const]
  δ_map_of_gt j hj := by
    obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (by grind)
    obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (by aesop)
    obtain _ | n := n
    · fin_cases i
    · rw [stdSimplex.δ_comp_σ_of_gt_assoc (by grind), δ_map, comp_const]

/-- The `RelStruct f' g' i` deduced from `r : RelStruct f g i` when
`f = f'` and `g = g'`. -/
@[simps]
def copy {f g : X.PtSimplex n x} {i : Fin (n + 1)} (r : RelStruct f g i)
    {f' g' : X.PtSimplex n x} (hf : f = f') (hg : g = g') :
    RelStruct f' g' i where
  map := r.map
  δ_castSucc_map := by rw [δ_castSucc_map, hf]
  δ_succ_map := by rw [δ_succ_map, hg]
  δ_map_of_lt j hj := by rw [δ_map_of_lt _ j hj]
  δ_map_of_gt j hj := by rw [δ_map_of_gt _ j hj]

/-- The `RelStruct f g i` deduced from an equality `f = g`. -/
@[simps! map]
def ofEq {f g : X.PtSimplex n x} (h : f = g) (i : Fin (n + 1)) :
    RelStruct f g i :=
  (refl f i).copy rfl h

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
