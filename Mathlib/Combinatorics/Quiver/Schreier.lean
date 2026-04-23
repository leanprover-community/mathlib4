/-
Copyright (c) 2026 Runtian Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Runtian Zhou
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Combinatorics.Quiver.Covering
public import Mathlib.Combinatorics.Quiver.SingleObj
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

/-!
# Schreier Graphs

This module defines Schreier graphs as quivers with labelled edges.

Given a monoid `M` acting on a type `V` and a map `ι : S → M`, the Schreier graph has
vertices `V` and a directed edge `x → ι(s) • x` for each `x : V` and `s : S`.

## Main definitions

* `SchreierGraph V ι` - The Schreier graph of an action, with vertices of type `V` and edges
  labelled by elements of `S` via `ι : S → M`.
* `SchreierGraph.labelling` - The prefunctor from a Schreier graph to `SingleObj S` that
  extracts edge labels.

## Main results

* `SchreierGraph.labelling_isCovering` - The labelling prefunctor is a covering when we have
  a group action.

## Examples

* The (left) **Cayley graph** of a group `M` with generators `ι : S → M` is the Schreier graph
  where `V = M` and the action is left multiplication.

## Implementation notes

Although referred to informally as graphs, Schreier graphs have multiple, directed, labelled
edges between nodes and so are implemented here as quivers.

## References

* [Y. Vorobets, *Notes on the Schreier graphs of the Grigorchuk group*][Vorobets2012]
-/

@[expose] public section

namespace Quiver

/-- A Schreier graph for a monoid `M` acting on `V` with generators `ι : S → M`.
Vertices are elements of `V`, and there is an edge from `x` to `y` for each `s : S`
such that `ι s • x = y`. -/
@[nolint unusedArguments, ext]
structure SchreierGraph (V : Type*) {M : Type*} [SMul M V] {S : Type*} (_ι : S → M) where
  /-- Wraps a vertex of the acted-upon type into the Schreier graph. -/
  ofVertex ::
  /-- The underlying vertex. -/
  toVertex : V

namespace SchreierGraph

section Basic

variable (V : Type*) {M : Type*} [SMul M V] {S : Type*} (ι : S → M)

/-- Equivalence between the original vertex type and the Schreier graph type. -/
@[simps]
def equiv : V ≃ SchreierGraph V ι where
  toFun := SchreierGraph.ofVertex
  invFun := SchreierGraph.toVertex
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transport the scalar multiplication to the Schreier graph vertices. -/
instance schreierGraphSMul : SMul M (SchreierGraph V ι) where
  smul x y := ⟨x • y.toVertex⟩

/-- The quiver structure on a Schreier graph. An arrow from `x` to `y` exists when
there is an `s : S` such that `(ι s) • x = y`. -/
instance schreierGraphQuiver : Quiver (SchreierGraph V ι) where
  Hom x y := { s : S // (ι s) • x = y }

/-- The labelling of arrows in a Schreier graph by elements of `S`.
This is encoded as a prefunctor to `SingleObj S`. -/
@[simps]
def labelling : SchreierGraph V ι ⥤q SingleObj S where
  obj _ := SingleObj.star S
  map e := e.val

end Basic

section MulAction

variable (V : Type*) {M : Type*} [Monoid M] [MulAction M V] {S : Type*} (ι : S → M)

/-- The monoid acts on the vertices of the Schreier graph. -/
instance : MulAction M (SchreierGraph V ι) where
  one_smul x := by
    ext
    exact one_smul M x.toVertex
  mul_smul a b x := by
    ext
    exact mul_smul a b x.toVertex

end MulAction

section GroupAction

/-!
### Schreier graphs for group actions

When we have a group action, the labelling becomes a covering.
-/

variable {V : Type*} {M : Type*} [Group M] [MulAction M V] {S : Type*} (ι : S → M)

/-- The star map of the labelling prefunctor as an equivalence. -/
@[simps]
def labellingStarEquiv (x : SchreierGraph V ι) :
    Quiver.Star x ≃ Quiver.Star (SingleObj.star S) where
  toFun := (labelling V ι).star x
  invFun := fun ⟨_, s⟩ => ⟨ι s • x, s, rfl⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

/-- The costar map of the labelling prefunctor as an equivalence. -/
@[simps]
def labellingCostarEquiv (x : SchreierGraph V ι) :
    Quiver.Costar x ≃ Quiver.Costar (SingleObj.star S) where
  toFun := (labelling V ι).costar x
  invFun := fun ⟨_, s⟩ => ⟨(ι s)⁻¹ • x, s, by simp⟩
  left_inv := by
    rintro ⟨v, s, hs⟩
    simp only [Prefunctor.costar_apply, labelling_map]
    have : (ι s)⁻¹ • x = v := by rw [← hs, inv_smul_smul]
    subst this; rfl
  right_inv := fun ⟨_, _⟩ => rfl

/-- The labelling prefunctor is a covering for Schreier graphs with group actions. -/
theorem labelling_isCovering : (labelling V ι).IsCovering where
  star_bijective u := (labellingStarEquiv ι u).bijective
  costar_bijective u := (labellingCostarEquiv ι u).bijective

/-- If a prefunctor between Schreier graphs commutes with the labelling (i.e., labels are
preserved), then it commutes with the group action. In other words, morphisms that preserve edge
labels also preserve the group structure. -/
lemma map_smul_of_comp_labelling_eq {W : Type*} [MulAction M W]
    (φ : SchreierGraph V ι ⥤q SchreierGraph W ι) (φm : φ ⋙q labelling W ι = labelling V ι)
    (v : SchreierGraph V ι) (s : S) :
    φ.obj (ι s • v) = ι s • (φ.obj v) := by
  -- The key is that φ preserves labels, so edges labelled 's' stay labelled 's'
  let e : v ⟶ ι s • v := ⟨s, rfl⟩
  -- φ.map e is an edge from φ.obj v, and its label is preserved
  have h := (φ.map e).property
  -- This says: `ι (φ.map e).val • φ.obj v = φ.obj (ι s • v)`
  -- We need to show `(φ.map e).val = s`
  have label_eq : (φ.map e).val = s := by
    -- `φm` says `φ ⋙q labelling = labelling`
    -- So `(φ ⋙q labelling).map e = labelling.map e`
    have : (φ ⋙q labelling W ι).map e = (labelling V ι).map e := by
      rw [φm]
    simp only [Prefunctor.comp_map, labelling_map] at this
    exact this
  rw [label_eq] at h
  exact h.symm

end GroupAction

end SchreierGraph

end Quiver
