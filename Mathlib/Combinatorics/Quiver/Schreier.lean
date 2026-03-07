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

/-!
# Schreier Graphs

This module defines Schreier graphs as quivers with labeled edges.

## Main definitions

* `SchreierGraph V ι` - The Schreier graph of an action, with vertices of type `V` and edges
  labeled by elements of `S` via `ι : S → M`.
* `schreierGraphLabelling` - The prefunctor from a Schreier graph to `SingleObj S` that
  extracts edge labels.

## Main results

* `schreierGraphLabelling_isCovering` - The labelling prefunctor is a covering when we have
  a group action.

## Implementation notes

This is a port of the Lean 3 formalization from PR #18693, using the quiver-based approach
rather than the simpler `SimpleGraph` approach.

## References

* [Lean 3 PR #18693](https://github.com/leanprover-community/mathlib3/pull/18693)
-/

@[expose] public section

namespace Quiver

section Basic

variable (V : Type*) {M : Type*} [SMul M V] {S : Type*} (ι : S → M)

/-- The type of vertices in a Schreier graph. This is just an alias for `V` to distinguish
the graph structure. -/
@[nolint unusedArguments]
def SchreierGraph (V : Type*) {M : Type*} [SMul M V] {S : Type*} (_ι : S → M) : Type _ := V

/-- Equivalence between the original vertex type and the Schreier graph type. -/
@[simps!]
def equivSchreierGraph (V : Type*) {M : Type*} [SMul M V] {S : Type*} (ι : S → M) :
    V ≃ SchreierGraph V ι := Equiv.refl V

/-- Transport the scalar multiplication to the Schreier graph vertices. -/
instance schreierGraphSMul : SMul M (SchreierGraph V ι) where
  smul x y := equivSchreierGraph V ι (x • (equivSchreierGraph V ι).symm y)

/-- The quiver structure on a Schreier graph. An arrow from `x` to `y` exists when
there is an `s : S` such that `(ι s) • x = y`. -/
instance schreierGraphQuiver : Quiver (SchreierGraph V ι) where
  Hom x y := { s : S // (ι s) • x = y }

/-- The labelling of arrows in a Schreier graph by elements of `S`.
This is encoded as a prefunctor to `SingleObj S`. -/
@[simps]
def schreierGraphLabelling : SchreierGraph V ι ⥤q SingleObj S where
  obj _ := SingleObj.star S
  map e := e.val

end Basic

section GroupAction

/-!
### Schreier graphs for group actions

When we have a group action, the labelling becomes a covering.
-/

variable (V : Type*) {M : Type*} [Group M] [MulAction M V] {S : Type*} (ι : S → M)

/-- The group acts on the Schreier graph vertices. -/
instance schreierGraphMulAction : MulAction M (SchreierGraph V ι) where
  smul := SMul.smul
  one_smul x := by
    change equivSchreierGraph V ι (1 • (equivSchreierGraph V ι).symm x) = x
    simp
  mul_smul a b x := by
    change equivSchreierGraph V ι ((a * b) • (equivSchreierGraph V ι).symm x) =
      equivSchreierGraph V ι (a • (equivSchreierGraph V ι).symm
        (equivSchreierGraph V ι (b • (equivSchreierGraph V ι).symm x)))
    simp [mul_smul]

/-- The star map of the labelling prefunctor is bijective. This is a component of the
covering property, extracted as a separate lemma for modularity. -/
lemma schreierGraphLabelling_star_bijective (x : SchreierGraph V ι) :
    ((schreierGraphLabelling V ι).star x).Bijective := by
  constructor
  · -- injective
    intro ⟨v, ⟨s, hs⟩⟩ ⟨w, ⟨t, ht⟩⟩ h
    simp only [Prefunctor.star_apply, schreierGraphLabelling_map] at h
    cases h
    have vw_eq : v = w := calc
      v = (ι s) • x := hs.symm
      _ = w := ht
    subst vw_eq
    rfl
  · -- surjective
    intro ⟨v', s⟩
    use ⟨ι s • x, ⟨s, rfl⟩⟩
    simp only [Prefunctor.star_apply, schreierGraphLabelling_map]
    rfl

/-- The costar map of the labelling prefunctor is bijective. This is a component of the
covering property, extracted as a separate lemma for modularity. -/
lemma schreierGraphLabelling_costar_bijective (x : SchreierGraph V ι) :
    ((schreierGraphLabelling V ι).costar x).Bijective := by
  constructor
  · -- injective
    intro ⟨v, ⟨s, hs⟩⟩ ⟨w, ⟨t, ht⟩⟩ h
    simp only [Prefunctor.costar_apply, schreierGraphLabelling_map] at h
    cases h
    have vw_eq : v = w := calc
      v = (ι s)⁻¹ • ((ι s) • v) := by rw [inv_smul_smul]
      _ = (ι s)⁻¹ • x := by rw [hs]
      _ = (ι s)⁻¹ • ((ι s) • w) := by rw [← ht]
      _ = w := by rw [inv_smul_smul]
    subst vw_eq
    rfl
  · -- surjective
    intro ⟨v', s⟩
    use ⟨(ι s)⁻¹ • x, ⟨s, by simp⟩⟩
    simp only [Prefunctor.costar_apply, schreierGraphLabelling_map]
    rfl

/-- The labelling prefunctor is a covering for Schreier graphs with group actions. -/
theorem schreierGraphLabelling_isCovering : (schreierGraphLabelling V ι).IsCovering := by
  constructor
  · -- star_bijective
    intro u
    exact schreierGraphLabelling_star_bijective V ι u
  · -- costar_bijective
    intro u
    exact schreierGraphLabelling_costar_bijective V ι u

/-- If a prefunctor φ on a Schreier graph commutes with the labelling (i.e., labels are preserved),
then φ commutes with the group action. In other words, morphisms that preserve edge labels also
preserve the group structure. -/
lemma schreierGraph_action_commute (φ : SchreierGraph V ι ⥤q SchreierGraph V ι)
    (φm : φ ⋙q schreierGraphLabelling V ι = schreierGraphLabelling V ι)
    (v : SchreierGraph V ι) (s : S) : φ.obj (ι s • v) = ι s • (φ.obj v) := by
  -- The key is that φ preserves labels, so edges labeled 's' stay labeled 's'
  let e : v ⟶ ι s • v := ⟨s, rfl⟩
  -- φ.map e is an edge from φ.obj v, and its label is preserved
  have h := (φ.map e).property
  -- This says: `ι (φ.map e).val • φ.obj v = φ.obj (ι s • v)`
  -- We need to show `(φ.map e).val = s`
  have label_eq : (φ.map e).val = s := by
    -- `φm` says `φ ⋙q labelling = labelling`
    -- So `(φ ⋙q labelling).map e = labelling.map e`
    have : (φ ⋙q schreierGraphLabelling V ι).map e = (schreierGraphLabelling V ι).map e := by
      rw [φm]
    simp only [Prefunctor.comp_map, schreierGraphLabelling_map] at this
    exact this
  rw [label_eq] at h
  exact h.symm

end GroupAction

end Quiver
