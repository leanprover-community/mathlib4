/-
Copyright (c) 2021 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Path

/-!
# Fundamental group of a space

Given a topological space `X` and a basepoint `x`, the fundamental group is the automorphism group
of `x` i.e. the group with elements being loops based at `x` (quotiented by homotopy equivalence).
-/

@[expose] public section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ : X}

noncomputable section

open CategoryTheory

variable (X)

/-- The fundamental group is the automorphism group (vertex group) of the basepoint
in the fundamental groupoid. -/
abbrev FundamentalGroup (x : X) :=
  End (FundamentalGroupoid.mk x)

variable {X}

namespace FundamentalGroup

variable {x : X} {p q : FundamentalGroup X x}

theorem one_def : (1 : FundamentalGroup X x) = .refl x := rfl
theorem mul_def : p * q = q.trans p := rfl
theorem inv_def : p⁻¹ = p.symm := rfl

/-- Get an isomorphism between the fundamental groups at two points given a path -/
def fundamentalGroupMulEquivOfPath (p : Path x₀ x₁) :
    FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  ((Groupoid.isoEquivHom ..).symm ⟦p⟧).conj

variable (x₀ x₁)

/-- The fundamental group of a path connected space is independent of the choice of basepoint. -/
def fundamentalGroupMulEquivOfPathConnected [PathConnectedSpace X] :
    FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath x₀ x₁)

/-- An element of the fundamental group as an arrow in the fundamental groupoid. -/
abbrev toArrow {x : X} (p : FundamentalGroup X x) :
    FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x :=
  p

/-- An element of the fundamental group as a quotient of homotopic paths. -/
abbrev toPath {x : X} (p : FundamentalGroup X x) : Path.Homotopic.Quotient x x :=
  toArrow p

/-- An element of the fundamental group, constructed from an arrow in the fundamental groupoid. -/
abbrev fromArrow {x : X}
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) :
    FundamentalGroup X x :=
  p

/-- An element of the fundamental group, constructed from a quotient of homotopic paths. -/
abbrev fromPath {x : X} (p : Path.Homotopic.Quotient x x) : FundamentalGroup X x :=
  fromArrow p

/-- The homomorphism between fundamental groups induced by a continuous map. -/
@[simps!] def map (f : C(X, Y)) (x : X) : FundamentalGroup X x →* FundamentalGroup Y (f x) :=
  (FundamentalGroupoid.map f).mapEnd _

/-- The homomorphism on fundamental groups induced by an inclusion of subspaces. -/
def mapOfSubset {U V : Set X} (h : U ⊆ V) (x : U) :
    FundamentalGroup U x →* FundamentalGroup V ⟨x, h x.property⟩ :=
  map (ContinuousMap.inclusion h) x

lemma coe_mapOfSubset {U V : Set X} (h : U ⊆ V) (x : U) :
    mapOfSubset h x = map (ContinuousMap.inclusion h) x := rfl

/-- The homomorphism on fundamental groups induced by inclusion into the ambient space. -/
def mapOfSubtype {U : Set X} (x : U) : FundamentalGroup U x →* FundamentalGroup X x :=
  map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) x

lemma coe_mapOfSubtype {U : Set X} (x : U) :
    mapOfSubtype x = map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) x := rfl

lemma mapOfSubtype_comp_mapOfSubset {U V : Set X} (h : U ⊆ V) (x : U) :
    (mapOfSubtype (U := V) ⟨x, h x.property⟩).comp (mapOfSubset h x) = mapOfSubtype x := by
  ext q
  exact (Path.Homotopic.Quotient.map_comp (f := ContinuousMap.inclusion h)).symm

variable (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)

/-- The homomorphism from π₁(X, x) to π₁(Y, y) induced by a continuous map `f` with `f x = y`. -/
def mapOfEq : FundamentalGroup X x →* FundamentalGroup Y y :=
  (eqToIso <| congr_arg FundamentalGroupoid.mk h).conj.toMonoidHom.comp (map f x)

theorem mapOfEq_apply (p : FundamentalGroup X x) :
    mapOfEq f h p = (Path.Homotopic.Quotient.map p f).cast h.symm h.symm :=
  FundamentalGroupoid.conj_eqToHom ..

end FundamentalGroup
