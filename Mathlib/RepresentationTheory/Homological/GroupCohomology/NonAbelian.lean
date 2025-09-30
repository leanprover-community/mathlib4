/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.CategoryTheory.Category.Pointed.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Non-abelian group cohomology

Let `G` be a group acting on another (not necessarily abelian) group `A`, in this file we define
`H⁰(G, A)` and `H¹(G, A)`, and prove some basic properties about it.

## Main Results

## Reference

-/

universe u

namespace groupCohomology

section basic

abbrev NonAbelianRep (G : Type u) [Monoid G] := Action MonCat.{u} G

variable (G : Type u) [Monoid G]

instance : CoeSort (NonAbelianRep G) (Type u) := ⟨fun V ↦ V.V⟩

instance (A : NonAbelianRep G) : MulAction G A := sorry

end basic

section H1

def Z1 (G : Type u) [Monoid G] (V : NonAbelianRep G) :=
  { f : G → V // ∀ g h : G, f (g * h) = f g * (g • f h) }

def Z1.setoid (G : Type u) [Group G] (V : NonAbelianRep G) : Setoid (Z1 G V) :=
  { r := fun f g ↦ ∃ a : V, ∀ h : G, g.val h = a⁻¹ * (f.val h) * (h • a),
    iseqv := sorry }
def H1 (V : NonAbelianRep G) : Pointed where
  X :=

end H1

end groupCohomology
