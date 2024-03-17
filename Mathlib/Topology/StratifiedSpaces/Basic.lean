/-
Copyright (c) 2024 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Basic theory of stratified topological spaces.

-/

universe u v

open Topology

namespace Topology

/-- For a stratification on a topological space we bundle a poset `I` with a continuous
function to the upper set topology on `I` indexing the strata. -/
structure Stratification (X : Type u) [TopologicalSpace X] where
  I : Type v
  [order : Preorder I]
  strata : C(X, WithUpperSet I)

end Topology

namespace Stratification

open Set WithUpperSet

instance instPreOrder {X : Type u}  [TopologicalSpace X] (S : Stratification X) :
    Preorder S.I :=
  S.order

variable {X : Type u} [TopologicalSpace X] (S : Stratification X)

/-- The stratum of a corresponding to the upper set of `v` in indexing set `I`. -/
def stratum (v : S.I) : Set X := S.strata ⁻¹' (ofUpperSet ⁻¹' (Ici v))

end Stratification

