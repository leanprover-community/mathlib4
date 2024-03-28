/-
Copyright (c) 2024 Anatole Dedeker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedeker, Etienne Marion, Florestan Martin-Baillon, Vincent Guirardel
-/

import Mathlib.Topology.ProperMap
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.PUnitInstances

/-!
# Proper Action

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/




/-- Additive version of proper action in the sense of Bourbaki:
the map `G×X→ X×X` is a proper map `isProperMap`
-/
@[mk_iff]
class ProperVAdd (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [AddGroup G]
    [AddAction G X] : Prop where
  /-- Additive version of proper action in the sense of Bourbaki:
the map `G×X→ X×X` is a proper map `isProperMap`  -/
  isProperMap_vadd_pair' : IsProperMap (fun gx ↦ ⟨gx.1 +ᵥ gx.2, gx.2⟩ : G × X → X × X)

/-- Proper action in the sense of Bourbaki:
the map `G×X→ X×X` is a proper map `isProperMap`
-/
@[to_additive existing, mk_iff]
class ProperSMul (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [Group G]
    [MulAction G X] : Prop where
  isProperMap_smul_pair' : IsProperMap (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X)

/-- By definition, if G acts properly on X
the map `G×X→ X×X` is a proper map `isProperMap`
-/
@[to_additive]
lemma isProperMap_smul_pair (G X : Type*) [Group G] [MulAction G X]
    [TopologicalSpace G] [TopologicalSpace X] [ProperSMul G X] :
    IsProperMap (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) :=
  ProperSMul.isProperMap_smul_pair'

open Filter Topology

variable {G X Y Z W : Type*} [Group G] [MulAction G X] [MulAction G Y]
variable [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]

@[to_additive]
instance continuousSmul_of_properSMul [ProperSMul G X] : ContinuousSMul G X where
  continuous_smul := (isProperMap_smul_pair G X).continuous.fst





theorem properSMul_iff_continuousSMul_ultrafilter_tendsto_t2 [T2Space X]:
ProperSMul G X ↔ ContinuousSMul G X ∧ (∀ ℱ : Ultrafilter (G × X), ∀ x₁ x₂ : X,
    Tendsto (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) ℱ (𝓝 (x₁, x₂)) →
    ∃ g : G, Tendsto Prod.fst (ℱ : Filter (G × X)) (𝓝 g)) := by
  sorry
