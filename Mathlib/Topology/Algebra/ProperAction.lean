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
variable [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace Z] [TopologicalSpace W]

@[to_additive]
instance continuousSmul_of_properSMul [ProperSMul G X] : ContinuousSMul G X where
  continuous_smul := (isProperMap_smul_pair G X).continuous.fst




/-
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto_t2 [T2Space X]:
    ProperSMul G X ↔ ContinuousSMul G X ∧ (∀ ℱ : Ultrafilter (G × X), ∀ x₁ x₂ : X,
    Tendsto (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) ℱ (𝓝 (x₁, x₂)) →
    ∃ g : G, Tendsto Prod.fst (ℱ : Filter (G × X)) (𝓝 g)) := by
  sorry


-/

/-- If G acts properly on X, then the quotient space is Hausdorff (T2) -/
theorem t2Space_of_ProperSMul (hproper:ProperSMul G X) :
  T2Space (Quotient (MulAction.orbitRel G X)) := by
  rw [t2_iff_isClosed_diagonal] -- T2 if the diagonal is closed
  set R := MulAction.orbitRel G X -- the orbit relation
  set XmodG := Quotient R -- the quotient
  set π : X → XmodG := Quotient.mk' -- the projection
  have hpiopen: IsOpenMap π := -- the projection is open
    isOpenMap_quotient_mk'_mul
  have picont : Continuous π := continuous_quotient_mk' -- π is continuous
  have pisurj : Function.Surjective π := by apply surjective_quotient_mk' -- π is surjective
  set pipi := Prod.map π π
  have pipiopen : IsOpenMap pipi := IsOpenMap.prod hpiopen hpiopen -- π × π open
  have pipisurj : (Function.Surjective (pipi) ) :=  -- π × π surj
    Function.Surjective.Prod_map pisurj pisurj
  have pipipquotient := -- π × π is q QuotientMap because open, continuous and surj
    IsOpenMap.to_quotientMap pipiopen (Continuous.prod_map picont picont) pipisurj
  rw [<-QuotientMap.isClosed_preimage pipipquotient] -- closed iff preimage closed
  set gr' := pipi ⁻¹' Set.diagonal (Quotient R) -- preimage of the diag
  set m : G × X → X × X := fun (g,x) => (g • x, x)
  set gr := Set.range m -- graph of the orbit relation
  have r_eq_r' : gr' = gr := by -- the preimage of the diag is the graph of the relation
    ext ⟨x,y⟩
    conv_lhs => -- we work only on the left hand side for now
      rw [Set.mem_preimage]
      rw [Set.mem_diagonal_iff]
      change (π x = π y)  --↔ (x, y) ∈ gr
      rw [Quotient.eq']
      change ((MulAction.orbitRel G X).Rel x y)-- ↔ (x, y) ∈ gr
      rw [MulAction.orbitRel_apply]
      rw [MulAction.orbit]
      change (∃ g : G, g • y = x)
    conv_rhs =>
      rw [Set.mem_range]
      simp
    simp [m]
  rw [r_eq_r']
  exact hproper.isProperMap_smul_pair'.isClosedMap.closed_range
