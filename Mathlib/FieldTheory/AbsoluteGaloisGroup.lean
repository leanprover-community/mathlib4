/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization

/-!
# The topological abelianization of the absolute Galois group.

We define the absolute Galois group of a field `K` and its topological abelianization.

## Main definitions
- `Field.absoluteGaloisGroup` : The Galois group of the field extension `K^sep/K`,
  where `K^sep` is a separable closure of `K`.
- `Field.absoluteGaloisGroupAbelianization` : The topological abelianization of
  `Field.absoluteGaloisGroup K`, that is, the quotient of `Field.absoluteGaloisGroup K` by the
  topological closure of its commutator subgroup.

## Main results
- `Field.absoluteGaloisGroup.commutator_closure_isNormal` : the topological closure of the
  commutator of `absoluteGaloisGroup` is a normal subgroup.

## Tags
field, separable closure, galois group, abelianization

-/

@[expose] public noncomputable section

namespace Field

variable (K L : Type*) [Field K] [Field L]

/-! ### The absolute Galois group -/

/-- The absolute Galois group of `K`, defined as the Galois group of the field extension `K^sep/K`,
  where `K^sep` is a separable closure of `K`. -/
def absoluteGaloisGroup := SeparableClosure K ≃ₐ[K] SeparableClosure K
deriving Group, TopologicalSpace, IsTopologicalGroup

/-- `absoluteGaloisGroup` is a topological space with the Krull topology. -/
add_decl_doc instTopologicalSpaceAbsoluteGaloisGroup

local notation "G_K" => absoluteGaloisGroup

section

variable [Algebra K L] [Algebra (SeparableClosure K) (SeparableClosure L)]
  [IsScalarTower K (SeparableClosure K) (SeparableClosure L)]

open IntermediateField in
/-- A commuting square of two fields and their separable closures induces a continuous homomorphism
of their absolute Galois groups. -/
@[simps!]
noncomputable def absoluteGaloisGroup.mapOfAlgebra : G_K L →ₜ* G_K K :=
  letI F : G_K L →* G_K K := (AlgEquiv.restrictNormalHom _).comp (AlgEquiv.restrictScalarsHom K)
  { __ := F
    continuous_toFun := by
      classical
      let f := IsScalarTower.toAlgHom K (SeparableClosure K) (SeparableClosure L)
      apply continuous_of_continuousAt_one F
      rw [ContinuousAt, map_one]
      refine ((galGroupBasis L (SeparableClosure L)).nhds_one_hasBasis.tendsto_iff
        (galGroupBasis K (SeparableClosure K)).nhds_one_hasBasis).mpr ?_
      rintro _ ⟨_, ⟨F, hF : FiniteDimensional _ _, rfl⟩, rfl⟩
      refine ⟨_, ⟨_, ⟨adjoin L (F.map f), ?_, rfl⟩, rfl⟩, fun σ hσ x ↦ ?_⟩
      · suffices Algebra.EssFiniteType L (adjoin L (F.map f : Set (SeparableClosure L))) by
          apply Algebra.finite_of_essFiniteType_of_isAlgebraic
        replace hF : Algebra.EssFiniteType K F := inferInstance
        rw [essFiniteType_iff] at hF ⊢
        obtain ⟨s, rfl⟩ := hF
        use s.image f
        rw [adjoin_map, adjoin_adjoin_right, Finset.coe_image]
      · exact f.injective <| ((σ.restrictScalarsHom K).restrictNormal_commutes
          (SeparableClosure K) x).trans <| hσ ⟨f x, subset_adjoin _ _ ⟨_, x.2, rfl⟩⟩ }

end

variable {K L} in
/-- An embedding of fields induces a continuous homomorphism of absolute Galois groups.
Note that this depends on an arbitrary choice of embedding of the separable closures. -/
@[simps!]
noncomputable def absoluteGaloisGroup.map (f : K →+* L) : G_K L →ₜ* G_K K :=
  letI : Algebra K L := f.toAlgebra
  letI g : SeparableClosure K →ₐ[K] SeparableClosure L := IsSepClosed.lift
  letI : Algebra (SeparableClosure K) (SeparableClosure L) := g.toAlgebra
  absoluteGaloisGroup.mapOfAlgebra K L

/-! ### The topological abelianization of the absolute Galois group -/

instance absoluteGaloisGroup.commutator_closure_isNormal :
    (commutator (G_K K)).topologicalClosure.Normal :=
  Subgroup.is_normal_topologicalClosure (commutator (G_K K))

/-- The topological abelianization of `absoluteGaloisGroup`, that is, the quotient of
  `absoluteGaloisGroup` by the topological closure of its commutator subgroup. -/
abbrev absoluteGaloisGroupAbelianization := TopologicalAbelianization (G_K K)

local notation "G_K_ab" => absoluteGaloisGroupAbelianization

end Field
