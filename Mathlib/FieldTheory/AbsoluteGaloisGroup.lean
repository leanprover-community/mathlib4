/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization

/-!
# The topological abelianization of the absolute Galois group.

We define the absolute Galois group of a field `K` and its topological abelianization.
The absolute Galois group acts on the separable and algebraic closures of `K`, and is a
Galois group for the separable closure in the sense of `IsGaloisGroup`.

## Main definitions
- `Field.absoluteGaloisGroup` : The Galois group of the field extension `K^sep/K`,
  where `K^sep` is a separable closure of `K`.
- `Field.absoluteGaloisGroup.mulSemiringActionOfNormal` : the action on a normal extension
  equipped with an embedding into the algebraic closure.
- `Field.absoluteGaloisGroupAbelianization` : The topological abelianization of
  `Field.absoluteGaloisGroup K`, that is, the quotient of `Field.absoluteGaloisGroup K` by the
  topological closure of its commutator subgroup.

## Main results
- `Field.absoluteGaloisGroup.restrictAlgebraicClosure` : restriction from the algebraic closure to
  the separable closure is an isomorphism of topological groups.
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
where `K^sep` is a separable closure of `K`.

It is canonically isomorphic to `Gal(AlgebraicClosure K/K)` as a topological group via
`Field.absoluteGaloisGroup.restrictAlgebraicClosure`. -/
def absoluteGaloisGroup := SeparableClosure K ≃ₐ[K] SeparableClosure K
deriving Group, TopologicalSpace, IsTopologicalGroup

/-- `absoluteGaloisGroup` is a topological space with the Krull topology. -/
add_decl_doc instTopologicalSpaceAbsoluteGaloisGroup

local notation "G_K" => absoluteGaloisGroup

instance : MulSemiringAction (G_K K) (SeparableClosure K) :=
  inferInstanceAs (MulSemiringAction Gal(SeparableClosure K/K) (SeparableClosure K))

instance : FaithfulSMul (G_K K) (SeparableClosure K) :=
  inferInstanceAs (FaithfulSMul Gal(SeparableClosure K/K) (SeparableClosure K))

instance : IsGaloisGroup (G_K K) K (SeparableClosure K) :=
  inferInstanceAs (IsGaloisGroup Gal(SeparableClosure K/K) K (SeparableClosure K))

/-- Restriction from the algebraic closure to the separable closure induces an isomorphism of
topological groups from the automorphism group of the algebraic closure to the absolute Galois
group. -/
noncomputable def absoluteGaloisGroup.restrictAlgebraicClosure :
    Gal(AlgebraicClosure K/K) ≃ₜ* G_K K :=
  AlgEquiv.restrictNormalEquivOfIsPurelyInseparable K (SeparableClosure K) (AlgebraicClosure K)

@[simp]
theorem absoluteGaloisGroup.restrictAlgebraicClosure_apply (σ : Gal(AlgebraicClosure K/K)) :
    restrictAlgebraicClosure K σ = σ.restrictNormal (SeparableClosure K) := rfl

/-! ### Actions on field extensions -/

instance : MulSemiringAction (G_K K) (AlgebraicClosure K) :=
  MulSemiringAction.compHom _ (absoluteGaloisGroup.restrictAlgebraicClosure K).symm.toMonoidHom

instance : SMulCommClass (G_K K) K (AlgebraicClosure K) :=
  SMul.comp.smulCommClass (absoluteGaloisGroup.restrictAlgebraicClosure K).symm

instance : FaithfulSMul (G_K K) (AlgebraicClosure K) :=
  ⟨fun h ↦ (absoluteGaloisGroup.restrictAlgebraicClosure K).symm.injective (AlgEquiv.ext h)⟩

theorem absoluteGaloisGroup.smul_algebraicClosure_def (σ : G_K K) (x : AlgebraicClosure K) :
    σ • x = (restrictAlgebraicClosure K).symm σ x := rfl

theorem absoluteGaloisGroup.restrictAlgebraicClosure_smul (σ : Gal(AlgebraicClosure K/K))
    (x : SeparableClosure K) :
    restrictAlgebraicClosure K σ • x = σ.restrictNormal (SeparableClosure K) x := rfl

@[simp]
theorem absoluteGaloisGroup.coe_smul (σ : G_K K) (x : SeparableClosure K) :
    ↑(σ • x) = σ • (x : AlgebraicClosure K) := by
  obtain ⟨τ, rfl⟩ := (restrictAlgebraicClosure K).surjective σ
  simpa only [smul_algebraicClosure_def, ContinuousMulEquiv.symm_apply_apply,
    restrictAlgebraicClosure_smul, IntermediateField.algebraMap_apply] using
    τ.restrictNormal_commutes (SeparableClosure K) x

section Normal

variable [Algebra K L] [Normal K L] [Algebra L (AlgebraicClosure K)]
  [IsScalarTower K L (AlgebraicClosure K)]

/-- The action of the absolute Galois group on a normal extension, using its given embedding
into the algebraic closure. -/
@[implicit_reducible]
noncomputable def absoluteGaloisGroup.mulSemiringActionOfNormal : MulSemiringAction (G_K K) L :=
  MulSemiringAction.compHom L
    ((AlgEquiv.restrictNormalHom L).comp (restrictAlgebraicClosure K).symm.toMonoidHom)

instance absoluteGaloisGroup.smulCommClassOfNormal : letI := mulSemiringActionOfNormal K L
    SMulCommClass (G_K K) K L :=
  SMul.comp.smulCommClass
    ((AlgEquiv.restrictNormalHom L).comp (restrictAlgebraicClosure K).symm.toMonoidHom)

@[simp]
theorem absoluteGaloisGroup.algebraMap_smulOfNormal (σ : G_K K) (x : L) :
    letI := mulSemiringActionOfNormal K L
    algebraMap L (AlgebraicClosure K) (σ • x) =
      σ • algebraMap L (AlgebraicClosure K) x :=
  ((restrictAlgebraicClosure K).symm σ).restrictNormal_commutes L x

end Normal

/-! ### Maps of absolute Galois groups -/

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
