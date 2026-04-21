/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Algebraic facts about the topology of uniform convergence

This file contains algebraic compatibility results about the uniform structure of uniform
convergence / `𝔖`-convergence. They will mostly be useful for defining strong topologies on the
space of continuous linear maps between two topological vector spaces.

## Main statements

* `UniformFun.uniform_group` : if `G` is a uniform group, then `α →ᵤ G` a uniform group
* `UniformOnFun.uniform_group` : if `G` is a uniform group, then for any `𝔖 : Set (Set α)`,
  `α →ᵤ[𝔖] G` a uniform group.

## Implementation notes

Like in `Mathlib/Topology/UniformSpace/UniformConvergenceTopology.lean`, we use the type aliases
`UniformFun` (denoted `α →ᵤ β`) and `UniformOnFun` (denoted `α →ᵤ[𝔖] β`) for functions from `α`
to `β` endowed with the structures of uniform convergence and `𝔖`-convergence.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, strong dual

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Filter

open scoped Topology Pointwise UniformConvergence Uniformity

section AlgebraicInstances

variable {α β ι R : Type*} {𝔖 : Set <| Set α} {x : α}

@[to_additive] instance [One β] : One (α →ᵤ β) := inferInstanceAs <| One (α → β)

@[to_additive (attr := simp)]
lemma UniformFun.toFun_one [One β] : toFun (1 : α →ᵤ β) = 1 := rfl

@[to_additive (attr := simp)]
lemma UniformFun.ofFun_one [One β] : ofFun (1 : α → β) = 1 := rfl

@[to_additive] instance [One β] : One (α →ᵤ[𝔖] β) := inferInstanceAs <| One (α → β)

@[to_additive (attr := simp)]
lemma UniformOnFun.toFun_one [One β] : toFun 𝔖 (1 : α →ᵤ[𝔖] β) = 1 := rfl

@[to_additive (attr := simp)]
lemma UniformOnFun.one_apply [One β] : ofFun 𝔖 (1 : α → β) = 1 := rfl

@[to_additive] instance [Mul β] : Mul (α →ᵤ β) := inferInstanceAs <| Mul (α → β)

@[to_additive (attr := simp)]
lemma UniformFun.toFun_mul [Mul β] (f g : α →ᵤ β) : toFun (f * g) = toFun f * toFun g := rfl

@[to_additive (attr := simp)]
lemma UniformFun.ofFun_mul [Mul β] (f g : α → β) : ofFun (f * g) = ofFun f * ofFun g := rfl

@[to_additive] instance [Mul β] : Mul (α →ᵤ[𝔖] β) := inferInstanceAs <| Mul (α → β)

@[to_additive (attr := simp)]
lemma UniformOnFun.toFun_mul [Mul β] (f g : α →ᵤ[𝔖] β) :
    toFun 𝔖 (f * g) = toFun 𝔖 f * toFun 𝔖 g :=
  rfl

@[to_additive (attr := simp)]
lemma UniformOnFun.ofFun_mul [Mul β] (f g : α → β) : ofFun 𝔖 (f * g) = ofFun 𝔖 f * ofFun 𝔖 g := rfl

@[to_additive] instance [Inv β] : Inv (α →ᵤ β) := inferInstanceAs <| Inv (α → β)

@[to_additive (attr := simp)]
lemma UniformFun.toFun_inv [Inv β] (f : α →ᵤ β) : toFun (f⁻¹) = (toFun f)⁻¹ := rfl

@[to_additive (attr := simp)]
lemma UniformFun.ofFun_inv [Inv β] (f : α → β) : ofFun (f⁻¹) = (ofFun f)⁻¹ := rfl

@[to_additive] instance [Inv β] : Inv (α →ᵤ[𝔖] β) := inferInstanceAs <| Inv (α → β)

@[to_additive (attr := simp)]
lemma UniformOnFun.toFun_inv [Inv β] (f : α →ᵤ[𝔖] β) : toFun 𝔖 (f⁻¹) = (toFun 𝔖 f)⁻¹ := rfl

@[to_additive (attr := simp)]
lemma UniformOnFun.ofFun_inv [Inv β] (f : α → β) : ofFun 𝔖 (f⁻¹) = (ofFun 𝔖 f)⁻¹ := rfl

@[to_additive] instance [Div β] : Div (α →ᵤ β) := inferInstanceAs <| Div (α → β)

@[to_additive (attr := simp)]
lemma UniformFun.toFun_div [Div β] (f g : α →ᵤ β) : toFun (f / g) = toFun f / toFun g := rfl

@[to_additive (attr := simp)]
lemma UniformFun.ofFun_div [Div β] (f g : α → β) : ofFun (f / g) = ofFun f / ofFun g := rfl

@[to_additive] instance [Div β] : Div (α →ᵤ[𝔖] β) := inferInstanceAs <| Div (α → β)

@[to_additive (attr := simp)]
lemma UniformOnFun.toFun_div [Div β] (f g : α →ᵤ[𝔖] β) :
    toFun 𝔖 (f / g) = toFun 𝔖 f / toFun 𝔖 g :=
  rfl

@[to_additive (attr := simp)]
lemma UniformOnFun.ofFun_div [Div β] (f g : α → β) : ofFun 𝔖 (f / g) = ofFun 𝔖 f / ofFun 𝔖 g := rfl

@[to_additive]
instance [Monoid β] : Monoid (α →ᵤ β) := inferInstanceAs <| Monoid (α → β)

@[to_additive]
instance [Monoid β] : Monoid (α →ᵤ[𝔖] β) := inferInstanceAs <| Monoid (α → β)

@[to_additive]
instance [CommMonoid β] : CommMonoid (α →ᵤ β) := inferInstanceAs <| CommMonoid (α → β)

@[to_additive]
instance [CommMonoid β] : CommMonoid (α →ᵤ[𝔖] β) := inferInstanceAs <| CommMonoid (α → β)

@[to_additive]
instance [Group β] : Group (α →ᵤ β) := inferInstanceAs <| Group (α → β)

@[to_additive]
instance [Group β] : Group (α →ᵤ[𝔖] β) := inferInstanceAs <| Group (α → β)

@[to_additive]
instance [CommGroup β] : CommGroup (α →ᵤ β) := inferInstanceAs <| CommGroup (α → β)

@[to_additive]
instance [CommGroup β] : CommGroup (α →ᵤ[𝔖] β) := inferInstanceAs <| CommGroup (α → β)

instance {M : Type*} [SMul M β] : SMul M (α →ᵤ β) := inferInstanceAs <| SMul M (α → β)

@[simp]
lemma UniformFun.toFun_smul {M : Type*} [SMul M β] (c : M) (f : α →ᵤ β) :
    toFun (c • f) = c • toFun f :=
  rfl

@[simp]
lemma UniformFun.ofFun_smul {M : Type*} [SMul M β] (c : M) (f : α → β) :
    ofFun (c • f) = c • ofFun f :=
  rfl

instance {M : Type*} [SMul M β] : SMul M (α →ᵤ[𝔖] β) := inferInstanceAs <| SMul M (α → β)

@[simp]
lemma UniformOnFun.toFun_smul {M : Type*} [SMul M β] (c : M) (f : α →ᵤ[𝔖] β) :
    toFun 𝔖 (c • f) = c • toFun 𝔖 f :=
  rfl

@[simp]
lemma UniformOnFun.ofFun_smul {M : Type*} [SMul M β] (c : M) (f : α → β) :
    ofFun 𝔖 (c • f) = c • ofFun 𝔖 f :=
  rfl

instance {M N : Type*} [SMul M N] [SMul M β] [SMul N β] [IsScalarTower M N β] :
    IsScalarTower M N (α →ᵤ β) :=
  inferInstanceAs <| IsScalarTower M N (α → β)

instance {M N : Type*} [SMul M N] [SMul M β] [SMul N β] [IsScalarTower M N β] :
    IsScalarTower M N (α →ᵤ[𝔖] β) :=
  inferInstanceAs <| IsScalarTower M N (α → β)

instance {M N : Type*} [SMul M β] [SMul N β] [SMulCommClass M N β] :
    SMulCommClass M N (α →ᵤ β) :=
  inferInstanceAs <| SMulCommClass M N (α → β)

instance {M N : Type*} [SMul M β] [SMul N β] [SMulCommClass M N β] :
    SMulCommClass M N (α →ᵤ[𝔖] β) :=
  inferInstanceAs <| SMulCommClass M N (α → β)

instance {M : Type*} [Monoid M] [MulAction M β] : MulAction M (α →ᵤ β) :=
  inferInstanceAs <| MulAction M (α → β)

instance {M : Type*} [Monoid M] [MulAction M β] : MulAction M (α →ᵤ[𝔖] β) :=
  inferInstanceAs <| MulAction M (α → β)

instance {M : Type*} [Monoid M] [AddMonoid β] [DistribMulAction M β] :
    DistribMulAction M (α →ᵤ β) :=
  inferInstanceAs <| DistribMulAction M (α → β)

instance {M : Type*} [Monoid M] [AddMonoid β] [DistribMulAction M β] :
    DistribMulAction M (α →ᵤ[𝔖] β) :=
  inferInstanceAs <| DistribMulAction M (α → β)

instance [Semiring R] [AddCommMonoid β] [Module R β] : Module R (α →ᵤ β) :=
  inferInstanceAs <| Module R (α → β)

instance [Semiring R] [AddCommMonoid β] [Module R β] : Module R (α →ᵤ[𝔖] β) :=
  inferInstanceAs <| Module R (α → β)

end AlgebraicInstances

section Group

variable {α G ι : Type*} [Group G] {𝔖 : Set <| Set α} [UniformSpace G] [IsUniformGroup G]

/-- If `G` is a uniform group, then `α →ᵤ G` is a uniform group as well. -/
@[to_additive /-- If `G` is a uniform additive group,
then `α →ᵤ G` is a uniform additive group as well. -/]
instance : IsUniformGroup (α →ᵤ G) :=
  ⟨(-- Since `(/) : G × G → G` is uniformly continuous,
    -- `UniformFun.postcomp_uniformContinuous` tells us that
    -- `((/) ∘ —) : (α →ᵤ G × G) → (α →ᵤ G)` is uniformly continuous too. By precomposing with
    -- `UniformFun.uniformEquivProdArrow`, this gives that
    -- `(/) : (α →ᵤ G) × (α →ᵤ G) → (α →ᵤ G)` is also uniformly continuous
    UniformFun.postcomp_uniformContinuous uniformContinuous_div).comp
    UniformFun.uniformEquivProdArrow.symm.uniformContinuous⟩

@[to_additive]
protected theorem UniformFun.hasBasis_nhds_one_of_basis {p : ι → Prop} {b : ι → Set G}
    (h : (𝓝 1 : Filter G).HasBasis p b) :
    (𝓝 1 : Filter (α →ᵤ G)).HasBasis p fun i => { f : α →ᵤ G | ∀ x, toFun f x ∈ b i } := by
  convert UniformFun.hasBasis_nhds_of_basis α _ (1 : α →ᵤ G) h.uniformity_of_nhds_one
  simp

@[to_additive]
protected theorem UniformFun.hasBasis_nhds_one :
    (𝓝 1 : Filter (α →ᵤ G)).HasBasis (fun V : Set G => V ∈ (𝓝 1 : Filter G)) fun V =>
      { f : α → G | ∀ x, f x ∈ V } :=
  UniformFun.hasBasis_nhds_one_of_basis (basis_sets _)

/-- Let `𝔖 : Set (Set α)`. If `G` is a uniform group, then `α →ᵤ[𝔖] G` is a uniform group as
well. -/
@[to_additive /-- Let `𝔖 : Set (Set α)`. If `G` is a uniform additive group,
then `α →ᵤ[𝔖] G` is a uniform additive group as well. -/]
instance : IsUniformGroup (α →ᵤ[𝔖] G) :=
  ⟨(-- Since `(/) : G × G → G` is uniformly continuous,
    -- `UniformOnFun.postcomp_uniformContinuous` tells us that
    -- `((/) ∘ —) : (α →ᵤ[𝔖] G × G) → (α →ᵤ[𝔖] G)` is uniformly continuous too. By precomposing with
    -- `UniformOnFun.uniformEquivProdArrow`, this gives that
    -- `(/) : (α →ᵤ[𝔖] G) × (α →ᵤ[𝔖] G) → (α →ᵤ[𝔖] G)` is also uniformly continuous
    UniformOnFun.postcomp_uniformContinuous uniformContinuous_div).comp
    UniformOnFun.uniformEquivProdArrow.symm.uniformContinuous⟩

@[to_additive]
protected theorem UniformOnFun.hasBasis_nhds_one_of_basis (𝔖 : Set <| Set α) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) {p : ι → Prop} {b : ι → Set G}
    (h : (𝓝 1 : Filter G).HasBasis p b) :
    (𝓝 1 : Filter (α →ᵤ[𝔖] G)).HasBasis (fun Si : Set α × ι => Si.1 ∈ 𝔖 ∧ p Si.2) fun Si =>
      { f : α →ᵤ[𝔖] G | ∀ x ∈ Si.1, toFun 𝔖 f x ∈ b Si.2 } := by
  convert UniformOnFun.hasBasis_nhds_of_basis α _ 𝔖 (1 : α →ᵤ[𝔖] G) h𝔖₁ h𝔖₂ <|
    h.uniformity_of_nhds_one_swapped
  simp [UniformOnFun.gen]

@[to_additive]
protected theorem UniformOnFun.hasBasis_nhds_one (𝔖 : Set <| Set α) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
    (𝓝 1 : Filter (α →ᵤ[𝔖] G)).HasBasis
      (fun SV : Set α × Set G => SV.1 ∈ 𝔖 ∧ SV.2 ∈ (𝓝 1 : Filter G)) fun SV =>
      { f : α →ᵤ[𝔖] G | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  UniformOnFun.hasBasis_nhds_one_of_basis 𝔖 h𝔖₁ h𝔖₂ (basis_sets _)

@[to_additive (attr := simp)]
lemma UniformOnFun.ofFun_prod {β : Type*} [CommMonoid β] {f : ι → α → β} (I : Finset ι) :
    ofFun 𝔖 (∏ i ∈ I, f i) = ∏ i ∈ I, ofFun 𝔖 (f i) :=
  rfl

@[to_additive (attr := simp)]
lemma UniformOnFun.toFun_prod {β : Type*} [CommMonoid β] {f : ι → α → β} (I : Finset ι) :
    toFun 𝔖 (∏ i ∈ I, f i) = ∏ i ∈ I, toFun 𝔖 (f i) :=
  rfl

@[to_additive (attr := simp)]
lemma UniformFun.ofFun_prod {β : Type*} [CommMonoid β] {f : ι → α → β} (I : Finset ι) :
    ofFun (∏ i ∈ I, f i) = ∏ i ∈ I, ofFun (f i) :=
  rfl

@[to_additive (attr := simp)]
lemma UniformFun.toFun_prod {β : Type*} [CommMonoid β] {f : ι → α → β} (I : Finset ι) :
    toFun (∏ i ∈ I, f i) = ∏ i ∈ I, toFun (f i) :=
  rfl

end Group

section ConstSMul

variable (M α X : Type*) [SMul M X] [UniformSpace X] [UniformContinuousConstSMul M X]

instance UniformFun.uniformContinuousConstSMul :
    UniformContinuousConstSMul M (α →ᵤ X) where
  uniformContinuous_const_smul c := UniformFun.postcomp_uniformContinuous <|
    uniformContinuous_const_smul c

instance UniformFunOn.uniformContinuousConstSMul {𝔖 : Set (Set α)} :
    UniformContinuousConstSMul M (α →ᵤ[𝔖] X) where
  uniformContinuous_const_smul c := UniformOnFun.postcomp_uniformContinuous <|
    uniformContinuous_const_smul c

end ConstSMul
