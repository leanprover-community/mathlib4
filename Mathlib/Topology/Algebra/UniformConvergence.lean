/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Topology.Algebra.FilterBasis

#align_import topology.algebra.uniform_convergence from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Algebraic facts about the topology of uniform convergence

This file contains algebraic compatibility results about the uniform structure of uniform
convergence / `𝔖`-convergence. They will mostly be useful for defining strong topologies on the
space of continuous linear maps between two topological vector spaces.

## Main statements

* `UniformFun.uniform_group` : if `G` is a uniform group, then `α →ᵤ G` a uniform group
* `UniformOnFun.uniform_group` : if `G` is a uniform group, then for any `𝔖 : Set (Set α)`,
  `α →ᵤ[𝔖] G` a uniform group.
* `UniformOnFun.continuousSMul_induced_of_image_bounded` : let `E` be a TVS, `𝔖 : Set (Set α)` and
  `H` a submodule of `α →ᵤ[𝔖] E`. If the image of any `S ∈ 𝔖` by any `u ∈ H` is bounded (in the
  sense of `Bornology.IsVonNBounded`), then `H`, equipped with the topology induced from
  `α →ᵤ[𝔖] E`, is a TVS.

## Implementation notes

Like in `Topology/UniformSpace/UniformConvergenceTopology`, we use the type aliases
`UniformFun` (denoted `α →ᵤ β`) and `UniformOnFun` (denoted `α →ᵤ[𝔖] β`) for functions from `α`
to `β` endowed with the structures of uniform convergence and `𝔖`-convergence.

## TODO

* `UniformOnFun.continuousSMul_induced_of_image_bounded` unnecessarily asks for `𝔖` to be
  nonempty and directed. This will be easy to solve once we know that replacing `𝔖` by its
  ***noncovering*** bornology (i.e ***not*** what `Bornology` currently refers to in mathlib)
  doesn't change the topology.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, strong dual

-/

open Filter
open scoped Topology Pointwise UniformConvergence

section AlgebraicInstances

variable {α β ι R : Type*} {𝔖 : Set <| Set α} {x : α}

@[to_additive] instance [One β] : One (α →ᵤ β) := Pi.instOne

@[to_additive (attr := simp)]
lemma UniformFun.toFun_one [One β] : toFun (1 : α →ᵤ β) = 1 := rfl

@[to_additive (attr := simp)]
lemma UniformFun.ofFun_one [One β] : ofFun (1 : α → β) = 1 := rfl

@[to_additive] instance [One β] : One (α →ᵤ[𝔖] β) := Pi.instOne

@[to_additive (attr := simp)]
lemma UniformOnFun.toFun_one [One β] : toFun 𝔖 (1 : α →ᵤ[𝔖] β) = 1 := rfl

@[to_additive (attr := simp)]
lemma UniformOnFun.one_apply [One β] : ofFun 𝔖 (1 : α → β) = 1 := rfl

@[to_additive] instance [Mul β] : Mul (α →ᵤ β) := Pi.instMul

@[to_additive (attr := simp)]
lemma UniformFun.toFun_mul [Mul β] (f g : α →ᵤ β) : toFun (f * g) = toFun f * toFun g := rfl

@[to_additive (attr := simp)]
lemma UniformFun.ofFun_mul [Mul β] (f g : α → β) : ofFun (f * g) = ofFun f * ofFun g := rfl

@[to_additive] instance [Mul β] : Mul (α →ᵤ[𝔖] β) := Pi.instMul

@[to_additive (attr := simp)]
lemma UniformOnFun.toFun_mul [Mul β] (f g : α →ᵤ[𝔖] β) :
    toFun 𝔖 (f * g) = toFun 𝔖 f * toFun 𝔖 g :=
  rfl

@[to_additive (attr := simp)]
lemma UniformOnFun.ofFun_mul [Mul β] (f g : α → β) : ofFun 𝔖 (f * g) = ofFun 𝔖 f * ofFun 𝔖 g := rfl

@[to_additive] instance [Inv β] : Inv (α →ᵤ β) := Pi.instInv

@[to_additive (attr := simp)]
lemma UniformFun.toFun_inv [Inv β] (f : α →ᵤ β) : toFun (f⁻¹) = (toFun f)⁻¹ := rfl

@[to_additive (attr := simp)]
lemma UniformFun.ofFun_inv [Inv β] (f : α → β) : ofFun (f⁻¹) = (ofFun f)⁻¹ := rfl

@[to_additive] instance [Inv β] : Inv (α →ᵤ[𝔖] β) := Pi.instInv

@[to_additive (attr := simp)]
lemma UniformOnFun.toFun_inv [Inv β] (f : α →ᵤ[𝔖] β) : toFun 𝔖 (f⁻¹) = (toFun 𝔖 f)⁻¹ := rfl

@[to_additive (attr := simp)]
lemma UniformOnFun.ofFun_inv [Inv β] (f : α → β) : ofFun 𝔖 (f⁻¹) = (ofFun 𝔖 f)⁻¹ := rfl

@[to_additive] instance [Div β] : Div (α →ᵤ β) := Pi.instDiv

@[to_additive (attr := simp)]
lemma UniformFun.toFun_div [Div β] (f g : α →ᵤ β) : toFun (f / g) = toFun f / toFun g := rfl

@[to_additive (attr := simp)]
lemma UniformFun.ofFun_div [Div β] (f g : α → β) : ofFun (f / g) = ofFun f / ofFun g := rfl

@[to_additive] instance [Div β] : Div (α →ᵤ[𝔖] β) := Pi.instDiv

@[to_additive (attr := simp)]
lemma UniformOnFun.toFun_div [Div β] (f g : α →ᵤ[𝔖] β) :
    toFun 𝔖 (f / g) = toFun 𝔖 f / toFun 𝔖 g :=
  rfl

@[to_additive (attr := simp)]
lemma UniformOnFun.ofFun_div [Div β] (f g : α → β) : ofFun 𝔖 (f / g) = ofFun 𝔖 f / ofFun 𝔖 g := rfl

@[to_additive]
instance [Monoid β] : Monoid (α →ᵤ β) :=
  Pi.monoid

@[to_additive]
instance [Monoid β] : Monoid (α →ᵤ[𝔖] β) :=
  Pi.monoid

@[to_additive]
instance [CommMonoid β] : CommMonoid (α →ᵤ β) :=
  Pi.commMonoid

@[to_additive]
instance [CommMonoid β] : CommMonoid (α →ᵤ[𝔖] β) :=
  Pi.commMonoid

@[to_additive]
instance [Group β] : Group (α →ᵤ β) :=
  Pi.group

@[to_additive]
instance [Group β] : Group (α →ᵤ[𝔖] β) :=
  Pi.group

@[to_additive]
instance [CommGroup β] : CommGroup (α →ᵤ β) :=
  Pi.commGroup

@[to_additive]
instance [CommGroup β] : CommGroup (α →ᵤ[𝔖] β) :=
  Pi.commGroup

instance {M : Type*} [SMul M β] : SMul M (α →ᵤ β) := Pi.instSMul

@[simp]
lemma UniformFun.toFun_smul {M : Type*} [SMul M β] (c : M) (f : α →ᵤ β) :
    toFun (c • f) = c • toFun f :=
  rfl

@[simp]
lemma UniformFun.ofFun_smul {M : Type*} [SMul M β] (c : M) (f : α → β) :
    ofFun (c • f) = c • ofFun f :=
  rfl

instance {M : Type*} [SMul M β] : SMul M (α →ᵤ[𝔖] β) := Pi.instSMul

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
  Pi.isScalarTower

instance {M N : Type*} [SMul M N] [SMul M β] [SMul N β] [IsScalarTower M N β] :
    IsScalarTower M N (α →ᵤ[𝔖] β) :=
  Pi.isScalarTower

instance {M N : Type*} [SMul M β] [SMul N β] [SMulCommClass M N β] :
    SMulCommClass M N (α →ᵤ β) :=
  Pi.smulCommClass

instance {M N : Type*} [SMul M β] [SMul N β] [SMulCommClass M N β] :
    SMulCommClass M N (α →ᵤ[𝔖] β) :=
  Pi.smulCommClass

instance {M : Type*} [Monoid M] [MulAction M β] : MulAction M (α →ᵤ β) := Pi.mulAction _

instance {M : Type*} [Monoid M] [MulAction M β] : MulAction M (α →ᵤ[𝔖] β) := Pi.mulAction _

instance {M : Type*} [Monoid M] [AddMonoid β] [DistribMulAction M β] :
    DistribMulAction M (α →ᵤ β) :=
  Pi.distribMulAction _

instance {M : Type*} [Monoid M] [AddMonoid β] [DistribMulAction M β] :
    DistribMulAction M (α →ᵤ[𝔖] β) :=
  Pi.distribMulAction _

instance [Semiring R] [AddCommMonoid β] [Module R β] : Module R (α →ᵤ β) :=
  Pi.module _ _ _

instance [Semiring R] [AddCommMonoid β] [Module R β] : Module R (α →ᵤ[𝔖] β) :=
  Pi.module _ _ _

end AlgebraicInstances

section Group

variable {α G ι : Type*} [Group G] {𝔖 : Set <| Set α} [UniformSpace G] [UniformGroup G]

/-- If `G` is a uniform group, then `α →ᵤ G` is a uniform group as well. -/
@[to_additive "If `G` is a uniform additive group,
then `α →ᵤ G` is a uniform additive group as well."]
instance : UniformGroup (α →ᵤ G) :=
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
  have := h.comap fun p : G × G => p.2 / p.1
  rw [← uniformity_eq_comap_nhds_one] at this
  convert UniformFun.hasBasis_nhds_of_basis α _ (1 : α →ᵤ G) this
  -- Porting note: removed `ext i f` here, as it has already been done by `convert`.
  simp
#align uniform_fun.has_basis_nhds_one_of_basis UniformFun.hasBasis_nhds_one_of_basis
#align uniform_fun.has_basis_nhds_zero_of_basis UniformFun.hasBasis_nhds_zero_of_basis

@[to_additive]
protected theorem UniformFun.hasBasis_nhds_one :
    (𝓝 1 : Filter (α →ᵤ G)).HasBasis (fun V : Set G => V ∈ (𝓝 1 : Filter G)) fun V =>
      { f : α → G | ∀ x, f x ∈ V } :=
  UniformFun.hasBasis_nhds_one_of_basis (basis_sets _)
#align uniform_fun.has_basis_nhds_one UniformFun.hasBasis_nhds_one
#align uniform_fun.has_basis_nhds_zero UniformFun.hasBasis_nhds_zero

/-- Let `𝔖 : Set (Set α)`. If `G` is a uniform group, then `α →ᵤ[𝔖] G` is a uniform group as
well. -/
@[to_additive "Let `𝔖 : Set (Set α)`. If `G` is a uniform additive group,
then `α →ᵤ[𝔖] G` is a uniform additive group as well."]
instance : UniformGroup (α →ᵤ[𝔖] G) :=
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
  have := h.comap fun p : G × G => p.1 / p.2
  rw [← uniformity_eq_comap_nhds_one_swapped] at this
  convert UniformOnFun.hasBasis_nhds_of_basis α _ 𝔖 (1 : α →ᵤ[𝔖] G) h𝔖₁ h𝔖₂ this
  -- Porting note: removed `ext i f` here, as it has already been done by `convert`.
  simp [UniformOnFun.gen]
#align uniform_on_fun.has_basis_nhds_one_of_basis UniformOnFun.hasBasis_nhds_one_of_basis
#align uniform_on_fun.has_basis_nhds_zero_of_basis UniformOnFun.hasBasis_nhds_zero_of_basis

@[to_additive]
protected theorem UniformOnFun.hasBasis_nhds_one (𝔖 : Set <| Set α) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
    (𝓝 1 : Filter (α →ᵤ[𝔖] G)).HasBasis
      (fun SV : Set α × Set G => SV.1 ∈ 𝔖 ∧ SV.2 ∈ (𝓝 1 : Filter G)) fun SV =>
      { f : α →ᵤ[𝔖] G | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  UniformOnFun.hasBasis_nhds_one_of_basis 𝔖 h𝔖₁ h𝔖₂ (basis_sets _)
#align uniform_on_fun.has_basis_nhds_one UniformOnFun.hasBasis_nhds_one
#align uniform_on_fun.has_basis_nhds_zero UniformOnFun.hasBasis_nhds_zero

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

section Module

variable (𝕜 α E H : Type*) {hom : Type*} [NormedField 𝕜] [AddCommGroup H] [Module 𝕜 H]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace H] [UniformSpace E] [UniformAddGroup E]
  [ContinuousSMul 𝕜 E] {𝔖 : Set <| Set α}
  [FunLike hom H (α →ᵤ[𝔖] E)] [LinearMapClass hom 𝕜 H (α →ᵤ[𝔖] E)]

/-- Let `E` be a TVS, `𝔖 : Set (Set α)` and `H` a submodule of `α →ᵤ[𝔖] E`. If the image of any
`S ∈ 𝔖` by any `u ∈ H` is bounded (in the sense of `Bornology.IsVonNBounded`), then `H`,
equipped with the topology of `𝔖`-convergence, is a TVS.

For convenience, we don't literally ask for `H : Submodule (α →ᵤ[𝔖] E)`. Instead, we prove the
result for any vector space `H` equipped with a linear inducing to `α →ᵤ[𝔖] E`, which is often
easier to use. We also state the `Submodule` version as
`UniformOnFun.continuousSMul_submodule_of_image_bounded`. -/
theorem UniformOnFun.continuousSMul_induced_of_image_bounded (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) (φ : hom) (hφ : Inducing φ)
    (h : ∀ u : H, ∀ s ∈ 𝔖, Bornology.IsVonNBounded 𝕜 ((φ u : α → E) '' s)) :
    ContinuousSMul 𝕜 H := by
  have : TopologicalAddGroup H := by
    rw [hφ.induced]
    exact topologicalAddGroup_induced φ
  have : (𝓝 0 : Filter H).HasBasis _ _ := by
    rw [hφ.induced, nhds_induced, map_zero]
    exact (UniformOnFun.hasBasis_nhds_zero 𝔖 h𝔖₁ h𝔖₂).comap φ
  refine' ContinuousSMul.of_basis_zero this _ _ _
  · rintro ⟨S, V⟩ ⟨hS, hV⟩
    have : Tendsto (fun kx : 𝕜 × E => kx.1 • kx.2) (𝓝 (0, 0)) (𝓝 <| (0 : 𝕜) • (0 : E)) :=
      continuous_smul.tendsto (0 : 𝕜 × E)
    rw [zero_smul, nhds_prod_eq] at this
    have := this hV
    rw [mem_map, mem_prod_iff] at this
    rcases this with ⟨U, hU, W, hW, hUW⟩
    refine' ⟨U, hU, ⟨S, W⟩, ⟨hS, hW⟩, _⟩
    rw [Set.smul_subset_iff]
    intro a ha u hu x hx
    rw [map_smul]
    exact hUW (⟨ha, hu x hx⟩ : (a, φ u x) ∈ U ×ˢ W)
  · rintro a ⟨S, V⟩ ⟨hS, hV⟩
    have : Tendsto (fun x : E => a • x) (𝓝 0) (𝓝 <| a • (0 : E)) := tendsto_id.const_smul a
    rw [smul_zero] at this
    refine' ⟨⟨S, (a • ·) ⁻¹' V⟩, ⟨hS, this hV⟩, fun f hf x hx => _⟩
    rw [map_smul]
    exact hf x hx
  · rintro u ⟨S, V⟩ ⟨hS, hV⟩
    rcases (h u S hS hV).exists_pos with ⟨r, hrpos, hr⟩
    rw [Metric.eventually_nhds_iff_ball]
    refine' ⟨r⁻¹, inv_pos.mpr hrpos, fun a ha x hx => _⟩
    by_cases ha0 : a = 0
    · rw [ha0]
      simpa using mem_of_mem_nhds hV
    · rw [mem_ball_zero_iff] at ha
      rw [map_smul, Pi.smul_apply]
      have : φ u x ∈ a⁻¹ • V := by
        have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr ha0
        refine' (hr a⁻¹ _) (Set.mem_image_of_mem (φ u) hx)
        rw [norm_inv, le_inv hrpos ha0]
        exact ha.le
      rwa [Set.mem_inv_smul_set_iff₀ ha0] at this
#align uniform_on_fun.has_continuous_smul_induced_of_image_bounded UniformOnFun.continuousSMul_induced_of_image_bounded

/-- Let `E` be a TVS, `𝔖 : Set (Set α)` and `H` a submodule of `α →ᵤ[𝔖] E`. If the image of any
`S ∈ 𝔖` by any `u ∈ H` is bounded (in the sense of `Bornology.IsVonNBounded`), then `H`,
equipped with the topology of `𝔖`-convergence, is a TVS.

If you have a hard time using this lemma, try the one above instead. -/
theorem UniformOnFun.continuousSMul_submodule_of_image_bounded (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) (H : Submodule 𝕜 (α →ᵤ[𝔖] E))
    (h : ∀ u ∈ H, ∀ s ∈ 𝔖, Bornology.IsVonNBounded 𝕜 (u '' s)) :
    @ContinuousSMul 𝕜 H _ _ ((UniformOnFun.topologicalSpace α E 𝔖).induced ((↑) : H → α →ᵤ[𝔖] E)) :=
  haveI : TopologicalAddGroup H :=
    topologicalAddGroup_induced (LinearMap.id.domRestrict H : H →ₗ[𝕜] α → E)
  UniformOnFun.continuousSMul_induced_of_image_bounded 𝕜 α E H h𝔖₁ h𝔖₂
    (LinearMap.id.domRestrict H : H →ₗ[𝕜] α → E) inducing_subtype_val fun ⟨u, hu⟩ => h u hu
#align uniform_on_fun.has_continuous_smul_submodule_of_image_bounded UniformOnFun.continuousSMul_submodule_of_image_bounded

end Module
