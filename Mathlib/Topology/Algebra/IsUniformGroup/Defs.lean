/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Anatole Dedecker
-/
import Mathlib.Topology.UniformSpace.DiscreteUniformity
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Uniform structure on topological groups

This file defines uniform groups and its additive counterpart. These typeclasses should be
preferred over using `[TopologicalSpace α] [IsTopologicalGroup α]` since every topological
group naturally induces a uniform structure.

## Main declarations
* `IsUniformGroup` and `IsUniformAddGroup`: Multiplicative and additive uniform groups,
  i.e., groups with uniformly continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`.

## Main results

* `IsTopologicalAddGroup.toUniformSpace` and `comm_topologicalAddGroup_is_uniform` can be used
  to construct a canonical uniformity for a topological additive group.

See `Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean` for further results.
-/

assert_not_exists Cauchy

noncomputable section

open Uniformity Topology Filter Pointwise

section LeftRight

open Filter Set

variable {G Gₗ Gᵣ Hₗ Hᵣ X : Type*}

class IsRightUniformAddGroup (G : Type*) [UniformSpace G] [AddGroup G] : Prop
    extends IsTopologicalAddGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G ↦ x.2 + (-x.1)) (𝓝 0)

@[to_additive]
class IsRightUniformGroup (G : Type*) [UniformSpace G] [Group G] : Prop
    extends IsTopologicalGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G ↦ x.2 * x.1⁻¹) (𝓝 1)

class IsLeftUniformAddGroup (G : Type*) [UniformSpace G] [AddGroup G] : Prop
    extends IsTopologicalAddGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G ↦ (-x.1) + x.2) (𝓝 0)

@[to_additive]
class IsLeftUniformGroup (G : Type*) [UniformSpace G] [Group G] : Prop
    extends IsTopologicalGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G ↦ x.1⁻¹ * x.2) (𝓝 1)

class inductive IsLeftOrRightUniformAddGroup (G : Type*) [UniformSpace G] [AddGroup G]
| right [IsRightUniformAddGroup G] : IsLeftOrRightUniformAddGroup G
| left [IsLeftUniformAddGroup G] : IsLeftOrRightUniformAddGroup G

@[to_additive]
class inductive IsLeftOrRightUniformGroup (G : Type*) [UniformSpace G] [Group G]
| right [IsRightUniformGroup G] : IsLeftOrRightUniformGroup G
| left [IsLeftUniformGroup G] : IsLeftOrRightUniformGroup G

attribute [instance] IsLeftOrRightUniformAddGroup.left
attribute [instance] IsLeftOrRightUniformAddGroup.right
attribute [instance] IsLeftOrRightUniformGroup.left
attribute [instance] IsLeftOrRightUniformGroup.right

variable [Group G] [UniformSpace G] [IsLeftOrRightUniformGroup G]
variable [UniformSpace Gₗ] [UniformSpace Gᵣ] [Group Gₗ] [Group Gᵣ]
variable [UniformSpace Hₗ] [UniformSpace Hᵣ] [Group Hₗ] [Group Hᵣ]
variable [IsLeftUniformGroup Gₗ] [IsRightUniformGroup Gᵣ]
variable [IsLeftUniformGroup Hₗ] [IsRightUniformGroup Hᵣ]
variable [UniformSpace X]

@[to_additive]
instance : IsTopologicalGroup G := by
  rcases ‹IsLeftOrRightUniformGroup G› <;> infer_instance

variable (Gₗ Gᵣ)

@[to_additive]
lemma uniformity_eq_comap_mul_inv_nhds_one :
    𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ ↦ x.2 * x.1⁻¹) (𝓝 1) :=
  IsRightUniformGroup.uniformity_eq

@[to_additive]
lemma uniformity_eq_comap_inv_mul_nhds_one :
    𝓤 Gₗ = comap (fun x : Gₗ × Gₗ ↦ x.1⁻¹ * x.2) (𝓝 1) :=
  IsLeftUniformGroup.uniformity_eq

@[to_additive]
lemma uniformity_eq_comap_mul_inv_nhds_one_swapped :
    𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ ↦ x.1 * x.2⁻¹) (𝓝 1) := by
  rw [← comap_swap_uniformity, uniformity_eq_comap_mul_inv_nhds_one, comap_comap]
  rfl

@[to_additive]
lemma uniformity_eq_comap_inv_mul_nhds_one_swapped :
    𝓤 Gₗ = comap (fun x : Gₗ × Gₗ ↦ x.2⁻¹ * x.1) (𝓝 1) := by
  rw [← comap_swap_uniformity, uniformity_eq_comap_inv_mul_nhds_one, comap_comap]
  rfl

@[to_additive]
theorem uniformity_eq_comap_nhds_one : 𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.2 / x.1) (𝓝 1) := by
  simp_rw [div_eq_mul_inv]
  exact uniformity_eq_comap_mul_inv_nhds_one Gᵣ

@[to_additive]
theorem uniformity_eq_comap_nhds_one_swapped :
    𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.1 / x.2) (𝓝 1) := by
  rw [← comap_swap_uniformity, uniformity_eq_comap_nhds_one, comap_comap]
  rfl

variable {Gₗ Gᵣ}

namespace MulOpposite

/-
@[to_additive]
theorem isRightUniformGroup_iff [UniformSpace G] :
    IsRightUniformGroup (Gᵐᵒᵖ) ↔ IsLeftUniformGroup G := by
  constructor <;> intro
  · have : IsTopologicalGroup G :=
    -- TODO: extract this as lemma?
    { continuous_mul := continuous_unop.comp <| continuous_mul.comp <| continuous_swap.comp <|
        continuous_op.prodMap continuous_op
      continuous_inv := continuous_unop.comp <| continuous_op.inv }
    sorry
  · sorry
-/

@[to_additive]
instance : IsRightUniformGroup Gₗᵐᵒᵖ where
  uniformity_eq := by
    rw [uniformity_mulOpposite, ← op_one, ← comap_unop_nhds,
        uniformity_eq_comap_inv_mul_nhds_one, comap_comap, comap_comap]
    rfl

@[to_additive]
instance : IsLeftUniformGroup Gᵣᵐᵒᵖ where
  uniformity_eq := by
    rw [uniformity_mulOpposite, ← op_one, ← comap_unop_nhds,
      uniformity_eq_comap_mul_inv_nhds_one, comap_comap, comap_comap]
    rfl

@[to_additive]
instance : IsLeftOrRightUniformGroup Gᵐᵒᵖ := by
  rcases ‹IsLeftOrRightUniformGroup G› <;> infer_instance

end MulOpposite

@[to_additive]
theorem comap_mul_left_uniformity (g : G) :
    comap ((g, g) * ·) (𝓤 G) = 𝓤 G := by
  rcases ‹IsLeftOrRightUniformGroup G›
  · rw [uniformity_eq_comap_mul_inv_nhds_one, comap_comap]
    -- TODO: clean
    have : 𝓝 (1 : G) = comap (g * · * g⁻¹) (𝓝 1) := by
      conv_lhs =>
        rw [((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)).isInducing.nhds_eq_comap]
      congr
      simp
    conv_rhs => rw [this, comap_comap]
    congr 1
    ext ⟨x, y⟩
    simp [mul_assoc]
  · rw [uniformity_eq_comap_inv_mul_nhds_one, comap_comap]
    congr
    ext ⟨x, y⟩
    simp [mul_assoc]

open MulOpposite in
@[to_additive]
theorem comap_mul_right_uniformity (g : G) :
    comap (· * (g, g)) (𝓤 G) = 𝓤 G := by
  have := congr(comap (Prod.map op op) $(comap_mul_left_uniformity (op g)))
  rw [← comap_uniformity_mulOpposite, comap_comap]
  rw [comap_comap] at this
  exact this

@[to_additive]
theorem uniformContinuous_mul_right (g : G) : UniformContinuous ((· * g) : G → G) := by
  rw [UniformContinuous, tendsto_iff_comap]
  exact comap_mul_right_uniformity g |>.ge

@[to_additive]
theorem uniformContinuous_mul_left (g : G) : UniformContinuous ((g * ·) : G → G) := by
  rw [UniformContinuous, tendsto_iff_comap]
  exact comap_mul_left_uniformity g |>.ge

@[to_additive]
theorem UniformContinuous.mul_const {f : X → G} (hf : UniformContinuous f)
    (g : G) : UniformContinuous fun x ↦ f x * g :=
  uniformContinuous_mul_right g |>.comp hf

@[to_additive]
theorem UniformContinuous.const_mul {f : X → G} (hf : UniformContinuous f)
    (g : G) : UniformContinuous fun x ↦ g * f x :=
  uniformContinuous_mul_left g |>.comp hf

@[to_additive]
theorem uniformity_translate_mul (a : G) :
    ((𝓤 G).map fun x : G × G => (x.1 * a, x.2 * a)) = 𝓤 G := by
  conv_rhs => rw [← comap_mul_right_uniformity a⁻¹]
  refine map_eq_comap_of_inverse ?_ ?_ <;>
  ext <;>
  simp

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_mul_inv {ι} {p : ι → Prop} {U : ι → Set Gᵣ}
    (h : (𝓝 (1 : Gᵣ)).HasBasis p U) :
    (𝓤 Gᵣ).HasBasis p fun i => { x : Gᵣ × Gᵣ | x.2 * x.1⁻¹ ∈ U i } := by
  rw [uniformity_eq_comap_mul_inv_nhds_one]
  exact h.comap _

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul {ι} {p : ι → Prop} {U : ι → Set Gₗ}
    (h : (𝓝 (1 : Gₗ)).HasBasis p U) :
    (𝓤 Gₗ).HasBasis p fun i => { x : Gₗ × Gₗ | x.1⁻¹ * x.2 ∈ U i } := by
  rw [uniformity_eq_comap_inv_mul_nhds_one]
  exact h.comap _

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one {ι} {p : ι → Prop} {U : ι → Set Gᵣ}
    (h : (𝓝 (1 : Gᵣ)).HasBasis p U) :
    (𝓤 Gᵣ).HasBasis p fun i => { x : Gᵣ × Gᵣ | x.2 / x.1 ∈ U i } := by
  rw [uniformity_eq_comap_nhds_one]
  exact h.comap _

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_mul_inv_swapped {ι} {p : ι → Prop} {U : ι → Set Gᵣ}
    (h : (𝓝 (1 : Gᵣ)).HasBasis p U) :
    (𝓤 Gᵣ).HasBasis p fun i => { x : Gᵣ × Gᵣ | x.1 * x.2⁻¹ ∈ U i } := by
  rw [uniformity_eq_comap_mul_inv_nhds_one_swapped]
  exact h.comap _

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped {ι} {p : ι → Prop} {U : ι → Set Gₗ}
    (h : (𝓝 (1 : Gₗ)).HasBasis p U) :
    (𝓤 Gₗ).HasBasis p fun i => { x : Gₗ × Gₗ | x.2⁻¹ * x.1 ∈ U i } := by
  rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
  exact h.comap _

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_swapped {ι} {p : ι → Prop} {U : ι → Set Gᵣ}
    (h : (𝓝 (1 : Gᵣ)).HasBasis p U) :
    (𝓤 Gᵣ).HasBasis p fun i => { x : Gᵣ × Gᵣ | x.1 / x.2 ∈ U i } := by
  rw [uniformity_eq_comap_nhds_one_swapped]
  exact h.comap _

@[to_additive]
theorem IsRightUniformGroup.uniformContinuous_of_tendsto_one {hom : Type*}
    [FunLike hom Gᵣ Hᵣ] [MonoidHomClass hom Gᵣ Hᵣ] {f : hom} (h : Tendsto f (𝓝 1) (𝓝 1)) :
    UniformContinuous f := by
  rw [UniformContinuous, uniformity_eq_comap_mul_inv_nhds_one, uniformity_eq_comap_mul_inv_nhds_one,
    tendsto_comap_iff]
  convert h.comp tendsto_comap
  ext
  simp

export IsRightUniformGroup (uniformContinuous_of_tendsto_one)
export IsRightUniformAddGroup (uniformContinuous_of_tendsto_zero)

@[to_additive]
theorem IsLeftUniformGroup.uniformContinuous_of_tendsto_one {hom : Type*}
    [FunLike hom Gₗ Hₗ] [MonoidHomClass hom Gₗ Hₗ] {f : hom} (h : Tendsto f (𝓝 1) (𝓝 1)) :
    UniformContinuous f := by
  rw [UniformContinuous, uniformity_eq_comap_inv_mul_nhds_one, uniformity_eq_comap_inv_mul_nhds_one,
    tendsto_comap_iff]
  convert h.comp tendsto_comap
  ext
  simp

/-- A group homomorphism (a bundled morphism of a type that implements `MonoidHomClass`) between
two uniform groups is uniformly continuous provided that it is continuous at one. See also
`continuous_of_continuousAt_one`. -/
@[to_additive /-- An additive group homomorphism (a bundled morphism of a type that implements
`AddMonoidHomClass`) between two uniform additive groups is uniformly continuous provided that it
is continuous at zero. See also `continuous_of_continuousAt_zero`. -/]
theorem IsRightUniformGroup.uniformContinuous_of_continuousAt_one {hom : Type*}
    [FunLike hom Gᵣ Hᵣ] [MonoidHomClass hom Gᵣ Hᵣ]
    (f : hom) (hf : ContinuousAt f 1) :
    UniformContinuous f :=
  uniformContinuous_of_tendsto_one (by simpa using hf.tendsto)

export IsRightUniformGroup (uniformContinuous_of_continuousAt_one)

/-- A group homomorphism (a bundled morphism of a type that implements `MonoidHomClass`) between
two uniform groups is uniformly continuous provided that it is continuous at one. See also
`continuous_of_continuousAt_one`. -/
@[to_additive /-- An additive group homomorphism (a bundled morphism of a type that implements
`AddMonoidHomClass`) between two uniform additive groups is uniformly continuous provided that it
is continuous at zero. See also `continuous_of_continuousAt_zero`. -/]
theorem IsLeftUniformGroup.uniformContinuous_of_continuousAt_one {hom : Type*}
    [FunLike hom Gₗ Hₗ] [MonoidHomClass hom Gₗ Hₗ]
    (f : hom) (hf : ContinuousAt f 1) :
    UniformContinuous f :=
  uniformContinuous_of_tendsto_one (by simpa using hf.tendsto)

@[to_additive]
theorem MonoidHom.uniformContinuous_of_continuousAt_one
    (f : Gᵣ →* Hᵣ) (hf : ContinuousAt f 1) : UniformContinuous f :=
  IsRightUniformGroup.uniformContinuous_of_continuousAt_one f hf

/-- A homomorphism from a uniform group to a discrete uniform group is continuous if and only if
its kernel is open. -/
@[to_additive /-- A homomorphism from a uniform additive group to a discrete uniform additive group
is continuous if and only if its kernel is open. -/]
theorem IsRightUniformGroup.uniformContinuous_iff_isOpen_ker {hom : Type*} [FunLike hom Gᵣ Hᵣ]
    [MonoidHomClass hom Gᵣ Hᵣ] [DiscreteTopology Hᵣ] {f : hom} :
    UniformContinuous f ↔ IsOpen ((f : Gᵣ →* Hᵣ).ker : Set Gᵣ) := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · apply (isOpen_discrete ({1} : Set Hᵣ)).preimage hf.continuous
  · apply uniformContinuous_of_continuousAt_one
    rw [ContinuousAt, nhds_discrete Hᵣ, map_one, tendsto_pure]
    exact hf.mem_nhds (map_one f)

/-- A homomorphism from a uniform group to a discrete uniform group is continuous if and only if
its kernel is open. -/
@[to_additive /-- A homomorphism from a uniform additive group to a discrete uniform additive group
is continuous if and only if its kernel is open. -/]
theorem IsLeftUniformGroup.uniformContinuous_iff_isOpen_ker {hom : Type*} [FunLike hom Gₗ Hₗ]
    [MonoidHomClass hom Gₗ Hₗ] [DiscreteTopology Hₗ] {f : hom} :
    UniformContinuous f ↔ IsOpen ((f : Gₗ →* Hₗ).ker : Set Gₗ) := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · apply (isOpen_discrete ({1} : Set Hₗ)).preimage hf.continuous
  · apply uniformContinuous_of_continuousAt_one
    rw [ContinuousAt, nhds_discrete Hₗ, map_one, tendsto_pure]
    exact hf.mem_nhds (map_one f)

/-- A group homomorphism (a bundled morphism of a type that implements `MonoidHomClass`) between
two uniform groups is uniformly continuous provided that it is continuous at one. See also
`continuous_of_continuousAt_one`. -/
@[to_additive /-- An additive group homomorphism (a bundled morphism of a type that implements
`AddMonoidHomClass`) between two uniform additive groups is uniformly continuous provided that it
is continuous at zero. See also `continuous_of_continuousAt_zero`. -/]
theorem IsRightUniformGroup.uniformContinuous_of_continuous {hom : Type*}
    [FunLike hom Gᵣ Hᵣ] [MonoidHomClass hom Gᵣ Hᵣ]
    (f : hom) (hf : Continuous f) :
    UniformContinuous f :=
  uniformContinuous_of_continuousAt_one f hf.continuousAt

@[to_additive, deprecated (since := "2025-09-25")]
alias uniformContinuous_monoidHom_of_continuous :=
  IsRightUniformGroup.uniformContinuous_of_continuous

/-- A group homomorphism (a bundled morphism of a type that implements `MonoidHomClass`) between
two uniform groups is uniformly continuous provided that it is continuous at one. See also
`continuous_of_continuousAt_one`. -/
@[to_additive /-- An additive group homomorphism (a bundled morphism of a type that implements
`AddMonoidHomClass`) between two uniform additive groups is uniformly continuous provided that it
is continuous at zero. See also `continuous_of_continuousAt_zero`. -/]
theorem IsLeftUniformGroup.uniformContinuous_monoidHom_of_continuous {hom : Type*}
    [FunLike hom Gₗ Hₗ] [MonoidHomClass hom Gₗ Hₗ]
    (f : hom) (hf : ContinuousAt f 1) :
    UniformContinuous f :=
  uniformContinuous_of_tendsto_one (by simpa using hf.tendsto)

section LatticeOps

omit [UniformSpace G]

@[to_additive]
theorem isRightUniformGroup_iInf {ι : Sort*} {us' : ι → UniformSpace G}
    (h' : ∀ i, @IsRightUniformGroup G (us' i) _) : @IsRightUniformGroup G (⨅ i, us' i) _ := by
  let := ⨅ i, us' i
  have : IsTopologicalGroup G := by
    rw [UniformSpace.toTopologicalSpace_iInf]
    exact topologicalGroup_iInf fun u ↦ (h' u).toIsTopologicalGroup
  constructor
  simp_rw [iInf_uniformity, UniformSpace.toTopologicalSpace_iInf, nhds_iInf, comap_iInf,
    IsRightUniformGroup.uniformity_eq]

@[to_additive]
theorem isLeftUniformGroup_iInf {ι : Sort*} {us' : ι → UniformSpace G}
    (h' : ∀ i, @IsLeftUniformGroup G (us' i) _) : @IsLeftUniformGroup G (⨅ i, us' i) _ := by
  let := ⨅ i, us' i
  have : IsTopologicalGroup G := by
    rw [UniformSpace.toTopologicalSpace_iInf]
    exact topologicalGroup_iInf fun u ↦ (h' u).toIsTopologicalGroup
  constructor
  simp_rw [iInf_uniformity, UniformSpace.toTopologicalSpace_iInf, nhds_iInf, comap_iInf,
    IsLeftUniformGroup.uniformity_eq]

@[to_additive]
theorem isRightUniformGroup_sInf {us : Set (UniformSpace G)}
    (h : ∀ u ∈ us, @IsRightUniformGroup G u _) :
    @IsRightUniformGroup G (sInf us) _ := by
  rw [sInf_eq_iInf]
  exact isRightUniformGroup_iInf fun u ↦ isRightUniformGroup_iInf fun hu ↦ h u hu

@[to_additive]
theorem isLeftUniformGroup_sInf {us : Set (UniformSpace G)}
    (h : ∀ u ∈ us, @IsLeftUniformGroup G u _) :
    @IsLeftUniformGroup G (sInf us) _ := by
  rw [sInf_eq_iInf]
  exact isLeftUniformGroup_iInf fun u ↦ isLeftUniformGroup_iInf fun hu ↦ h u hu

@[to_additive]
theorem isRightUniformGroup_inf {u₁ u₂ : UniformSpace G} (h₁ : @IsRightUniformGroup G u₁ _)
    (h₂ : @IsRightUniformGroup G u₂ _) : @IsRightUniformGroup G (u₁ ⊓ u₂) _ := by
  rw [inf_eq_iInf]
  refine isRightUniformGroup_iInf fun b => ?_
  cases b <;> assumption

@[to_additive]
theorem isLeftUniformGroup_inf {u₁ u₂ : UniformSpace G} (h₁ : @IsLeftUniformGroup G u₁ _)
    (h₂ : @IsLeftUniformGroup G u₂ _) : @IsLeftUniformGroup G (u₁ ⊓ u₂) _ := by
  rw [inf_eq_iInf]
  refine isLeftUniformGroup_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps

section Constructions

@[to_additive]
instance Prod.instIsRightUniformGroup :
    IsRightUniformGroup (Gᵣ × Hᵣ) :=
  sorry

end Constructions

@[to_additive]
theorem IsRightUniformGroup.ext {G : Type*} [Group G] {u v : UniformSpace G}
    (hu : @IsRightUniformGroup G u _)
    (hv : @IsRightUniformGroup G v _)
    (h : @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1) : u = v :=
  UniformSpace.ext <| by
    rw [@uniformity_eq_comap_mul_inv_nhds_one _ u _ hu,
        @uniformity_eq_comap_mul_inv_nhds_one _ v _ hv, h]

@[to_additive]
theorem IsLeftUniformGroup.ext {G : Type*} [Group G] {u v : UniformSpace G}
    (hu : @IsLeftUniformGroup G u _)
    (hv : @IsLeftUniformGroup G v _)
    (h : @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1) : u = v :=
  UniformSpace.ext <| by
    rw [@uniformity_eq_comap_inv_mul_nhds_one _ u _ hu,
        @uniformity_eq_comap_inv_mul_nhds_one _ v _ hv, h]

@[to_additive]
theorem IsRightUniformGroup.ext_iff {G : Type*} [Group G] {u v : UniformSpace G}
    (hu : @IsRightUniformGroup G u _) (hv : @IsRightUniformGroup G v _) :
    u = v ↔ @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1 :=
  ⟨fun h => h ▸ rfl, hu.ext hv⟩

@[to_additive]
theorem IsLeftUniformGroup.ext_iff {G : Type*} [Group G] {u v : UniformSpace G}
    (hu : @IsLeftUniformGroup G u _) (hv : @IsLeftUniformGroup G v _) :
    u = v ↔ @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1 :=
  ⟨fun h => h ▸ rfl, hu.ext hv⟩

@[to_additive IsUniformAddGroup.uniformity_countably_generated]
theorem IsUniformGroup.uniformity_countably_generated
    [(𝓝 (1 : G)).IsCountablyGenerated] :
    (𝓤 G).IsCountablyGenerated := by
  rcases ‹IsLeftOrRightUniformGroup G› <;>
  [rw [uniformity_eq_comap_mul_inv_nhds_one]; rw [uniformity_eq_comap_inv_mul_nhds_one]] <;>
  exact Filter.comap.isCountablyGenerated _ _

@[deprecated (since := "2025-03-31")] alias UniformAddGroup.uniformity_countably_generated :=
  IsUniformAddGroup.uniformity_countably_generated
@[to_additive existing UniformAddGroup.uniformity_countably_generated, deprecated
  (since := "2025-03-31")] alias
  UniformGroup.uniformity_countably_generated := IsUniformGroup.uniformity_countably_generated

end LeftRight

section IsTopologicalGroup

open Filter

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Right

/-- The right uniformity on a topological group (as opposed to the left uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`IsUniformGroup` structure. Two important special cases where they _do_ coincide are for
commutative groups (see `isUniformGroup_of_commGroup`) and for compact groups (see
`topologicalGroup_is_uniform_of_compactSpace`). -/
@[to_additive /-- The right uniformity on a topological additive group (as opposed to the left
uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`IsUniformAddGroup` structure. Two important special cases where they _do_ coincide are for
commutative additive groups (see `isUniformAddGroup_of_addCommGroup`) and for compact
additive groups (see `topologicalAddGroup_is_uniform_of_compactSpace`). -/]
def IsTopologicalGroup.rightUniformSpace : UniformSpace G where
  uniformity := comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 1)
  symm :=
    have : Tendsto (fun p : G × G ↦ (p.2 * p.1⁻¹)⁻¹) (comap (fun p : G × G ↦ p.2 * p.1⁻¹) (𝓝 1))
      (𝓝 1⁻¹) := tendsto_id.inv.comp tendsto_comap
    by simpa [tendsto_comap_iff]
  comp := Tendsto.le_comap fun U H ↦ by
    rcases exists_nhds_one_split H with ⟨V, V_nhds, V_mul⟩
    refine mem_map.2 (mem_of_superset (mem_lift' <| preimage_mem_comap V_nhds) ?_)
    rintro ⟨x, y⟩ ⟨z, hz₁, hz₂⟩
    simpa [mul_assoc] using V_mul _ hz₂ _ hz₁
  nhds_eq_comap_uniformity _ := by
    simp only [comap_comap, Function.comp_def, ← div_eq_mul_inv, nhds_translation_div]

attribute [local instance] IsTopologicalGroup.rightUniformSpace

@[to_additive]
instance : IsRightUniformGroup G := ⟨rfl⟩

@[to_additive, deprecated (since := "2025-09-25")]
alias uniformity_eq_comap_nhds_one' := uniformity_eq_comap_nhds_one

end Right

section Left

/-- The right uniformity on a topological group (as opposed to the left uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`IsUniformGroup` structure. Two important special cases where they _do_ coincide are for
commutative groups (see `isUniformGroup_of_commGroup`) and for compact groups (see
`topologicalGroup_is_uniform_of_compactSpace`). -/
@[to_additive /-- The right uniformity on a topological additive group (as opposed to the left
uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`IsUniformAddGroup` structure. Two important special cases where they _do_ coincide are for
commutative additive groups (see `isUniformAddGroup_of_addCommGroup`) and for compact
additive groups (see `topologicalAddGroup_is_uniform_of_compactSpace`). -/]
def IsTopologicalGroup.leftUniformSpace : UniformSpace G where
  uniformity := comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1)
  symm :=
    have : Tendsto (fun p : G × G ↦ (p.1⁻¹ * p.2)⁻¹) (comap (fun p : G × G ↦ p.1⁻¹ * p.2) (𝓝 1))
      (𝓝 1⁻¹) := tendsto_id.inv.comp tendsto_comap
    by simpa [tendsto_comap_iff]
  comp := Tendsto.le_comap fun U H ↦ by
    rcases exists_nhds_one_split H with ⟨V, V_nhds, V_mul⟩
    refine mem_map.2 (mem_of_superset (mem_lift' <| preimage_mem_comap V_nhds) ?_)
    rintro ⟨x, y⟩ ⟨z, hz₁, hz₂⟩
    simpa [mul_assoc] using V_mul _ hz₁ _ hz₂
  nhds_eq_comap_uniformity _ := by
    sorry

attribute [local instance] IsTopologicalGroup.leftUniformSpace

@[to_additive]
instance : IsLeftUniformGroup G := ⟨rfl⟩

end Left

end IsTopologicalGroup

section IsUniformGroup

open Filter Set

variable {α : Type*} {β : Type*}

/-- A uniform group is a group in which multiplication and inversion are uniformly continuous. -/
class IsUniformGroup (α : Type*) [UniformSpace α] [Group α] : Prop where
  uniformContinuous_div : UniformContinuous fun p : α × α => p.1 / p.2

@[deprecated (since := "2025-03-26")] alias UniformGroup := IsUniformGroup

/-- A uniform additive group is an additive group in which addition
  and negation are uniformly continuous. -/
class IsUniformAddGroup (α : Type*) [UniformSpace α] [AddGroup α] : Prop where
  uniformContinuous_sub : UniformContinuous fun p : α × α => p.1 - p.2

@[deprecated (since := "2025-03-26")] alias UniformAddGroup := IsUniformAddGroup

attribute [to_additive] IsUniformGroup

@[to_additive]
theorem IsUniformGroup.mk' {α} [UniformSpace α] [Group α]
    (h₁ : UniformContinuous fun p : α × α => p.1 * p.2) (h₂ : UniformContinuous fun p : α => p⁻¹) :
    IsUniformGroup α :=
  ⟨by simpa only [div_eq_mul_inv] using
    h₁.comp (uniformContinuous_fst.prodMk (h₂.comp uniformContinuous_snd))⟩

variable [UniformSpace α] [Group α] [IsUniformGroup α]

@[to_additive]
theorem uniformContinuous_div : UniformContinuous fun p : α × α => p.1 / p.2 :=
  IsUniformGroup.uniformContinuous_div

@[to_additive]
theorem UniformContinuous.div [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x / g x :=
  uniformContinuous_div.comp (hf.prodMk hg)

@[to_additive]
theorem UniformContinuous.inv [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    UniformContinuous fun x => (f x)⁻¹ := by
  have : UniformContinuous fun x => 1 / f x := uniformContinuous_const.div hf
  simp_all

@[to_additive]
theorem uniformContinuous_inv : UniformContinuous fun x : α => x⁻¹ :=
  uniformContinuous_id.inv

@[to_additive]
theorem UniformContinuous.mul [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x * g x := by
  have : UniformContinuous fun x => f x / (g x)⁻¹ := hf.div hg.inv
  simp_all

@[to_additive]
theorem uniformContinuous_mul : UniformContinuous fun p : α × α => p.1 * p.2 :=
  uniformContinuous_fst.mul uniformContinuous_snd

@[to_additive]
theorem UniformContinuous.div_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f)
    (a : α) : UniformContinuous fun x ↦ f x / a :=
  hf.div uniformContinuous_const

@[to_additive]
theorem uniformContinuous_div_const (a : α) : UniformContinuous fun b : α => b / a :=
  uniformContinuous_id.div_const _

@[to_additive]
theorem Filter.Tendsto.uniformity_mul {ι : Type*} {f g : ι → α × α} {l : Filter ι}
    (hf : Tendsto f l (𝓤 α)) (hg : Tendsto g l (𝓤 α)) :
    Tendsto (f * g) l (𝓤 α) :=
  have : Tendsto (fun (p : (α × α) × (α × α)) ↦ p.1 * p.2) (𝓤 α ×ˢ 𝓤 α) (𝓤 α) := by
    simpa [UniformContinuous, uniformity_prod_eq_prod] using uniformContinuous_mul (α := α)
  this.comp (hf.prodMk hg)

@[to_additive]
theorem Filter.Tendsto.uniformity_inv {ι : Type*} {f : ι → α × α} {l : Filter ι}
    (hf : Tendsto f l (𝓤 α)) :
    Tendsto (f⁻¹) l (𝓤 α) :=
  have : Tendsto (· ⁻¹) (𝓤 α) (𝓤 α) := uniformContinuous_inv
  this.comp hf

@[to_additive]
theorem Filter.Tendsto.uniformity_inv_iff {ι : Type*} {f : ι → α × α} {l : Filter ι} :
    Tendsto (f⁻¹) l (𝓤 α) ↔ Tendsto f l (𝓤 α) :=
  ⟨fun H ↦ inv_inv f ▸ H.uniformity_inv, Filter.Tendsto.uniformity_inv⟩

@[to_additive]
theorem Filter.Tendsto.uniformity_div {ι : Type*} {f g : ι → α × α} {l : Filter ι}
    (hf : Tendsto f l (𝓤 α)) (hg : Tendsto g l (𝓤 α)) :
    Tendsto (f / g) l (𝓤 α) := by
  rw [div_eq_mul_inv]
  exact hf.uniformity_mul hg.uniformity_inv

@[to_additive]
theorem Filter.Tendsto.uniformity_mul_iff_right {ι : Type*} {f g : ι → α × α} {l : Filter ι}
    (hf : Tendsto f l (𝓤 α)) :
    Tendsto (f * g) l (𝓤 α) ↔ Tendsto g l (𝓤 α) :=
  ⟨fun hfg ↦ by simpa using hf.uniformity_inv.uniformity_mul hfg, hf.uniformity_mul⟩

@[to_additive]
theorem Filter.Tendsto.uniformity_mul_iff_left {ι : Type*} {f g : ι → α × α} {l : Filter ι}
    (hg : Tendsto g l (𝓤 α)) :
    Tendsto (f * g) l (𝓤 α) ↔ Tendsto f l (𝓤 α) :=
  ⟨fun hfg ↦ by simpa using hfg.uniformity_mul hg.uniformity_inv, fun hf ↦ hf.uniformity_mul hg⟩

@[to_additive UniformContinuous.const_nsmul]
theorem UniformContinuous.pow_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    ∀ n : ℕ, UniformContinuous fun x => f x ^ n
  | 0 => by
    simp_rw [pow_zero]
    exact uniformContinuous_const
  | n + 1 => by
    simp_rw [pow_succ']
    exact hf.mul (hf.pow_const n)

@[to_additive uniformContinuous_const_nsmul]
theorem uniformContinuous_pow_const (n : ℕ) : UniformContinuous fun x : α => x ^ n :=
  uniformContinuous_id.pow_const n

@[to_additive UniformContinuous.const_zsmul]
theorem UniformContinuous.zpow_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    ∀ n : ℤ, UniformContinuous fun x => f x ^ n
  | (n : ℕ) => by
    simp_rw [zpow_natCast]
    exact hf.pow_const _
  | Int.negSucc n => by
    simp_rw [zpow_negSucc]
    exact (hf.pow_const _).inv

@[to_additive uniformContinuous_const_zsmul]
theorem uniformContinuous_zpow_const (n : ℤ) : UniformContinuous fun x : α => x ^ n :=
  uniformContinuous_id.zpow_const n

@[to_additive]
instance (priority := 10) IsUniformGroup.to_topologicalGroup : IsTopologicalGroup α where
  continuous_mul := uniformContinuous_mul.continuous
  continuous_inv := uniformContinuous_inv.continuous

@[deprecated (since := "2025-03-31")] alias UniformGroup.to_topologicalAddGroup :=
  IsUniformAddGroup.to_topologicalAddGroup
@[to_additive existing, deprecated
  (since := "2025-03-31")] alias
  UniformGroup.to_topologicalGroup := IsUniformGroup.to_topologicalGroup

@[to_additive]
instance Prod.instIsUniformGroup [UniformSpace β] [Group β] [IsUniformGroup β] :
    IsUniformGroup (α × β) :=
  ⟨((uniformContinuous_fst.comp uniformContinuous_fst).div
          (uniformContinuous_fst.comp uniformContinuous_snd)).prodMk
      ((uniformContinuous_snd.comp uniformContinuous_fst).div
        (uniformContinuous_snd.comp uniformContinuous_snd))⟩

@[deprecated (since := "2025-03-31")] alias Prod.instUniformAddGroup :=
  Prod.instIsUniformAddGroup
@[to_additive existing, deprecated
  (since := "2025-03-31")] alias Prod.instUniformGroup := Prod.instIsUniformGroup

/-- The discrete uniformity makes a group a `IsUniformGroup. -/
@[to_additive /-- The discrete uniformity makes an additive group a `IsUniformAddGroup`. -/]
instance [UniformSpace β] [Group β] [DiscreteUniformity β] : IsUniformGroup β where
  uniformContinuous_div := DiscreteUniformity.uniformContinuous (β × β) fun p ↦ p.1 / p.2

namespace MulOpposite

@[to_additive]
instance : IsUniformGroup αᵐᵒᵖ :=
  ⟨uniformContinuous_op.comp
      ((uniformContinuous_unop.comp uniformContinuous_snd).inv.mul <|
        uniformContinuous_unop.comp uniformContinuous_fst)⟩

end MulOpposite

section LatticeOps

variable [Group β]

@[to_additive]
theorem isUniformGroup_sInf {us : Set (UniformSpace β)} (h : ∀ u ∈ us, @IsUniformGroup β u _) :
    @IsUniformGroup β (sInf us) _ :=
  @IsUniformGroup.mk β (_) _ <|
    uniformContinuous_sInf_rng.mpr fun u hu =>
      uniformContinuous_sInf_dom₂ hu hu (@IsUniformGroup.uniformContinuous_div β u _ (h u hu))

@[deprecated (since := "2025-03-31")] alias uniformAddGroup_sInf := isUniformAddGroup_sInf
@[to_additive existing, deprecated
  (since := "2025-03-31")] alias uniformGroup_sInf := isUniformGroup_sInf

@[to_additive]
theorem isUniformGroup_iInf {ι : Sort*} {us' : ι → UniformSpace β}
    (h' : ∀ i, @IsUniformGroup β (us' i) _) : @IsUniformGroup β (⨅ i, us' i) _ := by
  rw [← sInf_range]
  exact isUniformGroup_sInf (Set.forall_mem_range.mpr h')

@[deprecated (since := "2025-03-31")] alias uniformAddGroup_iInf := isUniformAddGroup_iInf
@[to_additive existing, deprecated
  (since := "2025-03-31")] alias uniformGroup_iInf := isUniformGroup_iInf

@[to_additive]
theorem isUniformGroup_inf {u₁ u₂ : UniformSpace β} (h₁ : @IsUniformGroup β u₁ _)
    (h₂ : @IsUniformGroup β u₂ _) : @IsUniformGroup β (u₁ ⊓ u₂) _ := by
  rw [inf_eq_iInf]
  refine isUniformGroup_iInf fun b => ?_
  cases b <;> assumption

@[deprecated (since := "2025-03-31")] alias uniformAddGroup_inf := isUniformAddGroup_inf
@[to_additive existing, deprecated
  (since := "2025-03-31")] alias uniformGroup_inf := isUniformGroup_inf

end LatticeOps

section

@[to_additive]
instance IsUniformGroup.isRightUniformGroup : IsRightUniformGroup α where
  uniformity_eq := by
    refine eq_of_forall_le_iff fun 𝓕 ↦ ?_
    rw [nhds_eq_comap_uniformity, comap_comap, ← tendsto_iff_comap,
      ← (tendsto_diag_uniformity Prod.fst 𝓕).uniformity_mul_iff_left, ← tendsto_id']
    congrm Tendsto ?_ _ _
    ext <;> simp

@[to_additive]
instance IsUniformGroup.isLeftUniformGroup : IsLeftUniformGroup α where
  uniformity_eq := by
    refine eq_of_forall_le_iff fun 𝓕 ↦ ?_
    rw [nhds_eq_comap_uniformity, comap_comap, ← tendsto_iff_comap,
      ← (tendsto_diag_uniformity Prod.fst 𝓕).uniformity_mul_iff_right, ← tendsto_id']
    congrm Tendsto ?_ _ _
    ext <;> simp

@[to_additive]
theorem IsUniformGroup.ext {G : Type*} [Group G] {u v : UniformSpace G} (hu : @IsUniformGroup G u _)
    (hv : @IsUniformGroup G v _)
    (h : @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1) : u = v :=
  IsRightUniformGroup.ext inferInstance inferInstance h

@[deprecated (since := "2025-03-31")] alias UniformAddGroup.ext := IsUniformAddGroup.ext
@[to_additive existing UniformAddGroup.ext, deprecated (since := "2025-03-31")] alias
  UniformGroup.ext := IsUniformGroup.ext

@[to_additive]
theorem IsUniformGroup.ext_iff {G : Type*} [Group G] {u v : UniformSpace G}
    (hu : @IsUniformGroup G u _) (hv : @IsUniformGroup G v _) :
    u = v ↔ @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1 :=
  IsRightUniformGroup.ext_iff inferInstance inferInstance

@[deprecated (since := "2025-03-31")] alias UniformAddGroup.ext_iff :=
  IsUniformAddGroup.ext_iff
@[to_additive existing UniformAddGroup.ext_iff, deprecated (since := "2025-03-31")] alias
  UniformGroup.ext_iff := IsUniformGroup.ext_iff

end

section OfLeftAndRight

variable [UniformSpace β] [Group β] [IsLeftUniformGroup β] [IsRightUniformGroup β]

open Prod (snd) in
/-- Note: this assumes `[IsLeftUniformGroup β] [IsRightUniformGroup β]` instead of the more typical
(and equivalent) `[IsUniformGroup β]` because this is used in the proof of said equivalence. -/
@[to_additive /-- Note: this assumes `[IsLeftUniformAddGroup β] [IsRightUniformAddGroup β]`
instead of the more typical (and equivalent) `[IsUniformAddGroup β]` because this is used
in the proof of said equivalence. -/]
theorem tendsto_conj_comap_nhds_one :
    Tendsto (fun gx : β × β ↦ gx.1 * gx.2 * gx.1⁻¹) (comap snd (𝓝 1)) (𝓝 1) := by
  let φ : β × β → β := fun gx ↦ gx.1 * gx.2 * gx.1⁻¹
  let ψ : β × β ≃ β × β := (Equiv.refl β).prodShear (fun b ↦ Equiv.mulLeft b)
  have φ_comp_ψ_inv : φ ∘ ψ.symm = fun gx ↦ gx.2 * gx.1⁻¹ := by ext; simp [φ, ψ]
  have : comap snd (𝓝 1) = map ψ.symm (𝓤 β) := by
    rw [← map_inj ψ.injective, map_map, ψ.self_comp_symm, map_id, ← comap_equiv_symm,
        comap_comap, uniformity_eq_comap_inv_mul_nhds_one]
    rfl
  rw [this, tendsto_map'_iff, uniformity_eq_comap_mul_inv_nhds_one, φ_comp_ψ_inv]
  exact tendsto_comap

open Prod (fst snd) in
@[to_additive]
instance (priority := 100) IsUniformGroup.ofLeftRight : IsUniformGroup β where
  uniformContinuous_div := by
    let φ : (β × β) × (β × β) → β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ ↦ x₂ * y₂⁻¹ * y₁ * x₁⁻¹
    let ψ : (β × β) × (β × β) → β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ ↦ (x₁⁻¹ * x₂) * (y₂⁻¹ * y₁)
    let conj : β × β → β := fun gx ↦ gx.1 * gx.2 * gx.1⁻¹
    suffices Tendsto φ (𝓤 β ×ˢ 𝓤 β) (𝓝 1) by
      rw [UniformContinuous, uniformity_eq_comap_mul_inv_nhds_one β, tendsto_comap_iff,
        uniformity_prod_eq_prod, tendsto_map'_iff]
      simpa [Function.comp_def, div_eq_mul_inv, ← mul_assoc]
    have φ_ψ_conj : φ = conj ∘ (fun xy ↦ ⟨xy.1.1, ψ xy⟩) := by
      ext
      simp [φ, ψ, conj, mul_assoc]
    rw [φ_ψ_conj]
    refine tendsto_conj_comap_nhds_one.comp ?_
    rw [tendsto_comap_iff, ← one_mul 1]
    refine .mul ?_ ?_
    · rw [uniformity_eq_comap_inv_mul_nhds_one]
      exact tendsto_comap.comp tendsto_fst
    · rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
      exact tendsto_comap.comp tendsto_snd

theorem eventually_forall_conj_nhds_one {p : α → Prop}
    (hp : ∀ᶠ x in 𝓝 1, p x) :
    ∀ᶠ x in 𝓝 1, ∀ g, p (g * x * g⁻¹) := by
  simpa using tendsto_conj_comap_nhds_one.eventually hp

end OfLeftAndRight

end IsUniformGroup

section TopologicalCommGroup

universe u v w x

open Filter

variable (G : Type*) [CommGroup G]

variable [TopologicalSpace G] [IsTopologicalGroup G]
section

attribute [local instance] IsTopologicalGroup.toUniformSpace

variable {G}

@[to_additive]
theorem isUniformGroup_of_commGroup : IsUniformGroup G := by
  constructor
  simp only [UniformContinuous, uniformity_prod_eq_prod, uniformity_eq_comap_nhds_one',
    tendsto_comap_iff, tendsto_map'_iff, prod_comap_comap_eq, Function.comp_def,
    div_div_div_comm _ (Prod.snd (Prod.snd _)), ← nhds_prod_eq]
  exact (continuous_div'.tendsto' 1 1 (div_one 1)).comp tendsto_comap

alias comm_topologicalGroup_is_uniform := isUniformGroup_of_commGroup
@[deprecated (since := "2025-03-30")]
alias uniformAddGroup_of_addCommGroup := isUniformAddGroup_of_addCommGroup
@[to_additive existing, deprecated (since := "2025-03-30")]
alias uniformGroup_of_commGroup := isUniformGroup_of_commGroup

open Set

end

@[to_additive]
theorem IsUniformGroup.toUniformSpace_eq {G : Type*} [u : UniformSpace G] [Group G]
    [IsUniformGroup G] : IsTopologicalGroup.toUniformSpace G = u := by
  ext : 1
  rw [uniformity_eq_comap_nhds_one' G, uniformity_eq_comap_nhds_one G]

end TopologicalCommGroup

open Filter Set Function

section

variable {α : Type*} {β : Type*} {hom : Type*}
variable [TopologicalSpace α] [Group α] [IsTopologicalGroup α]

-- β is a dense subgroup of α, inclusion is denoted by e
variable [TopologicalSpace β] [Group β]
variable [FunLike hom β α] [MonoidHomClass hom β α] {e : hom}

@[to_additive]
theorem tendsto_div_comap_self (de : IsDenseInducing e) (x₀ : α) :
    Tendsto (fun t : β × β => t.2 / t.1) ((comap fun p : β × β => (e p.1, e p.2)) <| 𝓝 (x₀, x₀))
      (𝓝 1) := by
  have comm : ((fun x : α × α => x.2 / x.1) ∘ fun t : β × β => (e t.1, e t.2)) =
      e ∘ fun t : β × β => t.2 / t.1 := by
    ext t
    simp
  have lim : Tendsto (fun x : α × α => x.2 / x.1) (𝓝 (x₀, x₀)) (𝓝 (e 1)) := by
    simpa using (continuous_div'.comp (@continuous_swap α α _ _)).tendsto (x₀, x₀)
  simpa using de.tendsto_comap_nhds_nhds lim comm

end

namespace IsDenseInducing

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variable {G : Type*}

-- β is a dense subgroup of α, inclusion is denoted by e
-- δ is a dense subgroup of γ, inclusion is denoted by f
variable [TopologicalSpace α] [AddCommGroup α] [IsTopologicalAddGroup α]
variable [TopologicalSpace β] [AddCommGroup β]
variable [TopologicalSpace γ] [AddCommGroup γ] [IsTopologicalAddGroup γ]
variable [TopologicalSpace δ] [AddCommGroup δ]
variable [UniformSpace G] [AddCommGroup G]
variable {e : β →+ α} (de : IsDenseInducing e)
variable {f : δ →+ γ} (df : IsDenseInducing f)
variable {φ : β →+ δ →+ G}
variable (hφ : Continuous (fun p : β × δ => φ p.1 p.2))
variable {W' : Set G} (W'_nhds : W' ∈ 𝓝 (0 : G))
include de hφ

include W'_nhds in
private theorem extend_Z_bilin_aux (x₀ : α) (y₁ : δ) : ∃ U₂ ∈ comap e (𝓝 x₀), ∀ x ∈ U₂, ∀ x' ∈ U₂,
    (fun p : β × δ => φ p.1 p.2) (x' - x, y₁) ∈ W' := by
  let Nx := 𝓝 x₀
  let ee := fun u : β × β => (e u.1, e u.2)
  have lim1 : Tendsto (fun a : β × β => (a.2 - a.1, y₁))
      (comap e Nx ×ˢ comap e Nx) (𝓝 (0, y₁)) := by
    have := (tendsto_sub_comap_self de x₀).prodMk
      (tendsto_const_nhds : Tendsto (fun _ : β × β => y₁) (comap ee <| 𝓝 (x₀, x₀)) (𝓝 y₁))
    rw [nhds_prod_eq, prod_comap_comap_eq, ← nhds_prod_eq]
    exact (this :)
  have lim2 : Tendsto (fun p : β × δ => φ p.1 p.2) (𝓝 (0, y₁)) (𝓝 0) := by
    simpa using hφ.tendsto (0, y₁)
  have lim := lim2.comp lim1
  rw [tendsto_prod_self_iff] at lim
  simp_rw [forall_mem_comm]
  exact lim W' W'_nhds

variable [IsUniformAddGroup G]

include df W'_nhds in
private theorem extend_Z_bilin_key (x₀ : α) (y₀ : γ) : ∃ U ∈ comap e (𝓝 x₀), ∃ V ∈ comap f (𝓝 y₀),
    ∀ x ∈ U, ∀ x' ∈ U, ∀ (y) (_ : y ∈ V) (y') (_ : y' ∈ V),
    (fun p : β × δ => φ p.1 p.2) (x', y') - (fun p : β × δ => φ p.1 p.2) (x, y) ∈ W' := by
  let ee := fun u : β × β => (e u.1, e u.2)
  let ff := fun u : δ × δ => (f u.1, f u.2)
  have lim_φ : Filter.Tendsto (fun p : β × δ => φ p.1 p.2) (𝓝 (0, 0)) (𝓝 0) := by
    simpa using hφ.tendsto (0, 0)
  have lim_φ_sub_sub :
    Tendsto (fun p : (β × β) × δ × δ => (fun p : β × δ => φ p.1 p.2) (p.1.2 - p.1.1, p.2.2 - p.2.1))
      ((comap ee <| 𝓝 (x₀, x₀)) ×ˢ (comap ff <| 𝓝 (y₀, y₀))) (𝓝 0) := by
    have lim_sub_sub :
      Tendsto (fun p : (β × β) × δ × δ => (p.1.2 - p.1.1, p.2.2 - p.2.1))
        (comap ee (𝓝 (x₀, x₀)) ×ˢ comap ff (𝓝 (y₀, y₀))) (𝓝 0 ×ˢ 𝓝 0) := by
      have := Filter.prod_mono (tendsto_sub_comap_self de x₀) (tendsto_sub_comap_self df y₀)
      rwa [prod_map_map_eq] at this
    rw [← nhds_prod_eq] at lim_sub_sub
    exact Tendsto.comp lim_φ lim_sub_sub
  rcases exists_nhds_zero_quarter W'_nhds with ⟨W, W_nhds, W4⟩
  have :
    ∃ U₁ ∈ comap e (𝓝 x₀), ∃ V₁ ∈ comap f (𝓝 y₀), ∀ (x) (_ : x ∈ U₁) (x') (_ : x' ∈ U₁),
      ∀ (y) (_ : y ∈ V₁) (y') (_ : y' ∈ V₁), (fun p : β × δ => φ p.1 p.2) (x' - x, y' - y) ∈ W := by
    rcases tendsto_prod_iff.1 lim_φ_sub_sub W W_nhds with ⟨U, U_in, V, V_in, H⟩
    rw [nhds_prod_eq, ← prod_comap_comap_eq, mem_prod_same_iff] at U_in V_in
    rcases U_in with ⟨U₁, U₁_in, HU₁⟩
    rcases V_in with ⟨V₁, V₁_in, HV₁⟩
    exists U₁, U₁_in, V₁, V₁_in
    intro x x_in x' x'_in y y_in y' y'_in
    exact H _ _ (HU₁ (mk_mem_prod x_in x'_in)) (HV₁ (mk_mem_prod y_in y'_in))
  rcases this with ⟨U₁, U₁_nhds, V₁, V₁_nhds, H⟩
  obtain ⟨x₁, x₁_in⟩ : U₁.Nonempty := (de.comap_nhds_neBot _).nonempty_of_mem U₁_nhds
  obtain ⟨y₁, y₁_in⟩ : V₁.Nonempty := (df.comap_nhds_neBot _).nonempty_of_mem V₁_nhds
  have cont_flip : Continuous fun p : δ × β => φ.flip p.1 p.2 := by
    change Continuous ((fun p : β × δ => φ p.1 p.2) ∘ Prod.swap)
    exact hφ.comp continuous_swap
  rcases extend_Z_bilin_aux de hφ W_nhds x₀ y₁ with ⟨U₂, U₂_nhds, HU⟩
  rcases extend_Z_bilin_aux df cont_flip W_nhds y₀ x₁ with ⟨V₂, V₂_nhds, HV⟩
  exists U₁ ∩ U₂, inter_mem U₁_nhds U₂_nhds, V₁ ∩ V₂, inter_mem V₁_nhds V₂_nhds
  rintro x ⟨xU₁, xU₂⟩ x' ⟨x'U₁, x'U₂⟩ y ⟨yV₁, yV₂⟩ y' ⟨y'V₁, y'V₂⟩
  have key_formula : φ x' y' - φ x y
    = φ (x' - x) y₁ + φ (x' - x) (y' - y₁) + φ x₁ (y' - y) + φ (x - x₁) (y' - y) := by simp; abel
  rw [key_formula]
  have h₁ := HU x xU₂ x' x'U₂
  have h₂ := H x xU₁ x' x'U₁ y₁ y₁_in y' y'V₁
  have h₃ := HV y yV₂ y' y'V₂
  have h₄ := H x₁ x₁_in x xU₁ y yV₁ y' y'V₁
  exact W4 h₁ h₂ h₃ h₄

end IsDenseInducing
