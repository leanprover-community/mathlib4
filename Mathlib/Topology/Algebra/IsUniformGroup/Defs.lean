/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Anatole Dedecker
-/
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.UniformSpace.DiscreteUniformity
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Uniform structure on topological groups

Given a topological group `G`, one can naturally build two uniform structures
(the "left" and "right" ones) on `G` inducing its topology.
This file defines typeclasses for groups equipped with either of these uniform strucure, as well
as a separate typeclass for the (very common) case where the given uniform structure
coincides with **both** the left and right uniform structures.

## Main declarations

* `IsRightUniformGroup` and `IsRightUniformAddGroup`: Multiplicative and topological additive groups
  endowed with the associated right uniform structure. This means that two points `x` and `y`
  are close precisely when `y * x⁻¹` is close to `1` / `y + (-x)` close to `0`.
* `IsLeftUniformGroup` and `IsLeftUniformAddGroup`: Multiplicative and topological additive groups
  endowed with the associated left uniform structure. This means that two points `x` and `y`
  are close precisely when `x⁻¹ * y` is close to `1` / `(-x) + y` close to `0`.
* `IsUniformGroup` and `IsUniformAddGroup`: Multiplicative and additive uniform groups,
  i.e., groups with uniformly continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`. This corresponds
  to the conjuction of the two conditions above, although this result is not in Mathlib yet.

## Main results

* `IsTopologicalAddGroup.toUniformSpace` and `comm_topologicalAddGroup_is_uniform` can be used
  to construct a canonical uniformity for a topological additive group.

See `Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean` for further results.

## Implementation Notes

Since the most frequent use case is `G` being a commutative additive groups, `Mathlib` originally
did essentially all the theory under the assumption `IsUniformGroup G`.
For this reason, you may find results stated under this assumption even though they may hold
under either `IsRightUniformGroup G` or `IsLeftUniformGroup G`.
-/

assert_not_exists Cauchy

noncomputable section

open Uniformity Topology Filter Pointwise

section LeftRight

open Filter Set

variable {G Gₗ Gᵣ Hₗ Hᵣ X : Type*}

/-- A **right-uniform additive group** is a topological additive group endowed with the associated
right uniform structure: the uniformity filter `𝓤 G` is the inverse image of `𝓝 0` by the map
`(x, y) ↦ y + (-x)`.

In other words, we declare that two points `x` and `y` are infinitely close
precisely when `y + (-x)` is infinitely close to `0`. -/
class IsRightUniformAddGroup (G : Type*) [UniformSpace G] [AddGroup G] : Prop
    extends IsTopologicalAddGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G ↦ x.2 + (-x.1)) (𝓝 0)

/-- A **right-uniform group** is a topological group endowed with the associated
right uniform structure: the uniformity filter `𝓤 G` is the inverse image of `𝓝 1` by the map
`(x, y) ↦ y * x⁻¹`.

In other words, we declare that two points `x` and `y` are infinitely close
precisely when `y * x⁻¹` is infinitely close to `1`. -/
@[to_additive]
class IsRightUniformGroup (G : Type*) [UniformSpace G] [Group G] : Prop
    extends IsTopologicalGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G ↦ x.2 * x.1⁻¹) (𝓝 1)

/-- A **left-uniform additive group** is a topological additive group endowed with the associated
left uniform structure: the uniformity filter `𝓤 G` is the inverse image of `𝓝 0` by the map
`(x, y) ↦ (-x) + y`.

In other words, we declare that two points `x` and `y` are infinitely close
precisely when `(-x) + y` is infinitely close to `0`. -/
class IsLeftUniformAddGroup (G : Type*) [UniformSpace G] [AddGroup G] : Prop
    extends IsTopologicalAddGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G ↦ (-x.1) + x.2) (𝓝 0)

/-- A **left-uniform group** is a topological group endowed with the associated
left uniform structure: the uniformity filter `𝓤 G` is the inverse image of `𝓝 1` by the map
`(x, y) ↦ x⁻¹ * y`.

In other words, we declare that two points `x` and `y` are infinitely close
precisely when `x⁻¹ * y` is infinitely close to `1`. -/
@[to_additive]
class IsLeftUniformGroup (G : Type*) [UniformSpace G] [Group G] : Prop
    extends IsTopologicalGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G ↦ x.1⁻¹ * x.2) (𝓝 1)

/-- `IsLeftOrRightUniformAddGroup G` means that we have either `IsRightUniformAddGroup G`
or `IsLeftUniformAddGroup G`. This is a purely utilitary typeclass to avoid duplicating
API for results common to the left and the right uniformity.

For example, `UniformContinuous.add_const` will eventually hold in this generality. -/
@[mk_iff]
class inductive IsLeftOrRightUniformAddGroup (G : Type*) [UniformSpace G] [AddGroup G] : Prop
| right [IsRightUniformAddGroup G] : IsLeftOrRightUniformAddGroup G
| left [IsLeftUniformAddGroup G] : IsLeftOrRightUniformAddGroup G

/-- `IsLeftOrRightUniformGroup G` means that we have either `IsRightUniformGroup G`
or `IsRightUniformGroup G`. This is a purely utilitary typeclass to avoid duplicating
API for results common to the left and the right uniformity.

For example, `UniformContinuous.mul_const` will eventually hold in this generality. -/
@[to_additive, mk_iff]
class inductive IsLeftOrRightUniformGroup (G : Type*) [UniformSpace G] [Group G] : Prop
| right [IsRightUniformGroup G] : IsLeftOrRightUniformGroup G
| left [IsLeftUniformGroup G] : IsLeftOrRightUniformGroup G

attribute [instance 10] IsRightUniformAddGroup.toIsTopologicalAddGroup
attribute [instance 10] IsRightUniformGroup.toIsTopologicalGroup
attribute [instance 10] IsLeftUniformAddGroup.toIsTopologicalAddGroup
attribute [instance 10] IsLeftUniformGroup.toIsTopologicalGroup

attribute [instance] IsLeftOrRightUniformAddGroup.left
attribute [instance] IsLeftOrRightUniformAddGroup.right
attribute [instance] IsLeftOrRightUniformGroup.left
attribute [instance] IsLeftOrRightUniformGroup.right

variable [UniformSpace G] [Group G] [IsLeftOrRightUniformGroup G]
variable [UniformSpace Gₗ] [UniformSpace Gᵣ] [Group Gₗ] [Group Gᵣ]
variable [UniformSpace Hₗ] [UniformSpace Hᵣ] [Group Hₗ] [Group Hᵣ]
variable [IsLeftUniformGroup Gₗ] [IsRightUniformGroup Gᵣ]
variable [IsLeftUniformGroup Hₗ] [IsRightUniformGroup Hᵣ]
variable [UniformSpace X]

/-- Note: We give this instance the lowest priority as any concrete type satisfying it will
have an instance of either `IsLeftUniformGroup` or `IsRightUniformGroup`.

In other words, this instance only appears in lemmas assuming `IsLeftOrRightUniformGroup G`. -/
@[to_additive /-- Note: We give this instance the lowest priority as any concrete type satisfying
it will have an instance of either `IsLeftUniformAddGroup` or `IsRightUniformAddGroup`.

In other words, this instance only appears in lemmas assuming `IsLeftOrRightUniformAddGroup G`. -/]
instance (priority := 0) : IsTopologicalGroup G := by
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
    IsRightUniformGroup (Gᵣ × Hᵣ) := by
  constructor
  simp_rw [uniformity_prod_eq_comap_prod, uniformity_eq_comap_mul_inv_nhds_one,
    Prod.one_eq_mk, nhds_prod_eq, comap_prod, comap_comap]
  rfl

@[to_additive]
instance Prod.instIsLeftUniformGroup :
    IsRightUniformGroup (Gᵣ × Hᵣ) := by
  constructor
  simp_rw [uniformity_prod_eq_comap_prod, uniformity_eq_comap_mul_inv_nhds_one,
    Prod.one_eq_mk, nhds_prod_eq, comap_prod, comap_comap]
  rfl

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

variable {G}

@[to_additive]
lemma isRightUniformGroup_iff_rightUniformSpace {G : Type*} [U : UniformSpace G] [Group G]
    [IsTopologicalGroup G] :
    IsRightUniformGroup G ↔ U = IsTopologicalGroup.rightUniformSpace G :=
  ⟨fun H ↦ by ext; rw [uniformity_eq_comap_mul_inv_nhds_one G]; rfl, fun H ↦ ⟨H ▸ rfl⟩⟩

@[to_additive]
theorem IsRightUniformGroup.rightUniformSpace_eq {G : Type*} [U : UniformSpace G] [Group G]
    [IsRightUniformGroup G] : IsTopologicalGroup.rightUniformSpace G = U := by
  rw [← isRightUniformGroup_iff_rightUniformSpace.mp inferInstance]

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

@[to_additive]
lemma isLeftUniformGroup_iff_leftUniformSpace {G : Type*} [U : UniformSpace G] [Group G]
    [IsTopologicalGroup G] :
    IsLeftUniformGroup G ↔ U = IsTopologicalGroup.leftUniformSpace G :=
  ⟨fun H ↦ by ext; rw [uniformity_eq_comap_inv_mul_nhds_one G]; rfl, fun H ↦ ⟨H ▸ rfl⟩⟩

@[to_additive]
theorem IsLeftUniformGroup.leftUniformSpace_eq {G : Type*} [U : UniformSpace G] [Group G]
    [IsLeftUniformGroup G] : IsTopologicalGroup.leftUniformSpace G = U := by
  rw [← isLeftUniformGroup_iff_leftUniformSpace.mp inferInstance]

attribute [local instance] IsTopologicalGroup.leftUniformSpace

@[to_additive]
instance : IsLeftUniformGroup G := ⟨rfl⟩

end Left

end IsTopologicalGroup

section IsUniformGroup

open Filter Set

variable {α : Type*} {β : Type*}

/-- A uniform group is a group in which multiplication and inversion are uniformly continuous.

`IsUniformGroup G` is equivalent to the fact that `G` is a topological group, and the uniformity
coincides with **both** the associated left and right uniformities
(see `IsUniformGroup.isRightUniformGroup`, `IsUniformGroup.isLeftUniformGroup` and
`IsUniformGroup.of_left_right`).

Since there are topological groups where these two uniformities do **not** coincide,
not all topological groups admit a uniform group structure in this sense. This is however the
case for commutative groups, which are the main motivation for the existence of this
typeclass. -/
class IsUniformGroup (α : Type*) [UniformSpace α] [Group α] : Prop where
  uniformContinuous_div : UniformContinuous fun p : α × α => p.1 / p.2

/-- A uniform additive group is an additive group in which addition and negation are
uniformly continuous.

`IsUniformAddGroup G` is equivalent to the fact that `G` is a topological additive group, and the
uniformity coincides with **both** the associated left and right uniformities
(see `IsUniformAddGroup.isRightUniformAddGroup`, `IsUniformAddGroup.isLeftUniformAddGroup` and
`IsUniformAddGroup.of_left_right`).

Since there are topological groups where these two uniformities do **not** coincide,
not all topological groups admit a uniform group structure in this sense. This is however the
case for commutative groups, which are the main motivation for the existence of this
typeclass. -/
class IsUniformAddGroup (α : Type*) [UniformSpace α] [AddGroup α] : Prop where
  uniformContinuous_sub : UniformContinuous fun p : α × α => p.1 - p.2

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

/-- If `f : ι → G × G` converges to the uniformity, then any `g : ι → G × G` converges to the
uniformity iff `f * g` does. This is often useful when `f` is valued in the diagonal,
in which case its convergence is automatic. -/
@[to_additive /-- If `f : ι → G × G` converges to the uniformity, then any `g : ι → G × G`
converges to the uniformity iff `f + g` does. This is often useful when `f` is valued in the
diagonal, in which case its convergence is automatic. -/]
theorem Filter.Tendsto.uniformity_mul_iff_right {ι : Type*} {f g : ι → α × α} {l : Filter ι}
    (hf : Tendsto f l (𝓤 α)) :
    Tendsto (f * g) l (𝓤 α) ↔ Tendsto g l (𝓤 α) :=
  ⟨fun hfg ↦ by simpa using hf.uniformity_inv.uniformity_mul hfg, hf.uniformity_mul⟩

/-- If `g : ι → G × G` converges to the uniformity, then any `f : ι → G × G` converges to the
uniformity iff `f * g` does. This is often useful when `g` is valued in the diagonal,
in which case its convergence is automatic. -/
@[to_additive /-- If `g : ι → G × G` converges to the uniformity, then any `f : ι → G × G`
converges to the uniformity iff `f + g` does. This is often useful when `g` is valued in the
diagonal, in which case its convergence is automatic. -/]
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

@[to_additive]
instance (priority := low) IsLeftOrRightUniformGroup.discreteUniformity [Group β] [UniformSpace β]
    [IsLeftOrRightUniformGroup β] [DiscreteTopology β] :
    DiscreteUniformity β := by
  rw [discreteUniformity_iff_eq_principal_idRel]
  rcases ‹IsLeftOrRightUniformGroup β›
  · rw [uniformity_eq_comap_mul_inv_nhds_one_swapped, nhds_discrete, comap_pure,
        principal_eq_iff_eq]
    ext ⟨x, y⟩
    simp [mul_inv_eq_one]
  · rw [uniformity_eq_comap_inv_mul_nhds_one, nhds_discrete, comap_pure,
        principal_eq_iff_eq]
    ext ⟨x, y⟩
    simp [inv_mul_eq_one]

theorem uniformity_translate_mul (a : α) : ((𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a)) = 𝓤 α :=
  le_antisymm (uniformContinuous_id.mul uniformContinuous_const)
    (calc
      𝓤 α =
          ((𝓤 α).map fun x : α × α => (x.1 * a⁻¹, x.2 * a⁻¹)).map fun x : α × α =>
            (x.1 * a, x.2 * a) := by simp [Filter.map_map, Function.comp_def]
      _ ≤ (𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a) :=
        Filter.map_mono (uniformContinuous_id.mul uniformContinuous_const)
      )

namespace MulOpposite

@[to_additive]
instance : IsUniformGroup αᵐᵒᵖ :=
  ⟨uniformContinuous_op.comp
      ((uniformContinuous_unop.comp uniformContinuous_snd).inv.mul <|
        uniformContinuous_unop.comp uniformContinuous_fst)⟩

end MulOpposite

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

@[to_additive]
theorem IsUniformGroup.ext_iff {G : Type*} [Group G] {u v : UniformSpace G}
    (hu : @IsUniformGroup G u _) (hv : @IsUniformGroup G v _) :
    u = v ↔ @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1 :=
  IsRightUniformGroup.ext_iff inferInstance inferInstance

end

section OfLeftAndRight

variable [UniformSpace β] [Group β] [IsLeftUniformGroup β] [IsRightUniformGroup β]

open Prod (snd) in
/-- Note: this assumes `[IsLeftUniformGroup β] [IsRightUniformGroup β]` instead of the more typical
(and equivalent) `[IsUniformGroup β]` because this is used in the proof of said equivalence. -/
@[to_additive /-- Note: this assumes `[IsLeftUniformAddGroup β] [IsRightUniformAddGroup β]`
instead of the more typical (and equivalent) `[IsUniformAddGroup β]` because this is used
in the proof of said equivalence. -/]
theorem comap_conj_nhds_one :
    comap (fun gx : β × β ↦ gx.1 * gx.2 * gx.1⁻¹) (𝓝 1) = comap snd (𝓝 1) := by
  let dr : β × β → β := fun xy ↦ xy.2 * xy.1⁻¹
  let dl : β × β → β := fun xy ↦ xy.1⁻¹ * xy.2
  let conj : β × β → β := fun gx ↦ gx.1 * gx.2 * gx.1⁻¹
  let φ : β × β ≃ β × β := (Equiv.refl β).prodShear (fun b ↦ (Equiv.mulLeft b).symm)
  have conj_φ : conj ∘ φ = dr := by
    ext; simp [conj, φ, dr]
  have snd_φ : snd ∘ φ = dl := by
    ext; simp [φ, dl]
  rw [← (comap_injective φ.surjective).eq_iff, comap_comap, comap_comap, conj_φ, snd_φ,
      ← uniformity_eq_comap_inv_mul_nhds_one, ← uniformity_eq_comap_mul_inv_nhds_one]

open Prod (snd) in
/-- Note: this assumes `[IsLeftUniformGroup β] [IsRightUniformGroup β]` instead of the more typical
(and equivalent) `[IsUniformGroup β]` because this is used in the proof of said equivalence. -/
@[to_additive /-- Note: this assumes `[IsLeftUniformAddGroup β] [IsRightUniformAddGroup β]`
instead of the more typical (and equivalent) `[IsUniformAddGroup β]` because this is used
in the proof of said equivalence. -/]
theorem tendsto_conj_nhds_one :
    Tendsto (fun gx : β × β ↦ gx.1 * gx.2 * gx.1⁻¹) (comap snd (𝓝 1)) (𝓝 1) := by
  rw [tendsto_iff_comap, comap_conj_nhds_one]

/-- Note: this assumes `[IsLeftUniformGroup β] [IsRightUniformGroup β]` instead of the more typical
(and equivalent) `[IsUniformGroup β]` because this is used in the proof of said equivalence. -/
@[to_additive /-- Note: this assumes `[IsLeftUniformAddGroup β] [IsRightUniformAddGroup β]`
instead of the more typical (and equivalent) `[IsUniformAddGroup β]` because this is used
in the proof of said equivalence. -/]
theorem Filter.Tendsto.conj_nhds_one {ι : Type*} {l : Filter ι} {x : ι → β}
    (hx : Tendsto x l (𝓝 1)) (g : ι → β) :
    Tendsto (g * x * g⁻¹) l (𝓝 1) := by
  have : Tendsto (fun i ↦ (g i, x i)) l (comap Prod.snd (𝓝 1)) := by
    rwa [tendsto_comap_iff]
  -- `exact` works but is quite slow...
  convert tendsto_conj_nhds_one.comp this

instance (priority := 10) IsUniformGroup.of_left_right : IsUniformGroup β where
  uniformContinuous_div := by
    let φ : (β × β) × (β × β) → β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ ↦ x₂ * y₂⁻¹ * y₁ * x₁⁻¹
    let ψ : (β × β) × (β × β) → β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ ↦ (x₁⁻¹ * x₂) * (y₂⁻¹ * y₁)
    let g : (β × β) × (β × β) → β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ ↦ x₁
    suffices Tendsto φ (𝓤 β ×ˢ 𝓤 β) (𝓝 1) by
      rw [UniformContinuous, uniformity_eq_comap_mul_inv_nhds_one β, tendsto_comap_iff,
        uniformity_prod_eq_prod, tendsto_map'_iff]
      simpa [Function.comp_def, div_eq_mul_inv, ← mul_assoc]
    have φ_ψ_conj : φ = g * ψ * g⁻¹ := by
      ext
      simp [φ, ψ, g, mul_assoc]
    have ψ_tendsto : Tendsto ψ (𝓤 β ×ˢ 𝓤 β) (𝓝 1) := by
      rw [← one_mul 1]
      refine .mul ?_ ?_
      · rw [uniformity_eq_comap_inv_mul_nhds_one]
        exact tendsto_comap.comp tendsto_fst
      · rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
        exact tendsto_comap.comp tendsto_snd
    exact φ_ψ_conj ▸ ψ_tendsto.conj_nhds_one g

theorem eventually_forall_conj_nhds_one {p : α → Prop}
    (hp : ∀ᶠ x in 𝓝 1, p x) :
    ∀ᶠ x in 𝓝 1, ∀ g, p (g * x * g⁻¹) := by
  simpa using tendsto_conj_nhds_one.eventually hp

end OfLeftAndRight

section OfComm

variable (G : Type*) [CommGroup G] [UniformSpace G] [IsLeftOrRightUniformGroup G]

@[to_additive]
instance (priority := 100) IsUniformGroup.of_comm : IsUniformGroup G := by
  rcases ‹IsLeftOrRightUniformGroup G›
  · have : IsLeftUniformGroup G := by
      constructor
      conv_rhs => congr; enter [x]; rw [mul_comm]
      exact uniformity_eq_comap_mul_inv_nhds_one G
    infer_instance
  · have : IsRightUniformGroup G := by
      constructor
      conv_rhs => congr; enter [x]; rw [mul_comm]
      exact uniformity_eq_comap_inv_mul_nhds_one G
    infer_instance

end OfComm

end IsUniformGroup

section TopologicalCommGroup

universe u v w x

open Filter

variable (G : Type*) [CommGroup G]

variable [TopologicalSpace G] [IsTopologicalGroup G]
section

attribute [local instance] IsTopologicalGroup.rightUniformSpace

variable {G}

@[to_additive (attr := deprecated IsUniformGroup.of_comm (since := "2025-09-26"))]
theorem isUniformGroup_of_commGroup : IsUniformGroup G := by
  infer_instance

alias comm_topologicalGroup_is_uniform := isUniformGroup_of_commGroup
open Set

end

@[to_additive (attr := deprecated IsRightUniformGroup.rightUniformSpace_eq (since := "2025-09-26"))]
alias IsUniformGroup.toUniformSpace_eq := IsRightUniformGroup.rightUniformSpace_eq

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
