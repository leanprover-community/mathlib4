/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Anatole Dedecker
-/
import Mathlib.Topology.UniformSpace.Basic
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

end LeftRight

section IsUniformGroup

open Filter Set

variable {α : Type*} {β : Type*}

/-- A uniform group is a group in which multiplication and inversion are uniformly continuous.

`IsUniformGroup G` is equivalent to the fact that `G` is a topological group, and the uniformity
coincides with **both** the associated left and right uniformities
(this fact is not in Mathlib yet).

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
(this fact is not in Mathlib yet).

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
theorem UniformContinuous.mul_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f)
    (a : α) : UniformContinuous fun x ↦ f x * a :=
  hf.mul uniformContinuous_const

@[to_additive]
theorem UniformContinuous.const_mul [UniformSpace β] {f : β → α} (hf : UniformContinuous f)
    (a : α) : UniformContinuous fun x ↦ a * f x :=
  uniformContinuous_const.mul hf

@[to_additive]
theorem uniformContinuous_mul_left (a : α) : UniformContinuous fun b : α => a * b :=
  uniformContinuous_id.const_mul _

@[to_additive]
theorem uniformContinuous_mul_right (a : α) : UniformContinuous fun b : α => b * a :=
  uniformContinuous_id.mul_const _

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

variable (α)

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
  UniformSpace.ext <| by
    rw [(have := hu; uniformity_eq_comap_nhds_one), (have := hv; uniformity_eq_comap_nhds_one), h]

@[to_additive]
theorem IsUniformGroup.ext_iff {G : Type*} [Group G] {u v : UniformSpace G}
    (hu : @IsUniformGroup G u _) (hv : @IsUniformGroup G v _) :
    u = v ↔ @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1 :=
  ⟨fun h => h ▸ rfl, hu.ext hv⟩

variable {α}

@[to_additive]
theorem IsUniformGroup.uniformity_countably_generated [(𝓝 (1 : α)).IsCountablyGenerated] :
    (𝓤 α).IsCountablyGenerated := by
  rw [uniformity_eq_comap_nhds_one]
  exact Filter.comap.isCountablyGenerated _ _

open MulOpposite

end

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.2 / x.1 ∈ U i } := by
  rw [uniformity_eq_comap_nhds_one]
  exact h.comap _

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.1⁻¹ * x.2 ∈ U i } := by
  rw [uniformity_eq_comap_inv_mul_nhds_one]
  exact h.comap _

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_swapped {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.1 / x.2 ∈ U i } := by
  rw [uniformity_eq_comap_nhds_one_swapped]
  exact h.comap _

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.2⁻¹ * x.1 ∈ U i } := by
  rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
  exact h.comap _

@[to_additive]
theorem uniformContinuous_of_tendsto_one {hom : Type*} [UniformSpace β] [Group β] [IsUniformGroup β]
    [FunLike hom α β] [MonoidHomClass hom α β] {f : hom} (h : Tendsto f (𝓝 1) (𝓝 1)) :
    UniformContinuous f := by
  have :
    ((fun x : β × β => x.2 / x.1) ∘ fun x : α × α => (f x.1, f x.2)) = fun x : α × α =>
      f (x.2 / x.1) := by ext; simp only [Function.comp_apply, map_div]
  rw [UniformContinuous, uniformity_eq_comap_nhds_one α, uniformity_eq_comap_nhds_one β,
    tendsto_comap_iff, this]
  exact Tendsto.comp h tendsto_comap

/-- A group homomorphism (a bundled morphism of a type that implements `MonoidHomClass`) between
two uniform groups is uniformly continuous provided that it is continuous at one. See also
`continuous_of_continuousAt_one`. -/
@[to_additive /-- An additive group homomorphism (a bundled morphism of a type that implements
`AddMonoidHomClass`) between two uniform additive groups is uniformly continuous provided that it
is continuous at zero. See also `continuous_of_continuousAt_zero`. -/]
theorem uniformContinuous_of_continuousAt_one {hom : Type*} [UniformSpace β] [Group β]
    [IsUniformGroup β] [FunLike hom α β] [MonoidHomClass hom α β]
    (f : hom) (hf : ContinuousAt f 1) :
    UniformContinuous f :=
  uniformContinuous_of_tendsto_one (by simpa using hf.tendsto)

@[to_additive]
theorem MonoidHom.uniformContinuous_of_continuousAt_one [UniformSpace β] [Group β]
    [IsUniformGroup β] (f : α →* β) (hf : ContinuousAt f 1) : UniformContinuous f :=
  _root_.uniformContinuous_of_continuousAt_one f hf

/-- A homomorphism from a uniform group to a discrete uniform group is continuous if and only if
its kernel is open. -/
@[to_additive /-- A homomorphism from a uniform additive group to a discrete uniform additive group
is continuous if and only if its kernel is open. -/]
theorem IsUniformGroup.uniformContinuous_iff_isOpen_ker {hom : Type*} [UniformSpace β]
    [DiscreteTopology β] [Group β] [IsUniformGroup β] [FunLike hom α β] [MonoidHomClass hom α β]
    {f : hom} :
    UniformContinuous f ↔ IsOpen ((f : α →* β).ker : Set α) := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · apply (isOpen_discrete ({1} : Set β)).preimage hf.continuous
  · apply uniformContinuous_of_continuousAt_one
    rw [ContinuousAt, nhds_discrete β, map_one, tendsto_pure]
    exact hf.mem_nhds (map_one f)

@[to_additive]
theorem uniformContinuous_monoidHom_of_continuous {hom : Type*} [UniformSpace β] [Group β]
    [IsUniformGroup β] [FunLike hom α β] [MonoidHomClass hom α β] {f : hom} (h : Continuous f) :
    UniformContinuous f :=
  uniformContinuous_of_tendsto_one <|
    suffices Tendsto f (𝓝 1) (𝓝 (f 1)) by rwa [map_one] at this
    h.tendsto 1

end IsUniformGroup

section IsTopologicalGroup

open Filter

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The right uniformity on a topological group (as opposed to the left uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`IsUniformGroup` structure. Two important special cases where they _do_ coincide are for
commutative groups (see `isUniformGroup_of_commGroup`) and for compact groups (see
`IsUniformGroup.of_compactSpace`). -/
@[to_additive /-- The right uniformity on a topological additive group (as opposed to the left
uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`IsUniformAddGroup` structure. Two important special cases where they _do_ coincide are for
commutative additive groups (see `isUniformAddGroup_of_addCommGroup`) and for compact
additive groups (see `IsUniformAddGroup.of_compactSpace`). -/]
def IsTopologicalGroup.toUniformSpace : UniformSpace G where
  uniformity := comap (fun p : G × G => p.2 / p.1) (𝓝 1)
  symm :=
    have : Tendsto (fun p : G × G ↦ (p.2 / p.1)⁻¹) (comap (fun p : G × G ↦ p.2 / p.1) (𝓝 1))
      (𝓝 1⁻¹) := tendsto_id.inv.comp tendsto_comap
    by simpa [tendsto_comap_iff]
  comp := Tendsto.le_comap fun U H ↦ by
    rcases exists_nhds_one_split H with ⟨V, V_nhds, V_mul⟩
    refine mem_map.2 (mem_of_superset (mem_lift' <| preimage_mem_comap V_nhds) ?_)
    rintro ⟨x, y⟩ ⟨z, hz₁, hz₂⟩
    simpa using V_mul _ hz₂ _ hz₁
  nhds_eq_comap_uniformity _ := by simp only [comap_comap, Function.comp_def, nhds_translation_div]

attribute [local instance] IsTopologicalGroup.toUniformSpace

@[to_additive]
theorem uniformity_eq_comap_nhds_one' : 𝓤 G = comap (fun p : G × G => p.2 / p.1) (𝓝 (1 : G)) :=
  rfl

end IsTopologicalGroup

section TopologicalCommGroup

universe u v w x

open Filter

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

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
