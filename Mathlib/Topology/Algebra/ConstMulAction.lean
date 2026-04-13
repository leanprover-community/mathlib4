/-
Copyright (c) 2021 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Lattice
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Module.ULift
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Order.Filter.Pointwise
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Support

/-!
# Monoid actions continuous in the second variable

In this file we define class `ContinuousConstSMul`. We say `ContinuousConstSMul Γ T` if
`Γ` acts on `T` and for each `γ`, the map `x ↦ γ • x` is continuous. (This differs from
`ContinuousSMul`, which requires simultaneous continuity in both variables.)

## Main definitions

* `ContinuousConstSMul Γ T` : typeclass saying that the map `x ↦ γ • x` is continuous on `T`;
* `ProperlyDiscontinuousSMul`: says that the scalar multiplication `(•) : Γ → T → T`
  is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely
  many `γ:Γ` move `K` to have nontrivial intersection with `L`.
* `Homeomorph.smul`: scalar multiplication by an element of a group `Γ` acting on `T`
  is a homeomorphism of `T`.
* `Homeomorph.smulOfNeZero`: if a group with zero `G₀` (e.g., a field) acts on `X` and `c : G₀`
  is a nonzero element of `G₀`, then scalar multiplication by `c` is a homeomorphism of `X`;
* `Homeomorph.smul`: scalar multiplication by an element of a group `G` acting on `X`
  is a homeomorphism of `X`.

## Main results

* `isOpenMap_quotient_mk'_mul` : The quotient map by a group action is open.
* `t2Space_of_properlyDiscontinuousSMul_of_t2Space` : The quotient by a discontinuous group
  action of a locally compact T₂ space is T₂.

## Tags

Hausdorff, discrete group, properly discontinuous, quotient space

-/

@[expose] public section

assert_not_exists IsOrderedRing

open Topology Pointwise Filter Set TopologicalSpace

/-- Class `ContinuousConstSMul Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of multiplicative
actions, including (semi)modules and algebras.

Note that both `ContinuousConstSMul α α` and `ContinuousConstSMul αᵐᵒᵖ α` are
weaker versions of `ContinuousMul α`. -/
class ContinuousConstSMul (Γ : Type*) (T : Type*) [TopologicalSpace T] [SMul Γ T] : Prop where
  /-- The scalar multiplication `(•) : Γ → T → T` is continuous in the second argument. -/
  continuous_const_smul : ∀ γ : Γ, Continuous fun x : T => γ • x

/-- Class `ContinuousConstVAdd Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of additive actions,
including (semi)modules and algebras.

Note that both `ContinuousConstVAdd α α` and `ContinuousConstVAdd αᵐᵒᵖ α` are
weaker versions of `ContinuousVAdd α`. -/
class ContinuousConstVAdd (Γ : Type*) (T : Type*) [TopologicalSpace T] [VAdd Γ T] : Prop where
  /-- The additive action `(+ᵥ) : Γ → T → T` is continuous in the second argument. -/
  continuous_const_vadd : ∀ γ : Γ, Continuous fun x : T => γ +ᵥ x

attribute [to_additive] ContinuousConstSMul

export ContinuousConstSMul (continuous_const_smul)
export ContinuousConstVAdd (continuous_const_vadd)

variable {M α β : Type*}

section SMul

variable [TopologicalSpace α] [SMul M α] [ContinuousConstSMul M α]

@[to_additive]
instance : ContinuousConstSMul (ULift M) α := ⟨fun γ ↦ continuous_const_smul (ULift.down γ)⟩

@[to_additive]
theorem Filter.Tendsto.const_smul {f : β → α} {l : Filter β} {a : α} (hf : Tendsto f l (𝓝 a))
    (c : M) : Tendsto (fun x => c • f x) l (𝓝 (c • a)) :=
  ((continuous_const_smul _).tendsto _).comp hf

variable [TopologicalSpace β] {g : β → α} {b : β} {s : Set β}

@[to_additive]
nonrec theorem ContinuousWithinAt.const_smul (hg : ContinuousWithinAt g s b) (c : M) :
    ContinuousWithinAt (fun x => c • g x) s b :=
  hg.const_smul c

@[to_additive (attr := fun_prop)]
nonrec theorem ContinuousAt.const_smul (hg : ContinuousAt g b) (c : M) :
    ContinuousAt (fun x => c • g x) b :=
  hg.const_smul c

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.const_smul (hg : ContinuousOn g s) (c : M) :
    ContinuousOn (fun x => c • g x) s := fun x hx => (hg x hx).const_smul c

@[to_additive (attr := continuity, fun_prop)]
theorem Continuous.const_smul (hg : Continuous g) (c : M) : Continuous fun x => c • g x :=
  (continuous_const_smul _).comp hg

/-- If a scalar is central, then its right action is continuous when its left action is. -/
@[to_additive /-- If an additive action is central, then its right action is continuous when its
left action is. -/]
instance ContinuousConstSMul.op [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] :
    ContinuousConstSMul Mᵐᵒᵖ α :=
  ⟨MulOpposite.rec' fun c => by simpa only [op_smul_eq_smul] using continuous_const_smul c⟩

@[to_additive]
instance MulOpposite.continuousConstSMul : ContinuousConstSMul M αᵐᵒᵖ :=
  ⟨fun c => MulOpposite.continuous_op.comp <| MulOpposite.continuous_unop.const_smul c⟩

@[to_additive]
instance : ContinuousConstSMul M αᵒᵈ := ‹ContinuousConstSMul M α›

@[to_additive]
instance OrderDual.continuousConstSMul' : ContinuousConstSMul Mᵒᵈ α :=
  ‹ContinuousConstSMul M α›

@[to_additive]
instance Prod.continuousConstSMul [SMul M β] [ContinuousConstSMul M β] :
    ContinuousConstSMul M (α × β) :=
  ⟨fun _ => (continuous_fst.const_smul _).prodMk (continuous_snd.const_smul _)⟩

@[to_additive]
instance {ι : Type*} {γ : ι → Type*} [∀ i, TopologicalSpace (γ i)] [∀ i, SMul M (γ i)]
    [∀ i, ContinuousConstSMul M (γ i)] : ContinuousConstSMul M (∀ i, γ i) :=
  ⟨fun _ => continuous_pi fun i => (continuous_apply i).const_smul _⟩

@[to_additive]
theorem IsCompact.smul {α β} [SMul α β] [TopologicalSpace β] [ContinuousConstSMul α β] (a : α)
    {s : Set β} (hs : IsCompact s) : IsCompact (a • s) :=
  hs.image (continuous_id.const_smul a)

@[to_additive]
theorem Specializes.const_smul {x y : α} (h : x ⤳ y) (c : M) : (c • x) ⤳ (c • y) :=
  h.map (continuous_const_smul c)

@[to_additive]
theorem Inseparable.const_smul {x y : α} (h : Inseparable x y) (c : M) :
    Inseparable (c • x) (c • y) :=
  h.map (continuous_const_smul c)

@[to_additive]
theorem Topology.IsInducing.continuousConstSMul {N β : Type*} [SMul N β] [TopologicalSpace β]
    {g : β → α} (hg : IsInducing g) (f : N → M) (hf : ∀ {c : N} {x : β}, g (c • x) = f c • g x) :
    ContinuousConstSMul N β where
  continuous_const_smul c := by
    simpa only [Function.comp_def, hf, hg.continuous_iff] using hg.continuous.const_smul (f c)

@[to_additive]
theorem smul_closure_subset (c : M) (s : Set α) : c • closure s ⊆ closure (c • s) :=
  ((Set.mapsTo_image _ _).closure <| continuous_const_smul c).image_subset

@[to_additive]
theorem set_smul_closure_subset (s : Set M) (t : Set α) : s • closure t ⊆ closure (s • t) := by
  simp only [← iUnion_smul_set]
  exact iUnion₂_subset fun c hc ↦ (smul_closure_subset c t).trans <| closure_mono <|
    subset_biUnion_of_mem (u := (· • t)) hc

theorem isClosed_setOf_map_smul {N : Type*} (α β) [SMul M α] [SMul N β]
    [TopologicalSpace β] [T2Space β] [ContinuousConstSMul N β] (σ : M → N) :
    IsClosed { f : α → β | ∀ c x, f (c • x) = σ c • f x } := by
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun c => isClosed_iInter fun x =>
    isClosed_eq (continuous_apply _) ((continuous_apply _).const_smul _)

end SMul

section Monoid

variable [TopologicalSpace α]
variable [Monoid M] [MulAction M α] [ContinuousConstSMul M α]

@[to_additive]
instance Units.continuousConstSMul : ContinuousConstSMul Mˣ α where
  continuous_const_smul m := continuous_const_smul (m : M)

@[to_additive]
theorem smul_closure_orbit_subset (c : M) (x : α) :
    c • closure (MulAction.orbit M x) ⊆ closure (MulAction.orbit M x) :=
  (smul_closure_subset c _).trans <| closure_mono <| MulAction.smul_orbit_subset _ _

end Monoid

section Group

variable {G : Type*} [TopologicalSpace α] [Group G] [MulAction G α] [ContinuousConstSMul G α]

@[to_additive]
theorem tendsto_const_smul_iff {f : β → α} {l : Filter β} {a : α} (c : G) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul c⁻¹, fun h => h.const_smul _⟩

variable [TopologicalSpace β] {f : β → α} {b : β} {s : Set β}

@[to_additive]
theorem continuousWithinAt_const_smul_iff (c : G) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  tendsto_const_smul_iff c

@[to_additive]
theorem continuousOn_const_smul_iff (c : G) :
    ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  forall₂_congr fun _ _ => continuousWithinAt_const_smul_iff c

@[to_additive]
theorem continuousAt_const_smul_iff (c : G) :
    ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  tendsto_const_smul_iff c

@[to_additive]
theorem continuous_const_smul_iff (c : G) : (Continuous fun x => c • f x) ↔ Continuous f := by
  simp only [continuous_iff_continuousAt, continuousAt_const_smul_iff]

/-- The homeomorphism given by scalar multiplication by a given element of a group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
@[to_additive (attr := simps!)]
def Homeomorph.smul (γ : G) : α ≃ₜ α where
  toEquiv := MulAction.toPerm γ

/-- The homeomorphism given by affine-addition by an element of an additive group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
add_decl_doc Homeomorph.vadd

@[to_additive]
theorem isHomeomorph_smul (c : G) : IsHomeomorph fun x : α ↦ c • x :=
  (Homeomorph.smul c).isHomeomorph

@[to_additive]
theorem isOpenMap_smul (c : G) : IsOpenMap fun x : α => c • x :=
  (Homeomorph.smul c).isOpenMap

@[to_additive]
theorem IsOpen.smul {s : Set α} (hs : IsOpen s) (c : G) : IsOpen (c • s) :=
  isOpenMap_smul c s hs

@[to_additive]
theorem isClosedMap_smul (c : G) : IsClosedMap fun x : α => c • x :=
  (Homeomorph.smul c).isClosedMap

@[to_additive]
theorem IsClosed.smul {s : Set α} (hs : IsClosed s) (c : G) : IsClosed (c • s) :=
  isClosedMap_smul c s hs

@[to_additive]
theorem closure_smul (c : G) (s : Set α) : closure (c • s) = c • closure s :=
  ((Homeomorph.smul c).image_closure s).symm

@[to_additive]
theorem Dense.smul (c : G) {s : Set α} (hs : Dense s) : Dense (c • s) := by
  rw [dense_iff_closure_eq] at hs ⊢; rw [closure_smul, hs, smul_set_univ]

@[to_additive]
theorem interior_smul (c : G) (s : Set α) : interior (c • s) = c • interior s :=
  ((Homeomorph.smul c).image_interior s).symm

open scoped Pointwise in
@[to_additive]
lemma nhds_smul (c : G) (x : α) : 𝓝 (c • x) = c • 𝓝 x :=
  (Homeomorph.smul c).map_nhds_eq x |>.symm

open scoped Pointwise in
@[to_additive]
lemma punctured_nhds_smul (c : G) (x : α) : 𝓝[≠] (c • x) = c • 𝓝[≠] x :=
  (Homeomorph.smul c).map_punctured_nhds_eq x |>.symm

@[to_additive]
theorem IsOpen.smul_left {s : Set G} {t : Set α} (ht : IsOpen t) : IsOpen (s • t) := by
  rw [← iUnion_smul_set]
  exact isOpen_biUnion fun a _ => ht.smul _

@[to_additive]
theorem subset_interior_smul_right {s : Set G} {t : Set α} : s • interior t ⊆ interior (s • t) :=
  interior_maximal (Set.smul_subset_smul_left interior_subset) isOpen_interior.smul_left

@[to_additive (attr := simp)]
theorem smul_mem_nhds_smul_iff {t : Set α} (g : G) {a : α} : g • t ∈ 𝓝 (g • a) ↔ t ∈ 𝓝 a :=
  (Homeomorph.smul g).isOpenEmbedding.image_mem_nhds

@[to_additive] alias ⟨_, smul_mem_nhds_smul⟩ := smul_mem_nhds_smul_iff

@[to_additive (attr := simp)]
theorem smul_mem_nhds_self [TopologicalSpace G] [ContinuousConstSMul G G] {g : G} {s : Set G} :
    g • s ∈ 𝓝 g ↔ s ∈ 𝓝 1 := by
  rw [← smul_mem_nhds_smul_iff g⁻¹]; simp

namespace MulAction.IsPretransitive

variable (G)

@[to_additive]
lemma t1Space_iff (x : α) [IsPretransitive G α] :
    T1Space α ↔ IsClosed {x} := by
  refine ⟨fun H ↦ isClosed_singleton, fun hx ↦ ⟨fun y ↦ ?_⟩⟩
  rcases MulAction.exists_smul_eq G x y with ⟨g, rfl⟩
  rw [← image_singleton, image_smul]
  exact hx.smul _

@[to_additive]
lemma discreteTopology_iff (x : α) [IsPretransitive G α] :
    DiscreteTopology α ↔ IsOpen {x} := by
  rw [discreteTopology_iff_isOpen_singleton]
  refine ⟨fun H ↦ H _, fun hx y ↦ ?_⟩
  rcases MulAction.exists_smul_eq G x y with ⟨g, rfl⟩
  rw [← image_singleton, image_smul]
  exact hx.smul _

end MulAction.IsPretransitive

end Group

section GroupWithZero

variable {G₀ : Type*} [TopologicalSpace α] [GroupWithZero G₀] [MulAction G₀ α]
  [ContinuousConstSMul G₀ α]

theorem tendsto_const_smul_iff₀ {f : β → α} {l : Filter β} {a : α} {c : G₀} (hc : c ≠ 0) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  tendsto_const_smul_iff (Units.mk0 c hc)

variable [TopologicalSpace β] {f : β → α} {b : β} {c : G₀} {s : Set β}

theorem continuousWithinAt_const_smul_iff₀ (hc : c ≠ 0) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  tendsto_const_smul_iff (Units.mk0 c hc)

theorem continuousOn_const_smul_iff₀ (hc : c ≠ 0) :
    ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  continuousOn_const_smul_iff (Units.mk0 c hc)

theorem continuousAt_const_smul_iff₀ (hc : c ≠ 0) :
    ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  continuousAt_const_smul_iff (Units.mk0 c hc)

theorem continuous_const_smul_iff₀ (hc : c ≠ 0) : (Continuous fun x => c • f x) ↔ Continuous f :=
  continuous_const_smul_iff (Units.mk0 c hc)

/-- Scalar multiplication by a non-zero element of a group with zero acting on `α` is a
homeomorphism from `α` onto itself. -/
@[simps! -fullyApplied apply]
protected def Homeomorph.smulOfNeZero (c : G₀) (hc : c ≠ 0) : α ≃ₜ α :=
  Homeomorph.smul (Units.mk0 c hc)

@[simp]
theorem Homeomorph.smulOfNeZero_symm_apply {c : G₀} (hc : c ≠ 0) :
    ⇑(Homeomorph.smulOfNeZero c hc).symm = (c⁻¹ • · : α → α) :=
  rfl

theorem isHomeomorph_smul₀ {c : G₀} (hc : c ≠ 0) : IsHomeomorph fun x : α ↦ c • x :=
  (Homeomorph.smulOfNeZero c hc).isHomeomorph

theorem isOpenMap_smul₀ {c : G₀} (hc : c ≠ 0) : IsOpenMap fun x : α => c • x :=
  (Homeomorph.smulOfNeZero c hc).isOpenMap

theorem IsOpen.smul₀ {c : G₀} {s : Set α} (hs : IsOpen s) (hc : c ≠ 0) : IsOpen (c • s) :=
  isOpenMap_smul₀ hc s hs

theorem interior_smul₀ {c : G₀} (hc : c ≠ 0) (s : Set α) : interior (c • s) = c • interior s :=
  ((Homeomorph.smulOfNeZero c hc).image_interior s).symm

theorem closure_smul₀' {c : G₀} (hc : c ≠ 0) (s : Set α) :
    closure (c • s) = c • closure s :=
  ((Homeomorph.smulOfNeZero c hc).image_closure s).symm

theorem closure_smul₀ {E} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E] [T1Space E]
    [ContinuousConstSMul G₀ E] (c : G₀) (s : Set E) : closure (c • s) = c • closure s := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · rcases eq_empty_or_nonempty s with (rfl | hs)
    · simp
    · rw [zero_smul_set hs, zero_smul_set hs.closure]
      exact closure_singleton
  · exact closure_smul₀' hc s

open scoped Pointwise in
lemma nhds_smul₀ {c : G₀} (hc : c ≠ 0) (x : α) : 𝓝 (c • x) = c • 𝓝 x :=
  nhds_smul (Units.mk0 c hc) x

open scoped Pointwise in
lemma punctured_nhds_smul₀ {c : G₀} (hc : c ≠ 0) (x : α) : 𝓝[≠] (c • x) = c • 𝓝[≠] x :=
  punctured_nhds_smul (Units.mk0 c hc) x

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `isClosedMap_smul_left` in `Analysis.Normed.Module.FiniteDimension`. -/
theorem isClosedMap_smul_of_ne_zero {c : G₀} (hc : c ≠ 0) : IsClosedMap fun x : α => c • x :=
  (Homeomorph.smulOfNeZero c hc).isClosedMap

theorem IsClosed.smul_of_ne_zero {c : G₀} {s : Set α} (hs : IsClosed s) (hc : c ≠ 0) :
    IsClosed (c • s) :=
  isClosedMap_smul_of_ne_zero hc s hs

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `isClosedMap_smul_left` in `Analysis.Normed.Module.FiniteDimension`. -/
theorem isClosedMap_smul₀ {E : Type*} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E]
    [T1Space E] [ContinuousConstSMul G₀ E] (c : G₀) : IsClosedMap fun x : E => c • x := by
  rcases eq_or_ne c 0 with (rfl | hne)
  · simp only [zero_smul]
    exact isClosedMap_const
  · exact (Homeomorph.smulOfNeZero c hne).isClosedMap

theorem IsClosed.smul₀ {E : Type*} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E]
    [T1Space E] [ContinuousConstSMul G₀ E] (c : G₀) {s : Set E} (hs : IsClosed s) :
    IsClosed (c • s) :=
  isClosedMap_smul₀ c s hs

theorem HasCompactMulSupport.comp_smul {β : Type*} [One β] {f : α → β} (h : HasCompactMulSupport f)
    {c : G₀} (hc : c ≠ 0) : HasCompactMulSupport fun x => f (c • x) :=
  h.comp_homeomorph (Homeomorph.smulOfNeZero c hc)

theorem HasCompactSupport.comp_smul {β : Type*} [Zero β] {f : α → β} (h : HasCompactSupport f)
    {c : G₀} (hc : c ≠ 0) : HasCompactSupport fun x => f (c • x) :=
  h.comp_homeomorph (Homeomorph.smulOfNeZero c hc)

end GroupWithZero

namespace IsUnit

variable [Monoid M] [TopologicalSpace α] [MulAction M α] [ContinuousConstSMul M α]

nonrec theorem tendsto_const_smul_iff {f : β → α} {l : Filter β} {a : α} {c : M} (hc : IsUnit c) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  tendsto_const_smul_iff hc.unit

variable [TopologicalSpace β] {f : β → α} {b : β} {c : M} {s : Set β}

nonrec theorem continuousWithinAt_const_smul_iff (hc : IsUnit c) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  continuousWithinAt_const_smul_iff hc.unit

nonrec theorem continuousOn_const_smul_iff (hc : IsUnit c) :
    ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  continuousOn_const_smul_iff hc.unit

nonrec theorem continuousAt_const_smul_iff (hc : IsUnit c) :
    ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  continuousAt_const_smul_iff hc.unit

nonrec theorem continuous_const_smul_iff (hc : IsUnit c) :
    (Continuous fun x => c • f x) ↔ Continuous f :=
  continuous_const_smul_iff hc.unit

nonrec theorem isHomeomorph_smul (hc : IsUnit c) : IsHomeomorph fun x : α ↦ c • x :=
  isHomeomorph_smul hc.unit

nonrec theorem isOpenMap_smul (hc : IsUnit c) : IsOpenMap fun x : α => c • x :=
  isOpenMap_smul hc.unit

nonrec theorem isClosedMap_smul (hc : IsUnit c) : IsClosedMap fun x : α => c • x :=
  isClosedMap_smul hc.unit

nonrec theorem smul_mem_nhds_smul_iff (hc : IsUnit c) {s : Set α} {a : α} :
    c • s ∈ 𝓝 (c • a) ↔ s ∈ 𝓝 a :=
  smul_mem_nhds_smul_iff hc.unit

theorem isQuotientMap_smul {S β} [SMul S M] [SMul S α] [IsScalarTower S M α]
    [SMul S β] (f : α →[S] β) [TopologicalSpace β] (hf : IsQuotientMap f)
    (c : S) (hc : IsUnit (c • 1 : M)) : IsQuotientMap (c • · : β → β) :=
  hf.of_comp_isQuotientMap <| by convert hf.comp hc.isHomeomorph_smul.isQuotientMap; ext; simp

theorem isQuotientMap_nsmul {M β} [Semiring M] [AddCommMonoid α] [Module M α]
    [ContinuousConstSMul M α] [AddMonoid β] (f : α →+ β) [TopologicalSpace β]
    (hf : IsQuotientMap f) (n : ℕ) (hc : IsUnit (n : M)) : IsQuotientMap (n • · : β → β) :=
  isQuotientMap_smul (M := M) ⟨f, map_nsmul f⟩ hf _ <| by rwa [nsmul_one]

theorem isQuotientMap_zsmul {M β} [Ring M] [AddCommGroup α] [Module M α]
    [ContinuousConstSMul M α] [AddGroup β] (f : α →+ β) [TopologicalSpace β]
    (hf : IsQuotientMap f) (n : ℤ) (hc : IsUnit (n : M)) : IsQuotientMap (n • · : β → β) :=
  isQuotientMap_smul (M := M) ⟨f, map_zsmul f⟩ hf _ <| by rwa [zsmul_one n]

end IsUnit

/-- Class `ProperlyDiscontinuousSMul Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ : Γ` move `K` to have nontrivial intersection with `L`.
-/
class ProperlyDiscontinuousSMul (Γ : Type*) (T : Type*) [TopologicalSpace T] [SMul Γ T] :
    Prop where
  /-- Given two compact sets `K` and `L`, `γ • K ∩ L` is nonempty for finitely many `γ`. -/
  finite_disjoint_inter_image :
    ∀ {K L : Set T}, IsCompact K → IsCompact L → Set.Finite { γ : Γ | ((γ • ·) '' K ∩ L).Nonempty }

/-- Class `ProperlyDiscontinuousVAdd Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ : Γ` move `K` to have nontrivial intersection with `L`.
-/
class ProperlyDiscontinuousVAdd (Γ : Type*) (T : Type*) [TopologicalSpace T] [VAdd Γ T] :
  Prop where
  /-- Given two compact sets `K` and `L`, `γ +ᵥ K ∩ L` is nonempty for finitely many `γ`. -/
  finite_disjoint_inter_image :
    ∀ {K L : Set T}, IsCompact K → IsCompact L → Set.Finite { γ : Γ | ((γ +ᵥ ·) '' K ∩ L).Nonempty }

attribute [to_additive] ProperlyDiscontinuousSMul

export ProperlyDiscontinuousSMul (finite_disjoint_inter_image)
export ProperlyDiscontinuousVAdd (finite_disjoint_inter_image)

@[to_additive]
lemma properlyDiscontinuousSMul_iff [TopologicalSpace α] [SMul M α] :
    ProperlyDiscontinuousSMul M α ↔
      ∀ {K L : Set α}, IsCompact K → IsCompact L → {m : M | (m • K ∩ L).Nonempty}.Finite :=
  ⟨fun _ _ _ ↦ ProperlyDiscontinuousSMul.finite_disjoint_inter_image, .mk⟩

section

variable (Γ : Type*) {T : Type*}
variable [TopologicalSpace T] [SMul Γ T] [ProperlyDiscontinuousSMul Γ T] (x : T)

@[to_additive] lemma ProperlyDiscontinuousSMul.finite_stabilizer' : {γ : Γ | γ • x = x}.Finite := by
  simp_rw [← mem_singleton_iff, ← singleton_inter_nonempty, ← image_singleton]
  exact finite_disjoint_inter_image isCompact_singleton isCompact_singleton

variable [T2Space T] [LocallyCompactSpace T] [ContinuousConstSMul Γ T] (x : T)

@[to_additive] lemma ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self :
    ∃ U ∈ 𝓝 x, ∀ γ : Γ, ((γ • ·) '' U ∩ U).Nonempty → γ • x = x := by
  obtain ⟨V, V_cpt, V_nhd⟩ := exists_compact_mem_nhds x
  let Γ₀ := {γ : Γ | ((γ • ·) '' V ∩ V).Nonempty ∧ γ • x ≠ x}
  have : Finite Γ₀ := (finite_disjoint_inter_image V_cpt V_cpt).subset fun _ ↦ And.left
  choose u v hu hv u_v_disjoint using fun γ : Γ₀ ↦ t2_separation_nhds γ.2.2
  refine ⟨V ∩ ⋂ γ : Γ₀, (γ.1 • ·) ⁻¹' u γ ∩ v γ, inter_mem V_nhd (iInter_mem.mpr fun γ ↦
    inter_mem ((continuous_const_smul _).continuousAt <| hu γ) (hv γ)), fun γ hγ ↦ ?_⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, hγz⟩ := hγ
  by_contra h
  rw [mem_inter_iff, mem_iInter] at hz hγz
  let γ : Γ₀ := ⟨γ, ⟨_, ⟨z, hz.1, rfl⟩, hγz.1⟩, h⟩
  exact (u_v_disjoint γ).le_bot ⟨(hz.2 γ).1, (hγz.2 γ).2⟩

@[to_additive] lemma ProperlyDiscontinuousSMul.exists_nhds_disjoint_image :
    ∃ U ∈ 𝓝 x, ∀ γ : Γ, γ • x ≠ x → Disjoint ((γ • ·) '' U) U := by
  convert exists_nhds_image_smul_eq_self Γ x using 4
  rw [← not_imp_not]
  simp [Set.not_disjoint_iff_nonempty_inter]

end

variable {Γ : Type*} [Group Γ] {T : Type*} [TopologicalSpace T] [MulAction Γ T]

/-- A finite group action is always properly discontinuous. -/
@[to_additive /-- A finite group action is always properly discontinuous. -/]
instance (priority := 100) Finite.to_properlyDiscontinuousSMul [Finite Γ] :
    ProperlyDiscontinuousSMul Γ T where finite_disjoint_inter_image _ _ := Set.toFinite _

@[to_additive] lemma ProperlyDiscontinuousSMul.finite_stabilizer [ProperlyDiscontinuousSMul Γ T]
    (x : T) : (MulAction.stabilizer Γ x : Set Γ).Finite :=
  ProperlyDiscontinuousSMul.finite_stabilizer' Γ x

/-- The quotient map by a group action is open, i.e. the quotient by a group action is an open
  quotient. -/
@[to_additive /-- The quotient map by a group action is open, i.e. the quotient by a group
action is an open quotient. -/]
theorem isOpenMap_quotient_mk'_mul [ContinuousConstSMul Γ T] :
    letI := MulAction.orbitRel Γ T
    IsOpenMap (Quotient.mk' : T → Quotient (MulAction.orbitRel Γ T)) := fun U hU => by
  rw [isOpen_coinduced, MulAction.quotient_preimage_image_eq_union_mul U]
  exact isOpen_iUnion fun γ => isOpenMap_smul γ U hU

@[to_additive]
theorem MulAction.isOpenQuotientMap_quotientMk [ContinuousConstSMul Γ T] :
    IsOpenQuotientMap (Quotient.mk (MulAction.orbitRel Γ T)) :=
  ⟨Quot.mk_surjective, continuous_quot_mk, isOpenMap_quotient_mk'_mul⟩

/-- The quotient by a discontinuous group action of a locally compact T₂ space is T₂. -/
@[to_additive /-- The quotient by a discontinuous group action of a locally compact T₂
space is T₂. -/]
instance (priority := 100) t2Space_of_properlyDiscontinuousSMul_of_t2Space [T2Space T]
    [LocallyCompactSpace T] [ContinuousConstSMul Γ T] [ProperlyDiscontinuousSMul Γ T] :
    T2Space (Quotient (MulAction.orbitRel Γ T)) := by
  letI := MulAction.orbitRel Γ T
  set Q := Quotient (MulAction.orbitRel Γ T)
  rw [t2Space_iff_nhds]
  let f : T → Q := Quotient.mk'
  have f_op : IsOpenMap f := isOpenMap_quotient_mk'_mul
  rintro ⟨x₀⟩ ⟨y₀⟩ (hxy : f x₀ ≠ f y₀)
  change ∃ U ∈ 𝓝 (f x₀), ∃ V ∈ 𝓝 (f y₀), _
  have hγx₀y₀ : ∀ γ : Γ, γ • x₀ ≠ y₀ := not_exists.mp (mt Quotient.sound hxy.symm :)
  obtain ⟨K₀, hK₀, K₀_in⟩ := exists_compact_mem_nhds x₀
  obtain ⟨L₀, hL₀, L₀_in⟩ := exists_compact_mem_nhds y₀
  let bad_Γ_set := { γ : Γ | ((γ • ·) '' K₀ ∩ L₀).Nonempty }
  have bad_Γ_finite : bad_Γ_set.Finite := finite_disjoint_inter_image (Γ := Γ) hK₀ hL₀
  choose u v hu hv u_v_disjoint using fun γ => t2_separation_nhds (hγx₀y₀ γ)
  let U₀₀ := ⋂ γ ∈ bad_Γ_set, (γ • ·) ⁻¹' u γ
  let U₀ := U₀₀ ∩ K₀
  let V₀₀ := ⋂ γ ∈ bad_Γ_set, v γ
  let V₀ := V₀₀ ∩ L₀
  have U_nhds : f '' U₀ ∈ 𝓝 (f x₀) := by
    refine f_op.image_mem_nhds (inter_mem ((biInter_mem bad_Γ_finite).mpr fun γ _ => ?_) K₀_in)
    exact (continuous_const_smul _).continuousAt (hu γ)
  have V_nhds : f '' V₀ ∈ 𝓝 (f y₀) :=
    f_op.image_mem_nhds (inter_mem ((biInter_mem bad_Γ_finite).mpr fun γ _ => hv γ) L₀_in)
  refine ⟨f '' U₀, U_nhds, f '' V₀, V_nhds, MulAction.disjoint_image_image_iff.2 ?_⟩
  rintro x ⟨x_in_U₀₀, x_in_K₀⟩ γ
  by_cases H : γ ∈ bad_Γ_set
  · exact fun h => (u_v_disjoint γ).le_bot ⟨mem_iInter₂.mp x_in_U₀₀ γ H, mem_iInter₂.mp h.1 γ H⟩
  · rintro ⟨-, h'⟩
    simp only [bad_Γ_set, image_smul, not_nonempty_iff_eq_empty, mem_setOf_eq] at H
    exact eq_empty_iff_forall_notMem.mp H (γ • x) ⟨mem_image_of_mem _ x_in_K₀, h'⟩

/-- The quotient of a second countable space by a group action is second countable. -/
@[to_additive /-- The quotient of a second countable space by an additive group action is second
countable. -/]
theorem ContinuousConstSMul.secondCountableTopology [SecondCountableTopology T]
    [ContinuousConstSMul Γ T] : SecondCountableTopology (Quotient (MulAction.orbitRel Γ T)) :=
  TopologicalSpace.Quotient.secondCountableTopology isOpenMap_quotient_mk'_mul

section nhds

section MulAction

variable {G₀ : Type*} [GroupWithZero G₀] [MulAction G₀ α] [TopologicalSpace α]
  [ContinuousConstSMul G₀ α]

/-- Scalar multiplication by a nonzero scalar preserves neighborhoods. -/
theorem smul_mem_nhds_smul_iff₀ {c : G₀} {s : Set α} {x : α} (hc : c ≠ 0) :
    c • s ∈ 𝓝 (c • x : α) ↔ s ∈ 𝓝 x :=
  smul_mem_nhds_smul_iff (Units.mk0 c hc)

alias ⟨_, smul_mem_nhds_smul₀⟩ := smul_mem_nhds_smul_iff₀

end MulAction

section DistribMulAction

variable {G₀ : Type*} [GroupWithZero G₀] [AddMonoid α] [DistribMulAction G₀ α] [TopologicalSpace α]
  [ContinuousConstSMul G₀ α]

theorem set_smul_mem_nhds_zero_iff {s : Set α} {c : G₀} (hc : c ≠ 0) :
    c • s ∈ 𝓝 (0 : α) ↔ s ∈ 𝓝 (0 : α) := by
  refine Iff.trans ?_ (smul_mem_nhds_smul_iff₀ hc)
  rw [smul_zero]

end DistribMulAction

end nhds
