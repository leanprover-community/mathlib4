/-
Copyright (c) 2021 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Homeomorph
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Support

#align_import topology.algebra.const_mul_action from "leanprover-community/mathlib"@"d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46"

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

## Main results

* `isOpenMap_quotient_mk'_mul` : The quotient map by a group action is open.
* `t2Space_of_properlyDiscontinuousSMul_of_t2Space` : The quotient by a discontinuous group
  action of a locally compact t2 space is t2.

## Tags

Hausdorff, discrete group, properly discontinuous, quotient space

-/

set_option autoImplicit true


open Topology Pointwise Filter Set TopologicalSpace

/-- Class `ContinuousConstSMul Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of multiplicative
actions, including (semi)modules and algebras.

Note that both `ContinuousConstSMul α α` and `ContinuousConstSMul αᵐᵒᵖ α` are
weaker versions of `ContinuousMul α`. -/
class ContinuousConstSMul (Γ : Type*) (T : Type*) [TopologicalSpace T] [SMul Γ T] : Prop where
  /-- The scalar multiplication `(•) : Γ → T → T` is continuous in the second argument. -/
  continuous_const_smul : ∀ γ : Γ, Continuous fun x : T => γ • x
#align has_continuous_const_smul ContinuousConstSMul

/-- Class `ContinuousConstVAdd Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of additive actions,
including (semi)modules and algebras.

Note that both `ContinuousConstVAdd α α` and `ContinuousConstVAdd αᵐᵒᵖ α` are
weaker versions of `ContinuousVAdd α`. -/
class ContinuousConstVAdd (Γ : Type*) (T : Type*) [TopologicalSpace T] [VAdd Γ T] : Prop where
  /-- The additive action `(+ᵥ) : Γ → T → T` is continuous in the second argument. -/
  continuous_const_vadd : ∀ γ : Γ, Continuous fun x : T => γ +ᵥ x
#align has_continuous_const_vadd ContinuousConstVAdd

attribute [to_additive] ContinuousConstSMul

export ContinuousConstSMul (continuous_const_smul)
export ContinuousConstVAdd (continuous_const_vadd)

variable {M α β : Type*}

section SMul

variable [TopologicalSpace α] [SMul M α] [ContinuousConstSMul M α]

@[to_additive]
theorem Filter.Tendsto.const_smul {f : β → α} {l : Filter β} {a : α} (hf : Tendsto f l (𝓝 a))
    (c : M) : Tendsto (fun x => c • f x) l (𝓝 (c • a)) :=
  ((continuous_const_smul _).tendsto _).comp hf
#align filter.tendsto.const_smul Filter.Tendsto.const_smul
#align filter.tendsto.const_vadd Filter.Tendsto.const_vadd

variable [TopologicalSpace β] {f : β → M} {g : β → α} {b : β} {s : Set β}

@[to_additive]
nonrec theorem ContinuousWithinAt.const_smul (hg : ContinuousWithinAt g s b) (c : M) :
    ContinuousWithinAt (fun x => c • g x) s b :=
  hg.const_smul c
#align continuous_within_at.const_smul ContinuousWithinAt.const_smul
#align continuous_within_at.const_vadd ContinuousWithinAt.const_vadd

@[to_additive (attr := fun_prop)]
nonrec theorem ContinuousAt.const_smul (hg : ContinuousAt g b) (c : M) :
    ContinuousAt (fun x => c • g x) b :=
  hg.const_smul c
#align continuous_at.const_smul ContinuousAt.const_smul
#align continuous_at.const_vadd ContinuousAt.const_vadd

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.const_smul (hg : ContinuousOn g s) (c : M) :
    ContinuousOn (fun x => c • g x) s := fun x hx => (hg x hx).const_smul c
#align continuous_on.const_smul ContinuousOn.const_smul
#align continuous_on.const_vadd ContinuousOn.const_vadd

@[to_additive (attr := continuity, fun_prop)]
theorem Continuous.const_smul (hg : Continuous g) (c : M) : Continuous fun x => c • g x :=
  (continuous_const_smul _).comp hg
#align continuous.const_smul Continuous.const_smul
#align continuous.const_vadd Continuous.const_vadd

/-- If a scalar is central, then its right action is continuous when its left action is. -/
@[to_additive "If an additive action is central, then its right action is continuous when its left
action is."]
instance ContinuousConstSMul.op [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] :
    ContinuousConstSMul Mᵐᵒᵖ α :=
  ⟨MulOpposite.rec' fun c => by simpa only [op_smul_eq_smul] using continuous_const_smul c⟩
#align has_continuous_const_smul.op ContinuousConstSMul.op
#align has_continuous_const_vadd.op ContinuousConstVAdd.op

@[to_additive]
instance MulOpposite.continuousConstSMul : ContinuousConstSMul M αᵐᵒᵖ :=
  ⟨fun c => MulOpposite.continuous_op.comp <| MulOpposite.continuous_unop.const_smul c⟩
#align mul_opposite.has_continuous_const_smul MulOpposite.continuousConstSMul
#align add_opposite.has_continuous_const_vadd AddOpposite.continuousConstVAdd

@[to_additive]
instance : ContinuousConstSMul M αᵒᵈ := ‹ContinuousConstSMul M α›

@[to_additive]
instance OrderDual.continuousConstSMul' : ContinuousConstSMul Mᵒᵈ α :=
  ‹ContinuousConstSMul M α›
#align order_dual.has_continuous_const_smul' OrderDual.continuousConstSMul'
#align order_dual.has_continuous_const_vadd' OrderDual.continuousConstVAdd'

@[to_additive]
instance Prod.continuousConstSMul [SMul M β] [ContinuousConstSMul M β] :
    ContinuousConstSMul M (α × β) :=
  ⟨fun _ => (continuous_fst.const_smul _).prod_mk (continuous_snd.const_smul _)⟩

@[to_additive]
instance {ι : Type*} {γ : ι → Type*} [∀ i, TopologicalSpace (γ i)] [∀ i, SMul M (γ i)]
    [∀ i, ContinuousConstSMul M (γ i)] : ContinuousConstSMul M (∀ i, γ i) :=
  ⟨fun _ => continuous_pi fun i => (continuous_apply i).const_smul _⟩

@[to_additive]
theorem IsCompact.smul {α β} [SMul α β] [TopologicalSpace β] [ContinuousConstSMul α β] (a : α)
    {s : Set β} (hs : IsCompact s) : IsCompact (a • s) :=
  hs.image (continuous_id.const_smul a)
#align is_compact.smul IsCompact.smul
#align is_compact.vadd IsCompact.vadd

end SMul

section Monoid

variable [TopologicalSpace α]
variable [Monoid M] [MulAction M α] [ContinuousConstSMul M α]

@[to_additive]
instance Units.continuousConstSMul : ContinuousConstSMul Mˣ α where
  continuous_const_smul m := (continuous_const_smul (m : M) : _)
#align units.has_continuous_const_smul Units.continuousConstSMul
#align add_units.has_continuous_const_vadd AddUnits.continuousConstVAdd

@[to_additive]
theorem smul_closure_subset (c : M) (s : Set α) : c • closure s ⊆ closure (c • s) :=
  ((Set.mapsTo_image _ _).closure <| continuous_const_smul c).image_subset
#align smul_closure_subset smul_closure_subset
#align vadd_closure_subset vadd_closure_subset

@[to_additive]
theorem smul_closure_orbit_subset (c : M) (x : α) :
    c • closure (MulAction.orbit M x) ⊆ closure (MulAction.orbit M x) :=
  (smul_closure_subset c _).trans <| closure_mono <| MulAction.smul_orbit_subset _ _
#align smul_closure_orbit_subset smul_closure_orbit_subset
#align vadd_closure_orbit_subset vadd_closure_orbit_subset

theorem isClosed_setOf_map_smul [Monoid N] (α β) [MulAction M α] [MulAction N β]
    [TopologicalSpace β] [T2Space β] [ContinuousConstSMul N β] (σ : M → N) :
    IsClosed { f : α → β | ∀ c x, f (c • x) = σ c • f x } := by
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun c => isClosed_iInter fun x =>
    isClosed_eq (continuous_apply _) ((continuous_apply _).const_smul _)
#align is_closed_set_of_map_smul isClosed_setOf_map_smulₓ

variable [T2Space α] in
variable (α) in
/--
The set `MulAction.fixedBy α m` for a continuous, multiplicative action on a Hausdorff space
is closed.
-/
@[to_additive "The set `AddAction.fixedBy α m` for a continuous, additive action on a Hausdorff
space is closed."]
theorem MulAction.isClosed_fixedBy (m : M) : IsClosed (fixedBy α m) :=
  isClosed_eq (continuous_const_smul m) continuous_id

end Monoid

section Group

variable {G : Type*} [TopologicalSpace α] [Group G] [MulAction G α] [ContinuousConstSMul G α]

@[to_additive]
theorem tendsto_const_smul_iff {f : β → α} {l : Filter β} {a : α} (c : G) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul c⁻¹, fun h => h.const_smul _⟩
#align tendsto_const_smul_iff tendsto_const_smul_iff
#align tendsto_const_vadd_iff tendsto_const_vadd_iff

variable [TopologicalSpace β] {f : β → α} {b : β} {s : Set β}

@[to_additive]
theorem continuousWithinAt_const_smul_iff (c : G) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  tendsto_const_smul_iff c
#align continuous_within_at_const_smul_iff continuousWithinAt_const_smul_iff
#align continuous_within_at_const_vadd_iff continuousWithinAt_const_vadd_iff

@[to_additive]
theorem continuousOn_const_smul_iff (c : G) :
    ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  forall₂_congr fun _ _ => continuousWithinAt_const_smul_iff c
#align continuous_on_const_smul_iff continuousOn_const_smul_iff
#align continuous_on_const_vadd_iff continuousOn_const_vadd_iff

@[to_additive]
theorem continuousAt_const_smul_iff (c : G) :
    ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  tendsto_const_smul_iff c
#align continuous_at_const_smul_iff continuousAt_const_smul_iff
#align continuous_at_const_vadd_iff continuousAt_const_vadd_iff

@[to_additive]
theorem continuous_const_smul_iff (c : G) : (Continuous fun x => c • f x) ↔ Continuous f := by
  simp only [continuous_iff_continuousAt, continuousAt_const_smul_iff]
#align continuous_const_smul_iff continuous_const_smul_iff
#align continuous_const_vadd_iff continuous_const_vadd_iff

/-- The homeomorphism given by scalar multiplication by a given element of a group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
@[to_additive]
def Homeomorph.smul (γ : G) : α ≃ₜ α where
  toEquiv := MulAction.toPerm γ
  continuous_toFun := continuous_const_smul γ
  continuous_invFun := continuous_const_smul γ⁻¹
#align homeomorph.smul Homeomorph.smul
#align homeomorph.vadd Homeomorph.vadd

/-- The homeomorphism given by affine-addition by an element of an additive group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
add_decl_doc Homeomorph.vadd

@[to_additive]
theorem isOpenMap_smul (c : G) : IsOpenMap fun x : α => c • x :=
  (Homeomorph.smul c).isOpenMap
#align is_open_map_smul isOpenMap_smul
#align is_open_map_vadd isOpenMap_vadd

@[to_additive]
theorem IsOpen.smul {s : Set α} (hs : IsOpen s) (c : G) : IsOpen (c • s) :=
  isOpenMap_smul c s hs
#align is_open.smul IsOpen.smul
#align is_open.vadd IsOpen.vadd

@[to_additive]
theorem isClosedMap_smul (c : G) : IsClosedMap fun x : α => c • x :=
  (Homeomorph.smul c).isClosedMap
#align is_closed_map_smul isClosedMap_smul
#align is_closed_map_vadd isClosedMap_vadd

@[to_additive]
theorem IsClosed.smul {s : Set α} (hs : IsClosed s) (c : G) : IsClosed (c • s) :=
  isClosedMap_smul c s hs
#align is_closed.smul IsClosed.smul
#align is_closed.vadd IsClosed.vadd

@[to_additive]
theorem closure_smul (c : G) (s : Set α) : closure (c • s) = c • closure s :=
  ((Homeomorph.smul c).image_closure s).symm
#align closure_smul closure_smul
#align closure_vadd closure_vadd

@[to_additive]
theorem Dense.smul (c : G) {s : Set α} (hs : Dense s) : Dense (c • s) := by
  rw [dense_iff_closure_eq] at hs ⊢; rw [closure_smul, hs, smul_set_univ]
#align dense.smul Dense.smul
#align dense.vadd Dense.vadd

@[to_additive]
theorem interior_smul (c : G) (s : Set α) : interior (c • s) = c • interior s :=
  ((Homeomorph.smul c).image_interior s).symm
#align interior_smul interior_smul
#align interior_vadd interior_vadd

section GroupSeparation

variable [T2Space α]

/--
If the set of group elements `s` is finite and its action on the point `x` is injective,
then one can construct an open set `t` such that for every pair `g ≠ h` of `s`,
`g • t` is disjoint from `h • t`.
-/
@[to_additive "If the set of group elements `s` is finite and its action on the point `x` is
injective, then one can construct an open set `t` such that for every pair `g ≠ h` of `s`,
`g +ᵥ t` is disjoint from `h +ᵥ t`."]
theorem Set.InjOn.t2_separation_smul {s : Set G} {x : α} (inj_on : s.InjOn (· • x))
    (s_finite : s.Finite) : ∃ t : Set α, IsOpen t ∧ x ∈ t ∧
      s.PairwiseDisjoint (fun g => g • t) := by
  let ⟨t, ht, disj⟩ := Set.Finite.t2_separation <| Set.Finite.image (· • x) s_finite

  refine ⟨⋂ g ∈ s, g⁻¹ • t (g • x),
    Set.Finite.isOpen_biInter s_finite fun g _ => IsOpen.smul (ht (g • x)).right g⁻¹,
    ?mem,
    Set.PairwiseDisjoint.mono_on (inj_on.pairwiseDisjoint_image.mp disj) fun g g_in_s => ?disj⟩
  · simp_rw [Set.mem_iInter, Set.mem_inv_smul_set_iff, ht, forall_true_iff]
  · simp only [Function.comp_apply, Set.le_eq_subset, Set.set_smul_subset_iff]
    exact Set.biInter_subset_of_mem g_in_s

/--
If the action of a group `G` on `α` is continuous, then for all points not fixed by `g : G`,
there exists an open set `s` such that `x ∈ s` and `g • s` is disjoint from `s`.
-/
@[to_additive "If the action of a group `G` on `α` is continuous, then for all points not fixed
by `g : G`, there exists an open set `s` such that `x ∈ s` and `g +ᵥ s` is disjoint from `s`."]
theorem t2_separation_smul {x : α} {g : G} (gx_ne : g • x ≠ x) :
    ∃ s : Set α, IsOpen s ∧ x ∈ s ∧ Disjoint s (g • s) := by
  have inj : Set.InjOn (· • x) {g, 1} := by
    rw [Set.injOn_pair, one_smul]
    exact fun h => (gx_ne h).elim

  let ⟨t, t_open, x_in_t, pw_disj⟩ := Set.InjOn.t2_separation_smul inj (toFinite {g, 1})

  refine ⟨t, t_open, x_in_t, ?disj⟩
  simpa [Function.onFun_apply Disjoint, one_smul] using
    (pairwise_pair.mp pw_disj fun eq => gx_ne (eq.symm ▸ one_smul G x)).right


end GroupSeparation

end Group

section GroupWithZero

variable {G₀ : Type*} [TopologicalSpace α] [GroupWithZero G₀] [MulAction G₀ α]
  [ContinuousConstSMul G₀ α]

theorem tendsto_const_smul_iff₀ {f : β → α} {l : Filter β} {a : α} {c : G₀} (hc : c ≠ 0) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  tendsto_const_smul_iff (Units.mk0 c hc)
#align tendsto_const_smul_iff₀ tendsto_const_smul_iff₀

variable [TopologicalSpace β] {f : β → α} {b : β} {c : G₀} {s : Set β}

theorem continuousWithinAt_const_smul_iff₀ (hc : c ≠ 0) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  tendsto_const_smul_iff (Units.mk0 c hc)
#align continuous_within_at_const_smul_iff₀ continuousWithinAt_const_smul_iff₀

theorem continuousOn_const_smul_iff₀ (hc : c ≠ 0) :
    ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  continuousOn_const_smul_iff (Units.mk0 c hc)
#align continuous_on_const_smul_iff₀ continuousOn_const_smul_iff₀

theorem continuousAt_const_smul_iff₀ (hc : c ≠ 0) :
    ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  continuousAt_const_smul_iff (Units.mk0 c hc)
#align continuous_at_const_smul_iff₀ continuousAt_const_smul_iff₀

theorem continuous_const_smul_iff₀ (hc : c ≠ 0) : (Continuous fun x => c • f x) ↔ Continuous f :=
  continuous_const_smul_iff (Units.mk0 c hc)
#align continuous_const_smul_iff₀ continuous_const_smul_iff₀

/-- Scalar multiplication by a non-zero element of a group with zero acting on `α` is a
homeomorphism from `α` onto itself. -/
@[simps! (config := .asFn) apply]
protected def Homeomorph.smulOfNeZero (c : G₀) (hc : c ≠ 0) : α ≃ₜ α :=
  Homeomorph.smul (Units.mk0 c hc)
#align homeomorph.smul_of_ne_zero Homeomorph.smulOfNeZero

@[simp]
theorem Homeomorph.smulOfNeZero_symm_apply {c : G₀} (hc : c ≠ 0) :
    ⇑(Homeomorph.smulOfNeZero c hc).symm = (c⁻¹ • · : α → α) :=
  rfl

theorem isOpenMap_smul₀ {c : G₀} (hc : c ≠ 0) : IsOpenMap fun x : α => c • x :=
  (Homeomorph.smulOfNeZero c hc).isOpenMap
#align is_open_map_smul₀ isOpenMap_smul₀

theorem IsOpen.smul₀ {c : G₀} {s : Set α} (hs : IsOpen s) (hc : c ≠ 0) : IsOpen (c • s) :=
  isOpenMap_smul₀ hc s hs
#align is_open.smul₀ IsOpen.smul₀

theorem interior_smul₀ {c : G₀} (hc : c ≠ 0) (s : Set α) : interior (c • s) = c • interior s :=
  ((Homeomorph.smulOfNeZero c hc).image_interior s).symm
#align interior_smul₀ interior_smul₀

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
#align closure_smul₀ closure_smul₀

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `isClosedMap_smul_left` in `Analysis.NormedSpace.FiniteDimension`. -/
theorem isClosedMap_smul_of_ne_zero {c : G₀} (hc : c ≠ 0) : IsClosedMap fun x : α => c • x :=
  (Homeomorph.smulOfNeZero c hc).isClosedMap
#align is_closed_map_smul_of_ne_zero isClosedMap_smul_of_ne_zero

theorem IsClosed.smul_of_ne_zero {c : G₀} {s : Set α} (hs : IsClosed s) (hc : c ≠ 0) :
    IsClosed (c • s) :=
  isClosedMap_smul_of_ne_zero hc s hs
#align is_closed.smul_of_ne_zero IsClosed.smul_of_ne_zero

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `isClosedMap_smul_left` in `Analysis.NormedSpace.FiniteDimension`. -/
theorem isClosedMap_smul₀ {E : Type*} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E]
    [T1Space E] [ContinuousConstSMul G₀ E] (c : G₀) : IsClosedMap fun x : E => c • x := by
  rcases eq_or_ne c 0 with (rfl | hne)
  · simp only [zero_smul]
    exact isClosedMap_const
  · exact (Homeomorph.smulOfNeZero c hne).isClosedMap
#align is_closed_map_smul₀ isClosedMap_smul₀

theorem IsClosed.smul₀ {E : Type*} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E]
    [T1Space E] [ContinuousConstSMul G₀ E] (c : G₀) {s : Set E} (hs : IsClosed s) :
    IsClosed (c • s) :=
  isClosedMap_smul₀ c s hs
#align is_closed.smul₀ IsClosed.smul₀

theorem HasCompactMulSupport.comp_smul {β : Type*} [One β] {f : α → β} (h : HasCompactMulSupport f)
    {c : G₀} (hc : c ≠ 0) : HasCompactMulSupport fun x => f (c • x) :=
  h.comp_homeomorph (Homeomorph.smulOfNeZero c hc)
#align has_compact_mul_support.comp_smul HasCompactMulSupport.comp_smul

theorem HasCompactSupport.comp_smul {β : Type*} [Zero β] {f : α → β} (h : HasCompactSupport f)
    {c : G₀} (hc : c ≠ 0) : HasCompactSupport fun x => f (c • x) :=
  h.comp_homeomorph (Homeomorph.smulOfNeZero c hc)
#align has_compact_support.comp_smul HasCompactSupport.comp_smul

attribute [to_additive existing HasCompactSupport.comp_smul] HasCompactMulSupport.comp_smul

end GroupWithZero

namespace IsUnit

variable [Monoid M] [TopologicalSpace α] [MulAction M α] [ContinuousConstSMul M α]

nonrec theorem tendsto_const_smul_iff {f : β → α} {l : Filter β} {a : α} {c : M} (hc : IsUnit c) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  let ⟨u, hu⟩ := hc
  hu ▸ tendsto_const_smul_iff u
#align is_unit.tendsto_const_smul_iff IsUnit.tendsto_const_smul_iff

variable [TopologicalSpace β] {f : β → α} {b : β} {c : M} {s : Set β}

nonrec theorem continuousWithinAt_const_smul_iff (hc : IsUnit c) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuousWithinAt_const_smul_iff u
#align is_unit.continuous_within_at_const_smul_iff IsUnit.continuousWithinAt_const_smul_iff

nonrec theorem continuousOn_const_smul_iff (hc : IsUnit c) :
    ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuousOn_const_smul_iff u
#align is_unit.continuous_on_const_smul_iff IsUnit.continuousOn_const_smul_iff

nonrec theorem continuousAt_const_smul_iff (hc : IsUnit c) :
    ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuousAt_const_smul_iff u
#align is_unit.continuous_at_const_smul_iff IsUnit.continuousAt_const_smul_iff

nonrec theorem continuous_const_smul_iff (hc : IsUnit c) :
    (Continuous fun x => c • f x) ↔ Continuous f :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuous_const_smul_iff u
#align is_unit.continuous_const_smul_iff IsUnit.continuous_const_smul_iff

nonrec theorem isOpenMap_smul (hc : IsUnit c) : IsOpenMap fun x : α => c • x :=
  let ⟨u, hu⟩ := hc
  hu ▸ isOpenMap_smul u
#align is_unit.is_open_map_smul IsUnit.isOpenMap_smul

nonrec theorem isClosedMap_smul (hc : IsUnit c) : IsClosedMap fun x : α => c • x :=
  let ⟨u, hu⟩ := hc
  hu ▸ isClosedMap_smul u
#align is_unit.is_closed_map_smul IsUnit.isClosedMap_smul

end IsUnit

-- Porting note (#11215): TODO: use `Set.Nonempty`
/-- Class `ProperlyDiscontinuousSMul Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ:Γ` move `K` to have nontrivial intersection with `L`.
-/
class ProperlyDiscontinuousSMul (Γ : Type*) (T : Type*) [TopologicalSpace T] [SMul Γ T] :
    Prop where
  /-- Given two compact sets `K` and `L`, `γ • K ∩ L` is nonempty for finitely many `γ`. -/
  finite_disjoint_inter_image :
    ∀ {K L : Set T}, IsCompact K → IsCompact L → Set.Finite { γ : Γ | (γ • ·) '' K ∩ L ≠ ∅ }
#align properly_discontinuous_smul ProperlyDiscontinuousSMul

/-- Class `ProperlyDiscontinuousVAdd Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ:Γ` move `K` to have nontrivial intersection with `L`.
-/
class ProperlyDiscontinuousVAdd (Γ : Type*) (T : Type*) [TopologicalSpace T] [VAdd Γ T] :
  Prop where
  /-- Given two compact sets `K` and `L`, `γ +ᵥ K ∩ L` is nonempty for finitely many `γ`. -/
  finite_disjoint_inter_image :
    ∀ {K L : Set T}, IsCompact K → IsCompact L → Set.Finite { γ : Γ | (γ +ᵥ ·) '' K ∩ L ≠ ∅ }
#align properly_discontinuous_vadd ProperlyDiscontinuousVAdd

attribute [to_additive] ProperlyDiscontinuousSMul

variable {Γ : Type*} [Group Γ] {T : Type*} [TopologicalSpace T] [MulAction Γ T]

/-- A finite group action is always properly discontinuous. -/
@[to_additive "A finite group action is always properly discontinuous."]
instance (priority := 100) Finite.to_properlyDiscontinuousSMul [Finite Γ] :
    ProperlyDiscontinuousSMul Γ T where finite_disjoint_inter_image _ _ := Set.toFinite _
#align finite.to_properly_discontinuous_smul Finite.to_properlyDiscontinuousSMul
#align finite.to_properly_discontinuous_vadd Finite.to_properlyDiscontinuousVAdd

export ProperlyDiscontinuousSMul (finite_disjoint_inter_image)
export ProperlyDiscontinuousVAdd (finite_disjoint_inter_image)

/-- The quotient map by a group action is open, i.e. the quotient by a group action is an open
  quotient. -/
@[to_additive "The quotient map by a group action is open, i.e. the quotient by a group
action is an open quotient. "]
theorem isOpenMap_quotient_mk'_mul [ContinuousConstSMul Γ T] :
    letI := MulAction.orbitRel Γ T
    IsOpenMap (Quotient.mk' : T → Quotient (MulAction.orbitRel Γ T)) := fun U hU => by
  rw [isOpen_coinduced, MulAction.quotient_preimage_image_eq_union_mul U]
  exact isOpen_iUnion fun γ => isOpenMap_smul γ U hU
#align is_open_map_quotient_mk_mul isOpenMap_quotient_mk'_mul
#align is_open_map_quotient_mk_add isOpenMap_quotient_mk'_add

/-- The quotient by a discontinuous group action of a locally compact t2 space is t2. -/
@[to_additive "The quotient by a discontinuous group action of a locally compact t2
space is t2."]
instance (priority := 100) t2Space_of_properlyDiscontinuousSMul_of_t2Space [T2Space T]
    [LocallyCompactSpace T] [ContinuousConstSMul Γ T] [ProperlyDiscontinuousSMul Γ T] :
    T2Space (Quotient (MulAction.orbitRel Γ T)) := by
  letI := MulAction.orbitRel Γ T
  set Q := Quotient (MulAction.orbitRel Γ T)
  rw [t2Space_iff_nhds]
  let f : T → Q := Quotient.mk'
  have f_op : IsOpenMap f := isOpenMap_quotient_mk'_mul
  rintro ⟨x₀⟩ ⟨y₀⟩ (hxy : f x₀ ≠ f y₀)
  show ∃ U ∈ 𝓝 (f x₀), ∃ V ∈ 𝓝 (f y₀), _
  have hγx₀y₀ : ∀ γ : Γ, γ • x₀ ≠ y₀ := not_exists.mp (mt Quotient.sound hxy.symm : _)
  obtain ⟨K₀, hK₀, K₀_in⟩ := exists_compact_mem_nhds x₀
  obtain ⟨L₀, hL₀, L₀_in⟩ := exists_compact_mem_nhds y₀
  let bad_Γ_set := { γ : Γ | (γ • ·) '' K₀ ∩ L₀ ≠ ∅ }
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
  refine' ⟨f '' U₀, U_nhds, f '' V₀, V_nhds, MulAction.disjoint_image_image_iff.2 _⟩
  rintro x ⟨x_in_U₀₀, x_in_K₀⟩ γ
  by_cases H : γ ∈ bad_Γ_set
  · exact fun h => (u_v_disjoint γ).le_bot ⟨mem_iInter₂.mp x_in_U₀₀ γ H, mem_iInter₂.mp h.1 γ H⟩
  · rintro ⟨-, h'⟩
    simp only [bad_Γ_set, image_smul, Classical.not_not, mem_setOf_eq, Ne.def] at H
    exact eq_empty_iff_forall_not_mem.mp H (γ • x) ⟨mem_image_of_mem _ x_in_K₀, h'⟩
#align t2_space_of_properly_discontinuous_smul_of_t2_space t2Space_of_properlyDiscontinuousSMul_of_t2Space
#align t2_space_of_properly_discontinuous_vadd_of_t2_space t2Space_of_properlyDiscontinuousVAdd_of_t2Space

/-- The quotient of a second countable space by a group action is second countable. -/
@[to_additive "The quotient of a second countable space by an additive group action is second
countable."]
theorem ContinuousConstSMul.secondCountableTopology [SecondCountableTopology T]
    [ContinuousConstSMul Γ T] : SecondCountableTopology (Quotient (MulAction.orbitRel Γ T)) :=
  TopologicalSpace.Quotient.secondCountableTopology isOpenMap_quotient_mk'_mul
#align has_continuous_const_smul.second_countable_topology ContinuousConstSMul.secondCountableTopology
#align has_continuous_const_vadd.second_countable_topology ContinuousConstVAdd.secondCountableTopology

section nhds

section MulAction

variable {G₀ : Type*} [GroupWithZero G₀] [MulAction G₀ α] [TopologicalSpace α]
  [ContinuousConstSMul G₀ α]

-- Porting note: generalize to a group action + `IsUnit`
/-- Scalar multiplication preserves neighborhoods. -/
theorem set_smul_mem_nhds_smul {c : G₀} {s : Set α} {x : α} (hs : s ∈ 𝓝 x) (hc : c ≠ 0) :
    c • s ∈ 𝓝 (c • x : α) := by
  rw [mem_nhds_iff] at hs ⊢
  obtain ⟨U, hs', hU, hU'⟩ := hs
  exact ⟨c • U, Set.smul_set_mono hs', hU.smul₀ hc, Set.smul_mem_smul_set hU'⟩
#align set_smul_mem_nhds_smul set_smul_mem_nhds_smul

theorem set_smul_mem_nhds_smul_iff {c : G₀} {s : Set α} {x : α} (hc : c ≠ 0) :
    c • s ∈ 𝓝 (c • x : α) ↔ s ∈ 𝓝 x := by
  refine' ⟨fun h => _, fun h => set_smul_mem_nhds_smul h hc⟩
  rw [← inv_smul_smul₀ hc x, ← inv_smul_smul₀ hc s]
  exact set_smul_mem_nhds_smul h (inv_ne_zero hc)
#align set_smul_mem_nhds_smul_iff set_smul_mem_nhds_smul_iff

end MulAction

section DistribMulAction

variable {G₀ : Type*} [GroupWithZero G₀] [AddMonoid α] [DistribMulAction G₀ α] [TopologicalSpace α]
  [ContinuousConstSMul G₀ α]

theorem set_smul_mem_nhds_zero_iff {s : Set α} {c : G₀} (hc : c ≠ 0) :
    c • s ∈ 𝓝 (0 : α) ↔ s ∈ 𝓝 (0 : α) := by
  refine' Iff.trans _ (set_smul_mem_nhds_smul_iff hc)
  rw [smul_zero]
#align set_smul_mem_nhds_zero_iff set_smul_mem_nhds_zero_iff

end DistribMulAction

end nhds
