/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Pointwise operations on sets in topological groups

-/

@[expose] public section

open Set Filter TopologicalSpace Function Topology Pointwise MulOpposite

universe u v w x

variable {G : Type w} {H : Type x} {α : Type u} {β : Type v}


/-!
### Topological operations on pointwise sums and products

A few results about interior and closure of the pointwise addition/multiplication of sets in groups
with continuous addition/multiplication. See also `Submonoid.top_closure_mul_self_eq` in
`Topology.Algebra.Monoid`.
-/


section ContinuousConstSMul

variable [TopologicalSpace β] [Group α] [MulAction α β] [ContinuousConstSMul α β] {s : Set α}
  {t : Set β}

variable [TopologicalSpace α]

@[to_additive]
theorem subset_interior_smul : interior s • interior t ⊆ interior (s • t) :=
  (Set.smul_subset_smul_right interior_subset).trans subset_interior_smul_right

end ContinuousConstSMul

section ContinuousSMul

variable [TopologicalSpace α] [TopologicalSpace β] [Group α] [MulAction α β] [ContinuousInv α]
  [ContinuousSMul α β] {s : Set α} {t : Set β}

open Prod in
/-- If `G` acts on `X` continuously, the set `s • t` is closed when `s : Set G` is *compact* and
`t : Set X` is *closed*.

See also `IsClosed.smul_right_of_isCompact` for a version with the assumptions on `s` and `t`
reversed, assuming that the action is *proper*. -/
@[to_additive
/-- If `G` acts on `X` continuously, the set `s +ᵥ t` is closed when `s : Set G` is *compact* and
`t : Set X` is *closed*.

See also `IsClosed.vadd_right_of_isCompact` for a version with the assumptions on `s` and `t`
reversed, assuming that the action is *proper*. -/]
theorem IsClosed.smul_left_of_isCompact (ht : IsClosed t) (hs : IsCompact s) :
    IsClosed (s • t) := by
  let Φ : s × β ≃ₜ s × β :=
  { toFun := fun gx ↦ (gx.1, (gx.1 : α) • gx.2)
    invFun := fun gx ↦ (gx.1, (gx.1 : α)⁻¹ • gx.2)
    left_inv := fun _ ↦ by simp
    right_inv := fun _ ↦ by simp }
  have : s • t = (snd ∘ Φ) '' (snd ⁻¹' t) :=
    subset_antisymm
      (smul_subset_iff.mpr fun g hg x hx ↦ mem_image_of_mem (snd ∘ Φ) (x := ⟨⟨g, hg⟩, x⟩) hx)
      (image_subset_iff.mpr fun ⟨⟨g, hg⟩, x⟩ hx ↦ smul_mem_smul hg hx)
  rw [this]
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  exact (isProperMap_snd_of_compactSpace.comp Φ.isProperMap).isClosedMap _
    (ht.preimage continuous_snd)

@[to_additive]
theorem MulAction.isClosedMap_quotient [CompactSpace α] :
    letI := orbitRel α β
    IsClosedMap (Quotient.mk' : β → Quotient (orbitRel α β)) := by
  intro t ht
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage,
    MulAction.quotient_preimage_image_eq_union_mul]
  convert ht.smul_left_of_isCompact (isCompact_univ (X := α))
  rw [← biUnion_univ, ← iUnion_smul_left_image]
  simp only [image_smul]

end ContinuousSMul

section ContinuousConstSMul

variable [TopologicalSpace α] [Group α] [ContinuousConstSMul α α] {s t : Set α}

@[to_additive]
theorem IsOpen.mul_left : IsOpen t → IsOpen (s * t) :=
  IsOpen.smul_left

@[to_additive]
theorem subset_interior_mul_right : s * interior t ⊆ interior (s * t) :=
  subset_interior_smul_right

@[to_additive]
theorem subset_interior_mul : interior s * interior t ⊆ interior (s * t) :=
  subset_interior_smul

@[to_additive]
theorem singleton_mul_mem_nhds (a : α) {b : α} (h : s ∈ 𝓝 b) : {a} * s ∈ 𝓝 (a * b) := by
  rwa [← smul_eq_mul, ← smul_eq_mul, singleton_smul, smul_mem_nhds_smul_iff]

@[to_additive]
theorem singleton_mul_mem_nhds_of_nhds_one (a : α) (h : s ∈ 𝓝 (1 : α)) : {a} * s ∈ 𝓝 a := by
  simpa only [mul_one] using singleton_mul_mem_nhds a h

end ContinuousConstSMul

section ContinuousConstSMulOp

variable [TopologicalSpace α] [Group α] [ContinuousConstSMul αᵐᵒᵖ α] {s t : Set α}

@[to_additive]
theorem IsOpen.mul_right (hs : IsOpen s) : IsOpen (s * t) := by
  rw [← image_op_smul]
  exact hs.smul_left

@[to_additive]
theorem subset_interior_mul_left : interior s * t ⊆ interior (s * t) :=
  interior_maximal (Set.mul_subset_mul_right interior_subset) isOpen_interior.mul_right

@[to_additive]
theorem subset_interior_mul' : interior s * interior t ⊆ interior (s * t) :=
  (Set.mul_subset_mul_left interior_subset).trans subset_interior_mul_left

@[to_additive]
theorem mul_singleton_mem_nhds (a : α) {b : α} (h : s ∈ 𝓝 b) : s * {a} ∈ 𝓝 (b * a) := by
  rw [mul_singleton]
  exact smul_mem_nhds_smul (op a) h

@[to_additive]
theorem mul_singleton_mem_nhds_of_nhds_one (a : α) (h : s ∈ 𝓝 (1 : α)) : s * {a} ∈ 𝓝 a := by
  simpa only [one_mul] using mul_singleton_mem_nhds a h

end ContinuousConstSMulOp

section IsTopologicalGroup

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G] {s t : Set G}

@[to_additive]
theorem IsOpen.div_left (ht : IsOpen t) : IsOpen (s / t) := by
  rw [← iUnion_div_left_image]
  exact isOpen_biUnion fun a _ => isOpenMap_div_left a t ht

@[to_additive]
theorem IsOpen.div_right (hs : IsOpen s) : IsOpen (s / t) := by
  rw [← iUnion_div_right_image]
  exact isOpen_biUnion fun a _ => isOpenMap_div_right a s hs

@[to_additive]
theorem subset_interior_div_left : interior s / t ⊆ interior (s / t) :=
  interior_maximal (div_subset_div_right interior_subset) isOpen_interior.div_right

@[to_additive]
theorem subset_interior_div_right : s / interior t ⊆ interior (s / t) :=
  interior_maximal (div_subset_div_left interior_subset) isOpen_interior.div_left

@[to_additive]
theorem subset_interior_div : interior s / interior t ⊆ interior (s / t) :=
  (div_subset_div_left interior_subset).trans subset_interior_div_left

@[to_additive]
theorem IsOpen.mul_closure (hs : IsOpen s) (t : Set G) : s * closure t = s * t := by
  refine (mul_subset_iff.2 fun a ha b hb => ?_).antisymm (mul_subset_mul_left subset_closure)
  rw [mem_closure_iff] at hb
  have hbU : b ∈ s⁻¹ * {a * b} := ⟨a⁻¹, Set.inv_mem_inv.2 ha, a * b, rfl, inv_mul_cancel_left _ _⟩
  obtain ⟨_, ⟨c, hc, d, rfl : d = _, rfl⟩, hcs⟩ := hb _ hs.inv.mul_right hbU
  exact ⟨c⁻¹, hc, _, hcs, inv_mul_cancel_left _ _⟩

@[to_additive]
theorem IsOpen.closure_mul (ht : IsOpen t) (s : Set G) : closure s * t = s * t := by
  rw [← inv_inv (closure s * t), mul_inv_rev, inv_closure, ht.inv.mul_closure, mul_inv_rev, inv_inv,
    inv_inv]

@[to_additive]
theorem IsOpen.div_closure (hs : IsOpen s) (t : Set G) : s / closure t = s / t := by
  simp_rw [div_eq_mul_inv, inv_closure, hs.mul_closure]

@[to_additive]
theorem IsOpen.closure_div (ht : IsOpen t) (s : Set G) : closure s / t = s / t := by
  simp_rw [div_eq_mul_inv, ht.inv.closure_mul]

@[to_additive]
theorem IsClosed.mul_left_of_isCompact (ht : IsClosed t) (hs : IsCompact s) : IsClosed (s * t) :=
  ht.smul_left_of_isCompact hs

@[to_additive]
theorem IsClosed.mul_right_of_isCompact (ht : IsClosed t) (hs : IsCompact s) :
    IsClosed (t * s) := by
  rw [← image_op_smul]
  exact IsClosed.smul_left_of_isCompact ht (hs.image continuous_op)

@[to_additive]
lemma subset_mul_closure_one {G} [MulOneClass G] [TopologicalSpace G] (s : Set G) :
    s ⊆ s * (closure {1} : Set G) := by
  have : s ⊆ s * ({1} : Set G) := by simp
  exact this.trans (smul_subset_smul_left subset_closure)

@[to_additive]
lemma IsCompact.mul_closure_one_eq_closure {K : Set G} (hK : IsCompact K) :
    K * (closure {1} : Set G) = closure K := by
  apply Subset.antisymm ?_ ?_
  · calc
    K * (closure {1} : Set G) ⊆ closure K * (closure {1} : Set G) :=
      smul_subset_smul_right subset_closure
    _ ⊆ closure (K * ({1} : Set G)) := smul_set_closure_subset _ _
    _ = closure K := by simp
  · have : IsClosed (K * (closure {1} : Set G)) :=
      IsClosed.smul_left_of_isCompact isClosed_closure hK
    rw [IsClosed.closure_subset_iff this]
    exact subset_mul_closure_one K

@[to_additive]
lemma IsClosed.mul_closure_one_eq {F : Set G} (hF : IsClosed F) :
    F * (closure {1} : Set G) = F := by
  refine Subset.antisymm ?_ (subset_mul_closure_one F)
  calc
  F * (closure {1} : Set G) = closure F * closure ({1} : Set G) := by rw [hF.closure_eq]
  _ ⊆ closure (F * ({1} : Set G)) := smul_set_closure_subset _ _
  _ = F := by simp

@[to_additive]
lemma compl_mul_closure_one_eq {t : Set G} (ht : t * (closure {1} : Set G) = t) :
    tᶜ * (closure {1} : Set G) = tᶜ := by
  refine Subset.antisymm ?_ (subset_mul_closure_one tᶜ)
  rintro - ⟨x, hx, g, hg, rfl⟩
  by_contra H
  have : x ∈ t * (closure {1} : Set G) := by
    rw [← Subgroup.coe_topologicalClosure_bot G] at hg ⊢
    simp only [mem_compl_iff, not_not] at H
    exact ⟨x * g, H, g⁻¹, Subgroup.inv_mem _ hg, by simp⟩
  rw [ht] at this
  exact hx this

@[to_additive]
lemma compl_mul_closure_one_eq_iff {t : Set G} :
    tᶜ * (closure {1} : Set G) = tᶜ ↔ t * (closure {1} : Set G) = t :=
  ⟨fun h ↦ by simpa using compl_mul_closure_one_eq h, fun h ↦ compl_mul_closure_one_eq h⟩

@[to_additive]
lemma IsOpen.mul_closure_one_eq {U : Set G} (hU : IsOpen U) :
    U * (closure {1} : Set G) = U :=
  compl_mul_closure_one_eq_iff.1 (hU.isClosed_compl.mul_closure_one_eq)

end IsTopologicalGroup

section FilterMul

section

variable (G) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

@[to_additive]
instance (priority := 100) IsTopologicalGroup.regularSpace : RegularSpace G := by
  refine .of_exists_mem_nhds_isClosed_subset fun a s hs ↦ ?_
  have : Tendsto (fun p : G × G => p.1 * p.2) (𝓝 (a, 1)) (𝓝 a) :=
    continuous_mul.tendsto' _ _ (mul_one a)
  rcases mem_nhds_prod_iff.mp (this hs) with ⟨U, hU, V, hV, hUV⟩
  rw [← image_subset_iff, image_prod] at hUV
  refine ⟨closure U, mem_of_superset hU subset_closure, isClosed_closure, ?_⟩
  calc
    closure U ⊆ closure U * interior V := subset_mul_left _ (mem_interior_iff_mem_nhds.2 hV)
    _ = U * interior V := isOpen_interior.closure_mul U
    _ ⊆ U * V := mul_subset_mul_left interior_subset
    _ ⊆ s := hUV

variable {G}

@[to_additive]
theorem group_inseparable_iff {x y : G} : Inseparable x y ↔ x / y ∈ closure (1 : Set G) := by
  rw [← singleton_one, ← specializes_iff_mem_closure, specializes_comm, specializes_iff_inseparable,
    ← (Homeomorph.mulRight y⁻¹).isEmbedding.inseparable_iff]
  simp [div_eq_mul_inv]

@[to_additive]
theorem IsTopologicalGroup.t2Space_iff_one_closed : T2Space G ↔ IsClosed ({1} : Set G) :=
  ⟨fun _ ↦ isClosed_singleton, fun h ↦
    have := IsTopologicalGroup.t1Space G h; inferInstance⟩

@[to_additive]
theorem IsTopologicalGroup.t2Space_of_one_sep (H : ∀ x : G, x ≠ 1 → ∃ U ∈ 𝓝 (1 : G), x ∉ U) :
    T2Space G := by
  suffices T1Space G from inferInstance
  refine t1Space_iff_specializes_imp_eq.2 fun x y hspec ↦ by_contra fun hne ↦ ?_
  rcases H (x * y⁻¹) (by rwa [Ne, mul_inv_eq_one]) with ⟨U, hU₁, hU⟩
  exact hU <| mem_of_mem_nhds <| hspec.map (continuous_mul_const y⁻¹) (by rwa [mul_inv_cancel])

/-- Given a neighborhood `U` of the identity, one may find a neighborhood `V` of the identity which
is closed, symmetric, and satisfies `V * V ⊆ U`. -/
@[to_additive /-- Given a neighborhood `U` of the identity, one may find a neighborhood `V` of the
identity which is closed, symmetric, and satisfies `V + V ⊆ U`. -/]
theorem exists_closed_nhds_one_inv_eq_mul_subset {U : Set G} (hU : U ∈ 𝓝 1) :
    ∃ V ∈ 𝓝 1, IsClosed V ∧ V⁻¹ = V ∧ V * V ⊆ U := by
  rcases exists_open_nhds_one_mul_subset hU with ⟨V, V_open, V_mem, hV⟩
  rcases exists_mem_nhds_isClosed_subset (V_open.mem_nhds V_mem) with ⟨W, W_mem, W_closed, hW⟩
  refine ⟨W ∩ W⁻¹, Filter.inter_mem W_mem (inv_mem_nhds_one G W_mem), W_closed.inter W_closed.inv,
    by simp [inter_comm], ?_⟩
  calc
  W ∩ W⁻¹ * (W ∩ W⁻¹)
    ⊆ W * W := mul_subset_mul inter_subset_left inter_subset_left
  _ ⊆ V * V := mul_subset_mul hW hW
  _ ⊆ U := hV

@[to_additive] lemma IsDiscrete.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty
    (S : Subgroup G) (hS : IsDiscrete (S : Set G)) :
    ∃ U ∈ 𝓝 (1 : G), U⁻¹ = U ∧ ∀ g ∈ S, ((g * ·) '' U ∩ U).Nonempty → g = 1 := by
  obtain ⟨V, hV⟩ := nhds_inter_eq_singleton_of_mem_discrete hS S.one_mem
  obtain ⟨U, hU, -, hUinv, hUV⟩ := exists_closed_nhds_one_inv_eq_mul_subset hV.1
  refine ⟨U, hU, hUinv, fun g hgS ↦ ?_⟩
  rintro ⟨_, ⟨x, hx, rfl⟩, hgx⟩
  refine hV.2.subset ⟨hUV ?_, hgS⟩
  rw [← hUinv] at hx
  exact ⟨_, hgx, _, hx, by simp⟩

@[to_additive] lemma IsDiscrete.exists_nhds_eq_one_of_image_mulRight_inter_nonempty
    (S : Subgroup G) (hS : IsDiscrete (S : Set G)) :
    ∃ U ∈ 𝓝 (1 : G), U⁻¹ = U ∧ ∀ g ∈ S, ((· * g) '' U ∩ U).Nonempty → g = 1 := by
  have ⟨U, hU, hUinv, h⟩ := hS.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty
  refine ⟨U, hU, hUinv, fun g hgS hgU ↦ inv_eq_one.mp (h _ (S.inv_mem hgS) ?_)⟩
  rwa [Set.nonempty_image_mulLeft_inv_inter_iff, hUinv]

end

section

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- If a point in a topological group has a compact neighborhood, then the group is
locally compact. -/
@[to_additive]
theorem IsCompact.locallyCompactSpace_of_mem_nhds_of_group {K : Set G} (hK : IsCompact K) {x : G}
    (h : K ∈ 𝓝 x) : LocallyCompactSpace G := by
  suffices WeaklyLocallyCompactSpace G from inferInstance
  refine ⟨fun y ↦ ⟨(y * x⁻¹) • K, ?_, ?_⟩⟩
  · exact hK.smul _
  · rw [← preimage_smul_inv]
    exact (continuous_const_smul _).continuousAt.preimage_mem_nhds (by simpa using h)

/-- If a function defined on a topological group has a support contained in a
compact set, then either the function is trivial or the group is locally compact. -/
@[to_additive
      /-- If a function defined on a topological additive group has a support contained in a compact
      set, then either the function is trivial or the group is locally compact. -/]
theorem eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group
    [TopologicalSpace α] [Zero α] [T1Space α]
    {f : G → α} {k : Set G} (hk : IsCompact k) (hf : support f ⊆ k) (h'f : Continuous f) :
    f = 0 ∨ LocallyCompactSpace G := by
  refine or_iff_not_imp_left.mpr fun h => ?_
  simp_rw [funext_iff, Pi.zero_apply] at h
  push Not at h
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := h
  have : k ∈ 𝓝 x :=
    mem_of_superset (h'f.isOpen_support.mem_nhds hx) hf
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_group hk this

/-- If a function defined on a topological group has compact support, then either
the function is trivial or the group is locally compact. -/
@[to_additive
      /-- If a function defined on a topological additive group has compact support,
      then either the function is trivial or the group is locally compact. -/]
theorem HasCompactSupport.eq_zero_or_locallyCompactSpace_of_group
    [TopologicalSpace α] [Zero α] [T1Space α]
    {f : G → α} (hf : HasCompactSupport f) (h'f : Continuous f) :
    f = 0 ∨ LocallyCompactSpace G :=
  eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group hf (subset_tsupport f) h'f

end

end FilterMul
