/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.LocallyConvex.Basic

/-!
# Balanced Core and Balanced Hull

## Main definitions

* `balancedCore`: The largest balanced subset of a set `s`.
* `balancedHull`: The smallest balanced superset of a set `s`.

## Main statements

* `balancedCore_eq_iInter`: Characterization of the balanced core as an intersection over subsets.
* `nhds_basis_closed_balanced`: The closed balanced sets form a basis of the neighborhood filter.

## Implementation details

The hull is defined as the `ClosureOperator` associated to the predicate `Balanced 𝕜` (which is
stable under `Balanced.sInter`), i.e. as the intersection over all balanced sets containing `s`;
the `ClosureOperator` API then supplies its defining properties `subset_balancedHull` and
`Balanced.balancedHull_subset_of_subset`. The core is defined directly as the union over all
balanced sets contained in `s`, its defining properties being `balancedCore_subset` and
`Balanced.subset_balancedCore_of_subset`. Dually to the hull, it could be defined as the
`ClosureOperator` on `(Set E)ᵒᵈ` associated to `Balanced 𝕜` (which is stable under
`Balanced.sUnion`), but that gains little over the four one-line proofs below.

Under slightly stronger assumptions, the hull can be described as the union over `r • s`, for `r`
the scalars with `‖r‖ ≤ 1`; this is `balancedHull_eq_iUnion`. Likewise, the core can be
characterized as an intersection, this is `balancedCore_eq_iInter`.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

balanced
-/

@[expose] public section


open Set Pointwise Filter

open scoped Topology

variable {𝕜 E ι : Type*}

section balancedHull

section SeminormedRing

variable [SeminormedRing 𝕜]

section SMul

variable (𝕜) [SMul 𝕜 E] {s t : Set E} {x : E}

/-- The largest balanced subset of `s`. -/
def balancedCore (s : Set E) : Set E :=
  ⋃₀ { t : Set E | Balanced 𝕜 t ∧ t ⊆ s }

/-- The smallest balanced superset of `s`. -/
def balancedHull : ClosureOperator (Set E) :=
  .ofCompletePred (Balanced 𝕜) fun _ ↦ .sInter

variable {𝕜}

theorem balancedCore_subset (s : Set E) : balancedCore 𝕜 s ⊆ s :=
  sUnion_subset fun _ ht ↦ ht.2

theorem balancedCore_balanced (s : Set E) : Balanced 𝕜 (balancedCore 𝕜 s) :=
  .sUnion fun _ ht ↦ ht.1

/-- The balanced core of `t` is maximal in the sense that it contains any balanced subset
`s` of `t`. -/
theorem Balanced.subset_balancedCore_of_subset (hs : Balanced 𝕜 s) (h : s ⊆ t) :
    s ⊆ balancedCore 𝕜 t :=
  subset_sUnion_of_mem ⟨hs, h⟩

@[mono, gcongr]
theorem balancedCore_mono (hst : s ⊆ t) : balancedCore 𝕜 s ⊆ balancedCore 𝕜 t :=
  (balancedCore_balanced s).subset_balancedCore_of_subset ((balancedCore_subset s).trans hst)

theorem balancedCore_empty : balancedCore 𝕜 (∅ : Set E) = ∅ :=
  eq_empty_of_subset_empty (balancedCore_subset _)

theorem mem_balancedCore_iff : x ∈ balancedCore 𝕜 s ↔ ∃ t, Balanced 𝕜 t ∧ t ⊆ s ∧ x ∈ t := by
  simp_rw [balancedCore, mem_sUnion, mem_ofPred_eq, and_assoc]

theorem smul_balancedCore_subset (s : Set E) {a : 𝕜} (ha : ‖a‖ ≤ 1) :
    a • balancedCore 𝕜 s ⊆ balancedCore 𝕜 s :=
  balancedCore_balanced s a ha

lemma Balanced.balancedCore_eq (h : Balanced 𝕜 s) : balancedCore 𝕜 s = s :=
  le_antisymm (balancedCore_subset _) (h.subset_balancedCore_of_subset subset_rfl)

theorem balancedHull.balanced (s : Set E) : Balanced 𝕜 (balancedHull 𝕜 s) :=
  (balancedHull 𝕜).isClosed_closure s

variable (𝕜) in
theorem subset_balancedHull : s ⊆ balancedHull 𝕜 s :=
  (balancedHull 𝕜).le_closure s

/-- The balanced hull of `s` is minimal in the sense that it is contained in any balanced superset
`t` of `s`. -/
theorem Balanced.balancedHull_subset_of_subset (ht : Balanced 𝕜 t) (h : s ⊆ t) :
    balancedHull 𝕜 s ⊆ t :=
  ClosureOperator.closure_min h ht

@[mono, gcongr]
theorem balancedHull_mono (hst : s ⊆ t) : balancedHull 𝕜 s ⊆ balancedHull 𝕜 t :=
  (balancedHull 𝕜).monotone hst

end SMul

section Module

variable [AddCommGroup E] [Module 𝕜 E] {s : Set E} {x : E}

theorem balancedCore_zero_mem (hs : (0 : E) ∈ s) : (0 : E) ∈ balancedCore 𝕜 s :=
  mem_balancedCore_iff.2 ⟨0, balanced_zero, zero_subset.2 hs, Set.zero_mem_zero⟩

theorem balancedCore_nonempty_iff : (balancedCore 𝕜 s).Nonempty ↔ (0 : E) ∈ s :=
  ⟨fun h => zero_subset.1 <| (zero_smul_set h).superset.trans <|
    (balancedCore_balanced s (0 : 𝕜) <| norm_zero.trans_le zero_le_one).trans <|
      balancedCore_subset _,
    fun h => ⟨0, balancedCore_zero_mem h⟩⟩

lemma Balanced.zero_mem (hs : Balanced 𝕜 s) (hs_nonempty : s.Nonempty) : (0 : E) ∈ s := by
  rw [← hs.balancedCore_eq] at hs_nonempty
  exact balancedCore_nonempty_iff.mp hs_nonempty

/-- The balanced hull of `s` is the union of the sets `r • s`, for `r` a scalar with `‖r‖ ≤ 1`. -/
theorem balancedHull_eq_iUnion [NormOneClass 𝕜] (s : Set E) :
    balancedHull 𝕜 s = ⋃ (r : 𝕜) (_ : ‖r‖ ≤ 1), r • s := by
  refine subset_antisymm (Balanced.balancedHull_subset_of_subset ?_ ?_) ?_
  · intro a ha
    simp_rw [smul_set_iUnion₂, subset_def, mem_iUnion₂]
    rintro x ⟨r, hr, hx⟩
    rw [← smul_assoc] at hx
    exact ⟨a • r, (norm_mul_le _ _).trans (mul_le_one₀ ha (norm_nonneg r) hr), hx⟩
  · exact fun x hx ↦ mem_iUnion₂.2 ⟨1, norm_one.le, x, hx, one_smul _ _⟩
  · exact iUnion₂_subset fun r hr ↦
      (smul_set_mono (subset_balancedHull 𝕜)).trans (balancedHull.balanced s r hr)

theorem mem_balancedHull_iff [NormOneClass 𝕜] :
    x ∈ balancedHull 𝕜 s ↔ ∃ r : 𝕜, ‖r‖ ≤ 1 ∧ x ∈ r • s := by
  simp [balancedHull_eq_iUnion]

theorem balancedHull_add_subset {t : Set E} :
    balancedHull 𝕜 (s + t) ⊆ balancedHull 𝕜 s + balancedHull 𝕜 t :=
  (balancedHull 𝕜).closure_binop_le (fun _ _ _ _ h h' ↦ add_subset_add h h')
    (fun _ _ hs ht ↦ hs.add ht) s t

end Module

end SeminormedRing

section NormedField

variable [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Set E}

theorem iInter_smul_subset (s : Set E) : (⋂ (r : 𝕜) (_ : 1 ≤ ‖r‖), r • s) ⊆ s := fun x hx => by
  simpa only [one_smul] using mem_iInter₂.1 hx 1 norm_one.ge

/-- Any balanced subset of `s` is contained in `⋂ (r : 𝕜) (_ : 1 ≤ ‖r‖), r • s`. -/
theorem Balanced.subset_iInter_smul (ht : Balanced 𝕜 t) (h : t ⊆ s) :
    t ⊆ ⋂ (r : 𝕜) (_ : 1 ≤ ‖r‖), r • s := by
  refine fun x hx => mem_iInter₂.2 fun r hr => ?_
  rw [mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp <| zero_lt_one.trans_le hr)]
  refine h (ht.smul_mem ?_ hx)
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ hr

/-- If `s` contains the origin, then `⋂ (r : 𝕜) (_ : 1 ≤ ‖r‖), r • s` is balanced; by
`balancedCore_eq_iInter` it is then the balanced core of `s`. -/
theorem balanced_iInter_smul (hs : (0 : E) ∈ s) :
    Balanced 𝕜 (⋂ (r : 𝕜) (_ : 1 ≤ ‖r‖), r • s) := by
  have h0 : (0 : E) ∈ ⋂ (r : 𝕜) (_ : 1 ≤ ‖r‖), r • s :=
    mem_iInter₂.2 fun r _ => ⟨0, hs, smul_zero r⟩
  rintro a ha x ⟨y, hy, rfl⟩
  obtain rfl | h := eq_or_ne a 0
  · simp_rw [zero_smul, h0]
  rw [mem_iInter₂] at hy ⊢
  intro r hr
  have h'' : 1 ≤ ‖a⁻¹ • r‖ := by
    rw [norm_smul, norm_inv]
    exact one_le_mul_of_one_le_of_one_le ((one_le_inv₀ (norm_pos_iff.mpr h)).2 ha) hr
  have h' := hy (a⁻¹ • r) h''
  rwa [smul_assoc, mem_inv_smul_set_iff₀ h] at h'

theorem balancedCore_eq_iInter (hs : (0 : E) ∈ s) :
    balancedCore 𝕜 s = ⋂ (r : 𝕜) (_ : 1 ≤ ‖r‖), r • s :=
  ((balancedCore_balanced s).subset_iInter_smul (balancedCore_subset s)).antisymm
    ((balanced_iInter_smul hs).subset_balancedCore_of_subset (iInter_smul_subset s))

theorem subset_balancedCore (ht : (0 : E) ∈ t) (hst : ∀ a : 𝕜, ‖a‖ ≤ 1 → a • s ⊆ t) :
    s ⊆ balancedCore 𝕜 t := by
  rw [balancedCore_eq_iInter ht]
  refine subset_iInter₂ fun a ha ↦ ?_
  rw [subset_smul_set_iff₀ (norm_pos_iff.mp <| zero_lt_one.trans_le ha)]
  apply hst
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ ha

end NormedField

end balancedHull

/-! ### Topological properties -/

section Topology

variable [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [ContinuousSMul 𝕜 E] {U : Set E}

protected theorem IsClosed.balancedCore (hU : IsClosed U) : IsClosed (balancedCore 𝕜 U) := by
  obtain h | h := eq_empty_or_nonempty (balancedCore 𝕜 U)
  · simp [h]
  · rw [balancedCore_eq_iInter (balancedCore_nonempty_iff.mp h)]
    refine isClosed_iInter fun a => ?_
    refine isClosed_iInter fun ha => ?_
    have ha' := lt_of_lt_of_le zero_lt_one ha
    rw [norm_pos_iff] at ha'
    exact isClosedMap_smul_of_ne_zero ha' U hU

omit [ContinuousSMul 𝕜 E] in
protected theorem IsOpen.balancedHull [ContinuousConstSMul 𝕜 E] {s : Set E} (hs : IsOpen s)
    (hzero : 0 ∈ s) : IsOpen (balancedHull 𝕜 s) := by
  have : (⋃ r : 𝕜, ⋃ (_ : ‖r‖ ≤ 1), r • s) = (⋃ r : 𝕜, ⋃ (_ : ‖r‖ ≤ 1 ∧ r ≠ 0), r • s) := by
    refine subset_antisymm (Set.iUnion₂_mono' fun r hr ↦ ?_) (Set.iUnion₂_mono' (by grind))
    obtain rfl | hr_ne := eq_or_ne r 0
    · exact ⟨1, by simp, by simpa [Set.zero_smul_set ⟨0, hzero⟩]⟩
    · use r
  rw [balancedHull_eq_iUnion, this]
  exact isOpen_biUnion (fun r hr ↦ hs.smul₀ hr.2)

-- We don't have a `NontriviallyNormedDivisionRing`, so we use a `NeBot` assumption instead
variable [NeBot (𝓝[≠] (0 : 𝕜))]

theorem balancedCore_mem_nhds_zero (hU : U ∈ 𝓝 (0 : E)) : balancedCore 𝕜 U ∈ 𝓝 (0 : E) := by
  -- Getting neighborhoods of the origin for `0 : 𝕜` and `0 : E`
  obtain ⟨r, V, hr, hV, hrVU⟩ : ∃ (r : ℝ) (V : Set E),
      0 < r ∧ V ∈ 𝓝 (0 : E) ∧ ∀ (c : 𝕜) (y : E), ‖c‖ < r → y ∈ V → c • y ∈ U := by
    have h : Filter.Tendsto (fun x : 𝕜 × E => x.fst • x.snd) (𝓝 (0, 0)) (𝓝 0) :=
      continuous_smul.tendsto' (0, 0) _ (smul_zero _)
    simpa only [← Prod.exists', ← Prod.forall', ← and_imp, ← and_assoc, exists_prop] using!
      h.basis_left (NormedAddGroup.nhds_zero_basis_norm_lt.prod_nhds (𝓝 _).basis_sets) U hU
  obtain ⟨y, hyr, hy₀⟩ : ∃ y : 𝕜, ‖y‖ < r ∧ y ≠ 0 :=
    Filter.nonempty_of_mem <|
      (nhdsWithin_hasBasis NormedAddGroup.nhds_zero_basis_norm_lt {0}ᶜ).mem_of_mem hr
  have : y • V ∈ 𝓝 (0 : E) := (set_smul_mem_nhds_zero_iff hy₀).mpr hV
  -- It remains to show that `y • V ⊆ balancedCore 𝕜 U`
  refine Filter.mem_of_superset this (subset_balancedCore (mem_of_mem_nhds hU) fun a ha => ?_)
  rw [smul_smul]
  rintro _ ⟨z, hz, rfl⟩
  refine hrVU _ _ ?_ hz
  rw [norm_mul, ← one_mul r]
  exact mul_lt_mul' ha hyr (norm_nonneg y) one_pos

variable (𝕜 E)

theorem nhds_basis_balanced :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ 𝓝 (0 : E) ∧ Balanced 𝕜 s) id :=
  Filter.hasBasis_self.mpr fun s hs =>
    ⟨balancedCore 𝕜 s, balancedCore_mem_nhds_zero hs, balancedCore_balanced s,
      balancedCore_subset s⟩

/-- The open balanced sets form a basis of the neighborhood filter of the origin: the balanced hull
of an open neighborhood of `0` is again open. -/
theorem nhds_basis_open_balanced :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ 𝓝 (0 : E) ∧ IsOpen s ∧ Balanced 𝕜 s) id :=
  (nhds_basis_opens' 0).and_isClosed (c := balancedHull 𝕜) (nhds_basis_balanced 𝕜 E)
    fun _ hs hso ↦ hso.balancedHull (mem_of_mem_nhds hs)

/-- The closed balanced sets form a basis of the neighborhood filter of the origin: the closure of
a balanced neighborhood of `0` is again balanced. -/
theorem nhds_basis_closed_balanced [RegularSpace E] :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ 𝓝 (0 : E) ∧ IsClosed s ∧ Balanced 𝕜 s) id :=
  ((nhds_basis_balanced 𝕜 E).and_isClosed (c := closureOperator E) (closed_nhds_basis 0)
    fun _ _ ht ↦ ht.closure).to_hasBasis
      (fun s hs ↦ ⟨s, ⟨hs.1, hs.2.2, hs.2.1⟩, Subset.rfl⟩)
      (fun s hs ↦ ⟨s, ⟨hs.1, hs.2.2, hs.2.1⟩, Subset.rfl⟩)

end Topology
