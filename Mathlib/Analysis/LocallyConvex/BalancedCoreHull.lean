/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.LocallyConvex.Basic

/-!
# Balanced Core and Balanced Hull

## Main definitions

* `balancedCore`: The largest balanced subset of a set `s`.
* `balancedHull`: The smallest balanced superset of a set `s`.

## Main statements

* `balancedCore_eq_iInter`: Characterization of the balanced core as an intersection over subsets.
* `nhds_basis_closed_balanced`: The closed balanced sets form a basis of the neighborhood filter.

## Implementation details

The balanced core and hull are implemented differently: for the core we take the obvious definition
of the union over all balanced sets that are contained in `s`, whereas for the hull, we take the
union over `r • s`, for `r` the scalars with `‖r‖ ≤ 1`. We show that `balancedHull` has the
defining properties of a hull in `Balanced.balancedHull_subset_of_subset` and `subset_balancedHull`.
For the core we need slightly stronger assumptions to obtain a characterization as an intersection,
this is `balancedCore_eq_iInter`.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

balanced
-/


open Set Pointwise Topology Filter

variable {𝕜 E ι : Type*}

section balancedHull

section SeminormedRing

variable [SeminormedRing 𝕜]

section SMul

variable (𝕜) [SMul 𝕜 E] {s t : Set E} {x : E}

/-- The largest balanced subset of `s`. -/
def balancedCore (s : Set E) :=
  ⋃₀ { t : Set E | Balanced 𝕜 t ∧ t ⊆ s }

/-- Helper definition to prove `balanced_core_eq_iInter` -/
def balancedCoreAux (s : Set E) :=
  ⋂ (r : 𝕜) (_ : 1 ≤ ‖r‖), r • s

/-- The smallest balanced superset of `s`. -/
def balancedHull (s : Set E) :=
  ⋃ (r : 𝕜) (_ : ‖r‖ ≤ 1), r • s

variable {𝕜}

theorem balancedCore_subset (s : Set E) : balancedCore 𝕜 s ⊆ s :=
  sUnion_subset fun _ ht => ht.2

theorem balancedCore_empty : balancedCore 𝕜 (∅ : Set E) = ∅ :=
  eq_empty_of_subset_empty (balancedCore_subset _)

theorem mem_balancedCore_iff : x ∈ balancedCore 𝕜 s ↔ ∃ t, Balanced 𝕜 t ∧ t ⊆ s ∧ x ∈ t := by
  simp_rw [balancedCore, mem_sUnion, mem_setOf_eq, and_assoc]

theorem smul_balancedCore_subset (s : Set E) {a : 𝕜} (ha : ‖a‖ ≤ 1) :
    a • balancedCore 𝕜 s ⊆ balancedCore 𝕜 s := by
  rintro x ⟨y, hy, rfl⟩
  rw [mem_balancedCore_iff] at hy
  rcases hy with ⟨t, ht1, ht2, hy⟩
  exact ⟨t, ⟨ht1, ht2⟩, ht1 a ha (smul_mem_smul_set hy)⟩

theorem balancedCore_balanced (s : Set E) : Balanced 𝕜 (balancedCore 𝕜 s) := fun _ =>
  smul_balancedCore_subset s

/-- The balanced core of `t` is maximal in the sense that it contains any balanced subset
`s` of `t`. -/
theorem Balanced.subset_balancedCore_of_subset (hs : Balanced 𝕜 s) (h : s ⊆ t) :
    s ⊆ balancedCore 𝕜 t :=
  subset_sUnion_of_mem ⟨hs, h⟩

lemma Balanced.balancedCore_eq (h : Balanced 𝕜 s) : balancedCore 𝕜 s = s :=
  le_antisymm (balancedCore_subset _) (h.subset_balancedCore_of_subset (subset_refl _))

theorem mem_balancedCoreAux_iff : x ∈ balancedCoreAux 𝕜 s ↔ ∀ r : 𝕜, 1 ≤ ‖r‖ → x ∈ r • s :=
  mem_iInter₂

theorem mem_balancedHull_iff : x ∈ balancedHull 𝕜 s ↔ ∃ r : 𝕜, ‖r‖ ≤ 1 ∧ x ∈ r • s := by
  simp [balancedHull]

/-- The balanced hull of `s` is minimal in the sense that it is contained in any balanced superset
`t` of `s`. -/
theorem Balanced.balancedHull_subset_of_subset (ht : Balanced 𝕜 t) (h : s ⊆ t) :
    balancedHull 𝕜 s ⊆ t := by
  intros x hx
  obtain ⟨r, hr, y, hy, rfl⟩ := mem_balancedHull_iff.1 hx
  exact ht.smul_mem hr (h hy)

@[mono, gcongr]
theorem balancedHull_mono (hst : s ⊆ t) : balancedHull 𝕜 s ⊆ balancedHull 𝕜 t := by
  intro x hx
  rw [mem_balancedHull_iff] at *
  obtain ⟨r, hr₁, hr₂⟩ := hx
  use r
  exact ⟨hr₁, smul_set_mono hst hr₂⟩

end SMul

section Module

variable [AddCommGroup E] [Module 𝕜 E] {s : Set E}

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

variable (𝕜) in
theorem subset_balancedHull [NormOneClass 𝕜] {s : Set E} : s ⊆ balancedHull 𝕜 s := fun _ hx =>
  mem_balancedHull_iff.2 ⟨1, norm_one.le, _, hx, one_smul _ _⟩

theorem balancedHull.balanced (s : Set E) : Balanced 𝕜 (balancedHull 𝕜 s) := by
  intro a ha
  simp_rw [balancedHull, smul_set_iUnion₂, subset_def, mem_iUnion₂]
  rintro x ⟨r, hr, hx⟩
  rw [← smul_assoc] at hx
  exact ⟨a • r, (norm_mul_le _ _).trans (mul_le_one₀ ha (norm_nonneg r) hr), hx⟩

open Balanced in
theorem balancedHull_add_subset [NormOneClass 𝕜] {t : Set E} :
    balancedHull 𝕜 (s + t) ⊆ balancedHull 𝕜 s + balancedHull 𝕜 t :=
  balancedHull_subset_of_subset (add (balancedHull.balanced _) (balancedHull.balanced _))
    (add_subset_add (subset_balancedHull _) (subset_balancedHull _))

end Module

end SeminormedRing

section NormedField

variable [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Set E}

@[simp]
theorem balancedCoreAux_empty : balancedCoreAux 𝕜 (∅ : Set E) = ∅ := by
  simp_rw [balancedCoreAux, iInter₂_eq_empty_iff, smul_set_empty]
  exact fun _ => ⟨1, norm_one.ge, notMem_empty _⟩

theorem balancedCoreAux_subset (s : Set E) : balancedCoreAux 𝕜 s ⊆ s := fun x hx => by
  simpa only [one_smul] using mem_balancedCoreAux_iff.1 hx 1 norm_one.ge

theorem balancedCoreAux_balanced (h0 : (0 : E) ∈ balancedCoreAux 𝕜 s) :
    Balanced 𝕜 (balancedCoreAux 𝕜 s) := by
  rintro a ha x ⟨y, hy, rfl⟩
  obtain rfl | h := eq_or_ne a 0
  · simp_rw [zero_smul, h0]
  rw [mem_balancedCoreAux_iff] at hy ⊢
  intro r hr
  have h'' : 1 ≤ ‖a⁻¹ • r‖ := by
    rw [norm_smul, norm_inv]
    exact one_le_mul_of_one_le_of_one_le ((one_le_inv₀ (norm_pos_iff.mpr h)).2 ha) hr
  have h' := hy (a⁻¹ • r) h''
  rwa [smul_assoc, mem_inv_smul_set_iff₀ h] at h'

theorem balancedCoreAux_maximal (h : t ⊆ s) (ht : Balanced 𝕜 t) : t ⊆ balancedCoreAux 𝕜 s := by
  refine fun x hx => mem_balancedCoreAux_iff.2 fun r hr => ?_
  rw [mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp <| zero_lt_one.trans_le hr)]
  refine h (ht.smul_mem ?_ hx)
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ hr

theorem balancedCore_subset_balancedCoreAux : balancedCore 𝕜 s ⊆ balancedCoreAux 𝕜 s :=
  balancedCoreAux_maximal (balancedCore_subset s) (balancedCore_balanced s)

theorem balancedCore_eq_iInter (hs : (0 : E) ∈ s) :
    balancedCore 𝕜 s = ⋂ (r : 𝕜) (_ : 1 ≤ ‖r‖), r • s := by
  refine balancedCore_subset_balancedCoreAux.antisymm ?_
  refine (balancedCoreAux_balanced ?_).subset_balancedCore_of_subset (balancedCoreAux_subset s)
  exact balancedCore_subset_balancedCoreAux (balancedCore_zero_mem hs)

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
  by_cases h : (0 : E) ∈ U
  · rw [balancedCore_eq_iInter h]
    refine isClosed_iInter fun a => ?_
    refine isClosed_iInter fun ha => ?_
    have ha' := lt_of_lt_of_le zero_lt_one ha
    rw [norm_pos_iff] at ha'
    exact isClosedMap_smul_of_ne_zero ha' U hU
  · have : balancedCore 𝕜 U = ∅ := by
      contrapose! h
      exact balancedCore_nonempty_iff.mp h
    rw [this]
    exact isClosed_empty

-- We don't have a `NontriviallyNormedDivisionRing`, so we use a `NeBot` assumption instead
variable [NeBot (𝓝[≠] (0 : 𝕜))]

theorem balancedCore_mem_nhds_zero (hU : U ∈ 𝓝 (0 : E)) : balancedCore 𝕜 U ∈ 𝓝 (0 : E) := by
  -- Getting neighborhoods of the origin for `0 : 𝕜` and `0 : E`
  obtain ⟨r, V, hr, hV, hrVU⟩ : ∃ (r : ℝ) (V : Set E),
      0 < r ∧ V ∈ 𝓝 (0 : E) ∧ ∀ (c : 𝕜) (y : E), ‖c‖ < r → y ∈ V → c • y ∈ U := by
    have h : Filter.Tendsto (fun x : 𝕜 × E => x.fst • x.snd) (𝓝 (0, 0)) (𝓝 0) :=
      continuous_smul.tendsto' (0, 0) _ (smul_zero _)
    simpa only [← Prod.exists', ← Prod.forall', ← and_imp, ← and_assoc, exists_prop] using
      h.basis_left (NormedAddCommGroup.nhds_zero_basis_norm_lt.prod_nhds (𝓝 _).basis_sets) U hU
  obtain ⟨y, hyr, hy₀⟩ : ∃ y : 𝕜, ‖y‖ < r ∧ y ≠ 0 :=
    Filter.nonempty_of_mem <|
      (nhdsWithin_hasBasis NormedAddCommGroup.nhds_zero_basis_norm_lt {0}ᶜ).mem_of_mem hr
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

theorem nhds_basis_closed_balanced [RegularSpace E] :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ 𝓝 (0 : E) ∧ IsClosed s ∧ Balanced 𝕜 s) id := by
  refine
    (closed_nhds_basis 0).to_hasBasis (fun s hs => ?_) fun s hs => ⟨s, ⟨hs.1, hs.2.1⟩, rfl.subset⟩
  refine ⟨balancedCore 𝕜 s, ⟨balancedCore_mem_nhds_zero hs.1, ?_⟩, balancedCore_subset s⟩
  exact ⟨hs.2.balancedCore, balancedCore_balanced s⟩

end Topology
