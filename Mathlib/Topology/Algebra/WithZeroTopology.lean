/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Algebra.Order.Group.Units
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.OrderClosed

/-!
# The topology on linearly ordered commutative groups with zero

Let `Γ₀` be a linearly ordered commutative group to which we have adjoined a zero element.  Then
`Γ₀` may naturally be endowed with a topology that turns `Γ₀` into a topological monoid.
Neighborhoods of zero are sets containing `{ γ | γ < γ₀ }` for some invertible element `γ₀` and
every invertible element is open.  In particular the topology is the following: "a subset `U ⊆ Γ₀`
is open if `0 ∉ U` or if there is an invertible `γ₀ ∈ Γ₀` such that `{ γ | γ < γ₀ } ⊆ U`", see
`WithZeroTopology.isOpen_iff`.

We prove this topology is ordered and T₅ (in addition to be compatible with the monoid
structure).

All this is useful to extend a valuation to a completion. This is an abstract version of how the
absolute value (resp. `p`-adic absolute value) on `ℚ` is extended to `ℝ` (resp. `ℚₚ`).

## Implementation notes

This topology is defined as a scoped instance since it may not be the desired topology on
a linearly ordered commutative group with zero. You can locally activate this topology using
`open WithZeroTopology`.
-/

open Topology Filter TopologicalSpace Filter Set Function

namespace WithZeroTopology

variable {α Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {γ γ₁ γ₂ : Γ₀} {l : Filter α}
  {f : α → Γ₀}

/-- The topology on a linearly ordered commutative group with a zero element adjoined.
A subset U is open if 0 ∉ U or if there is an invertible element γ₀ such that {γ | γ < γ₀} ⊆ U. -/
scoped instance (priority := 100) topologicalSpace : TopologicalSpace Γ₀ :=
  nhdsAdjoint 0 <| ⨅ γ ≠ 0, 𝓟 (Iio γ)

theorem nhds_eq_update : (𝓝 : Γ₀ → Filter Γ₀) = update pure 0 (⨅ γ ≠ 0, 𝓟 (Iio γ)) := by
  rw [nhds_nhdsAdjoint, sup_of_le_right]
  exact le_iInf₂ fun γ hγ ↦ le_principal_iff.2 <| zero_lt_iff.2 hγ

/-!
### Neighbourhoods of zero
-/

theorem nhds_zero : 𝓝 (0 : Γ₀) = ⨅ γ ≠ 0, 𝓟 (Iio γ) := by
  rw [nhds_eq_update, update_self]

/-- In a linearly ordered group with zero element adjoined, `U` is a neighbourhood of `0` if and
only if there exists a nonzero element `γ₀` such that `Iio γ₀ ⊆ U`. -/
theorem hasBasis_nhds_zero : (𝓝 (0 : Γ₀)).HasBasis (fun γ : Γ₀ => γ ≠ 0) Iio := by
  rw [nhds_zero]
  refine hasBasis_biInf_principal ?_ ⟨1, one_ne_zero⟩
  exact directedOn_iff_directed.2 (Monotone.directed_ge fun a b hab => Iio_subset_Iio hab)

theorem Iio_mem_nhds_zero (hγ : γ ≠ 0) : Iio γ ∈ 𝓝 (0 : Γ₀) :=
  hasBasis_nhds_zero.mem_of_mem hγ

/-- If `γ` is an invertible element of a linearly ordered group with zero element adjoined, then
`Iio (γ : Γ₀)` is a neighbourhood of `0`. -/
theorem nhds_zero_of_units (γ : Γ₀ˣ) : Iio ↑γ ∈ 𝓝 (0 : Γ₀) :=
  Iio_mem_nhds_zero γ.ne_zero

theorem tendsto_zero : Tendsto f l (𝓝 (0 : Γ₀)) ↔ ∀ (γ₀) (_ : γ₀ ≠ 0), ∀ᶠ x in l, f x < γ₀ := by
  simp [nhds_zero]

/-!
### Neighbourhoods of non-zero elements
-/

/-- The neighbourhood filter of a nonzero element consists of all sets containing that
element. -/
@[simp]
theorem nhds_of_ne_zero {γ : Γ₀} (h₀ : γ ≠ 0) : 𝓝 γ = pure γ :=
  nhds_nhdsAdjoint_of_ne _ h₀

/-- The neighbourhood filter of an invertible element consists of all sets containing that
element. -/
theorem nhds_coe_units (γ : Γ₀ˣ) : 𝓝 (γ : Γ₀) = pure (γ : Γ₀) :=
  nhds_of_ne_zero γ.ne_zero

/-- If `γ` is an invertible element of a linearly ordered group with zero element adjoined, then
`{γ}` is a neighbourhood of `γ`. -/
theorem singleton_mem_nhds_of_units (γ : Γ₀ˣ) : ({↑γ} : Set Γ₀) ∈ 𝓝 (γ : Γ₀) := by simp

/-- If `γ` is a nonzero element of a linearly ordered group with zero element adjoined, then `{γ}`
is a neighbourhood of `γ`. -/
theorem singleton_mem_nhds_of_ne_zero (h : γ ≠ 0) : ({γ} : Set Γ₀) ∈ 𝓝 (γ : Γ₀) := by simp [h]

theorem hasBasis_nhds_of_ne_zero {x : Γ₀} (h : x ≠ 0) :
    HasBasis (𝓝 x) (fun _ : Unit => True) fun _ => {x} := by
  rw [nhds_of_ne_zero h]
  exact hasBasis_pure _

theorem hasBasis_nhds_units (γ : Γ₀ˣ) :
    HasBasis (𝓝 (γ : Γ₀)) (fun _ : Unit => True) fun _ => {↑γ} :=
  hasBasis_nhds_of_ne_zero γ.ne_zero

theorem tendsto_of_ne_zero {γ : Γ₀} (h : γ ≠ 0) : Tendsto f l (𝓝 γ) ↔ ∀ᶠ x in l, f x = γ := by
  rw [nhds_of_ne_zero h, tendsto_pure]

theorem tendsto_units {γ₀ : Γ₀ˣ} : Tendsto f l (𝓝 (γ₀ : Γ₀)) ↔ ∀ᶠ x in l, f x = γ₀ :=
  tendsto_of_ne_zero γ₀.ne_zero

theorem Iio_mem_nhds (h : γ₁ < γ₂) : Iio γ₂ ∈ 𝓝 γ₁ := by
  rcases eq_or_ne γ₁ 0 with (rfl | h₀) <;> simp [*, h.ne', Iio_mem_nhds_zero]

/-!
### Open/closed sets
-/

theorem isOpen_iff {s : Set Γ₀} : IsOpen s ↔ (0 : Γ₀) ∉ s ∨ ∃ γ, γ ≠ 0 ∧ Iio γ ⊆ s := by
  rw [isOpen_iff_mem_nhds, ← and_forall_ne (0 : Γ₀)]
  simp +contextual [nhds_of_ne_zero, imp_iff_not_or,
    hasBasis_nhds_zero.mem_iff]

theorem isClosed_iff {s : Set Γ₀} : IsClosed s ↔ (0 : Γ₀) ∈ s ∨ ∃ γ, γ ≠ 0 ∧ s ⊆ Ici γ := by
  simp only [← isOpen_compl_iff, isOpen_iff, mem_compl_iff, not_not, ← compl_Ici,
    compl_subset_compl]

theorem isOpen_Iio {a : Γ₀} : IsOpen (Iio a) :=
  isOpen_iff.mpr <| imp_iff_not_or.mp fun ha => ⟨a, ne_of_gt ha, Subset.rfl⟩

lemma isOpen_singleton (h : γ ≠ 0) : IsOpen {γ} := by simp [isOpen_iff, h.symm]

/-!
### Instances
-/

/-- The topology on a linearly ordered group with zero element adjoined is compatible with the order
structure: the set `{p : Γ₀ × Γ₀ | p.1 ≤ p.2}` is closed. -/
@[nolint defLemma]
scoped instance (priority := 100) orderClosedTopology : OrderClosedTopology Γ₀ where
  isClosed_le' := by
    simp only [← isOpen_compl_iff, compl_setOf, not_le, isOpen_iff_mem_nhds]
    rintro ⟨a, b⟩ (hab : b < a)
    rw [nhds_prod_eq, nhds_of_ne_zero (zero_le'.trans_lt hab).ne', pure_prod]
    exact Iio_mem_nhds hab

/-- The topology on a linearly ordered group with zero element adjoined is T₅. -/
@[nolint defLemma]
scoped instance (priority := 100) t5Space : T5Space Γ₀ where
  completely_normal := fun s t h₁ h₂ => by
    by_cases hs : 0 ∈ s
    · have ht : 0 ∉ t := fun ht => disjoint_left.1 h₁ (subset_closure hs) ht
      rwa [(isOpen_iff.2 (.inl ht)).nhdsSet_eq, disjoint_nhdsSet_principal]
    · rwa [(isOpen_iff.2 (.inl hs)).nhdsSet_eq, disjoint_principal_nhdsSet]

/-- The topology on a linearly ordered group with zero element adjoined makes it a topological
monoid. -/
@[nolint defLemma]
scoped instance (priority := 100) : ContinuousMul Γ₀ where
  continuous_mul := by
    simp only [continuous_iff_continuousAt, ContinuousAt]
    rintro ⟨x, y⟩
    wlog hle : x ≤ y generalizing x y
    · have := (this y x (le_of_not_ge hle)).comp (continuous_swap.tendsto (x, y))
      simpa only [mul_comm, Function.comp_def, Prod.swap] using this
    rcases eq_or_ne x 0 with (rfl | hx) <;> [rcases eq_or_ne y 0 with (rfl | hy); skip]
    · rw [zero_mul]
      refine ((hasBasis_nhds_zero.prod_nhds hasBasis_nhds_zero).tendsto_iff hasBasis_nhds_zero).2
        fun γ hγ => ⟨(γ, 1), ⟨hγ, one_ne_zero⟩, ?_⟩
      rintro ⟨x, y⟩ ⟨hx : x < γ, hy : y < 1⟩
      exact (mul_lt_mul'' hx hy zero_le' zero_le').trans_eq (mul_one γ)
    · rw [zero_mul, nhds_prod_eq, nhds_of_ne_zero hy, prod_pure, tendsto_map'_iff]
      refine (hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero).2 fun γ hγ => ?_
      refine ⟨γ / y, div_ne_zero hγ hy, fun x hx => ?_⟩
      calc x * y < γ / y * y := mul_lt_mul_of_pos_right hx (zero_lt_iff.2 hy)
      _ = γ := div_mul_cancel₀ _ hy
    · have hy : y ≠ 0 := ((zero_lt_iff.mpr hx).trans_le hle).ne'
      rw [nhds_prod_eq, nhds_of_ne_zero hx, nhds_of_ne_zero hy, prod_pure_pure]
      exact pure_le_nhds (x * y)

@[nolint defLemma]
scoped instance (priority := 100) : HasContinuousInv₀ Γ₀ :=
  ⟨fun γ h => by
    rw [ContinuousAt, nhds_of_ne_zero h]
    exact pure_le_nhds γ⁻¹⟩

scoped instance : DiscreteTopology Γ₀ˣ := by
  simp [discreteTopology_iff_singleton_mem_nhds, nhds_induced, nhds_prod_eq, Units.val_inj]

lemma isOpenEmbedding_units_val : IsOpenEmbedding (Units.val : Γ₀ˣ → Γ₀) where
  eq_induced := by
    simp [← isInducing_iff, isInducing_iff_nhds, ← Set.image_singleton,
      Units.val_injective.preimage_image]
  injective := Units.val_injective
  isOpen_range := by simp [isOpen_iff]

lemma locallyCompactSpace_of_compact_Iic {x : Γ₀} (hx : x ≠ 0)
    (h : IsCompact (Iic x)) : LocallyCompactSpace Γ₀ where
  local_compact_nhds y s hy := by
    rcases (GroupWithZero.eq_zero_or_unit y).symm with ⟨y, rfl⟩ | rfl
    · use {y.val}
      simpa using hy
    · simp only [hasBasis_nhds_zero.mem_iff, ne_eq] at hy ⊢
      obtain ⟨r, hr', hr⟩ := hy
      lift x to Γ₀ˣ using IsUnit.mk0 _ hx
      lift r to Γ₀ˣ using IsUnit.mk0 _ hr'
      rcases subsingleton_or_nontrivial Γ₀ˣ with _ | _
      · refine ⟨s, ⟨r, hr', hr⟩, subset_refl _, ?_⟩
        have : IsCompact (Units.val ⁻¹' s) := subsingleton_of_subsingleton.isCompact
        convert (this.image Units.continuous_val).insert 0
        ext x
        rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨y, hy⟩
        · simp only [mem_insert_iff, mem_image, mem_preimage, Units.ne_zero, and_false,
          exists_const, or_false, iff_true]
          refine hr ?_
          simp [zero_lt_iff]
        · simp [hy, Units.val_inj]
      obtain ⟨z, hz⟩ : ∃ z : Γ₀ˣ, (z : Γ₀) < 1 := exists_lt 1
      refine ⟨Iic (Units.val (min (min z x) r) ^ 2), ⟨_, ?_, Iio_subset_Iic_self⟩, hr.trans' ?_,
        h.of_isClosed_subset isClosed_Iic (Iic_subset_Iic.mpr ?_)⟩
      · simp [← zero_lt_iff]
      · simp only [le_eq_subset, Iic_subset_Iio, Units.val_lt_val, ← Units.val_pow_eq_pow_val]
        refine (pow_lt_self_of_lt_one₀ (by simp) ?_ one_lt_two).trans_le ?_ <;>
        simp [hz]
      · simp only [← Units.val_pow_eq_pow_val, Units.val_le_val]
        refine (pow_le_of_le_one (by simp) ?_ two_ne_zero).trans ?_ <;>
        simp [hz.le]

lemma locallyCompactSpace_iff_locallyFiniteOrder_units :
    LocallyCompactSpace Γ₀ ↔ Nonempty (LocallyFiniteOrder Γ₀ˣ) := by
  constructor
  · intro h
    refine ⟨LocallyFiniteOrder.ofFiniteIcc ?_⟩
    suffices ∀ x : Γ₀ˣ, (Icc x 1).Finite by
      rintro x y
      rcases lt_trichotomy y x with hxy | rfl | hxy
      · rw [Set.Icc_eq_empty_of_lt]
        · exact Set.finite_empty
        · simp [hxy]
      · simp
      wlog h : x ≤ 1 generalizing x y
      · push_neg at h
        specialize this y⁻¹ x⁻¹ (inv_lt_inv' hxy) (inv_le_one_of_one_le (h.trans hxy).le)
        refine (this.image (· ⁻¹)).subset ?_
        simp
      generalize_proofs _ _ _ _ hxu hyu
      rcases le_total y 1 with hy | hy
      · exact (this x).subset (Set.Icc_subset_Icc_right hy)
      · have H : (Set.Icc y⁻¹ 1).Finite := this _
        refine ((this x).union H.inv).subset (le_of_eq ?_)
        rw [Set.inv_Icc, inv_one, Set.Icc_union_Icc_eq_Icc] <;>
        simp [h, hy]
    intro z
    obtain ⟨t, ht, ht', ht''⟩ := local_compact_nhds (x := 0) (n := Iio z.val)
      (by simp [hasBasis_nhds_zero.mem_of_mem])
    rw [hasBasis_nhds_zero.mem_iff] at ht
    obtain ⟨y, hy', hy⟩ := ht
    lift y to Γ₀ˣ using IsUnit.mk0 _ hy'
    rw [← Set.image_subset_image_iff (OrderIso.mulLeft₀ y.val⁻¹ (by simp)).injective,
      (OrderIso.mulLeft₀ _ _).image_Iio]
      at hy
    simp only [OrderIso.mulLeft₀_apply, ne_eq, Units.ne_zero, not_false_eq_true,
      inv_mul_cancel₀] at hy
    have : IsCompact (Iic (1 : Γ₀)) := by
      refine ((ht''.image (continuous_mul_left y.val⁻¹)).insert 1).of_isClosed_subset
        isClosed_Iic ?_
      simp [← Iio_insert, insert_subset_insert_iff, hy]
    let f : Γ₀ → Set Γ₀ := fun x ↦ if x < z then Iio z else {x}
    have := this.elim_finite_subcover f ?_ ?_
    · obtain ⟨s, hs⟩ := this
      suffices (Icc z.val 1).Finite from this.preimage (Units.val_injective.injOn)
      refine (s.finite_toSet).subset (
        ((Set.inter_subset_inter_right (Icc z.val 1) hs).trans ?_).trans' ?_)
      · intro x
        simp only [mem_inter_iff, mem_Icc, mem_iUnion, mem_ite, mem_Iio, not_lt, mem_singleton_iff,
          exists_and_left, exists_prop, Finset.mem_coe, and_imp, forall_exists_index, f]
        intro hzx
        simp only [hzx.not_gt, imp_false, not_lt]
        grind
      · simp [Icc_subset_Iic_self]
    · intro x
      simp only [f]
      split_ifs with hx
      · exact isOpen_Iio
      · refine isOpen_singleton ?_
        push_neg at hx
        rw [← zero_lt_iff]
        refine hx.trans_lt' ?_
        simp
    · intro x
      simp only [mem_iUnion, f]
      intro
      use x
      simp [mem_ite]
  · rintro ⟨_⟩
    apply locallyCompactSpace_of_compact_Iic one_ne_zero
    refine isCompact_of_finite_subcover ?_
    intro ι f hf hs
    choose g hg hg' using hs
    choose i hi using hg
    simp only at hi
    simp only [isOpen_iff, ne_eq] at hf
    obtain ⟨y, hy', hy⟩ := (hf (i zero_le_one)).neg_resolve_left (hi zero_le_one ▸ hg' zero_le_one)
    classical
    refine ⟨{i zero_le_one} ∪ (Finset.Icc (Units.mk0 _ hy') 1).attach.image
      (fun z ↦ @i z.val ?_), ?_⟩
    · have := z.prop
      rw [Finset.mem_Icc] at this
      simpa [← Units.val_lt_val] using this.right
    · intro z
      simp only [mem_Iic, Finset.singleton_union, Finset.mem_insert, Finset.mem_image,
        Finset.mem_attach, true_and, Subtype.exists, Finset.mem_Icc, ← Units.val_le_val,
        Units.val_mk0, Units.val_one, iUnion_iUnion_eq_or_left, iUnion_exists, biUnion_and',
        iUnion_iUnion_eq', mem_union, mem_iUnion]
      intro hzx
      rcases lt_or_ge z y with hzy | hzy
      · exact Or.inl (hy (by simp [hzy]))
      · refine Or.inr ⟨Units.mk0 z (ne_of_gt (hzy.trans_lt' (zero_lt_iff.mpr hy'))), ?_⟩
        simp [hzy, hzx, hi, hg']

end WithZeroTopology
