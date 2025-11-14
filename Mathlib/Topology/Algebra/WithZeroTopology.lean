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

lemma isOpen_singleton (h : γ ≠ 0) : IsOpen {γ} := isOpen_singleton_nhdsAdjoint _ h

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

instance : DiscreteTopology { g : Γ₀ // g ≠ 0 } := by
  simpa [discreteTopology_iff_singleton_mem_nhds, nhds_induced] using by aesop

instance : DiscreteTopology Γ₀ˣ :=
  unitsHomeomorphNeZero.symm.discreteTopology

theorem isInducing_unitsVal : IsInducing (Units.val : Γ₀ˣ → Γ₀) :=
  by simp [isInducing_iff_nhds, ← image_singleton, Units.val_injective.preimage_image]

lemma isOpenEmbedding_units_val : IsOpenEmbedding (Units.val : Γ₀ˣ → Γ₀) where
  eq_induced := isInducing_unitsVal.1
  injective := Units.val_injective
  isOpen_range := by simp [isOpen_iff]

lemma locallyCompactSpace_of_compact_Iio (h : IsCompact (Iio (1 : Γ₀))) :
    LocallyCompactSpace Γ₀ := by
  have key (x : Γ₀) : (𝓝 x).HasBasis (fun r : Γ₀ ↦ x = 0 → r ≠ 0)
      fun r ↦ if x = 0 then Iio r else {x} := by
    split_ifs with h
    · simpa [h] using hasBasis_nhds_zero
    · simpa [h] using (Filter.hasBasis_pure x).to_hasBasis (by simp) (by simp)
  refine LocallyCompactSpace.of_hasBasis key fun r i hr ↦ ?_
  split_ifs with hr0
  · convert h.image (continuous_mul_left i)
    rw [image_mul_left_Iio (zero_lt_iff.mpr <| hr hr0), mul_one]
  · exact isCompact_singleton

theorem compact_Iio_of_locallyCompactSpace [LocallyCompactSpace Γ₀] (r : Γ₀) :
    IsCompact (Iio r) := by
  obtain rfl | hr0 := eq_or_ne r 0
  · simp [← bot_eq_zero'']
  obtain ⟨s, hs0, _, hcs⟩ := local_compact_nhds <| Iio_mem_nhds_zero (Γ₀ := Γ₀) one_ne_zero
  obtain ⟨w, hw0, hws⟩ := hasBasis_nhds_zero.mem_iff.mp hs0
  convert (hcs.of_isClosed_subset (by simp_all [isClosed_iff, zero_lt_iff]) hws).image
    (continuous_mul_left (r / w))
  rw [image_mul_left_Iio (by simp_all [zero_lt_iff]), div_mul_cancel₀ _ hw0]

theorem compact_Iic_of_locallyCompactSpace [LocallyCompactSpace Γ₀] (r : Γ₀) :
    IsCompact (Iic r) :=
  Set.Iio_insert (a := r) ▸ (compact_Iio_of_locallyCompactSpace r).insert _

theorem compact_Icc_of_locallyCompactSpace [LocallyCompactSpace Γ₀] (x y : Γ₀) :
    IsCompact (Icc x y) :=
  (compact_Iic_of_locallyCompactSpace y).of_isClosed_subset isClosed_Icc Icc_subset_Iic_self

lemma locallyCompactSpace_iff_locallyFiniteOrder_units :
    LocallyCompactSpace Γ₀ ↔ Nonempty (LocallyFiniteOrder Γ₀ˣ) := by
  -- `[x, y]` is compact, but `Γ₀ˣ` is discrete, so `[x, y]` is finite.
  constructor
  · intro h
    refine ⟨LocallyFiniteOrder.ofFiniteIcc fun x y ↦ IsCompact.finite_of_discrete <|
      isInducing_unitsVal.isCompact_iff.mpr ?_⟩
    convert compact_Icc_of_locallyCompactSpace x.val y.val
    exact Set.ext fun z ↦ ⟨fun ⟨z', h1, h2⟩ ↦ h2 ▸ h1,
      fun h ↦ ⟨.mk0 z <| ne_of_gt <| x.zero_lt.trans_le h.1, h, rfl⟩⟩
  · rintro ⟨_⟩
    -- it suffices to show that `[0, 1)` is compact
    refine locallyCompactSpace_of_compact_Iio ?_
    -- for that, it suffices to show that the cofinite filter on `{ γ : Γ₀ˣ | γ < 1 }` tends to 0
    let c : Iio (1 : Γ₀ˣ) → Γ₀ := (·.1.1)
    have : Tendsto c cofinite (𝓝 0) := fun s hs ↦ by
      obtain ⟨r, hr0, hrs⟩ := hasBasis_nhds_zero.mem_iff.mp hs
      refine .of_finite_image ((finite_Ico (.mk0 r hr0) 1).subset ?_) Subtype.val_injective.injOn
      exact fun y ⟨x, hx, hxy⟩ ↦ hxy ▸ ⟨le_of_not_gt fun hxr ↦ hx <| hrs hxr, x.2⟩
    convert this.isCompact_insert_range_of_cofinite
    exact Set.ext fun x ↦ ⟨fun hx ↦ or_iff_not_imp_left.mpr fun hx0 ↦ ⟨⟨.mk0 x hx0, hx⟩, rfl⟩,
      Or.rec (· ▸ zero_lt_one) fun ⟨y, hxy⟩ ↦ hxy ▸ y.2⟩

end WithZeroTopology
