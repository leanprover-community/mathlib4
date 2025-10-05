/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.WithZeroTopology

/-!

# Valuative Relations with a Valuative Topology are Valued

The `IsValuativeTopology` is described in various equivalent forms as filter bases,
with helper lemmas to construct it under the `ContinuousConstVAdd R R` assumption.
When present on a `ValuativeRel R`, this implies `Valued R (ValueGroupWithZero R)`,
which is provided as an instance.

-/

open ValuativeRel TopologicalSpace Filter Topology Set

namespace IsValuativeTopology

variable {R : Type*} [CommRing R] [ValuativeRel R]

local notation "v" => valuation R

theorem hasBasis_nhds_iff [TopologicalSpace R] :
    IsValuativeTopology R ↔ ∀ x : R,
    (𝓝 x).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero R)ˣ => { z | v (z - x) < γ } := by
  simp_rw [hasBasis_iff, ← neg_add_eq_sub]
  constructor <;> intro h
  · simp [mem_nhds_iff]
  · constructor
    simp [h]

/-- A version mentioning subtraction. -/
lemma mem_nhds_iff' [TopologicalSpace R] [IsValuativeTopology R] {s : Set R} {x : R} :
    s ∈ 𝓝 x ↔
    ∃ γ : (ValueGroupWithZero R)ˣ, { z | v (z - x) < γ } ⊆ s := by
  simp [(hasBasis_nhds_iff.mp _ _).mem_iff]

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.mem_nhds := mem_nhds_iff'

section

variable [TopologicalSpace R] [ContinuousConstVAdd R R]

/-- Assuming `ContinuousConstVAdd R R`, we only need to check the neighbourhood of `0` in order to
prove `IsValuativeTopology R`. -/
theorem iff_nhds_zero :
    IsValuativeTopology R ↔
      ∀ s : Set R, s ∈ 𝓝 0 ↔ ∃ γ : (ValueGroupWithZero R)ˣ, { z | v z < γ } ⊆ s := by
  constructor <;> intro h
  · simp [IsValuativeTopology.mem_nhds_iff]
  · constructor
    intro s x
    simpa [← vadd_mem_nhds_vadd_iff (t := s) (-x), ← image_vadd, ← image_subset_iff] using
      h ((x + ·) ⁻¹' s)

/-- Assuming `ContinuousConstVAdd R R`, we only need to check the neighbourhood of `0` in order to
prove `IsValuativeTopology R`. -/
lemma iff_hasBasis_zero :
    IsValuativeTopology R ↔ (𝓝 (0 : R)).HasBasis (fun _ ↦ True)
      fun γ : (ValueGroupWithZero R)ˣ ↦ { x | (valuation R) x < γ } :=
  iff_nhds_zero.trans ⟨fun h ↦ ⟨by simpa using h⟩, fun h ↦ by simp [h.mem_iff]⟩

end

lemma of_subgroups_basis {R : Type*} [CommRing R] [ValuativeRel R] :
    letI := ((valuation R).subgroups_basis.topology)
    IsValuativeTopology R :=
  letI := ((valuation R).subgroups_basis.topology)
  iff_hasBasis_zero.mpr ((valuation R).subgroups_basis.hasBasis_nhds_zero)

/-- The correctness result. -/
lemma _root_.isValuativeTopology_iff_subgroups_basis_topology_eq [t : TopologicalSpace R] :
    IsValuativeTopology R ↔ (valuation R).subgroups_basis.topology = t := by
  let := (valuation R).subgroups_basis
  refine ⟨fun _ ↦ ext_nhds fun x ↦ Filter.ext fun s ↦ ?_, ?_⟩
  · rw [(this.hasBasis_nhds _).mem_iff, mem_nhds_iff']; simp_rw [true_and]; rfl
  · rintro rfl
    exact .of_subgroups_basis

section

/-! # Results assuming IsValuativeTopology -/

variable [TopologicalSpace R] [IsValuativeTopology R]

variable (R) in
theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero R)ˣ => { x | v x < γ } := by
  simpa using hasBasis_nhds_iff.mp inferInstance (0 : R)

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.hasBasis_nhds_zero := hasBasis_nhds_zero

lemma mem_nhds_zero_iff (s : Set R) : s ∈ 𝓝 (0 : R) ↔
    ∃ γ : (ValueGroupWithZero R)ˣ, { x | v x < γ } ⊆ s := by
  simp [(hasBasis_nhds_zero _).mem_iff]

@[deprecated (since := "2025-08-04")]
alias _root_.ValuativeTopology.mem_nhds_iff := mem_nhds_zero_iff

/-- Helper `Valued` instance when `ValuativeTopology R` over a `UniformSpace R`,
for use in porting files from `Valued` to `ValuativeRel`. -/
instance (priority := low) {R : Type*} [CommRing R] [ValuativeRel R] [UniformSpace R]
    [IsUniformAddGroup R] [IsValuativeTopology R] :
    Valued R (ValueGroupWithZero R) where
  «v» := valuation R
  is_topological_valuation := mem_nhds_zero_iff

variable (R) in
instance (priority := low) instContinuousConstVAdd : ContinuousConstVAdd R R :=
  ⟨fun x ↦ continuous_iff_continuousAt.2 fun z ↦
    ((hasBasis_nhds_iff.mp inferInstance z).tendsto_iff
      (hasBasis_nhds_iff.mp inferInstance (x + z))).2 fun γ _ ↦
      ⟨γ, trivial, fun y hy ↦ by simpa using hy⟩⟩

variable (R) in
instance (priority := low) isTopologicalAddGroup : IsTopologicalAddGroup R := by
  have basis := hasBasis_nhds_zero R
  refine .of_comm_of_nhds_zero ?_ ?_ fun x₀ ↦ (map_eq_of_inverse (-x₀ + ·) ?_ ?_ ?_).symm
  · exact (basis.prod_self.tendsto_iff basis).2 fun γ _ ↦
      ⟨γ, trivial, fun ⟨_, _⟩ hx ↦ (v).map_add_lt hx.left hx.right⟩
  · exact (basis.tendsto_iff basis).2 fun γ _ ↦ ⟨γ, trivial, fun y hy ↦ by simpa using hy⟩
  · ext; simp
  · simpa [ContinuousAt] using (continuous_const_vadd x₀).continuousAt (x := (0 : R))
  · simpa [ContinuousAt] using (continuous_const_vadd (-x₀)).continuousAt (x := x₀)

instance (priority := low) : IsTopologicalRing R :=
  letI := IsTopologicalAddGroup.toUniformSpace R
  letI := isUniformAddGroup_of_addCommGroup (G := R)
  inferInstance

theorem isOpen_ball (r : ValueGroupWithZero R) :
    IsOpen {x | v x < r} := by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · intro x hx
    rw [mem_nhds_iff']
    simp only [setOf_subset_setOf]
    exact ⟨Units.mk0 _ hr,
      fun y hy => (sub_add_cancel y x).symm ▸ ((v).map_add _ x).trans_lt (max_lt hy hx)⟩

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isOpen_ball := isOpen_ball

theorem isClosed_ball (r : ValueGroupWithZero R) :
    IsClosed {x | v x < r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · exact AddSubgroup.isClosed_of_isOpen (Valuation.ltAddSubgroup v (Units.mk0 r hr))
      (isOpen_ball _)

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isClosed_ball := isClosed_ball

theorem isClopen_ball (r : ValueGroupWithZero R) :
    IsClopen {x | v x < r} :=
  ⟨isClosed_ball _, isOpen_ball _⟩

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isClopen_ball := isClopen_ball

lemma isOpen_closedBall {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsOpen {x | v x ≤ r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds_iff']
  simp only [setOf_subset_setOf]
  exact ⟨Units.mk0 _ hr, fun y hy => (sub_add_cancel y x).symm ▸
    le_trans ((v).map_add _ _) (max_le (le_of_lt hy) hx)⟩

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isOpen_closedBall := isOpen_closedBall

theorem isClosed_closedBall (r : ValueGroupWithZero R) :
    IsClosed {x | v x ≤ r} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_setOf_eq, not_le] at hx
  rw [mem_nhds_iff']
  have hx' : v x ≠ 0 := ne_of_gt <| lt_of_le_of_lt zero_le' <| hx
  exact ⟨Units.mk0 _ hx', fun y hy hy' => ne_of_lt hy <| Valuation.map_sub_swap v x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' hx)⟩

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isClosed_closedBall := isClosed_closedBall

theorem isClopen_closedBall {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsClopen {x | v x ≤ r} :=
  ⟨isClosed_closedBall _, isOpen_closedBall hr⟩

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isClopen_closedBall := isClopen_closedBall

theorem isClopen_sphere {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsClopen {x | v x = r} := by
  have h : {x : R | v x = r} = {x | v x ≤ r} \ {x | v x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall hr) (isClopen_ball _)

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isClopen_sphere := isClopen_sphere

lemma isOpen_sphere {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsOpen {x | v x = r} :=
  isClopen_sphere hr |>.isOpen

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isOpen_sphere := isOpen_sphere

open WithZeroTopology in
lemma continuous_valuation : Continuous v := by
  simp only [continuous_iff_continuousAt, ContinuousAt]
  rintro x
  by_cases hx : v x = 0
  · simpa [hx, (hasBasis_nhds_iff.mp inferInstance _).tendsto_iff
      WithZeroTopology.hasBasis_nhds_zero,
      Valuation.map_sub_of_right_eq_zero _ hx] using fun i hi ↦ ⟨.mk0 i hi, fun y ↦ id⟩
  · simpa [(hasBasis_nhds_iff.mp inferInstance _).tendsto_iff
      (WithZeroTopology.hasBasis_nhds_of_ne_zero hx)]
      using ⟨.mk0 (v x) hx, fun _ ↦ Valuation.map_eq_of_sub_lt _⟩
end

section

/-! # Alternate constructors -/

variable [TopologicalSpace R] [ContinuousConstVAdd R R]

/-- A "metatheorem" saying that if we proved that a valuative topology has a certain basis of
`nhds 0`, then any topology having the same basis of `nhds 0` which is also `ContinuousConstVAdd` is
automatically an `IsValuativeTopology`. -/
theorem of_hasBasis {R : Type*} [CommRing R] [ValuativeRel R]
    {ι : Type*} (p : ι → Prop) (s : ι → Set R)
    (ih : ∀ [TopologicalSpace R] [IsValuativeTopology R], (nhds 0).HasBasis p s)
    [τ : TopologicalSpace R] [ContinuousConstVAdd R R] (h : (nhds 0).HasBasis p s) :
    IsValuativeTopology R := by
  rw [isValuativeTopology_iff_subgroups_basis_topology_eq]
  let := (valuation R).subgroups_basis
  specialize @ih this.topology of_subgroups_basis
  refine ext_nhds fun x ↦ Filter.ext fun t ↦ ?_
  rw [← @vadd_mem_nhds_vadd_iff _ _ this.topology _ _ _ _ (-x),
    ← @vadd_mem_nhds_vadd_iff _ _ τ _ _ _ _ (-x),
    vadd_eq_add, neg_add_cancel, h.mem_iff, ih.mem_iff]

lemma iff_hasBasis_ne_zero :
    IsValuativeTopology R ↔
    (𝓝 (0 : R)).HasBasis (· ≠ 0) fun γ ↦ { x | (valuation R) x < γ } :=
  iff_hasBasis_zero.trans <| HasBasis.to_hasBasis_iff
    (fun γ _ ↦ ⟨γ, γ.ne_zero, subset_rfl⟩)
    (fun _ h ↦ ⟨Units.mk0 _ h, trivial, subset_rfl⟩)

variable (R) in
lemma hasBasis_nhds_zero_ne_zero [IsValuativeTopology R] :
    (𝓝 (0 : R)).HasBasis (· ≠ 0) ({ x | (valuation R) x < · }) :=
  iff_hasBasis_ne_zero.mp inferInstance

lemma of_hasBasis_ne_zero
    (h : (𝓝 (0 : R)).HasBasis (· ≠ 0) fun γ ↦ { x | (valuation R) x < γ }) :
    IsValuativeTopology R :=
  iff_hasBasis_ne_zero.mpr h

lemma iff_hasBasis_ne_zero_and_le_one :
    IsValuativeTopology R ↔
    (𝓝 (0 : R)).HasBasis (fun γ ↦ γ ≠ 0 ∧ γ ≤ 1) fun γ ↦ { x | (valuation R) x < γ } :=
  iff_hasBasis_ne_zero.trans <| HasBasis.to_hasBasis_iff
    (fun γ hγ ↦ ⟨min γ 1, ⟨zero_lt_iff.1 <| lt_min (zero_lt_iff.2 hγ) zero_lt_one,
      min_le_right _ _⟩, fun x hx ↦ hx.trans_le (a := v x) (min_le_left _ _)⟩)
    (fun γ hγ ↦ ⟨γ, hγ.1, subset_refl _⟩)

lemma hasBasis_nhds_zero_ne_zero_and_le_one [IsValuativeTopology R] :
    (𝓝 (0 : R)).HasBasis (fun γ ↦ γ ≠ 0 ∧ γ ≤ 1) ({ x | (valuation R) x < · }) :=
  iff_hasBasis_ne_zero_and_le_one.mp inferInstance

lemma of_hasBasis_ne_zero_and_le_one
    (h : (𝓝 (0 : R)).HasBasis (fun γ ↦ γ ≠ 0 ∧ γ ≤ 1) fun γ ↦ { x | (valuation R) x < γ }) :
    IsValuativeTopology R :=
  iff_hasBasis_ne_zero_and_le_one.mpr h

lemma iff_hasBasis_pair :
    IsValuativeTopology R ↔
    (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ rs.1 ∈ posSubmonoid R ∧ rs.2 ∈ posSubmonoid R)
      fun rs ↦ { x | x * rs.2 <ᵥ rs.1 } := by
  rw [iff_hasBasis_zero]
  refine HasBasis.to_hasBasis_iff ?_ ?_
  · simp only [posSubmonoid_def, setOf_subset_setOf, Prod.exists, forall_const]
    intro γ
    obtain ⟨r, s, h⟩ := valuation_surjective γ.val
    by_cases hr : valuation R r = 0
    · simp [hr, eq_comm] at h
    · refine ⟨r, s, ⟨by simpa [valuation_eq_zero_iff] using hr, s.prop⟩, ?_⟩
      simp only [← h]
      intro x hx
      rw [lt_div_iff₀ (by simp [zero_lt_iff])]
      simp [valuation, hx]
  · rintro ⟨r, s⟩ ⟨hr, hs⟩
    refine ⟨Units.mk0 (.mk r ⟨s, hs⟩) ?_, trivial, ?_⟩
    · simpa using hr
    · simp [valuation]

lemma hasBasis_nhds_zero_pair [IsValuativeTopology R] :
    (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ rs.1 ∈ posSubmonoid R ∧ rs.2 ∈ posSubmonoid R)
      fun rs ↦ { x | x * rs.2 <ᵥ rs.1 } :=
  iff_hasBasis_pair.mp inferInstance

lemma of_hasBasis_pair
    (h : (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ rs.1 ∈ posSubmonoid R ∧ rs.2 ∈ posSubmonoid R)
      fun rs ↦ { x | x * rs.2 <ᵥ rs.1 }) :
    IsValuativeTopology R :=
  iff_hasBasis_pair.mpr h

lemma iff_hasBasis_min_inv :
    IsValuativeTopology R ↔
    (𝓝 (0 : R)).HasBasis (fun r : R ↦ r ∈ posSubmonoid R)
      fun r ↦ { x | x <ᵥ r ∧ x * r <ᵥ 1 } := by
  rw [iff_hasBasis_pair]
  refine HasBasis.to_hasBasis_iff ?_ ?_
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain hxy | hxy := rel_total (x * y) 1
    · refine ⟨x * x, mul_mem hx hx, setOf_subset_setOf.mpr fun z hz ↦ ?_⟩
      simp only [Valuation.Compatible.rel_iff_le («v» := v),
        Valuation.Compatible.rel_lt_iff_lt («v» := v), map_mul] at *
      refine ((mul_lt_mul_right (zero_lt_iff.2 ((v).apply_posSubmonoid_ne_zero
        ⟨y, hy⟩))).2 hz.1).trans_le ?_
      rw [mul_assoc]
      exact (mul_le_iff_le_one_right (zero_lt_iff.2 ((v).apply_posSubmonoid_ne_zero
        ⟨x, hx⟩))).2 hxy
    · refine ⟨y * y, mul_mem hy hy, setOf_subset_setOf.mpr fun z hz ↦ ?_⟩
      simp only [Valuation.Compatible.rel_iff_le («v» := v),
        Valuation.Compatible.rel_lt_iff_lt («v» := v), map_mul] at *
      rw [← mul_lt_mul_right (zero_lt_iff.2 ((valuation R).apply_posSubmonoid_ne_zero
         ⟨y, hy⟩)), mul_assoc]
      exact hz.2.trans_le hxy
  · rintro x hx
    obtain hx1 | h1x := le_total (v x) 1
    · refine ⟨(x, 1), ⟨hx, one_mem _⟩, setOf_subset_setOf.mpr fun z hz ↦ ⟨?_, ?_⟩⟩
      · rwa [mul_one] at hz
      · simp only [Valuation.Compatible.rel_lt_iff_lt («v» := v), map_mul, map_one, mul_one] at hz ⊢
        rw [← mul_lt_mul_right (zero_lt_iff.2 ((valuation R).apply_posSubmonoid_ne_zero
          ⟨x, hx⟩))] at hz
        exact hz.trans_le (mul_le_one' hx1 hx1)
    · refine ⟨(1, x), ⟨one_mem _, hx⟩, setOf_subset_setOf.mpr fun z hz ↦ ⟨?_, hz⟩⟩
      simp only [Valuation.Compatible.rel_lt_iff_lt («v» := v), map_mul, map_one] at hz ⊢
      refine lt_of_lt_of_le (lt_of_le_of_lt ?_ hz) h1x
      exact le_mul_of_one_le_right' h1x

lemma hasBasis_nhds_zero_min_inv [IsValuativeTopology R] :
    (𝓝 (0 : R)).HasBasis (fun r : R ↦ r ∈ posSubmonoid R)
      fun r ↦ { x | x <ᵥ r ∧ x * r <ᵥ 1 } :=
  iff_hasBasis_min_inv.mp inferInstance

lemma of_hasBasis_min_inv
    (h : (𝓝 (0 : R)).HasBasis (fun r : R ↦ r ∈ posSubmonoid R)
      fun r ↦ { x | x <ᵥ r ∧ x * r <ᵥ 1 }) :
    IsValuativeTopology R :=
  iff_hasBasis_min_inv.mpr h

lemma iff_hasBasis_compatible {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    {v' : Valuation R Γ₀} [v'.Compatible] :
    IsValuativeTopology R ↔
    (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ v' rs.1 ≠ 0 ∧ v' rs.2 ≠ 0)
      fun rs : R × R ↦ { x | v' x * v' rs.2 < v' rs.1 } := by
  rw [iff_hasBasis_pair]
  refine HasBasis.to_hasBasis_iff ?_ ?_ <;>
  · simp [Valuation.Compatible.rel_iff_le («v» := v'),
      Valuation.Compatible.rel_lt_iff_lt («v» := v')];
    grind

lemma hasBasis_nhds_zero_compatible {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    {v' : Valuation R Γ₀} [v'.Compatible] [IsValuativeTopology R] :
    (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ v' rs.1 ≠ 0 ∧ v' rs.2 ≠ 0)
      fun rs : R × R ↦ { x | v' x * v' rs.2 < v' rs.1 } :=
  iff_hasBasis_compatible.mp inferInstance

lemma of_hasBasis_compatible {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    {v' : Valuation R Γ₀} [v'.Compatible]
    (h : (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ v' rs.1 ≠ 0 ∧ v' rs.2 ≠ 0)
      fun rs : R × R ↦ { x | v' x * v' rs.2 < v' rs.1 }) :
    IsValuativeTopology R :=
  iff_hasBasis_compatible.mpr h

lemma iff_hasBasis_map_ne_zero
    {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [ContinuousConstVAdd F F]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v' : Valuation F Γ₀} [v'.Compatible] :
    IsValuativeTopology F ↔
    (𝓝 (0 : F)).HasBasis (fun r ↦ v' r ≠ 0) fun r ↦ { x | v' x < v' r } :=
  (iff_hasBasis_compatible (v' := v')).trans <| HasBasis.to_hasBasis_iff
  (fun ⟨x, y⟩ hxy ↦ ⟨x / y, by simpa using hxy, by simp [lt_div_iff₀ (zero_lt_iff.2 hxy.2)]⟩)
  fun x hx ↦ ⟨(x, 1), by simp [hx], by simp⟩

lemma hasBasis_nhds_zero_map_ne_zero
    {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [ContinuousConstVAdd F F]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v' : Valuation F Γ₀} [v'.Compatible] [IsValuativeTopology F] :
    (𝓝 (0 : F)).HasBasis (fun r ↦ v' r ≠ 0) fun r ↦ { x | v' x < v' r } :=
  iff_hasBasis_map_ne_zero.mp inferInstance

lemma of_hasBasis_map_ne_zero
    {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [ContinuousConstVAdd F F]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v' : Valuation F Γ₀} [v'.Compatible]
    (h : (𝓝 (0 : F)).HasBasis (fun r ↦ v' r ≠ 0) fun r ↦ { x | v' x < v' r }) :
    IsValuativeTopology F :=
  iff_hasBasis_map_ne_zero.mpr h

end

end IsValuativeTopology

namespace ValuativeRel

@[inherit_doc]
scoped notation "𝒪[" R "]" => Valuation.integer (valuation R)

@[inherit_doc]
scoped notation "𝓂[" K "]" => IsLocalRing.maximalIdeal 𝒪[K]

@[inherit_doc]
scoped notation "𝓀[" K "]" => IsLocalRing.ResidueField 𝒪[K]

end ValuativeRel
