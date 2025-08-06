/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.RingTheory.Valuation.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!

# Valuative Relations as Valued

In this temporary file, we provide a helper instance
for `Valued R Γ` derived from a `ValuativeRel R`,
so that downstream files can refer to `ValuativeRel R`,
to facilitate a refactor.

-/

open ValuativeRel TopologicalSpace Filter Topology Set

/-- A density lemma saying that a fraction `x / y` can be bounded below by either `x * x` (written
without inverses) or `y⁻¹ * y⁻¹` (written only with inverses).

In other words, for a linearly ordered monoid with zero `M` with a "groupification" `G`, `M ∪ M⁻¹`
is dense in `G`.

See `ValuativeRel.exists_min_le` for an application. -/
lemma min_sq_sq_inv_le_div {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (x : Γ₀) {y : Γ₀} (hy : y ≠ 0) :
    min (x * x) (y⁻¹ * y⁻¹) ≤ x / y := by
  obtain hxy | hxy := le_total (x * y) 1
  · calc
    _ ≤ x * x := min_le_left _ _
    _ = x / y * (x * y) := by rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ _ hy]
    _ ≤ x / y := mul_le_of_le_one_right' hxy
  · calc
    _ ≤ y⁻¹ * y⁻¹ := min_le_right _ _
    _ ≤ y⁻¹ * y⁻¹ * (x * y) := le_mul_of_one_le_right' hxy
    _ = (x / y) := by rw [mul_comm, mul_assoc, ← mul_assoc y, mul_inv_cancel₀ hy, one_mul,
        div_eq_mul_inv]

/-- The set `{ min (v r) (v r)⁻¹ | r ∈ posSubmonoid R }` is dense in `Γ₀`.

Intuitively, `{v r} ∪ {(v r)⁻¹}` "tends to" 0. -/
lemma ValuativeRel.exists_min_le {R : Type*} [CommRing R] [ValuativeRel R]
    (γ : (ValueGroupWithZero R)ˣ) :
    ∃ r, valuation R r ≠ 0 ∧ min (valuation R r) (valuation R r)⁻¹ ≤ γ := by
  obtain ⟨x, y, hxy⟩ := valuation_surjective γ.val
  by_cases hx : valuation R x = 0
  · exact (γ.ne_zero <| by rw [← hxy, hx, zero_div, eq_comm]).elim
  have hy : valuation R y ≠ 0 := valuation_eq_zero_iff.not.mpr y.prop
  obtain hxx | hyy := min_le_iff.1 <| min_sq_sq_inv_le_div (valuation R x) hy
  · exact ⟨x * x, by simp [hx], min_le_of_left_le <| by simpa [← hxy] using hxx⟩
  · exact ⟨y * y, by simp [hy], min_le_of_right_le <| by simpa [← hxy] using hyy⟩

namespace IsValuativeTopology

variable {R : Type*} [CommRing R] [ValuativeRel R]
  {F : Type*} [Field F] [ValuativeRel F]
  {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
  {Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀']

local notation "v" => valuation R
local notation "v₀" => valuation F

/-- A version mentioning subtraction. -/
lemma mem_nhds_iff' [TopologicalSpace R] [IsValuativeTopology R] {s : Set R} {x : R} :
    s ∈ 𝓝 (x : R) ↔
    ∃ γ : (ValueGroupWithZero R)ˣ, { z | v (z - x) < γ } ⊆ s := by
  convert mem_nhds_iff (s := s) using 4
  ext z
  simp [neg_add_eq_sub]

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.mem_nhds := mem_nhds_iff'

section

variable [TopologicalSpace R] [ContinuousConstVAdd R R]

/-- Assuming `ContinuousConstVAdd R R`, we only need to check the neighbourhood of `0` in order to
prove `IsValuativeTopology R`. -/
theorem of_zero
    (h₀ : ∀ s : Set R, s ∈ 𝓝 0 ↔ ∃ γ : (ValueGroupWithZero R)ˣ, { z | v z < γ } ⊆ s) :
    IsValuativeTopology R where
  mem_nhds_iff {s x} := by
    simpa [← vadd_mem_nhds_vadd_iff (t := s) (-x), ← image_vadd, ← image_subset_iff] using
      h₀ ((x + ·) ⁻¹' s)

/-- Assuming `ContinuousConstVAdd R R`, we only need to check the neighbourhood of `0` in order to
prove `IsValuativeTopology R`. -/
lemma of_hasBasis_zero (h : (𝓝 (0 : R)).HasBasis (fun _ ↦ True)
    fun γ : (ValueGroupWithZero R)ˣ ↦ { x | (valuation R) x < γ }) :
    IsValuativeTopology R :=
  .of_zero <| by simp [h.mem_iff]

end

instance of_subgroups_basis :
    letI := (v).subgroups_basis.topology
    IsValuativeTopology R :=
  letI := (v).subgroups_basis.topology
  of_hasBasis_zero <| (v).subgroups_basis.hasBasis_nhds_zero

/-- The correctness result. -/
lemma _root_.isValuativeTopology_iff_subgroups_basis_topology_eq [t : TopologicalSpace R] :
    IsValuativeTopology R ↔ (v).subgroups_basis.topology = t := by
  let := (valuation R).subgroups_basis
  refine ⟨fun _ ↦ ext_nhds fun x ↦ Filter.ext fun s ↦ ?_, ?_⟩
  · rw [(this.hasBasis_nhds _).mem_iff, mem_nhds_iff']; simp_rw [true_and]; rfl
  · rintro rfl; infer_instance

example : ∃! _ : TopologicalSpace R, IsValuativeTopology R :=
  ⟨(v).subgroups_basis.topology, of_subgroups_basis, fun _ ht ↦
    (isValuativeTopology_iff_subgroups_basis_topology_eq.mp ht).symm⟩

section

/-! # Results assuming IsValuativeTopology -/

variable [TopologicalSpace R] [IsValuativeTopology R]
  [TopologicalSpace F] [IsValuativeTopology F]

lemma mem_nhds_zero_iff (s : Set R) : s ∈ 𝓝 (0 : R) ↔
    ∃ γ : (ValueGroupWithZero R)ˣ, { x | v x < γ } ⊆ s := by
  convert IsValuativeTopology.mem_nhds_iff' (x := (0 : R))
  rw [sub_zero]

@[deprecated (since := "2025-08-04")]
alias _root_.ValuativeTopology.mem_nhds_iff := mem_nhds_zero_iff

@[simp] lemma ball_mem_nhds_zero_iff (γ : ValueGroupWithZero R) :
    { x | v x < γ } ∈ 𝓝 (0 : R) ↔ γ ≠ 0 :=
  ⟨fun h hγ0 ↦ by simpa [hγ0] using mem_of_mem_nhds h,
  fun hγ0 ↦ (mem_nhds_zero_iff _).mpr ⟨Units.mk0 _ hγ0, subset_refl _⟩⟩

@[simp] lemma rel_ball_mem_nhds_zero_iff (r : R) :
    { x | x <ᵥ r } ∈ 𝓝 (0 : R) ↔ r ∈ posSubmonoid R := by
  simp_rw [Valuation.Compatible.rel_lt_iff_lt («v» := v), ball_mem_nhds_zero_iff,
    ne_eq, valuation_eq_zero_iff, posSubmonoid_def]

@[simp] lemma rel_mul_ball_mem_nhds_zero_iff (r s : R) :
    { x | x * r <ᵥ s } ∈ 𝓝 (0 : R) ↔ s ∈ posSubmonoid R := by
  simp_rw [Valuation.Compatible.rel_lt_iff_lt («v» := v), map_mul]
  by_cases hr : v r = 0
  · simp_rw [hr, mul_zero]
    by_cases hs : v s = 0
    · simp [hs, ← valuation_eq_zero_iff]
    · simp [zero_lt_iff, hs, ← valuation_eq_zero_iff]
  simp_rw [← lt_div_iff₀ (zero_lt_iff.2 hr), ball_mem_nhds_zero_iff, div_ne_zero_iff]
  simp [valuation_eq_zero_iff, hr]

/-- Helper `Valued` instance when `ValuativeTopology R` over a `UniformSpace R`,
for use in porting files from `Valued` to `ValuativeRel`. -/
instance (priority := low) {R : Type*} [CommRing R] [ValuativeRel R] [UniformSpace R]
    [IsUniformAddGroup R] [IsValuativeTopology R] :
    Valued R (ValueGroupWithZero R) where
  «v» := valuation R
  is_topological_valuation := mem_nhds_zero_iff

theorem hasBasis_nhds (x : R) :
    (𝓝 x).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero R)ˣ => { z | v (z - x) < γ } := by
  simp [Filter.hasBasis_iff, mem_nhds_iff']

variable (R) in
theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero R)ˣ => { x | v x < γ } := by
  convert hasBasis_nhds (0 : R); rw [sub_zero]

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.hasBasis_nhds_zero := hasBasis_nhds_zero

variable (R) in
lemma hasBasis_nhds_zero_ne_zero :
    (𝓝 (0 : R)).HasBasis (· ≠ 0) fun γ ↦ { x | (valuation R) x < γ } :=
  (hasBasis_nhds_zero R).to_hasBasis'
    (fun γ _ ↦ ⟨γ, γ.ne_zero, subset_refl _⟩)
    fun γ hγ ↦ by simpa

variable (R) in
lemma hasBasis_nhds_zero_ne_zero_and_le_one :
    (𝓝 (0 : R)).HasBasis (fun γ ↦ γ ≠ 0 ∧ γ ≤ 1) fun γ ↦ { x | (valuation R) x < γ } :=
  (hasBasis_nhds_zero_ne_zero R).to_hasBasis'
    (fun γ hγ ↦ ⟨min γ 1, ⟨zero_lt_iff.1 <| lt_min (zero_lt_iff.2 hγ) zero_lt_one,
      min_le_right _ _⟩, fun x hx ↦ hx.trans_le (a := v x) (min_le_left _ _)⟩)
    fun γ hγ ↦ by simp [hγ.1]

variable (R) in
private lemma hasBasis_nhds_zero_pair_aux :
    (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ v rs.1 ≠ 0 ∧ v rs.2 ≠ 0)
      fun rs ↦ { x | v x < v rs.1 / v rs.2 } := by
  refine (hasBasis_nhds_zero_ne_zero R).to_hasBasis' (fun γ hγ ↦ ?_) (by simp)
  obtain ⟨r, s, rfl⟩ := valuation_surjective γ
  by_cases hr : v r = 0
  · exact (hγ <| by simp [hr]).elim
  · exact ⟨(r, s), ⟨hr, valuation_eq_zero_iff.not.mpr s.prop⟩, subset_refl _⟩

variable (R) in
lemma hasBasis_nhds_zero_pair :
    (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ rs.1 ∈ posSubmonoid R ∧ rs.2 ∈ posSubmonoid R)
      fun rs ↦ { x | x * rs.2 <ᵥ rs.1 } := by
  simp_rw [posSubmonoid_def, ← valuation_eq_zero_iff]
  exact (hasBasis_nhds_zero_pair_aux R).to_hasBasis'
    (fun p hp ↦ ⟨p, hp, by simp_rw [lt_div_iff₀ (zero_lt_iff.2 hp.2), ← map_mul,
      ← Valuation.Compatible.rel_lt_iff_lt, subset_refl]⟩)
    fun p hp ↦ by simpa [valuation_eq_zero_iff] using hp.1

lemma hasBasis_nhds_zero_compatible (v' : Valuation R Γ₀) [v'.Compatible] :
    (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ v' rs.1 ≠ 0 ∧ v' rs.2 ≠ 0)
      fun rs : R × R ↦ { x | v' x * v' rs.2 < v' rs.1 } := by
  convert hasBasis_nhds_zero_pair R <;>
  simp [Valuation.Compatible.rel_iff_le («v» := v'), Valuation.Compatible.rel_lt_iff_lt («v» := v')]

variable (R) in
private lemma hasBasis_nhds_zero_min_inv_aux :
    (𝓝 (0 : R)).HasBasis (fun r : R ↦ v r ≠ 0)
      fun r ↦ { x | v x < min (v r) (v r)⁻¹ } :=
  (hasBasis_nhds_zero R).to_hasBasis'
    (fun γ _ ↦ let ⟨r, hr0, hr⟩ := exists_min_le γ
      ⟨r, hr0, setOf_subset_setOf.mpr fun x hx ↦ hx.trans_le hr⟩)
    fun r hr ↦ by simp_rw [lt_min_iff, setOf_and]; exact inter_mem (by simpa) (by simpa)

lemma hasBasis_nhds_zero_compatible_min_inv (v' : Valuation R Γ₀') [v'.Compatible] :
    (𝓝 (0 : R)).HasBasis (fun r : R ↦ v' r ≠ 0)
      fun r ↦ { x | v' x < min (v' r) (v' r)⁻¹ } := by
  have e := isEquiv (v) v'
  convert hasBasis_nhds_zero_min_inv_aux R with _ _ x
  · rw [← map_zero v', ← map_zero (v), e.val_eq]
  · by_cases h : v x = 0
    · have h' : v' x = 0 := by rwa [← map_zero v', ← e.val_eq, map_zero]
      simp [h, h']
    · have h' : v' x ≠ 0 := by rwa [← map_zero v', ne_eq, ← e.val_eq, map_zero]
      simp_rw [lt_min_iff, inv_eq_one_div, lt_div_iff₀ (zero_lt_iff.2 h),
        lt_div_iff₀ (zero_lt_iff.2 h'), ← map_mul, ← map_one (v), ← map_one (v'), e.lt_iff_lt]

variable (R) in
lemma hasBasis_nhds_zero_lt_and_mul_lt_one :
    (𝓝 (0 : R)).HasBasis (fun r : R ↦ r ∈ posSubmonoid R)
      fun r ↦ { x | x <ᵥ r ∧ x * r <ᵥ 1 } := by
  refine (hasBasis_nhds_zero_min_inv_aux R).to_hasBasis' ?_ ?_
  · intro r hr
    refine ⟨r, valuation_eq_zero_iff.not.mp hr, setOf_subset_setOf.mpr fun x hx ↦ ?_⟩
    rwa [lt_min_iff, inv_eq_one_div, lt_div_iff₀ (zero_lt_iff.2 hr), ← map_mul, ← (v).map_one,
      ← Valuation.Compatible.rel_lt_iff_lt, ← Valuation.Compatible.rel_lt_iff_lt]
  · intro r hr
    rw [setOf_and]
    exact inter_mem (by simpa) (by simp)

variable (F) in
private lemma hasBasis_nhds_zero_ne_zero_aux :
    (𝓝 (0 : F)).HasBasis (· ≠ 0) fun r ↦ { x | v₀ x < v₀ r } :=
  (hasBasis_nhds_zero_min_inv_aux F).to_hasBasis'
    (fun γ hγ ↦ (le_total (v₀ γ) (v₀ γ)⁻¹).casesOn
      (fun h ↦ ⟨γ, (map_ne_zero _).mp hγ, by rw [min_eq_left h]⟩)
      fun h ↦ ⟨γ⁻¹, by simpa using hγ, by rw [min_eq_right h, (v₀).map_inv]⟩)
    fun γ hγ ↦ by simpa

lemma hasBasis_nhds_zero_compatible_ne_zero (v' : Valuation F Γ₀') [v'.Compatible] :
    (𝓝 (0 : F)).HasBasis (· ≠ 0) fun r ↦ { x | v' x < v' r } := by
  convert hasBasis_nhds_zero_ne_zero_aux F
  rw [(isEquiv v' (v₀)).lt_iff_lt]

variable (F) in
lemma hasBasis_nhds_zero_ne_zero' :
    (𝓝 (0 : F)).HasBasis (· ≠ 0) fun r ↦ { x | x <ᵥ r } :=
  (hasBasis_nhds_zero_ne_zero_aux F).to_hasBasis'
    (fun r hr ↦ ⟨r, hr, by simp_rw [← Valuation.Compatible.rel_lt_iff_lt]; rfl⟩)
    fun r hr ↦ by simpa [← valuation_eq_zero_iff]

variable (F) in
private lemma hasBasis_nhds_zero_ne_zero_and_le_one_aux :
    (𝓝 (0 : F)).HasBasis (fun r ↦ r ≠ 0 ∧ v₀ r ≤ 1) fun r ↦ { x | v₀ x < v₀ r } :=
  (hasBasis_nhds_zero_ne_zero_aux F).to_hasBasis'
    (fun r hr ↦ (le_total (v₀ r) 1).casesOn
      (fun h ↦ ⟨r, ⟨hr, h⟩, subset_refl _⟩)
      fun h ↦ ⟨r⁻¹, ⟨inv_ne_zero hr, by rw [map_inv₀]; exact inv_le_one_of_one_le₀ h⟩,
        setOf_subset_setOf.mpr fun x hx ↦ hx.trans_le <| by
          rw [map_inv₀, inv_le_iff_one_le_mul₀ (by simpa [zero_lt_iff])]
          exact one_le_mul h h⟩)
    fun r hr ↦ by simp [hr.1]

lemma hasBasis_nhds_zero_compatible_ne_zero_and_le_one (v' : Valuation F Γ₀') [v'.Compatible] :
    (𝓝 (0 : F)).HasBasis (fun r ↦ r ≠ 0 ∧ v' r ≤ 1) fun r ↦ { x | v' x < v' r } := by
  let e := isEquiv (v₀) v'
  convert hasBasis_nhds_zero_ne_zero_and_le_one_aux F
  · rw [e.le_one_iff_le_one]
  · rw [e.lt_iff_lt]

variable (F) in
lemma hasBasis_nhds_zero_ne_zero_and_le_one' :
    (𝓝 (0 : F)).HasBasis (fun r ↦ r ≠ 0 ∧ r ≤ᵥ 1) fun r ↦ { x | x <ᵥ r } := by
  convert hasBasis_nhds_zero_ne_zero_and_le_one_aux F
  · rw [← map_one v₀, ← Valuation.Compatible.rel_iff_le]
  · rw [← Valuation.Compatible.rel_lt_iff_lt]

variable (R) in
instance (priority := low) isTopologicalAddGroup : IsTopologicalAddGroup R := by
  have cts_add : ContinuousConstVAdd R R :=
    ⟨fun x ↦ continuous_iff_continuousAt.2 fun z ↦
      ((hasBasis_nhds z).tendsto_iff (hasBasis_nhds (x + z))).2 fun γ _ ↦
        ⟨γ, trivial, fun y hy ↦ by simpa using hy⟩⟩
  have basis := hasBasis_nhds_zero R
  refine .of_comm_of_nhds_zero ?_ ?_ fun x₀ ↦ (map_eq_of_inverse (-x₀ + ·) ?_ ?_ ?_).symm
  · exact (basis.prod_self.tendsto_iff basis).2 fun γ _ ↦
      ⟨γ, trivial, fun ⟨_, _⟩ hx ↦ (v).map_add_lt hx.left hx.right⟩
  · exact (basis.tendsto_iff basis).2 fun γ _ ↦ ⟨γ, trivial, fun y hy ↦ by simpa using hy⟩
  · ext; simp
  · simpa [ContinuousAt] using (cts_add.1 x₀).continuousAt (x := (0 : R))
  · simpa [ContinuousAt] using (cts_add.1 (-x₀)).continuousAt (x := x₀)

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

end

section

/-! # Alternate constructors -/

variable [TopologicalSpace R] [ContinuousConstVAdd R R]
  [TopologicalSpace F] [ContinuousConstVAdd F F]

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

lemma of_hasBasis_ne_zero
    (h : (𝓝 (0 : R)).HasBasis (· ≠ 0) fun γ ↦ { x | (valuation R) x < γ }) :
    IsValuativeTopology R :=
  of_hasBasis _ _ (hasBasis_nhds_zero_ne_zero R) h

lemma of_hasBasis_ne_zero_and_le_one
    (h : (𝓝 (0 : R)).HasBasis (fun γ ↦ γ ≠ 0 ∧ γ ≤ 1) fun γ ↦ { x | (valuation R) x < γ }) :
    IsValuativeTopology R :=
  of_hasBasis _ _ (hasBasis_nhds_zero_ne_zero_and_le_one R) h

lemma of_hasBasis_pair
    (h : (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ rs.1 ∈ posSubmonoid R ∧ rs.2 ∈ posSubmonoid R)
      fun rs  ↦ { x | x * rs.2 <ᵥ rs.1 }) :
    IsValuativeTopology R :=
  of_hasBasis _ _ (hasBasis_nhds_zero_pair R) h

lemma of_hasBasis_compatible {v' : Valuation R Γ₀} [v'.Compatible]
    (h : (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ v' rs.1 ≠ 0 ∧ v' rs.2 ≠ 0)
    fun rs : R × R ↦ { x | v' x * v' rs.2 < v' rs.1 }) :
    IsValuativeTopology R :=
  of_hasBasis _ _ (hasBasis_nhds_zero_compatible v') h

lemma of_hasBasis_compatible_min_inv {v' : Valuation R Γ₀'} [v'.Compatible]
    (h : (𝓝 (0 : R)).HasBasis (fun r : R ↦ v' r ≠ 0)
      fun r ↦ { x | v' x < min (v' r) (v' r)⁻¹ }) :
    IsValuativeTopology R :=
  of_hasBasis _ _ (hasBasis_nhds_zero_compatible_min_inv v') h

lemma of_hasBasis_min_inv
    (h : (𝓝 (0 : R)).HasBasis (fun r : R ↦ r ∈ posSubmonoid R)
      fun r ↦ { x | x <ᵥ r ∧ x * r <ᵥ 1 }) :
    IsValuativeTopology R :=
  of_hasBasis _ _ (hasBasis_nhds_zero_lt_and_mul_lt_one R) h

lemma of_hasBasis_compatible_ne_zero {v' : Valuation F Γ₀'} [v'.Compatible]
    (h : (𝓝 (0 : F)).HasBasis (fun r ↦ r ≠ 0) fun r ↦ { x | v' x < v' r }) :
    IsValuativeTopology F :=
  of_hasBasis _ _ (hasBasis_nhds_zero_compatible_ne_zero v') h

lemma of_hasBasis_ne_zero'
    (h : (𝓝 (0 : F)).HasBasis (· ≠ 0) fun r ↦ { x | x <ᵥ r }) :
    IsValuativeTopology F :=
  of_hasBasis _ _ (hasBasis_nhds_zero_ne_zero' F) h

lemma of_hasBasis_compatible_ne_zero_and_le_one {v' : Valuation F Γ₀'} [v'.Compatible]
    (h : (𝓝 (0 : F)).HasBasis (fun r ↦ r ≠ 0 ∧ v' r ≤ 1) fun r ↦ { x | v' x < v' r }) :
    IsValuativeTopology F :=
  of_hasBasis _ _ (hasBasis_nhds_zero_compatible_ne_zero_and_le_one v') h

lemma of_hasBasis_ne_zero_and_le_one'
    (h : (𝓝 (0 : F)).HasBasis (fun r ↦ r ≠ 0 ∧ r ≤ᵥ 1) fun r ↦ { x | x <ᵥ r }) :
    IsValuativeTopology F :=
  of_hasBasis _ _ (hasBasis_nhds_zero_ne_zero_and_le_one' F) h

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
