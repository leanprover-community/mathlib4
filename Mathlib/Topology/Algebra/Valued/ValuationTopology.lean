/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Algebra.Order.Group.Units
import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.Topology.Algebra.UniformFilterBasis
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# The topology on a valued ring

In this file, we define the non archimedean topology induced by a valuation on a ring.
The main definition is a `Valued` type class which equips a ring with a valuation taking
values in a group with zero. Other instances are then deduced from this.
-/

open scoped Topology uniformity
open Set Valuation

noncomputable section

universe v u

variable {R : Type u} [Ring R] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

variable (v : Valuation R Γ₀)

instance {M : Type*} [Monoid M] {r : M → M → Prop}
    [CovariantClass M M (· * ·) r] (N : Submonoid M):
      CovariantClass N N (· * ·) (fun x y ↦ r x y) := ⟨ by
  rintro ⟨m, _⟩ ⟨n₁, _⟩ ⟨n₂, _⟩
  simpa only [Submonoid.mk_mul_mk] using CovariantClass.elim m ⟩

instance {M : Type*} [Monoid M] [LT M]
    [CovariantClass M M (· * ·) (· < ·)] (N : Submonoid M):
      CovariantClass N N (· * ·) (fun x y ↦ x < y) := ⟨ by
  rintro ⟨m, _⟩ ⟨n₁, _⟩ ⟨n₂, _⟩
  simp only [Subtype.mk_lt_mk, Submonoid.mk_mul_mk]
  exact fun a ↦ mul_lt_mul_left' a m
  ⟩

lemma units_min_eq (γ₀ γ₁ : v.rangeGroup₀ˣ) :
    (min γ₀ γ₁).map v.rangeGroup₀.subtype =
      min (γ₀.map v.rangeGroup₀.subtype) (γ₁.map v.rangeGroup₀.subtype) := by
  simp [Units.ext_iff]

lemma units_max_eq (γ₀ γ₁ : v.rangeGroup₀ˣ) :
    (max γ₀ γ₁).map v.rangeGroup₀.subtype =
      max (γ₀.map v.rangeGroup₀.subtype) (γ₁.map v.rangeGroup₀.subtype) := by
  simp [Units.ext_iff]

/-- The basis of open subgroups for the topology on a ring determined by a valuation. -/
theorem subgroups_basis :
    RingSubgroupsBasis fun γ : v.rangeGroup₀ˣ ↦
      (v.ltAddSubgroup (γ.map v.rangeGroup₀.subtype) : AddSubgroup R) :=
  { inter γ₀ γ₁ := by
      use min γ₀ γ₁
      simp only [units_min_eq, ltAddSubgroup_min]
      apply le_of_eq
      congr
    mul γ := by
      obtain ⟨γ₀, h⟩ := exists_square_le γ
      use γ₀
      rintro - ⟨r, r_in, s, s_in, rfl⟩
      simp only [SetLike.mem_coe, mem_ltAddSubgroup_iff] at r_in s_in
      simp only [SetLike.mem_coe, mem_ltAddSubgroup_iff, _root_.map_mul]
      exact lt_of_lt_of_le ((mul_lt_mul'' r_in s_in) zero_le' zero_le') h
    leftMul x γ := by
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        rintro y hy
        simp only [mem_preimage, SetLike.mem_coe, mem_ltAddSubgroup_iff, map_mul, Hx, zero_mul,
          Units.coe_map, Submonoid.subtype_apply]
        apply γ.zero_lt
      · have Hx' : IsUnit (⟨v x, mem_rangeGroup₀ v⟩ : v.rangeGroup₀) := by
          simp [isUnit_iff_ne_zero, ne_eq, ← Subtype.coe_inj, Hx]
        use Hx'.unit⁻¹ * γ
        intro y vy_lt
        simp only [mem_preimage, SetLike.mem_coe, mem_ltAddSubgroup_iff, _root_.map_mul, Hx]
        simpa [mem_ltAddSubgroup_iff, mul_comm, Hx, lt_mul_inv_iff₀' γx.zero_lt] using vy_lt
    rightMul x γ := by
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        rintro y _
        simp only [mem_preimage, SetLike.mem_coe, mem_ltAddSubgroup_iff]
        rw [Valuation.map_mul, Hx, mul_zero]
        exact Units.zero_lt _
      · have Hx' : IsUnit (⟨v x, mem_rangeGroup₀ v⟩ : v.rangeGroup₀) := by
          simp [isUnit_iff_ne_zero, ne_eq, ← Subtype.coe_inj, Hx]
        use Hx'.unit⁻¹ * γ
        rintro y vy_lt
        simp only [mem_preimage, SetLike.mem_coe, mem_ltAddSubgroup_iff, _root_.map_mul, Hx]
        simpa [mem_ltAddSubgroup_iff, mul_comm, Hx, lt_mul_inv_iff₀' γx.zero_lt] using vy_lt }

end Valuation


/-- A valued ring is a ring that comes equipped with a distinguished group-valued valuation.
The class `Valued` is designed for the situation that there is a canonical valuation on the ring.

TODO: show that there always exists an equivalent valuation taking values in a type belonging to
the same universe as the ring.

See Note [forgetful inheritance] for why we extend `UniformSpace`, `IsUniformAddGroup`. -/
class Valued (R : Type u) [Ring R] (Γ₀ : outParam (Type v))
  [LinearOrderedCommGroupWithZero Γ₀] extends UniformSpace R, IsUniformAddGroup R where
  v : Valuation R Γ₀
  is_topological_valuation : ∀ s, s ∈ 𝓝 (0 : R) ↔
    ∃ γ ∈ v.rangeGroup₀, γ ≠ 0 ∧ { x : R | v x < γ } ⊆ s

namespace Valued

lemma exists_iff_exists (v : Valuation R Γ₀) (motive : Γ₀ → Prop) :
    (∃ u : v.rangeGroup₀ˣ, motive u) ↔
      ∃ γ ∈ v.rangeGroup₀, γ ≠ 0 ∧ motive γ := by
  constructor
  · rintro ⟨u, h⟩
    refine ⟨u.val, u.val.prop, fun h' ↦ ?_, h⟩
    apply u.ne_zero
    rw [← Subtype.coe_inj, h', MonoidHomWithZero.range₀_coe_zero]
  · rintro ⟨γ, hγ, h, h'⟩
    have hγ' : IsUnit (⟨γ, hγ⟩ : v.rangeGroup₀) := by
      simp [← Subtype.coe_inj, h]
    exact ⟨hγ'.unit, h'⟩

/-- Alternative `Valued` constructor for use when there is no preferred `UniformSpace` structure. -/
def mk' (v : Valuation R Γ₀) : Valued R Γ₀ :=
  { v
    toUniformSpace := @IsTopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _
    toIsUniformAddGroup := @isUniformAddGroup_of_addCommGroup _ _ v.subgroups_basis.topology _
    is_topological_valuation := by
      letI := @IsTopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _
      intro s
      rw [Filter.hasBasis_iff.mp v.subgroups_basis.hasBasis_nhds_zero s]
      simp only [true_and, Subtype.exists, exists_prop]
      exact exists_iff_exists v (fun γ ↦ {x | v x < γ} ⊆ s) }

variable (R Γ₀)
variable [_i : Valued R Γ₀]

theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True) fun γ : _i.v.rangeGroup₀ˣ ↦ { x | v x < γ } := by
  simp [Filter.hasBasis_iff, is_topological_valuation]
  intro s
  rw [iff_comm]
  apply exists_iff_exists _i.v (fun γ ↦ {x | v x < γ} ⊆ s)

open Uniformity in
theorem hasBasis_uniformity : (𝓤 R).HasBasis (fun _ => True)
    fun γ : _i.v.rangeGroup₀ˣ ↦
      { p : R × R | v (p.2 - p.1) < γ.map v.rangeGroup₀.subtype } := by
  rw [uniformity_eq_comap_nhds_zero]
  exact (hasBasis_nhds_zero R Γ₀).comap _

theorem toUniformSpace_eq :
    toUniformSpace = @IsTopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _ :=
  UniformSpace.ext
    ((hasBasis_uniformity R Γ₀).eq_of_same_basis <| v.subgroups_basis.hasBasis_nhds_zero.comap _)

variable {R Γ₀}

theorem mem_nhds {s : Set R} {x : R} : s ∈ 𝓝 x ↔ ∃ γ : _i.v.rangeGroup₀ˣ,
    { y | v (y - x) < γ.map v.rangeGroup₀.subtype } ⊆ s := by
  simp [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_setOf_eq, true_and,
    ((hasBasis_nhds_zero R Γ₀).comap fun y => y - x).mem_iff]

theorem mem_nhds_zero {s : Set R} : s ∈ 𝓝 (0 : R) ↔
    ∃ γ : _i.v.rangeGroup₀ˣ, { x | _i.v x < γ.map v.rangeGroup₀.subtype } ⊆ s := by
  simp only [mem_nhds, sub_zero]

theorem loc_const {x : R} (h : (v x : Γ₀) ≠ 0) : { y : R | v y = v x } ∈ 𝓝 x := by
  rw [mem_nhds]
  have hx : IsUnit (⟨v x, v.mem_rangeGroup₀⟩ : v.rangeGroup₀) := by
    simp [← Subtype.coe_inj, h]
  use hx.unit
  intro y
  exact Valuation.map_eq_of_sub_lt _

/-- A valued ring is a topological ring -/
instance (priority := 100) : IsTopologicalRing R :=
  (toUniformSpace_eq R Γ₀).symm ▸ v.subgroups_basis.toRingFilterBasis.isTopologicalRing

theorem cauchy_iff {F : Filter R} : Cauchy F ↔
    F.NeBot ∧ ∀ γ : _i.v.rangeGroup₀ˣ, ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M),
      v (y - x) < γ.map v.rangeGroup₀.subtype := by
  rw [toUniformSpace_eq, AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [Valued.v.subgroups_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h γ
    exact h _ (Valued.v.subgroups_basis.mem_addGroupFilterBasis _)
  · rintro h - ⟨γ, rfl⟩
    exact h γ

variable (R)

theorem ball_subset_ball {a b : R} {r s : Γ₀}
    (hrs : r ≤ s) (hab : v (a - b) < s) :
    { x | v (x - a) < r } ⊆ { x | v (x - b) < s } := by
  intro x
  simp only [mem_setOf_eq]
  intro hx
  rw [← sub_add_sub_cancel x a b]
  apply map_add_lt _ (lt_of_lt_of_le hx hrs) hab

/-- An open ball in a valued ring is open if its radius is a unit of `rangeGroup₀` -/
theorem isOpen_ball (a : R) (r : _i.v.rangeGroup₀ˣ) :
    IsOpen (X := R) {x | v (x - a) < r } := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [setOf_subset_setOf]
  simp only [mem_setOf_eq] at hx
  use r
  intro y hy
  simp only [Units.coe_map, Submonoid.subtype_apply] at hy
  rw [← sub_add_sub_cancel y x a]
  apply v.map_add_lt hy hx

/-- An open ball centered at the origin in a valued ring is closed. -/
theorem isClosed_ball (a : R) (r : Γ₀) :
    IsClosed (X := R) {x | v (x - a) < r} := by
  rcases eq_or_ne r 0 with rfl|hr
  · simp
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro b hb
  simp only [mem_compl_iff, mem_setOf_eq, not_lt] at hb
  simp only [mem_nhds_iff]
  use {x | v (x - b) < v (b - a) }
  constructor
  · intro x hx
    simp only [mem_setOf_eq, mem_compl_iff, not_lt] at ⊢ hx
    rwa [← sub_add_sub_cancel x b a, map_add_eq_of_lt_right v hx]
  constructor
  · have ha' : IsUnit (⟨v (b - a) , v.mem_rangeGroup₀⟩ : v.rangeGroup₀) := by
      simp only [isUnit_iff_ne_zero, ne_eq, ← Subtype.coe_inj, MonoidHomWithZero.range₀_coe_zero]
      intro h
      apply hr
      rwa [h, le_zero_iff] at hb
    exact isOpen_ball R b ha'.unit
  · simp only [mem_setOf_eq, sub_self, map_zero]
    exact lt_of_lt_of_le (zero_lt_iff.mpr hr) hb

/-- In a valued ring, an open ball whose radius is unit in `rangeGroup₀` is clopen. -/
theorem isClopen_ball (a : R) (r : _i.v.rangeGroup₀ˣ) :
    IsClopen (X := R) {x | v (x - a) < r } :=
  ⟨isClosed_ball _ _ _, isOpen_ball _ _ _⟩

/-- In a valued ring, a closed ball whose radius is a unit of `rangeGroup₀` is open. -/
theorem isOpen_closedball {a : R} {r : _i.v.rangeGroup₀ˣ} :
    IsOpen (X := R) {x | v (x - a) ≤ r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [setOf_subset_setOf]
  use r
  intro b hb
  simp only [mem_setOf_eq] at hx
  simp only [Units.coe_map, Submonoid.subtype_apply] at hb
  rw [← sub_add_sub_cancel b x a]
  exact v.map_add_le (le_of_lt hb) hx

/-- A closed ball in a valued ring is closed. -/
theorem isClosed_closedBall (a : R) (r : Γ₀) :
    IsClosed (X := R) {x | v (x - a) ≤ r} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [mem_compl_iff, mem_setOf_eq, not_le] at hx
  have : IsUnit (⟨v (x - a), v.mem_rangeGroup₀⟩ : v.rangeGroup₀) := by
    simp only [isUnit_iff_ne_zero, ne_eq]
    simp only [← Subtype.coe_inj, MonoidHomWithZero.range₀_coe_zero,
      ← zero_lt_iff]
    exact lt_of_le_of_lt zero_le' hx
  use this.unit
  intro y
  simp only [Units.coe_map, IsUnit.unit_spec, Submonoid.subtype_apply, mem_setOf_eq, mem_compl_iff,
    not_le]
  intro hy
  rw [← sub_add_sub_cancel y x a, add_comm, map_add_eq_of_lt_left v hy]
  exact hx

/-- In a valued ring, a closed ball whose radius is a unit of `v.rangeGroup₀` is clopen. -/
theorem isClopen_closedBall {a : R} {r : _i.v.rangeGroup₀ˣ} :
    IsClopen (X := R) {x | v (x - a) ≤ r} :=
  ⟨isClosed_closedBall _ _ _, isOpen_closedball _⟩

/-- A sphere centred at the origin in a valued ring is clopen. -/
theorem isClopen_sphere {a : R} {r : Γ₀} (hr : r ≠ 0) :
    IsClopen (X := R) {x | v (x - a) = r} := by
  by_cases h : ∃ x, v (x - a) = r
  · have H : {x : R | v (x - a) = r} = {x | v (x - a) ≤ r} \ {x | v (x - a) < r} := by
      ext x; simp [← le_antisymm_iff]
    rw [H]
    suffices ∃ γ : _i.v.rangeGroup₀ˣ, γ = r by
      obtain ⟨γ, rfl⟩ := this
      exact IsClopen.diff (isClopen_closedBall R) (isClopen_ball R a γ)
    obtain ⟨x, h⟩ := h
    have h' : IsUnit (⟨v (x-a), v.mem_rangeGroup₀⟩ : v.rangeGroup₀) := by
      simpa [isUnit_iff_ne_zero, ne_eq, ← Subtype.coe_inj, h] using hr
    use h'.unit
    simp [← h]
  · convert isClopen_empty
    apply Set.eq_empty_of_forall_not_mem
    push_neg at h
    exact h

/-- A sphere centred at the origin in a valued ring is open. -/
theorem isOpen_sphere {a : R} {r : Γ₀} (hr : r ≠ 0) :
    IsOpen (X := R) {x | v (x - a) = r} :=
  isClopen_sphere _ hr |>.isOpen

/-- A sphere centred at the origin in a valued ring is closed. -/
theorem isClosed_sphere (a : R) (r : Γ₀) :
    IsClosed (X := R) {x | v (x - a) = r} := by
  rcases eq_or_ne r 0 with rfl|hr
  · simpa using isClosed_closedBall R a 0
  exact isClopen_sphere _ hr |>.isClosed

/-- The closed unit ball in a valued ring is open. -/
theorem isOpen_integer : IsOpen (_i.v.integer : Set R) := by
  simpa only [sub_zero, Units.val_one, OneMemClass.coe_one] using
    isOpen_closedball R (a := 0) (r := 1)

@[deprecated (since := "2025-04-25")]
alias integer_isOpen := isOpen_integer

/-- The closed unit ball of a valued ring is closed. -/
theorem isClosed_integer : IsClosed (_i.v.integer : Set R) := by
  simpa only [sub_zero] using isClosed_closedBall R 0 1

/-- The closed unit ball of a valued ring is clopen. -/
theorem isClopen_integer : IsClopen (_i.v.integer : Set R) :=
  ⟨isClosed_integer _, isOpen_integer _⟩

/-- The valuation subring of a valued field is open. -/
theorem isOpen_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsOpen (hv.v.valuationSubring : Set K) :=
  isOpen_integer K

@[deprecated (since := "2025-04-25")]
alias valuationSubring_isOpen := isOpen_valuationSubring

/-- The valuation subring of a valued field is closed. -/
theorem isClosed_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsClosed (hv.v.valuationSubring : Set K) :=
  isClosed_integer K

/-- The valuation subring of a valued field is clopen. -/
theorem isClopen_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsClopen (hv.v.valuationSubring : Set K) :=
  isClopen_integer K

end Valued
