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

*NOTE* (2025-07-02):
The `Valued` class defined in this file will eventually get replaced with `ValuativeRel`
from `Mathlib.RingTheory.Valuation.ValuativeRel`. New developments on valued rings/fields
should take this into considation.

-/

open scoped Topology uniformity
open Set Valuation

noncomputable section

universe v u

variable {R K : Type u} [Ring R] [DivisionRing K] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

variable (v : Valuation R Γ₀)

/-- The basis of open additive subgroups for the topology on a ring determined by a valuation.
This basis induces a finer topology than the basis of open additive subgroups that are bounded
by values in the valuation's value group (`Valuation.subgroups_range_basis`),
since the codomain here have elements that are smaller than any in the range of the valuation,
causing the trivial additive subgroup `{0}` to be open, which induces the discrete topology.
-/
theorem subgroups_basis : RingSubgroupsBasis fun γ : Γ₀ˣ => (v.ltAddSubgroup γ : AddSubgroup R) :=
  { inter := by
      rintro γ₀ γ₁
      use min γ₀ γ₁
      simp only [ltAddSubgroup, Units.min_val, lt_min_iff,
        AddSubgroup.mk_le_mk, setOf_subset_setOf, le_inf_iff, and_imp, imp_self, implies_true,
        and_true]
      tauto
    mul := by
      rintro γ
      obtain ⟨γ₀, h⟩ := exists_square_le γ
      use γ₀
      rintro - ⟨r, r_in, s, s_in, rfl⟩
      simp only [ltAddSubgroup, AddSubgroup.coe_set_mk, mem_setOf_eq] at r_in s_in
      calc
        (v (r * s) : Γ₀) = v r * v s := Valuation.map_mul _ _ _
        _ < γ₀ * γ₀ := by gcongr <;> exact zero_le'
        _ ≤ γ := mod_cast h
    leftMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use (1 : Γ₀ˣ)
        rintro y _
        change v (x * y) < _
        rw [Valuation.map_mul, Hx, zero_mul]
        exact Units.zero_lt γ
      · use γx⁻¹ * γ
        rintro y (vy_lt : v y < ↑(γx⁻¹ * γ))
        change (v (x * y) : Γ₀) < γ
        rw [Valuation.map_mul, Hx, mul_comm]
        rw [Units.val_mul, mul_comm] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt
    rightMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        rintro y _
        change v (y * x) < _
        rw [Valuation.map_mul, Hx, mul_zero]
        exact Units.zero_lt γ
      · use γx⁻¹ * γ
        rintro y (vy_lt : v y < ↑(γx⁻¹ * γ))
        change (v (y * x) : Γ₀) < γ
        rw [Valuation.map_mul, Hx]
        rw [Units.val_mul, mul_comm] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt }

/-- The basis of open additive subgroups for the topology on a ring determined by a valuation.
This basis induces a coarser topology than the basis of open additive subgroups that are bounded
by a positive element of the codomain (`Valuation.subgroups_basis`),
since the codomain might be larger than the range of the valuation.
-/
theorem subgroups_range_basis : RingSubgroupsBasis
    fun rs : {rs : R × R // v rs.1 ≠ 0 ∧ v rs.2 ≠ 0} ↦
    (v.ltAddSubgroup (Units.mk0 (v rs.val.2 / v rs.val.1) (by simp [rs.prop])) : AddSubgroup R) :=
  { inter := by
      rintro ⟨⟨r, s⟩, hr, hs⟩ ⟨⟨t, u⟩, ht, hu⟩
      rcases le_total (v s / v r) (v u / v t) with h | h
      · use ⟨⟨r, s⟩, hr, hs⟩
        simpa [ltAddSubgroup, AddSubgroup.mk_le_mk] using fun _ ↦ h.trans_lt'
      · use ⟨⟨t, u⟩, ht, hu⟩
        simpa [ltAddSubgroup, AddSubgroup.mk_le_mk] using fun _ ↦ h.trans_lt'
    mul := by
      intro γ
      refine (le_total (v γ.val.2) (v γ.val.1)).elim (fun h ↦ ⟨γ, ?_⟩)
        (fun h ↦ ⟨⟨γ.val.swap, γ.prop.symm⟩, ?_⟩)
      all_goals
        intro x
        simp only [ltAddSubgroup, Units.val_mk0, AddSubgroup.coe_set_mk, mem_mul, mem_setOf_eq,
          forall_exists_index, and_imp]
        rintro y hy z hz rfl
        rw [map_mul]
        refine (mul_lt_mul'' hy hz zero_le' zero_le').trans_le ?_
      · refine mul_le_of_le_one_right' ?_
        exact div_le_one_of_le₀ h zero_le'
      · simp only [ne_eq, Prod.snd_swap, Prod.fst_swap]
        rw [div_mul_div_comm, div_le_div_iff₀, mul_assoc]
        · gcongr
        · simp [zero_lt_iff, γ.prop]
        · simp [zero_lt_iff, γ.prop]
    leftMul := by
      rintro x ⟨⟨r, s⟩, hr, hs⟩
      rcases eq_or_ne (v x) 0 with (Hx | Hx)
      · use ⟨1, by simp⟩
        rintro y
        simp [ltAddSubgroup, Hx, zero_lt_iff, hr, hs]
      · use ⟨⟨r * x, s⟩, by simp [Hx, hr, hs]⟩
        rintro y
        simp only [ltAddSubgroup, map_mul, Units.val_mk0, AddSubgroup.coe_set_mk, mem_setOf_eq,
          preimage_setOf_eq]
        simp [← lt_div_iff₀' (zero_lt_iff.mpr Hx), div_div]
    rightMul := by
      rintro x ⟨⟨r, s⟩, hr, hs⟩
      rcases eq_or_ne (v x) 0 with (Hx | Hx)
      · use ⟨1, by simp⟩
        rintro y
        simp [ltAddSubgroup, Hx, zero_lt_iff, hr, hs]
      · use ⟨⟨r * x, s⟩, by simp [Hx, hr, hs]⟩
        rintro y
        simp only [ltAddSubgroup, map_mul, Units.val_mk0, AddSubgroup.coe_set_mk, mem_setOf_eq,
          preimage_setOf_eq]
        rw [mul_comm (v y)]
        simp [← lt_div_iff₀' (zero_lt_iff.mpr Hx), div_div] }

lemma subgroups_basis_le_subgroups_range_basis :
    haveI : Nonempty { rs : R × R // v rs.1 ≠ 0 ∧ v rs.2 ≠ 0 } := ⟨⟨⟨1, 1⟩, by simp⟩⟩
    v.subgroups_basis.topology ≤ v.subgroups_range_basis.topology := by
  haveI : Nonempty { rs : R × R // v rs.1 ≠ 0 ∧ v rs.2 ≠ 0 } := ⟨⟨⟨1, 1⟩, by simp⟩⟩
  intro U
  simp_rw [@isOpen_iff_mem_nhds, (RingSubgroupsBasis.hasBasis_nhds _ _).mem_iff]
  simp only [ne_eq, ltAddSubgroup, Units.val_mk0, AddSubgroup.mem_mk, mem_setOf_eq, true_and,
    Subtype.exists, exists_prop, Prod.exists]
  intro H x hx
  obtain ⟨r, s, ⟨hr, hs⟩, h⟩ := H x hx
  refine ⟨Units.mk0 (v s / v r) ?_, h⟩
  simp [hr, hs]

end Valuation

/-- A valued ring is a ring that comes equipped with a distinguished valuation. The class `Valued`
is designed for the situation that there is a canonical valuation on the ring.

TODO: show that there always exists an equivalent valuation taking values in a type belonging to
the same universe as the ring.

See Note [forgetful inheritance] for why we extend `UniformSpace`, `IsUniformAddGroup`. -/
class Valued (R : Type u) [Ring R] (Γ₀ : outParam (Type v))
  [LinearOrderedCommGroupWithZero Γ₀] extends UniformSpace R, IsUniformAddGroup R where
  v : Valuation R Γ₀
  is_topological_valuation : ∀ s, s ∈ 𝓝 (0 : R) ↔ ∃ rs : {rs : R × R // v rs.1 ≠ 0 ∧ v rs.2 ≠ 0},
    { x : R | v rs.val.1 * v x < v rs.val.2 } ⊆ s

namespace Valued

/-- Alternative `Valued` constructor for use when there is no preferred `UniformSpace` structure. -/
def mk' (v : Valuation R Γ₀) : Valued R Γ₀ :=
  haveI : Nonempty { rs : R × R // v rs.1 ≠ 0 ∧ v rs.2 ≠ 0 } := ⟨⟨⟨1, 1⟩, by simp⟩⟩
  { v
    toUniformSpace := @IsTopologicalAddGroup.toUniformSpace R _ v.subgroups_range_basis.topology _
    toIsUniformAddGroup := @isUniformAddGroup_of_addCommGroup _ _ v.subgroups_range_basis.topology _
    is_topological_valuation := by
      letI := @IsTopologicalAddGroup.toUniformSpace R _ v.subgroups_range_basis.topology _
      intro s
      rw [Filter.hasBasis_iff.mp v.subgroups_range_basis.hasBasis_nhds_zero s]
      refine exists_congr ?_
      simp only [ne_eq, ltAddSubgroup, Units.val_mk0, AddSubgroup.coe_set_mk, true_and,
        Subtype.forall, and_imp, Prod.forall]
      intro r s hr hs
      simp [lt_div_iff₀' (zero_lt_iff.mpr hr)] }

variable (R Γ₀)
variable [_i : Valued R Γ₀] [Valued K Γ₀]

theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ v rs.1 ≠ 0 ∧ v rs.2 ≠ 0)
    fun rs : R × R ↦ { x | v x * v rs.1 < v rs.2 } := by
  simp [Filter.hasBasis_iff, is_topological_valuation, mul_comm]

open Uniformity in
theorem hasBasis_uniformity : (𝓤 R).HasBasis (fun rs : R × R ↦ v rs.1 ≠ 0 ∧ v rs.2 ≠ 0)
    fun rs : R × R => { p : R × R | v (p.2 - p.1) * v rs.1 < v rs.2 } := by
  rw [uniformity_eq_comap_nhds_zero]
  exact (hasBasis_nhds_zero R Γ₀).comap _

theorem toUniformSpace_eq :
    haveI : Nonempty { rs : R × R // v rs.1 ≠ 0 ∧ v rs.2 ≠ 0 } := ⟨⟨⟨1, 1⟩, by simp⟩⟩
    toUniformSpace =
      @IsTopologicalAddGroup.toUniformSpace R _ v.subgroups_range_basis.topology _ := by
  refine UniformSpace.ext ((hasBasis_uniformity R Γ₀).eq_of_same_basis ?_)
  rw [uniformity_eq_comap_nhds_zero']
  haveI : Nonempty { rs : R × R // v rs.1 ≠ 0 ∧ v rs.2 ≠ 0 } := ⟨⟨⟨1, 1⟩, by simp⟩⟩
  refine (v.subgroups_range_basis.hasBasis_nhds_zero.comap _).to_hasBasis ?_ ?_ <;>
  · simp only [ne_eq, ltAddSubgroup, Units.val_mk0, AddSubgroup.coe_set_mk, preimage_setOf_eq,
    setOf_subset_setOf, Prod.forall, Prod.exists, forall_const, Subtype.forall, and_imp, ne_eq,
    Subtype.exists, exists_prop]
    intro r s hr hs
    use r, s
    simp [hr, hs, lt_div_iff₀ (zero_lt_iff.mpr hr)]

variable {R Γ₀}

theorem mem_nhds {s : Set R} {x : R} : s ∈ 𝓝 x ↔ ∃ rs : { rs : R × R // v rs.1 ≠ 0 ∧ v rs.2 ≠ 0 },
    { y | (v (y - x) : Γ₀) * v rs.val.1 < v rs.val.2 } ⊆ s := by
  simp [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_setOf_eq,
    ((hasBasis_nhds_zero R Γ₀).comap fun y => y - x).mem_iff]

theorem mem_nhds_zero {s : Set R} : s ∈ 𝓝 (0 : R) ↔ ∃ rs : {rs : R × R // v rs.1 ≠ 0 ∧ v rs.2 ≠ 0},
    { x | v x * v rs.val.1 < v rs.val.2 } ⊆ s := by
  simp only [mem_nhds, sub_zero]

theorem loc_const {x : R} (h : (v x : Γ₀) ≠ 0) : { y : R | v y = v x } ∈ 𝓝 x := by
  rw [mem_nhds]
  refine ⟨⟨⟨1, x⟩, by simp [h]⟩, ?_⟩
  simp only [map_one, mul_one, setOf_subset_setOf]
  intro y y_in
  exact Valuation.map_eq_of_sub_lt _ y_in

instance (priority := 100) : IsTopologicalRing R :=
  haveI : Nonempty { rs : R × R // v rs.1 ≠ 0 ∧ v rs.2 ≠ 0 } := ⟨⟨⟨1, 1⟩, by simp⟩⟩
  (toUniformSpace_eq R Γ₀).symm ▸ v.subgroups_range_basis.toRingFilterBasis.isTopologicalRing

lemma discreteTopology_of_ne_zero_imp_v_eq_one (h : ∀ x : R, x ≠ 0 → v x = 1) :
    DiscreteTopology R := by
  simp only [discreteTopology_iff_isOpen_singleton_zero, isOpen_iff_mem_nhds, mem_singleton_iff,
    forall_eq, mem_nhds_zero, subset_singleton_iff, mem_setOf_eq, Subtype.exists, exists_prop,
    Prod.exists]
  use 1, 1
  simp only [map_one, ne_eq, one_ne_zero, not_false_eq_true, and_self, mul_one, true_and]
  contrapose! h
  obtain ⟨x, hx, hx'⟩ := h
  exact ⟨x, hx', hx.ne⟩

theorem cauchy_iff {F : Filter R} : Cauchy F ↔
    F.NeBot ∧ ∀ rs : { rs : R × R // v rs.1 ≠ 0 ∧ v rs.2 ≠ 0 },
      ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), (v (y - x) : Γ₀) * v rs.val.1 < v rs.val.2 := by
  rw [toUniformSpace_eq, AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [Valued.v.subgroups_range_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h rs
    specialize h ({x | v x * v rs.val.1 < v rs.val.2})
    apply h
    use rs
    simp [ltAddSubgroup, lt_div_iff₀ (zero_lt_iff.mpr rs.prop.1)]
  · rintro h - ⟨rs, rfl⟩
    specialize h rs
    convert h
    simp [ltAddSubgroup, lt_div_iff₀ (zero_lt_iff.mpr rs.prop.1)]

/-- A sphere centred at the origin in a valued ring is open. -/
theorem isOpen_sphere {r : Γ₀} (hr : r ≠ 0) :
    IsOpen (X := R) {x | v x = r} := by
  by_cases hr' : ∃ (x : R), v x = r
  · obtain ⟨y, rfl⟩ := hr'
    rw [isOpen_iff_mem_nhds]
    simp only [mem_setOf_eq]
    intro x hx
    convert loc_const (hx.trans_ne hr) using 1
    ext
    simp [hx]
  · push_neg at hr'
    convert isOpen_empty
    ext
    simp [hr']

/-- A closed ball centred at the origin in a valued ring is closed. -/
theorem isClosed_closedBall (r : Γ₀) :
    IsClosed (X := R) {x | v x ≤ r} := by
  simp only [← isOpen_compl_iff, compl_setOf, not_le, isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  have hx0 : 0 < v x := zero_le'.trans_lt hx
  simp only [ne_eq, setOf_subset_setOf, Subtype.exists, exists_prop, Prod.exists]
  use 1, x
  simp only [map_one, one_ne_zero, not_false_eq_true, true_and, mul_one, hx0.ne']
  intro a ha
  simpa [map_eq_of_sub_lt _ ha] using hx

/-- An open ball centred at the origin in a valued ring is closed. -/
theorem isClosed_ball (r : Γ₀) :
    IsClosed (X := R) {x | v x < r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  have := (isClosed_closedBall (R := R) r).sdiff (isOpen_sphere (R := R) hr)
  convert this using 1
  ext
  simp [lt_iff_le_and_ne]

/-- An open ball centred at the origin in a valued ring is open. -/
theorem isOpen_ball' {r : Γ₀} (hr : ∃ (x : R), v x ≠ 0 ∧ v x ≤ r) :
    IsOpen (X := R) {x | v x < r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [ne_eq, setOf_subset_setOf, Subtype.exists, exists_prop, Prod.exists]
  by_cases hx' : ∃ y : R, v x < v y ∧ v y ≤ r
  · obtain ⟨y, hy, hy'⟩ := hx'
    use 1, y
    simp only [map_one, one_ne_zero, not_false_eq_true, (hy.trans_le' zero_le').ne', and_self,
      mul_one, true_and]
    intro z hz
    rw [← sub_add_cancel z x] at hz
    simpa using ((v.map_add (z - x + x - x) x).trans_lt (max_lt hz hy)).trans_le hy'
  · push_neg at hx'
    obtain ⟨y, hy, hy'⟩ := hr
    have hx' : v y ≤ v x := by
      specialize hx' y
      contrapose! hx'
      simp [hx', hy']
    use 1, y
    simp only [map_one, one_ne_zero, not_false_eq_true, hy, and_self, mul_one, true_and]
    intro z hz
    simpa [map_eq_of_sub_lt _ (hz.trans_le hx')] using hx

lemma val_discrete_of_forall_lt [MulArchimedean Γ₀] {r : Γ₀} (hr : r ≠ 0)
    (h : ∀ x : K, v x ≠ 0 → r < v x) (x : K) (hx : v x ≠ 0) : v x = 1 := by
  lift r to Γ₀ˣ using IsUnit.mk0 _ hr
  rcases lt_trichotomy (Units.mk0 _ hx) 1 with H | H | H
  · obtain ⟨k, hk⟩ := exists_pow_lt H r
    specialize h (x ^ k) (by simp [hx])
    simp [← Units.val_lt_val, ← map_pow, h.not_gt] at hk
  · simpa [Units.ext_iff] using H
  · rw [← inv_lt_one'] at H
    obtain ⟨k, hk⟩ := exists_pow_lt H r
    specialize h (x ^ (-k : ℤ)) (by simp [hx])
    simp only [zpow_neg, zpow_natCast, map_inv₀, map_pow] at h
    simp [← Units.val_lt_val, h.not_gt, inv_pow] at hk

lemma discreteTopology_of_forall_lt [MulArchimedean Γ₀] {r : Γ₀} (hr : r ≠ 0)
    (h : ∀ x : K, v x ≠ 0 → r < v x) :
    DiscreteTopology K :=
  discreteTopology_of_ne_zero_imp_v_eq_one (by simpa using val_discrete_of_forall_lt hr h)

/-- An open ball centred at the origin in a valued ring is open. -/
theorem isOpen_ball [MulArchimedean Γ₀] {r : Γ₀} (hr : r ≠ 0) :
    IsOpen (X := K) {x | v x < r} := by
  by_cases hr' : ∃ (x : K), v x ≠ 0 ∧ v x ≤ r
  · exact isOpen_ball' hr'
  · push_neg at hr'
    have := discreteTopology_of_forall_lt hr hr'
    simp

/-- An open ball centred at the origin in a valued ring is clopen. -/
theorem isClopen_ball' {r : Γ₀} (hr : ∃ (x : R), v x ≠ 0 ∧ v x ≤ r) :
    IsClopen (X := R) {x | v x < r} :=
  ⟨isClosed_ball r, isOpen_ball' hr⟩

/-- An open ball centred at the origin in a valued ring is clopen. -/
theorem isClopen_ball [MulArchimedean Γ₀] {r : Γ₀} (hr : r ≠ 0) :
    IsClopen (X := K) {x | v x < r} :=
  ⟨isClosed_ball r, isOpen_ball hr⟩

/-- A closed ball centred at the origin in a valued ring is open. -/
theorem isOpen_closedball' {r : Γ₀} (hr : ∃ (x : R), v x ≠ 0 ∧ v x ≤ r) :
    IsOpen (X := R) {x | v x ≤ r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [ne_eq, setOf_subset_setOf, Subtype.exists, exists_prop, Prod.exists]
  by_cases hx' : ∃ y : R, v x < v y ∧ v y ≤ r
  · obtain ⟨y, hy, hy'⟩ := hx'
    use 1, y
    simp only [map_one, one_ne_zero, not_false_eq_true, (hy.trans_le' zero_le').ne', and_self,
      mul_one, true_and]
    intro z hz
    rw [← sub_add_cancel z x] at hz
    simpa using (((v.map_add (z - x + x - x) x).trans_lt (max_lt hz hy)).trans_le hy').le
  · push_neg at hx'
    obtain ⟨y, hy, hy'⟩ := hr
    have hx' : v y ≤ v x := by
      specialize hx' y
      contrapose! hx'
      simp [hx', hy']
    use 1, y
    simp only [map_one, one_ne_zero, not_false_eq_true, hy, and_self, mul_one, true_and]
    intro z hz
    simpa [map_eq_of_sub_lt _ (hz.trans_le hx')] using hx

/-- A closed ball centred at the origin in a valued ring is open. -/
theorem isOpen_closedBall [MulArchimedean Γ₀] {r : Γ₀} (hr : r ≠ 0) :
    IsOpen (X := K) {x | v x ≤ r} := by
  by_cases hr' : ∃ (x : K), v x ≠ 0 ∧ v x ≤ r
  · exact isOpen_closedball' hr'
  · push_neg at hr'
    have := discreteTopology_of_forall_lt hr hr'
    simp

/-- A closed ball centred at the origin in a valued ring is clopen. -/
theorem isClopen_closedBall' {r : Γ₀} (hr : ∃ (x : R), v x ≠ 0 ∧ v x ≤ r) :
    IsClopen (X := R) {x | v x ≤ r} :=
  ⟨isClosed_closedBall r, isOpen_closedball' hr⟩

/-- A closed ball centred at the origin in a valued ring is clopen. -/
theorem isClopen_closedBall [MulArchimedean Γ₀] {r : Γ₀} (hr : r ≠ 0) :
    IsClopen (X := K) {x | v x ≤ r} :=
  ⟨isClosed_closedBall r, isOpen_closedBall hr⟩

/-- A sphere centred at the origin in a valued ring is clopen. -/
theorem isClopen_sphere' {r : Γ₀} (hr : ∃ (x : R), v x ≠ 0 ∧ v x ≤ r) :
    IsClopen (X := R) {x | v x = r} := by
  have h : {x : R | v x = r} = {x | v x ≤ r} \ {x | v x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall' hr) (isClopen_ball' hr)

/-- A sphere centred at the origin in a valued ring is clopen. -/
theorem isClopen_sphere [MulArchimedean Γ₀] {r : Γ₀} (hr : r ≠ 0) :
    IsClopen (X := K) {x | v x = r} := by
  have h : {x : K | v x = r} = {x | v x ≤ r} \ {x | v x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall hr) (isClopen_ball hr)

/-- A sphere centred at the origin in a valued ring is closed. -/
theorem isClosed_sphere' {r : Γ₀} (hr : ∃ (x : R), v x ≠ 0 ∧ v x ≤ r) :
    IsClosed (X := R) {x | v x = r} :=
  isClopen_sphere' hr |>.isClosed

/-- A sphere centred at the origin in a valued ring is closed. -/
theorem isClosed_sphere [MulArchimedean Γ₀] {r : Γ₀} (hr : r ≠ 0) :
    IsClosed (X := K) {x | v x = r} :=
  isClopen_sphere hr |>.isClosed

/-- The closed unit ball in a valued ring is open. -/
theorem isOpen_integer : IsOpen (_i.v.integer : Set R) :=
  isOpen_closedball' ⟨1, by simp⟩

@[deprecated (since := "2025-04-25")]
alias integer_isOpen := isOpen_integer

/-- The closed unit ball of a valued ring is closed. -/
theorem isClosed_integer : IsClosed (_i.v.integer : Set R) :=
  isClosed_closedBall 1

/-- The closed unit ball of a valued ring is clopen. -/
theorem isClopen_integer : IsClopen (_i.v.integer : Set R) :=
  ⟨isClosed_integer, isOpen_integer⟩

/-- The valuation subring of a valued field is open. -/
theorem isOpen_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsOpen (hv.v.valuationSubring : Set K) :=
  isOpen_integer

@[deprecated (since := "2025-04-25")]
alias valuationSubring_isOpen := isOpen_valuationSubring

/-- The valuation subring of a valued field is closed. -/
theorem isClosed_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsClosed (hv.v.valuationSubring : Set K) :=
  isClosed_integer

/-- The valuation subring of a valued field is clopen. -/
theorem isClopen_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsClopen (hv.v.valuationSubring : Set K) :=
  isClopen_integer

end Valued
