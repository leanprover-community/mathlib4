/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Algebra.Order.Group.Units
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import Mathlib.Topology.Algebra.UniformFilterBasis
public import Mathlib.RingTheory.Valuation.ValuationSubring

public import Mathlib.Algebra.Order.GroupWithZero.Range

/-!
# The topology on a valued ring

In this file, we define the non-Archimedean topology induced by a valuation on a ring.
The main definition is a `Valued` type class which equips a ring with a valuation taking
values in a group with zero. Other instances are then deduced from this.

*NOTE* (2025-07-02):
The `Valued` class defined in this file will eventually get replaced with `ValuativeRel`
from `Mathlib.RingTheory.Valuation.ValuativeRel.Basic`. New developments on valued rings/fields
should take this into consideration.

-/

@[expose] public section

open scoped Topology uniformity
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ Set Valuation

noncomputable section

universe v u

variable {R K : Type u} [Ring R] [DivisionRing K] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

variable (v : Valuation R Γ₀)

lemma map_eq_one_of_forall_lt [MulArchimedean Γ₀] {v : Valuation K Γ₀} {r : Γ₀} (hr : r ≠ 0)
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

set_option backward.isDefEq.respectTransparency false in
/-- The basis of open subgroups for the topology on a ring determined by a valuation. -/
theorem subgroups_basis :
    RingSubgroupsBasis fun γ : (ValueGroup₀ v)ˣ =>
      (v.ltAddSubgroup (Units.map (ValueGroup₀.embedding (f := v)) γ) : AddSubgroup R) :=
  { inter := by
      classical
      rintro γ₀ γ₁
      use min γ₀ γ₁
      have hmin : embedding (min γ₀.1 γ₁.1) = min (embedding γ₀.1) (embedding γ₁.1) :=
        embedding_strictMono.monotone.map_inf γ₀.1 γ₁.1
      simp only [ltAddSubgroup, Units.coe_map, Units.min_val, MonoidHom.coe_coe, hmin, lt_inf_iff,
        le_inf_iff, AddSubgroup.mk_le_mk, AddSubmonoid.mk_le_mk,
        AddSubsemigroup.mk_le_mk, setOf_subset_setOf]
      tauto
    mul := by
      letI : LinearOrderedCommGroupWithZero (ValueGroup₀ v) := --inferInstance failed (?)
        MonoidWithZeroHom.ValueGroup₀.instLinearOrderedCommGroupWithZero
      rintro γ
      obtain ⟨γ₀, h⟩ := exists_square_le γ
      use γ₀
      rintro - ⟨r, r_in, s, s_in, rfl⟩
      simp only [ltAddSubgroup, Units.coe_map, MonoidHom.coe_coe, AddSubgroup.coe_set_mk,
        AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, mem_setOf_eq] at r_in s_in
      simp only [coe_ltAddSubgroup, Units.coe_map, MonoidHom.coe_coe, mem_setOf_eq]
      rw [← restrict_lt_iff_lt_embedding] at *
      calc
        v.restrict (r * s) = v.restrict r * v.restrict s := Valuation.map_mul _ _ _
        _ < γ₀.1 * γ₀.1 := by gcongr <;> exact zero_le'
        _ ≤ γ := mod_cast h
    leftMul := by
      classical
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use (1 : (ValueGroup₀ v)ˣ)
        rintro y _
        change v (x * y) < _
        rw [Valuation.map_mul, Hx, zero_mul]
        exact Units.zero_lt _
      · set u : (ValueGroup₀ v)ˣ := Units.mk0 ((restrict₀ v) x)
          (by simp [restrict₀_apply]; aesop) with hu_def
        have hu : ValueGroup₀.embedding u⁻¹.1 = γx⁻¹ := by
          simp [restrict₀_apply, embedding_apply, hu_def, Hx]
        use u⁻¹ * γ
        rintro y (vy_lt : v y < ValueGroup₀.embedding (u⁻¹ * γ).1)
        change (v (x * y) : Γ₀) < ValueGroup₀.embedding γ.1
        rw [Valuation.map_mul, Hx, mul_comm]
        rw [Units.val_mul, mul_comm, map_mul, hu] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt
    rightMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        rintro y _
        change v (y * x) < _
        rw [Valuation.map_mul, Hx, mul_zero]
        exact Units.zero_lt _
      · set u : (ValueGroup₀ v)ˣ := Units.mk0 ((restrict₀ v) x)
          (by simp [restrict₀_apply]; aesop) with hu_def
        have hu : ValueGroup₀.embedding u⁻¹.1 = γx⁻¹ := by simp [restrict₀_apply, embedding_apply,
          hu_def, Hx]
        use u⁻¹ * γ
        rintro y (vy_lt : v y < ValueGroup₀.embedding (u⁻¹ * γ).1)
        change (v (y * x) : Γ₀) < ValueGroup₀.embedding γ.1
        rw [Valuation.map_mul, Hx]
        rw [Units.val_mul, mul_comm, map_mul, hu] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt }

end Valuation

/-- A valued ring is a ring that comes equipped with a distinguished valuation. The class `Valued`
is designed for the situation that there is a canonical valuation on the ring.

TODO: show that there always exists an equivalent valuation taking values in a type belonging to
the same universe as the ring.

See Note [forgetful inheritance] for why we extend `UniformSpace`, `IsUniformAddGroup`. -/
class Valued (R : Type u) [Ring R] (Γ₀ : outParam (Type v))
  [LinearOrderedCommGroupWithZero Γ₀] extends UniformSpace R, IsUniformAddGroup R where
  v : Valuation R Γ₀
  is_topological_valuation : ∀ s, s ∈ 𝓝 (0 : R) ↔
    ∃ γ : (MonoidWithZeroHom.ValueGroup₀ v)ˣ, { x : R | v.restrict x < γ.1 } ⊆ s

namespace Valued

set_option backward.isDefEq.respectTransparency false in
/-- Alternative `Valued` constructor for use when there is no preferred `UniformSpace` structure. -/
def mk' (v : Valuation R Γ₀) : Valued R Γ₀ :=
  { v
    toUniformSpace := @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _
    toIsUniformAddGroup := @isUniformAddGroup_of_addCommGroup _ _ v.subgroups_basis.topology _
    is_topological_valuation := by
      letI := @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _
      intro s
      rw [Filter.hasBasis_iff.mp v.subgroups_basis.hasBasis_nhds_zero s]
      simp_rw [restrict_lt_iff_lt_embedding]
      exact exists_congr fun γ => by rw [true_and]; rfl }

variable (R Γ₀)
variable [_i : Valued R Γ₀]

theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True)
      fun γ : (MonoidWithZeroHom.ValueGroup₀ _i.v)ˣ => { x | v.restrict x < γ.1 } := by
  simp [Filter.hasBasis_iff, is_topological_valuation]

/- theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True)
      fun γ : (MonoidWithZeroHom.ValueGroup₀ _i.v)ˣ =>
      { x | v x < (ValueGroup₀.embedding (f := _i.v) γ) } := by
  simp [Filter.hasBasis_iff, is_topological_valuation] -/

/- open Uniformity in
theorem hasBasis_uniformity : (𝓤 R).HasBasis (fun _ => True)
    fun γ : Γ₀ˣ => { p : R × R | v (p.2 - p.1) < (γ : Γ₀) } := by
  rw [uniformity_eq_comap_nhds_zero]
  exact (hasBasis_nhds_zero R Γ₀).comap _ -/

open Uniformity in
theorem hasBasis_uniformity : (𝓤 R).HasBasis (fun _ => True)
    fun γ : (MonoidWithZeroHom.ValueGroup₀ _i.v)ˣ =>
      { p : R × R | v.restrict (p.2 - p.1) < γ.1 } := by
  rw [uniformity_eq_comap_nhds_zero]
  exact (hasBasis_nhds_zero R Γ₀).comap _

set_option backward.isDefEq.respectTransparency false in
theorem toUniformSpace_eq : toUniformSpace =
    @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _ := by
  refine UniformSpace.ext ((hasBasis_uniformity R Γ₀).eq_of_same_basis ?_)
  convert v.subgroups_basis.hasBasis_nhds_zero.comap _
  simp_rw [restrict_lt_iff_lt_embedding, sub_eq_add_neg]
  simp

variable {R Γ₀}

theorem mem_nhds {s : Set R} {x : R} : s ∈ 𝓝 x ↔
    ∃ γ : (MonoidWithZeroHom.ValueGroup₀ _i.v)ˣ, { y | (v.restrict (y - x) ) < γ.1 } ⊆ s := by
  simp only [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_setOf_eq, true_and,
    ((hasBasis_nhds_zero R Γ₀).comap fun y => y - x).mem_iff]

theorem mem_nhds_zero {s : Set R} : s ∈ 𝓝 (0 : R) ↔
    ∃ γ : (MonoidWithZeroHom.ValueGroup₀ _i.v)ˣ, { x | v.restrict x < γ.1 } ⊆ s := by
  simp only [mem_nhds, sub_zero]

theorem loc_const {x : R} (h : (v x : Γ₀) ≠ 0) : { y : R | v y = v x } ∈ 𝓝 x := by
  rw [mem_nhds]
  have h' : v.restrict x ≠ 0 := by simp [h]
  use Units.mk0 _ h'
  rw [Units.val_mk0]
  intro y y_in
  exact Valuation.map_eq_of_sub_lt _ (v.restrict_lt_iff.mp y_in)

instance (priority := 100) : IsTopologicalRing R :=
  (toUniformSpace_eq R Γ₀).symm ▸ v.subgroups_basis.toRingFilterBasis.isTopologicalRing

section Discrete

lemma discreteTopology_of_forall_map_eq_one (h : ∀ x : R, x ≠ 0 → v x = 1) :
    DiscreteTopology R := by
  simp only [discreteTopology_iff_isOpen_singleton_zero, isOpen_iff_mem_nhds, mem_singleton_iff,
    forall_eq, mem_nhds_zero, subset_singleton_iff, mem_setOf_eq]
  use 1
  contrapose! h
  obtain ⟨x, hx, hx'⟩ := h
  rw [restrict_lt_iff_lt_embedding, Units.val_one, map_one] at hx
  exact ⟨x, hx', hx.ne⟩

lemma discreteTopology_of_forall_lt [MulArchimedean Γ₀] [Valued K Γ₀] {r : Γ₀} (hr : r ≠ 0)
    (h : ∀ x : K, v x ≠ 0 → r < v x) :
    DiscreteTopology K :=
  discreteTopology_of_forall_map_eq_one (by simpa using Valued.v.map_eq_one_of_forall_lt hr h)

end Discrete

set_option backward.isDefEq.respectTransparency false in
theorem cauchy_iff {F : Filter R} : Cauchy F ↔
    F.NeBot ∧ ∀ γ : (MonoidWithZeroHom.ValueGroup₀ _i.v)ˣ,
      ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), _i.v.restrict (y - x) < γ.1 := by
  rw [toUniformSpace_eq, AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [Valued.v.subgroups_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h γ
    simp_rw [restrict_lt_iff_lt_embedding]
    exact h _ (Valued.v.subgroups_basis.mem_addGroupFilterBasis γ)
  · rintro h - ⟨γ, rfl⟩
    simp_rw [restrict_lt_iff_lt_embedding] at h
    exact h γ

variable (R)

set_option backward.isDefEq.respectTransparency false in
/-- An open ball centred at the origin in a valued ring is open. -/
theorem isOpen_ball (r : ValueGroup₀ _i.v) : IsOpen (X := R) {x | v.restrict x < r} := by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  intro x hx
  rw [mem_nhds]
  simp only [setOf_subset_setOf]
  exact ⟨Units.mk0 _ hr,
    fun y hy => (sub_add_cancel y x).symm ▸ (v.restrict.map_add _ x).trans_lt (max_lt hy hx)⟩

set_option backward.isDefEq.respectTransparency false in
/-- An open ball centred at the origin in a valued ring is closed. -/
theorem isClosed_ball (r : ValueGroup₀ _i.v) : IsClosed (X := R) {x | v.restrict x < r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  exact AddSubgroup.isClosed_of_isOpen (Valuation.ltAddSubgroup v.restrict (Units.mk0 r hr))
    (isOpen_ball _ _)

/-- An open ball centred at the origin in a valued ring is clopen. -/
theorem isClopen_ball (r : ValueGroup₀ _i.v) : IsClopen (X := R) {x | v.restrict x < r} :=
  ⟨isClosed_ball _ _, isOpen_ball _ _⟩

/-- A closed ball centred at the origin in a valued ring is open. -/
theorem isOpen_closedBall {r : ValueGroup₀ _i.v} (hr : r ≠ 0) :
  IsOpen (X := R) {x | v.restrict x ≤ r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [setOf_subset_setOf]
  exact ⟨Units.mk0 _ hr, fun y hy =>
    (sub_add_cancel y x).symm ▸ le_trans (v.restrict.map_add _ _) (max_le (le_of_lt hy) hx)⟩

@[deprecated (since := "2025-10-09")]
alias isOpen_closedball := isOpen_closedBall

/-- A closed ball centred at the origin in a valued ring is closed. -/
theorem isClosed_closedBall (r : ValueGroup₀ _i.v) : IsClosed (X := R) {x | v.restrict x ≤ r} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_setOf_eq, not_le] at hx
  rw [mem_nhds]
  have hx' : v.restrict x ≠ 0 := ne_of_gt <| lt_of_le_of_lt zero_le' <| hx
  exact ⟨Units.mk0 _ hx', fun y hy hy' => ne_of_lt hy <| map_sub_swap v.restrict x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' hx)⟩

/-- A closed ball centred at the origin in a valued ring is clopen. -/
theorem isClopen_closedBall {r : ValueGroup₀ _i.v} (hr : r ≠ 0) :
    IsClopen (X := R) {x | v.restrict x ≤ r} :=
  ⟨isClosed_closedBall _ _, isOpen_closedBall _ hr⟩

/-- A sphere centred at the origin in a valued ring is clopen. -/
theorem isClopen_sphere {r : ValueGroup₀ _i.v} (hr : r ≠ 0) :
    IsClopen (X := R) {x | v.restrict x = r} := by
  have h : {x : R | v.restrict x = r} = {x | v.restrict x ≤ r} \ {x | v.restrict x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall _ hr) (isClopen_ball _ _)

/-- A sphere centred at the origin in a valued ring is open. -/
theorem isOpen_sphere {r : ValueGroup₀ _i.v} (hr : r ≠ 0) :
    IsOpen (X := R) {x | v.restrict x = r} :=
  isClopen_sphere _ hr |>.isOpen

set_option backward.isDefEq.respectTransparency false in
/-- A sphere centred at the origin in a valued ring is closed. -/
theorem isClosed_sphere (r : ValueGroup₀ _i.v) : IsClosed (X := R) {x | v.restrict x = r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simpa using isClosed_closedBall R 0
  exact isClopen_sphere _ hr |>.isClosed

set_option backward.isDefEq.respectTransparency false in
/-- The closed unit ball in a valued ring is open. -/
theorem isOpen_integer : IsOpen (_i.v.integer : Set R) := by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isOpen_closedBall _ one_ne_zero

/-- The closed unit ball of a valued ring is closed. -/
theorem isClosed_integer : IsClosed (_i.v.integer : Set R) := by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isClosed_closedBall _ _

/-- The closed unit ball of a valued ring is clopen. -/
theorem isClopen_integer : IsClopen (_i.v.integer : Set R) :=
  ⟨isClosed_integer _, isOpen_integer _⟩

/-- The valuation subring of a valued field is open. -/
theorem isOpen_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsOpen (hv.v.valuationSubring : Set K) :=
  isOpen_integer K

/-- The valuation subring of a valued field is closed. -/
theorem isClosed_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsClosed (hv.v.valuationSubring : Set K) :=
  isClosed_integer K

/-- The valuation subring of a valued field is clopen. -/
theorem isClopen_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsClopen (hv.v.valuationSubring : Set K) :=
  isClopen_integer K

end Valued
