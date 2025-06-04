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

/-- The basis of open subgroups for the topology on a ring determined by a valuation. -/
theorem subgroups_basis : RingSubgroupsBasis fun γ : Γ₀ˣ => (v.ltAddSubgroup γ : AddSubgroup R) :=
  { inter _ _ :=
      ⟨_, le_inf
        (ltAddSubgroup_mono _ (min_le_left _ _)) (ltAddSubgroup_mono _ (min_le_right _ _))⟩
    mul := by
      rintro γ
      obtain ⟨γ₀, h⟩ := exists_square_le γ
      use γ₀
      rintro - ⟨r, r_in, s, s_in, rfl⟩
      simp only [SetLike.mem_coe, mem_ltAddSubgroup_iff] at r_in s_in
      calc
        (v (r * s) : Γ₀) = v r * v s := Valuation.map_mul _ _ _
        _ < γ₀ * γ₀ := by gcongr <;> exact zero_le'
        _ ≤ γ := mod_cast h
    leftMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use (1 : Γ₀ˣ)
        rintro y
        simp [Hx]
      · use γx⁻¹ * γ
        simp [subset_def, lt_inv_mul_iff₀, Hx]
    rightMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        simp [subset_def, Hx]
      · use γx⁻¹ * γ
        simp [subset_def, lt_mul_inv_iff₀, Hx, mul_comm] }

end Valuation

/-- A valued ring is a ring that comes equipped with a distinguished valuation. The class `Valued`
is designed for the situation that there is a canonical valuation on the ring.

TODO: show that there always exists an equivalent valuation taking values in a type belonging to
the same universe as the ring.

See Note [forgetful inheritance] for why we extend `UniformSpace`, `IsUniformAddGroup`. -/
class Valued (R : Type u) [Ring R] (Γ₀ : outParam (Type v))
  [LinearOrderedCommGroupWithZero Γ₀] extends UniformSpace R, IsUniformAddGroup R where
  v : Valuation R Γ₀
  is_topological_valuation : ∀ s, s ∈ 𝓝 (0 : R) ↔ ∃ γ : Γ₀ˣ, { x : R | v x < γ } ⊆ s

namespace Valued

/-- Alternative `Valued` constructor for use when there is no preferred `UniformSpace` structure. -/
def mk' (v : Valuation R Γ₀) : Valued R Γ₀ :=
  { v
    toUniformSpace := @IsTopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _
    toIsUniformAddGroup := @isUniformAddGroup_of_addCommGroup _ _ v.subgroups_basis.topology _
    is_topological_valuation := by
      letI := @IsTopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _
      intro s
      rw [Filter.hasBasis_iff.mp v.subgroups_basis.hasBasis_nhds_zero s]
      exact exists_congr fun γ => by rw [true_and]; rfl }

variable (R Γ₀)
variable [_i : Valued R Γ₀]

theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True) fun γ : Γ₀ˣ => { x | v x < (γ : Γ₀) } := by
  simp [Filter.hasBasis_iff, is_topological_valuation]

open Uniformity in
theorem hasBasis_uniformity : (𝓤 R).HasBasis (fun _ => True)
    fun γ : Γ₀ˣ => { p : R × R | v (p.2 - p.1) < (γ : Γ₀) } := by
  rw [uniformity_eq_comap_nhds_zero]
  exact (hasBasis_nhds_zero R Γ₀).comap _

theorem toUniformSpace_eq :
    toUniformSpace = @IsTopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _ :=
  UniformSpace.ext
    ((hasBasis_uniformity R Γ₀).eq_of_same_basis <| v.subgroups_basis.hasBasis_nhds_zero.comap _)

variable {R Γ₀}

theorem mem_nhds {s : Set R} {x : R} : s ∈ 𝓝 x ↔ ∃ γ : Γ₀ˣ, { y | (v (y - x) : Γ₀) < γ } ⊆ s := by
  simp only [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_setOf_eq, true_and,
    ((hasBasis_nhds_zero R Γ₀).comap fun y => y - x).mem_iff]

theorem mem_nhds_zero {s : Set R} : s ∈ 𝓝 (0 : R) ↔ ∃ γ : Γ₀ˣ, { x | v x < (γ : Γ₀) } ⊆ s := by
  simp only [mem_nhds, sub_zero]

theorem loc_const {x : R} (h : (v x : Γ₀) ≠ 0) : { y : R | v y = v x } ∈ 𝓝 x := by
  rw [mem_nhds]
  use Units.mk0 _ h
  rw [Units.val_mk0]
  intro y y_in
  exact Valuation.map_eq_of_sub_lt _ y_in

instance (priority := 100) : IsTopologicalRing R :=
  (toUniformSpace_eq R Γ₀).symm ▸ v.subgroups_basis.toRingFilterBasis.isTopologicalRing

theorem cauchy_iff {F : Filter R} : Cauchy F ↔
    F.NeBot ∧ ∀ γ : Γ₀ˣ, ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), (v (y - x) : Γ₀) < γ := by
  rw [toUniformSpace_eq, AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [Valued.v.subgroups_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h γ
    exact h _ (Valued.v.subgroups_basis.mem_addGroupFilterBasis _)
  · rintro h - ⟨γ, rfl⟩
    exact h γ

variable (R)

/-- An open ball centred at the origin in a valued ring is open. -/
theorem isOpen_ball (r : Γ₀) : IsOpen (X := R) {x | v x < r} := by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl|hr
  · simp
  intro x hx
  rw [mem_nhds]
  simp only [setOf_subset_setOf]
  exact ⟨Units.mk0 _ hr,
    fun y hy => (sub_add_cancel y x).symm ▸ (v.map_add _ x).trans_lt (max_lt hy hx)⟩

/-- An open ball centred at the origin in a valued ring is closed. -/
theorem isClosed_ball (r : Γ₀) : IsClosed (X := R) {x | v x < r} := by
  rcases eq_or_ne r 0 with rfl|hr
  · simp
  exact AddSubgroup.isClosed_of_isOpen
    (Valuation.ltAddSubgroup v (Units.mk0 r hr))
    (isOpen_ball _ _)

/-- An open ball centred at the origin in a valued ring is clopen. -/
theorem isClopen_ball (r : Γ₀) : IsClopen (X := R) {x | v x < r} :=
  ⟨isClosed_ball _ _, isOpen_ball _ _⟩

lemma isOpen_ltAddSubgroup (γ : Γ₀ˣ) :
    IsOpen ((v.ltAddSubgroup γ : AddSubgroup R) : Set R) :=
  isOpen_ball _ _

lemma isClosed_ltAddSubgroup (γ : Γ₀ˣ) :
    IsClosed ((v.ltAddSubgroup γ : AddSubgroup R) : Set R) :=
  isClosed_ball _ _

lemma isClopen_ltAddSubgroup (γ : Γ₀ˣ) :
    IsClopen ((v.ltAddSubgroup γ : AddSubgroup R) : Set R) :=
  isClopen_ball _ _

/-- A closed ball centred at the origin in a valued ring is open. -/
theorem isOpen_closedBall {r : Γ₀} (hr : r ≠ 0) : IsOpen (X := R) {x | v x ≤ r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [setOf_subset_setOf]
  exact ⟨Units.mk0 _ hr,
    fun y hy => (sub_add_cancel y x).symm ▸ le_trans (v.map_add _ _) (max_le (le_of_lt hy) hx)⟩

@[deprecated (since := "2025-06-04")]
alias isOpen_closedball := isOpen_closedBall

/-- A closed ball centred at the origin in a valued ring is closed. -/
theorem isClosed_closedBall (r : Γ₀) : IsClosed (X := R) {x | v x ≤ r} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  have hx' : v x ≠ 0 := ne_of_gt <| lt_of_le_of_lt zero_le' <| lt_of_not_ge hx
  exact ⟨Units.mk0 _ hx', fun y hy hy' => ne_of_lt hy <| map_sub_swap v x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' (lt_of_not_ge hx))⟩

/-- A closed ball centred at the origin in a valued ring is clopen. -/
theorem isClopen_closedBall {r : Γ₀} (hr : r ≠ 0) : IsClopen (X := R) {x | v x ≤ r} :=
  ⟨isClosed_closedBall _ _, isOpen_closedBall _ hr⟩

lemma isOpen_leAddSubgroup {γ : Γ₀} (hγ : γ ≠ 0) :
    IsOpen ((v.leAddSubgroup γ : AddSubgroup R) : Set R) :=
  isOpen_closedBall _ hγ

lemma isClosed_leAddSubgroup (γ : Γ₀) :
    IsClosed ((v.leAddSubgroup γ : AddSubgroup R) : Set R) :=
  isClosed_closedBall _ _

lemma isClopen_leAddSubgroup {γ : Γ₀} (hγ : γ ≠ 0) :
    IsClopen ((v.leAddSubgroup γ : AddSubgroup R) : Set R) :=
  isClopen_closedBall _ hγ

/-- A sphere centred at the origin in a valued ring is clopen. -/
theorem isClopen_sphere {r : Γ₀} (hr : r ≠ 0) : IsClopen (X := R) {x | v x = r} := by
  have h : {x : R | v x = r} = {x | v x ≤ r} \ {x | v x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall _ hr) (isClopen_ball _ _)

/-- A sphere centred at the origin in a valued ring is open. -/
theorem isOpen_sphere {r : Γ₀} (hr : r ≠ 0) : IsOpen (X := R) {x | v x = r} :=
  isClopen_sphere _ hr |>.isOpen

/-- A sphere centred at the origin in a valued ring is closed. -/
theorem isClosed_sphere (r : Γ₀) : IsClosed (X := R) {x | v x = r} := by
  rcases eq_or_ne r 0 with rfl|hr
  · simpa using isClosed_closedBall R 0
  exact isClopen_sphere _ hr |>.isClosed

/-- The closed unit ball in a valued ring is open. -/
theorem isOpen_integer : IsOpen (_i.v.integer : Set R) :=
  isOpen_closedBall _ one_ne_zero

@[deprecated (since := "2025-04-25")]
alias integer_isOpen := isOpen_integer

/-- The closed unit ball of a valued ring is closed. -/
theorem isClosed_integer : IsClosed (_i.v.integer : Set R) :=
  isClosed_closedBall _ _

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

section Ideal

local notation "𝓞" => _i.v.integer

/-- The submodule of over the valuation subring whose valuation is less than or equal to a
certain value. -/
def leSubmodule (γ : Γ₀) : Submodule 𝓞 R where
  __ := leAddSubgroup v γ
  smul_mem' r x h := by
    simpa [Subring.smul_def] using mul_le_of_le_one_of_le r.prop h

/-- The submodule of over the valuation subring whose valuation is less than a certain unit. -/
def ltSubmodule (γ : Γ₀ˣ) : Submodule 𝓞 R where
  __ := ltAddSubgroup v γ
  smul_mem' r x h := by
    simpa [Subring.smul_def] using mul_lt_of_le_one_of_lt r.prop h

lemma leSubmodule_mono : Monotone (leSubmodule R) :=
  leAddSubgroup_mono v

lemma ltSubmodule_mono : Monotone (ltSubmodule R) :=
  ltAddSubgroup_mono v

lemma ltSubmodule_le_leSubmodule (γ : Γ₀ˣ) :
    ltSubmodule R γ ≤ leSubmodule R (γ : Γ₀) :=
  ltAddSubgroup_le_leAddSubgroup v γ

lemma isOpen_ltSubmodule (γ : Γ₀ˣ) :
    IsOpen (ltSubmodule R γ : Set R) :=
  isOpen_ball _ _

lemma isClosed_ltSubmodule (γ : Γ₀ˣ) :
    IsClosed (ltSubmodule R γ : Set R) :=
  isClosed_ball _ _

lemma isClopen_ltSubmodule (γ : Γ₀ˣ) :
    IsClopen (ltSubmodule R γ : Set R) :=
  isClopen_ball _ _

lemma isOpen_leSubmodule {γ : Γ₀} (hγ : γ ≠ 0) :
    IsOpen (leSubmodule R γ : Set R) :=
  isOpen_closedBall _ hγ

lemma isClosed_leSubmodule (γ : Γ₀) :
    IsClosed (leSubmodule R γ : Set R) :=
  isClosed_closedBall _ _

lemma isClopen_leSubmodule {γ : Γ₀} (hγ : γ ≠ 0) :
    IsClopen (leSubmodule R γ : Set R) :=
  isClopen_closedBall _ hγ

variable {R} in
@[simp]
lemma mem_leSubmodule_iff {γ : Γ₀} {x : R} :
    x ∈ leSubmodule R γ ↔ v x ≤ γ :=
  Iff.rfl

variable {R} in
@[simp]
lemma mem_ltSubmodule_iff {γ : Γ₀ˣ} {x : R} :
    x ∈ ltSubmodule R γ ↔ v x < γ :=
  Iff.rfl

@[simp]
lemma leSubmodule_zero (K : Type u) [Field K] [hv : Valued K Γ₀] :
    leSubmodule K (0 : Γ₀) = ⊥ := by
  ext; simp

--- the ideals do not use the submodules due to `Ideal.comap` requiring commutativity

/-- The ideal of elements of the valuation subring whose valuation is less than or equal to a
certain value. -/
def leIdeal (γ : Γ₀) : Ideal 𝓞 where
  __ := AddSubgroup.addSubgroupOf (leAddSubgroup v γ) _i.v.integer.toAddSubgroup
  smul_mem' r x h := by
    change v ((r : R) * x) ≤ γ -- not sure why simp can't get us to here
    simpa [Subring.smul_def] using mul_le_of_le_one_of_le r.prop h

/-- The ideal of elements of the valuation subring whose valuation is less than a certain unit. -/
def ltIdeal (γ : Γ₀ˣ) : Ideal 𝓞 where
  __ := AddSubgroup.addSubgroupOf (ltAddSubgroup v γ) _i.v.integer.toAddSubgroup
  smul_mem' r x h := by
    change v ((r : R) * x) < γ -- not sure why simp can't get us to here
    simpa [Subring.smul_def] using mul_lt_of_le_one_of_lt r.prop h

-- Can't use `leAddSubgroup` because `addSubgroupOf` is a dependent function
lemma leIdeal_mono : Monotone (leIdeal R) :=
  fun _ _ h _ ↦ h.trans'

lemma ltIdeal_mono : Monotone (ltIdeal R) :=
  fun _ _ h _ ↦ (Units.val_le_val.mpr h).trans_lt'

lemma ltIdeal_le_leIdeal (γ : Γ₀ˣ) :
    ltIdeal R γ ≤ leIdeal R (γ : Γ₀) :=
  fun _ h ↦ h.le

variable {R} in
@[simp]
lemma mem_leIdeal_iff {γ : Γ₀} {x : 𝓞} :
    x ∈ leIdeal R γ ↔ v (x : R) ≤ γ :=
  Iff.rfl

variable {R} in
@[simp]
lemma mem_ltIdeal_iff {γ : Γ₀ˣ} {x : 𝓞} :
    x ∈ ltIdeal R γ ↔ v (x : R) < γ :=
  Iff.rfl

@[simp]
lemma leIdeal_zero (K : Type u) [Field K] [hv : Valued K Γ₀] :
    leIdeal K (0 : Γ₀) = ⊥ := by
  ext; simp

lemma isOpen_ltIdeal (γ : Γ₀ˣ) :
    IsOpen (ltIdeal R γ : Set 𝓞) :=
  isOpen_ball _ _ |>.preimage continuous_subtype_val

lemma isClosed_ltIdeal (γ : Γ₀ˣ) :
    IsClosed (ltIdeal R γ : Set 𝓞) :=
  isClosed_ball _ _ |>.preimage continuous_subtype_val

lemma isClopen_ltIdeal (γ : Γ₀ˣ) :
    IsClopen (ltIdeal R γ : Set 𝓞) :=
  isClopen_ball _ _ |>.preimage continuous_subtype_val

lemma isOpen_leIdeal {γ : Γ₀} (hγ : γ ≠ 0) :
    IsOpen (leIdeal R γ : Set 𝓞) :=
  isOpen_closedBall _ hγ |>.preimage continuous_subtype_val

lemma isClosed_leIdeal (γ : Γ₀) :
    IsClosed (leIdeal R γ : Set 𝓞) :=
  isClosed_closedBall _ _ |>.preimage continuous_subtype_val

lemma isClopen_leIdeal {γ : Γ₀} (hγ : γ ≠ 0) :
    IsClopen (leIdeal R γ : Set 𝓞) :=
  isClopen_closedBall _ hγ |>.preimage continuous_subtype_val

end Ideal

end Valued
