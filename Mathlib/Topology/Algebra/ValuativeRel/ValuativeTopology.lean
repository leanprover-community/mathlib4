/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.WithZeroTopology

/-!
# The topology on a ring induced by a valuation

In this file, we define the non-Archimedean topology induced by a valuation on a ring.

## Main definitions

* If we have both `[ValuativeRel R]` and `[TopologicalSpace R]`, then writing
  `[IsValuativeTopology R]` ensures that the topology on `R` agrees with the one induced by the
  valuation.
* `ValuativeRel.uniformSpace`: The uniform structure introduced by a `ValuativeRel`.

*NOTE* (2026-03-17): The `Valued` instance on a ring `R` would be
replaced by `[ValuativeRel R] [UniformSpace R] [IsValuativeTopology R] [IsUniformAddGroup R]`
(or `[ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]` when the uniformity is
not relevant). Additional input `(v : Valuation R Γ₀) [v.Compatible]` can be introduced whenever
a specific compatible valuation is chosen.

The canonical way to introduce the topological structure from a chosen valuation is:
1. First define the `ValuativeRel` structure using `ValuativeRel.ofValuation`;
2. Then define the `UniformSpace` structure using `ValuativeRel.uniformSpace`.
-/

public section

open scoped Topology Uniformity
open Set Filter Valuation ValuativeRel MonoidWithZeroHom ValueGroup₀ ValueGroupWithZero

noncomputable section

variable (R : Type*) [CommRing R] [ValuativeRel R]

variable {R} in
lemma Valuation.exists_setOf_restrict_le_iff {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) [v.Compatible] (x : R) (s : Set R) :
    (∃ γ : (ValueGroup₀ v)ˣ, {z | v.restrict (z - x) < γ.val} ⊆ s) ↔
    ∃ γ : (ValueGroupWithZero R)ˣ, {a | valuation R (a - x) < γ} ⊆ s := by
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨r.mapEquiv (orderMonoidIso v).symm, ?_⟩,
    fun ⟨r, hr⟩ ↦ ⟨r.mapEquiv (orderMonoidIso v), ?_⟩⟩
  all_goals convert hr; simp

/-- We say that a topology on `R` is valuative if the neighborhoods of `0` in `R`
are determined by the valuative relation `· ≤ᵥ ·`. -/
class IsValuativeTopology [TopologicalSpace R] where
  mem_nhds_iff {s : Set R} {x : R} : s ∈ 𝓝 (x : R) ↔
    ∃ γ : (ValueGroupWithZero R)ˣ, (x + ·) '' { z | valuation _ z < γ } ⊆ s

namespace ValuativeRel

/-- The topology induced by a valuative relation. Note that this is not made into a global instance
to avoid diamonds. If desired, one can equip a ring with a topological space from a valuative
relation by hand. But as long as they do so, the fact that the topology is valuative and
nonarchemidean can be automatically inferred. -/
local instance topologicalSpace : TopologicalSpace R := (valuation R).subgroups_basis.topology

instance nonarchimedeanRing : NonarchimedeanRing R :=
  (valuation R).subgroups_basis.nonarchimedean

instance isValuativeTopology : IsValuativeTopology R where
  mem_nhds_iff {s x} := by
    rw [Filter.hasBasis_iff.mp ((valuation R).subgroups_basis.hasBasis_nhds x) s]
    simp [neg_add_eq_sub, ← (valuation R).exists_setOf_restrict_le_iff,
      ← restrict_lt_iff_lt_embedding]

/-- The uniform structure induced by a valuative relation. Note that this is not made into a
global instance to avoid diamonds. If desired, one can equip a ring with a uniform space
from a valuative relation by hand. But as long as they do so, the fact that the topology is
valuative and nonarchimedean, and the addition is uniformly continuous,
can be automatically inferred. -/
local instance uniformSpace : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R

instance isUniformAddGroup : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup

end ValuativeRel

variable {R}

variable {K : Type*} [Field K] [ValuativeRel K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section TopologicalSpace

variable [TopologicalSpace R] [IsValuativeTopology R] (v : Valuation R Γ₀) [v.Compatible]

namespace IsValuativeTopology

/-- A variant of `IsValuativeTopology.mem_nhds_iff` using subtraction. -/
lemma mem_nhds_iff' {s : Set R} {x : R} :
    s ∈ 𝓝 x ↔ ∃ γ : (ValueGroupWithZero R)ˣ, { z | valuation R (z - x) < γ } ⊆ s := by
  convert mem_nhds_iff (s := s) using 4
  simp [neg_add_eq_sub]

lemma mem_nhds_zero_iff (s : Set R) :
    s ∈ 𝓝 0 ↔ ∃ γ : (ValueGroupWithZero R)ˣ, { x | valuation R x < γ } ⊆ s := by
  simp [mem_nhds_iff']

theorem hasBasis_nhds (x : R) :
    (𝓝 x).HasBasis (fun _ ↦ True)
      fun γ : (ValueGroupWithZero R)ˣ ↦ { z | valuation R (z - x) < γ } := by
  simp [Filter.hasBasis_iff, mem_nhds_iff']

/-- A variant of `hasBasis_nhds` where `· ≠ 0` is unbundled. -/
lemma hasBasis_nhds' (x : R) :
    (𝓝 x).HasBasis (· ≠ 0) ({ y | valuation R (y - x) < · }) :=
  (hasBasis_nhds x).to_hasBasis (fun γ _ ↦ ⟨γ, by simp⟩)
    fun γ hγ ↦ ⟨.mk0 γ hγ, by simp⟩

variable (R) in
theorem hasBasis_nhds_zero :
    (𝓝 0).HasBasis (fun _ ↦ True)
      fun γ : (ValueGroupWithZero R)ˣ ↦ { x | valuation R x < γ } := by
  convert hasBasis_nhds (0 : R)
  rw [sub_zero]

variable (R) in
/-- A variant of `hasBasis_nhds_zero` where `· ≠ 0` is unbundled. -/
lemma hasBasis_nhds_zero' :
    (𝓝 0).HasBasis (· ≠ 0) ({ x | valuation R x < · }) :=
  (hasBasis_nhds_zero R).to_hasBasis (fun γ _ ↦ ⟨γ, by simp⟩)
    fun γ hγ ↦ ⟨.mk0 γ hγ, by simp⟩

end IsValuativeTopology

open IsValuativeTopology

namespace Valuation

lemma mem_nhds_iff {s : Set R} {x : R} : s ∈ 𝓝 x ↔
    ∃ γ : (MonoidWithZeroHom.ValueGroup₀ v)ˣ, { z | v.restrict (z - x) < γ.val } ⊆ s := by
  convert IsValuativeTopology.mem_nhds_iff (s := s) using 4
  simpa [neg_add_eq_sub] using v.exists_setOf_restrict_le_iff _ _

lemma mem_nhds_zero_iff (s : Set R) : s ∈ 𝓝 0 ↔
    ∃ γ : (MonoidWithZeroHom.ValueGroup₀ v)ˣ, { x | v.restrict x < γ.val } ⊆ s := by
  simp [v.mem_nhds_iff]

alias is_topological_valuation := mem_nhds_zero_iff

theorem hasBasis_nhds (x : R) :
    (𝓝 x).HasBasis (fun _ ↦ True)
      fun γ : (MonoidWithZeroHom.ValueGroup₀ v)ˣ ↦ { z | v.restrict (z - x) < γ.val } := by
  simp [Filter.hasBasis_iff, v.mem_nhds_iff]

theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ ↦ True)
      fun γ : (MonoidWithZeroHom.ValueGroup₀ v)ˣ ↦ { x | v.restrict x < γ.val } := by
  simp [Filter.hasBasis_iff, v.is_topological_valuation]

/-- The set `{ y : R | v y = v x }` is a neighbourhood of `x`.
This does not imply that `v` is locally constant everywhere (since `v ⁻¹' {0}` is not open),
but it is equivalent to the restriction of `v` to the complement of its support being
locally constant. -/
theorem locally_const {x : R} (h : (v x : Γ₀) ≠ 0) : { y : R | v y = v x } ∈ 𝓝 x := by
  rw [v.mem_nhds_iff]
  have h' : v.restrict x ≠ 0 := by simp [h]
  use Units.mk0 _ h'
  rw [Units.val_mk0]
  intro y y_in
  exact Valuation.map_eq_of_sub_lt _ (v.restrict_lt_iff.mp y_in)

end Valuation

namespace IsValuativeTopology

variable (R) in
instance (priority := low) : IsTopologicalAddGroup R := by
  have cts_add : ContinuousConstVAdd R R :=
    ⟨fun x ↦ continuous_iff_continuousAt.2 fun z ↦
      (((valuation R).hasBasis_nhds z).tendsto_iff ((valuation R).hasBasis_nhds (x + z))).2
        fun γ _ ↦ ⟨γ, trivial, fun y hy ↦ by simpa using hy⟩⟩
  have basis := (valuation R).hasBasis_nhds_zero
  refine .of_comm_of_nhds_zero ?_ ?_ fun x₀ ↦ (map_eq_of_inverse (-x₀ + ·) ?_ ?_ ?_).symm
  · exact (basis.prod_self.tendsto_iff basis).2 fun γ _ ↦
      ⟨γ, trivial, fun ⟨_, _⟩ hx ↦ (valuation R).restrict.map_add_lt hx.left hx.right⟩
  · exact (basis.tendsto_iff basis).2 fun γ _ ↦ ⟨γ, trivial, fun y hy ↦ by simpa using hy⟩
  · ext; simp
  · simpa [ContinuousAt] using (cts_add.1 x₀).continuousAt (x := 0)
  · simpa [ContinuousAt] using (cts_add.1 (-x₀)).continuousAt (x := x₀)

end IsValuativeTopology

end TopologicalSpace

namespace Valuation

section UniformSpace

variable [_u : UniformSpace R] [IsUniformAddGroup R] [IsValuativeTopology R] (v : Valuation R Γ₀)
  [v.Compatible]

theorem hasBasis_uniformity : (𝓤 R).HasBasis (fun _ ↦ True)
    fun γ : (MonoidWithZeroHom.ValueGroup₀ v)ˣ ↦
      { p : R × R | v.restrict (p.2 - p.1) < γ.1 } := by
  rw [uniformity_eq_comap_nhds_zero]
  exact v.hasBasis_nhds_zero.comap _

theorem toUniformSpace_eq : _u =
    @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _ := by
  refine UniformSpace.ext (v.hasBasis_uniformity.eq_of_same_basis ?_)
  convert v.subgroups_basis.hasBasis_nhds_zero.comap _
  simp [restrict_lt_iff_lt_embedding, sub_eq_add_neg]

theorem cauchy_iff {F : Filter R} : Cauchy F ↔
    F.NeBot ∧ ∀ γ : (MonoidWithZeroHom.ValueGroup₀ v)ˣ,
      ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), v.restrict (y - x) < γ.1 := by
  rw [v.toUniformSpace_eq, AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [v.subgroups_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h γ
    simp_rw [restrict_lt_iff_lt_embedding]
    exact h _ (v.subgroups_basis.mem_addGroupFilterBasis γ)
  · rintro h - ⟨γ, rfl⟩
    simp_rw [restrict_lt_iff_lt_embedding] at h
    exact h γ

end UniformSpace

section TopologicalSpace

variable [_t : TopologicalSpace R] [IsValuativeTopology R] (v : Valuation R Γ₀) [v.Compatible]
  [TopologicalSpace K] [IsValuativeTopology K]

theorem toTopologicalSpace_eq :
    _t = v.subgroups_basis.topology := by
  letI u := IsTopologicalAddGroup.rightUniformSpace R
  letI := isUniformAddGroup_of_addCommGroup (G := R)
  exact congrArg (fun u ↦ @UniformSpace.toTopologicalSpace R u) v.toUniformSpace_eq

instance (priority := low) _root_.IsValuativeTopology.isTopologicalRing : IsTopologicalRing R := by
  convert (ValuativeRel.nonarchimedeanRing R).toIsTopologicalRing
  exact toTopologicalSpace_eq _

section Discrete

lemma discreteTopology_of_forall_map_eq_one (h : ∀ x : R, x ≠ 0 → v x = 1) :
    DiscreteTopology R := by
  simp only [discreteTopology_iff_isOpen_singleton_zero, isOpen_iff_mem_nhds, mem_singleton_iff,
    forall_eq, v.mem_nhds_zero_iff, subset_singleton_iff, mem_setOf_eq]
  use 1
  contrapose! h
  obtain ⟨x, hx, hx'⟩ := h
  rw [restrict_lt_iff_lt_embedding, Units.val_one, map_one] at hx
  exact ⟨x, hx', hx.ne⟩

lemma discreteTopology_of_forall_lt [MulArchimedean Γ₀] (v : Valuation K Γ₀)
    [v.Compatible] {r : Γ₀} (hr : r ≠ 0) (h : ∀ x : K, v x ≠ 0 → r < v x) :
    DiscreteTopology K :=
  v.discreteTopology_of_forall_map_eq_one (by simpa using v.map_eq_one_of_forall_lt hr h)

end Discrete

variable {v}

set_option backward.isDefEq.respectTransparency false in
/-- For any valuation `v` compatible with the valuative relation on `R`, the open `r`-ball
around zero `{x | v.restrict x < r}` is open in the valuative topology. -/
theorem isOpen_ball (r : ValueGroup₀ v) : IsOpen (X := R) {x | v.restrict x < r} := by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  intro x hx
  rw [v.mem_nhds_iff]
  simp only [setOf_subset_setOf]
  exact ⟨Units.mk0 _ hr,
    fun y hy ↦ (sub_add_cancel y x).symm ▸ (v.restrict.map_add _ x).trans_lt (max_lt hy hx)⟩

set_option backward.isDefEq.respectTransparency false in
/-- For any valuation `v` compatible with the valuative relation on `R`, the open `r`-ball
around zero `{x | v.restrict x < r}` is closed in the valuative topology. -/
theorem isClosed_ball (r : ValueGroup₀ v) : IsClosed (X := R) {x | v.restrict x < r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  exact AddSubgroup.isClosed_of_isOpen (Valuation.ltAddSubgroup v.restrict (Units.mk0 r hr))
    (isOpen_ball _)

/-- For any valuation `v` compatible with the valuative relation on `R`, the open `r`-ball
around zero `{x | v.restrict x < r}` is clopen in the valuative topology. -/
theorem isClopen_ball (r : ValueGroup₀ v) : IsClopen (X := R) {x | v.restrict x < r} :=
  ⟨isClosed_ball _, isOpen_ball _⟩

/-- For any valuation `v` compatible with the valuative relation on `R`, the closed `r`-ball
around zero `{x | v.restrict x ≤ r}` is open in the valuative topology. -/
theorem isOpen_closedBall {r : ValueGroup₀ v} (hr : r ≠ 0) :
  IsOpen (X := R) {x | v.restrict x ≤ r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  simp only [v.mem_nhds_iff, setOf_subset_setOf]
  exact ⟨Units.mk0 _ hr, fun y hy ↦
    (sub_add_cancel y x).symm ▸ le_trans (v.restrict.map_add _ _) (max_le (le_of_lt hy) hx)⟩

/-- For any valuation `v` compatible with the valuative relation on `R`, the closed `r`-ball
around zero `{x | v.restrict x ≤ r}` is closed in the valuative topology. -/
theorem isClosed_closedBall (r : ValueGroup₀ v) : IsClosed (X := R) {x | v.restrict x ≤ r} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_setOf_eq, not_le] at hx
  rw [v.mem_nhds_iff]
  have hx' : v.restrict x ≠ 0 := ne_of_gt <| lt_of_le_of_lt zero_le' <| hx
  exact ⟨Units.mk0 _ hx', fun y hy hy' ↦ ne_of_lt hy <| map_sub_swap v.restrict x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' hx)⟩

/-- For any valuation `v` compatible with the valuative relation on `R`, the closed `r`-ball
around zero `{x | v.restrict x ≤ r}` is clopen in the valuative topology. -/
theorem isClopen_closedBall {r : ValueGroup₀ v} (hr : r ≠ 0) :
    IsClopen (X := R) {x | v.restrict x ≤ r} :=
  ⟨isClosed_closedBall _, isOpen_closedBall hr⟩

/-- For any valuation `v` compatible with the valuative relation on `R`, the sphere of radius `r`
around zero `{x | v.restrict x = r}` is clopen in the valuative topology. -/
theorem isClopen_sphere {r : ValueGroup₀ v} (hr : r ≠ 0) :
    IsClopen (X := R) {x | v.restrict x = r} := by
  have h : {x : R | v.restrict x = r} = {x | v.restrict x ≤ r} \ {x | v.restrict x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall hr) (isClopen_ball _)

/-- For any valuation `v` compatible with the valuative relation on `R`, the sphere of radius `r`
around zero `{x | v.restrict x = r}` is open in the valuative topology. -/
theorem isOpen_sphere {r : ValueGroup₀ v} (hr : r ≠ 0) :
    IsOpen (X := R) {x | v.restrict x = r} :=
  isClopen_sphere hr |>.isOpen

/-- For any valuation `v` compatible with the valuative relation on `R`, the sphere of radius `r`
around zero `{x | v.restrict x = r}` is closed in the valuative topology. -/
theorem isClosed_sphere (r : ValueGroup₀ v) : IsClosed (X := R) {x | v.restrict x = r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · convert v.isClosed_closedBall 0 using 3
    exact le_zero_iff.symm
  exact isClopen_sphere hr |>.isClosed

/-- For any valuation `v` compatible with the valuative relation on `R`, the closed unit ball
around zero `{x | v x ≤ 1}` is open in the valuative topology. -/
theorem isOpen_integer : IsOpen (v.integer : Set R) := by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  apply isOpen_closedBall one_ne_zero

/-- For any valuation `v` compatible with the valuative relation on `R`, the closed unit ball
around zero `{x | v x ≤ 1}` is closed in the valuative topology. -/
theorem isClosed_integer : IsClosed (v.integer : Set R) := by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isClosed_closedBall _

/-- For any valuation `v` compatible with the valuative relation on `R`, the closed unit ball
around zero `{x | v x ≤ 1}` is clopen in the valuative topology. -/
theorem isClopen_integer : IsClopen (v.integer : Set R) :=
  ⟨isClosed_integer, isOpen_integer⟩

/-- For any valuation `v` compatible with the valuative relation on a field `K`, the valuation
subring defined by `v` is open in the valuative topology. -/
theorem isOpen_valuationSubring (v : Valuation K Γ₀) [v.Compatible] :
    IsOpen (v.valuationSubring : Set K) :=
  isOpen_integer

/-- For any valuation `v` compatible with the valuative relation on a field `K`, the valuation
subring defined by `v` is closed in the valuative topology. -/
theorem isClosed_valuationSubring (v : Valuation K Γ₀) [v.Compatible] :
    IsClosed (v.valuationSubring : Set K) :=
  isClosed_integer

/-- For any valuation `v` compatible with the valuative relation on a field `K`, the valuation
subring defined by `v` is clopen in the valuative topology. -/
theorem isClopen_valuationSubring (v : Valuation K Γ₀) [v.Compatible] :
    IsClopen (v.valuationSubring : Set K) :=
  isClopen_integer

end TopologicalSpace

end Valuation

namespace IsValuativeTopology

@[deprecated (since := "2026-03-17")] alias isOpen_ball := Valuation.isOpen_ball
@[deprecated (since := "2026-03-17")] alias isClosed_ball := Valuation.isClosed_ball
@[deprecated (since := "2026-03-17")] alias isClopen_ball := Valuation.isClopen_ball
@[deprecated (since := "2026-03-17")] alias isOpen_closedBall := Valuation.isOpen_closedBall
@[deprecated (since := "2026-03-17")] alias isClosed_closedBall := Valuation.isClosed_closedBall
@[deprecated (since := "2026-03-17")] alias isClopen_closedBall := Valuation.isClopen_closedBall
@[deprecated (since := "2026-03-17")] alias isClopen_sphere := Valuation.isClopen_sphere
@[deprecated (since := "2026-03-17")] alias isOpen_sphere := Valuation.isOpen_sphere

end IsValuativeTopology
