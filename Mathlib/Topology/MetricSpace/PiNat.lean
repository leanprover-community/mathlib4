/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance

#align_import topology.metric_space.pi_nat from "leanprover-community/mathlib"@"49b7f94aab3a3bdca1f9f34c5d818afb253b3993"

/-!
# Topological study of spaces `Π (n : ℕ), E n`

When `E n` are topological spaces, the space `Π (n : ℕ), E n` is naturally a topological space
(with the product topology). When `E n` are uniform spaces, it also inherits a uniform structure.
However, it does not inherit a canonical metric space structure of the `E n`. Nevertheless, one
can put a noncanonical metric space structure (or rather, several of them). This is done in this
file.

## Main definitions and results

One can define a combinatorial distance on `Π (n : ℕ), E n`, as follows:

* `PiNat.cylinder x n` is the set of points `y` with `x i = y i` for `i < n`.
* `PiNat.firstDiff x y` is the first index at which `x i ≠ y i`.
* `PiNat.dist x y` is equal to `(1/2) ^ (firstDiff x y)`. It defines a distance
  on `Π (n : ℕ), E n`, compatible with the topology when the `E n` have the discrete topology.
* `PiNat.metricSpace`: the metric space structure, given by this distance. Not registered as an
  instance. This space is a complete metric space.
* `PiNat.metricSpaceOfDiscreteUniformity`: the same metric space structure, but adjusting the
  uniformity defeqness when the `E n` already have the discrete uniformity. Not registered as an
  instance
* `PiNat.metricSpaceNatNat`: the particular case of `ℕ → ℕ`, not registered as an instance.

These results are used to construct continuous functions on `Π n, E n`:

* `PiNat.exists_retraction_of_isClosed`: given a nonempty closed subset `s` of `Π (n : ℕ), E n`,
  there exists a retraction onto `s`, i.e., a continuous map from the whole space to `s`
  restricting to the identity on `s`.
* `exists_nat_nat_continuous_surjective_of_completeSpace`: given any nonempty complete metric
  space with second-countable topology, there exists a continuous surjection from `ℕ → ℕ` onto
  this space.

One can also put distances on `Π (i : ι), E i` when the spaces `E i` are metric spaces (not discrete
in general), and `ι` is countable.

* `PiCountable.dist` is the distance on `Π i, E i` given by
    `dist x y = ∑' i, min (1/2)^(encode i) (dist (x i) (y i))`.
* `PiCountable.metricSpace` is the corresponding metric space structure, adjusted so that
  the uniformity is definitionally the product uniformity. Not registered as an instance.
-/


noncomputable section

open scoped Classical
open Topology Filter

open TopologicalSpace Set Metric Filter Function

attribute [local simp] pow_le_pow_iff_right one_lt_two inv_le_inv zero_le_two zero_lt_two

variable {E : ℕ → Type*}

namespace PiNat

/-! ### The firstDiff function -/

/-- In a product space `Π n, E n`, then `firstDiff x y` is the first index at which `x` and `y`
differ. If `x = y`, then by convention we set `firstDiff x x = 0`. -/
irreducible_def firstDiff (x y : ∀ n, E n) : ℕ :=
  if h : x ≠ y then Nat.find (ne_iff.1 h) else 0
#align pi_nat.first_diff PiNat.firstDiff

theorem apply_firstDiff_ne {x y : ∀ n, E n} (h : x ≠ y) :
    x (firstDiff x y) ≠ y (firstDiff x y) := by
  rw [firstDiff_def, dif_pos h]
  exact Nat.find_spec (ne_iff.1 h)
#align pi_nat.apply_first_diff_ne PiNat.apply_firstDiff_ne

theorem apply_eq_of_lt_firstDiff {x y : ∀ n, E n} {n : ℕ} (hn : n < firstDiff x y) : x n = y n := by
  rw [firstDiff_def] at hn
  split_ifs at hn with h
  · convert Nat.find_min (ne_iff.1 h) hn
    simp
  · exact (not_lt_zero' hn).elim
#align pi_nat.apply_eq_of_lt_first_diff PiNat.apply_eq_of_lt_firstDiff

theorem firstDiff_comm (x y : ∀ n, E n) : firstDiff x y = firstDiff y x := by
  simp only [firstDiff_def, ne_comm]
#align pi_nat.first_diff_comm PiNat.firstDiff_comm

theorem min_firstDiff_le (x y z : ∀ n, E n) (h : x ≠ z) :
    min (firstDiff x y) (firstDiff y z) ≤ firstDiff x z := by
  by_contra! H
  rw [lt_min_iff] at H
  refine apply_firstDiff_ne h ?_
  calc
    x (firstDiff x z) = y (firstDiff x z) := apply_eq_of_lt_firstDiff H.1
    _ = z (firstDiff x z) := apply_eq_of_lt_firstDiff H.2
#align pi_nat.min_first_diff_le PiNat.min_firstDiff_le

/-! ### Cylinders -/

/-- In a product space `Π n, E n`, the cylinder set of length `n` around `x`, denoted
`cylinder x n`, is the set of sequences `y` that coincide with `x` on the first `n` symbols, i.e.,
such that `y i = x i` for all `i < n`.
-/
def cylinder (x : ∀ n, E n) (n : ℕ) : Set (∀ n, E n) :=
  { y | ∀ i, i < n → y i = x i }
#align pi_nat.cylinder PiNat.cylinder

theorem cylinder_eq_pi (x : ∀ n, E n) (n : ℕ) :
    cylinder x n = Set.pi (Finset.range n : Set ℕ) fun i : ℕ => {x i} := by
  ext y
  simp [cylinder]
#align pi_nat.cylinder_eq_pi PiNat.cylinder_eq_pi

@[simp]
theorem cylinder_zero (x : ∀ n, E n) : cylinder x 0 = univ := by simp [cylinder_eq_pi]
#align pi_nat.cylinder_zero PiNat.cylinder_zero

theorem cylinder_anti (x : ∀ n, E n) {m n : ℕ} (h : m ≤ n) : cylinder x n ⊆ cylinder x m :=
  fun _y hy i hi => hy i (hi.trans_le h)
#align pi_nat.cylinder_anti PiNat.cylinder_anti

@[simp]
theorem mem_cylinder_iff {x y : ∀ n, E n} {n : ℕ} : y ∈ cylinder x n ↔ ∀ i < n, y i = x i :=
  Iff.rfl
#align pi_nat.mem_cylinder_iff PiNat.mem_cylinder_iff

theorem self_mem_cylinder (x : ∀ n, E n) (n : ℕ) : x ∈ cylinder x n := by simp
#align pi_nat.self_mem_cylinder PiNat.self_mem_cylinder

theorem mem_cylinder_iff_eq {x y : ∀ n, E n} {n : ℕ} :
    y ∈ cylinder x n ↔ cylinder y n = cylinder x n := by
  constructor
  · intro hy
    apply Subset.antisymm
    · intro z hz i hi
      rw [← hy i hi]
      exact hz i hi
    · intro z hz i hi
      rw [hy i hi]
      exact hz i hi
  · intro h
    rw [← h]
    exact self_mem_cylinder _ _
#align pi_nat.mem_cylinder_iff_eq PiNat.mem_cylinder_iff_eq

theorem mem_cylinder_comm (x y : ∀ n, E n) (n : ℕ) : y ∈ cylinder x n ↔ x ∈ cylinder y n := by
  simp [mem_cylinder_iff_eq, eq_comm]
#align pi_nat.mem_cylinder_comm PiNat.mem_cylinder_comm

theorem mem_cylinder_iff_le_firstDiff {x y : ∀ n, E n} (hne : x ≠ y) (i : ℕ) :
    x ∈ cylinder y i ↔ i ≤ firstDiff x y := by
  constructor
  · intro h
    by_contra!
    exact apply_firstDiff_ne hne (h _ this)
  · intro hi j hj
    exact apply_eq_of_lt_firstDiff (hj.trans_le hi)
#align pi_nat.mem_cylinder_iff_le_first_diff PiNat.mem_cylinder_iff_le_firstDiff

theorem mem_cylinder_firstDiff (x y : ∀ n, E n) : x ∈ cylinder y (firstDiff x y) := fun _i hi =>
  apply_eq_of_lt_firstDiff hi
#align pi_nat.mem_cylinder_first_diff PiNat.mem_cylinder_firstDiff

theorem cylinder_eq_cylinder_of_le_firstDiff (x y : ∀ n, E n) {n : ℕ} (hn : n ≤ firstDiff x y) :
    cylinder x n = cylinder y n := by
  rw [← mem_cylinder_iff_eq]
  intro i hi
  exact apply_eq_of_lt_firstDiff (hi.trans_le hn)
#align pi_nat.cylinder_eq_cylinder_of_le_first_diff PiNat.cylinder_eq_cylinder_of_le_firstDiff

theorem iUnion_cylinder_update (x : ∀ n, E n) (n : ℕ) :
    ⋃ k, cylinder (update x n k) (n + 1) = cylinder x n := by
  ext y
  simp only [mem_cylinder_iff, mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩ i hi
    simpa [hi.ne] using hk i (Nat.lt_succ_of_lt hi)
  · intro H
    refine ⟨y n, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with (h'i | rfl)
    · simp [H i h'i, h'i.ne]
    · simp
#align pi_nat.Union_cylinder_update PiNat.iUnion_cylinder_update

theorem update_mem_cylinder (x : ∀ n, E n) (n : ℕ) (y : E n) : update x n y ∈ cylinder x n :=
  mem_cylinder_iff.2 fun i hi => by simp [hi.ne]
#align pi_nat.update_mem_cylinder PiNat.update_mem_cylinder

section Res

variable {α : Type*}

open List

/-- In the case where `E` has constant value `α`,
the cylinder `cylinder x n` can be identified with the element of `List α`
consisting of the first `n` entries of `x`. See `cylinder_eq_res`.
We call this list `res x n`, the restriction of `x` to `n`. -/
def res (x : ℕ → α) : ℕ → List α
  | 0 => nil
  | Nat.succ n => x n :: res x n
#align pi_nat.res PiNat.res

@[simp]
theorem res_zero (x : ℕ → α) : res x 0 = @nil α :=
  rfl
#align pi_nat.res_zero PiNat.res_zero

@[simp]
theorem res_succ (x : ℕ → α) (n : ℕ) : res x n.succ = x n :: res x n :=
  rfl
#align pi_nat.res_succ PiNat.res_succ

@[simp]
theorem res_length (x : ℕ → α) (n : ℕ) : (res x n).length = n := by induction n <;> simp [*]
#align pi_nat.res_length PiNat.res_length

/-- The restrictions of `x` and `y` to `n` are equal if and only if `x m = y m` for all `m < n`. -/
theorem res_eq_res {x y : ℕ → α} {n : ℕ} :
    res x n = res y n ↔ ∀ ⦃m⦄, m < n → x m = y m := by
  constructor <;> intro h <;> induction' n with n ih; · simp
  · intro m hm
    rw [Nat.lt_succ_iff_lt_or_eq] at hm
    simp only [res_succ, cons.injEq] at h
    cases' hm with hm hm
    · exact ih h.2 hm
    rw [hm]
    exact h.1
  · simp
  simp only [res_succ, cons.injEq]
  refine ⟨h (Nat.lt_succ_self _), ih fun m hm => ?_⟩
  exact h (hm.trans (Nat.lt_succ_self _))
#align pi_nat.res_eq_res PiNat.res_eq_res

theorem res_injective : Injective (@res α) := by
  intro x y h
  ext n
  apply res_eq_res.mp _ (Nat.lt_succ_self _)
  rw [h]
#align pi_nat.res_injective PiNat.res_injective

/-- `cylinder x n` is equal to the set of sequences `y` with the same restriction to `n` as `x`. -/
theorem cylinder_eq_res (x : ℕ → α) (n : ℕ) :
    cylinder x n = { y | res y n = res x n } := by
  ext y
  dsimp [cylinder]
  rw [res_eq_res]
#align pi_nat.cylinder_eq_res PiNat.cylinder_eq_res

end Res

/-!
### A distance function on `Π n, E n`

We define a distance function on `Π n, E n`, given by `dist x y = (1/2)^n` where `n` is the first
index at which `x` and `y` differ. When each `E n` has the discrete topology, this distance will
define the right topology on the product space. We do not record a global `Dist` instance nor
a `MetricSpace` instance, as other distances may be used on these spaces, but we register them as
local instances in this section.
-/

/-- The distance function on a product space `Π n, E n`, given by `dist x y = (1/2)^n` where `n` is
the first index at which `x` and `y` differ. -/
protected def dist : Dist (∀ n, E n) :=
  ⟨fun x y => if x ≠ y then (1 / 2 : ℝ) ^ firstDiff x y else 0⟩
#align pi_nat.has_dist PiNat.dist

attribute [local instance] PiNat.dist

theorem dist_eq_of_ne {x y : ∀ n, E n} (h : x ≠ y) : dist x y = (1 / 2 : ℝ) ^ firstDiff x y := by
  simp [dist, h]
#align pi_nat.dist_eq_of_ne PiNat.dist_eq_of_ne

protected theorem dist_self (x : ∀ n, E n) : dist x x = 0 := by simp [dist]
#align pi_nat.dist_self PiNat.dist_self

protected theorem dist_comm (x y : ∀ n, E n) : dist x y = dist y x := by
  simp [dist, @eq_comm _ x y, firstDiff_comm]
#align pi_nat.dist_comm PiNat.dist_comm

protected theorem dist_nonneg (x y : ∀ n, E n) : 0 ≤ dist x y := by
  rcases eq_or_ne x y with (rfl | h)
  · simp [dist]
  · simp [dist, h, zero_le_two]
#align pi_nat.dist_nonneg PiNat.dist_nonneg

theorem dist_triangle_nonarch (x y z : ∀ n, E n) : dist x z ≤ max (dist x y) (dist y z) := by
  rcases eq_or_ne x z with (rfl | hxz)
  · simp [PiNat.dist_self x, PiNat.dist_nonneg]
  rcases eq_or_ne x y with (rfl | hxy)
  · simp
  rcases eq_or_ne y z with (rfl | hyz)
  · simp
  simp only [dist_eq_of_ne, hxz, hxy, hyz, inv_le_inv, one_div, inv_pow, zero_lt_two, Ne,
    not_false_iff, le_max_iff, pow_le_pow_iff_right, one_lt_two, pow_pos,
    min_le_iff.1 (min_firstDiff_le x y z hxz)]
#align pi_nat.dist_triangle_nonarch PiNat.dist_triangle_nonarch

protected theorem dist_triangle (x y z : ∀ n, E n) : dist x z ≤ dist x y + dist y z :=
  calc
    dist x z ≤ max (dist x y) (dist y z) := dist_triangle_nonarch x y z
    _ ≤ dist x y + dist y z := max_le_add_of_nonneg (PiNat.dist_nonneg _ _) (PiNat.dist_nonneg _ _)
#align pi_nat.dist_triangle PiNat.dist_triangle

protected theorem eq_of_dist_eq_zero (x y : ∀ n, E n) (hxy : dist x y = 0) : x = y := by
  rcases eq_or_ne x y with (rfl | h); · rfl
  simp [dist_eq_of_ne h] at hxy
#align pi_nat.eq_of_dist_eq_zero PiNat.eq_of_dist_eq_zero

theorem mem_cylinder_iff_dist_le {x y : ∀ n, E n} {n : ℕ} :
    y ∈ cylinder x n ↔ dist y x ≤ (1 / 2) ^ n := by
  rcases eq_or_ne y x with (rfl | hne)
  · simp [PiNat.dist_self]
  suffices (∀ i : ℕ, i < n → y i = x i) ↔ n ≤ firstDiff y x by simpa [dist_eq_of_ne hne]
  constructor
  · intro hy
    by_contra! H
    exact apply_firstDiff_ne hne (hy _ H)
  · intro h i hi
    exact apply_eq_of_lt_firstDiff (hi.trans_le h)
#align pi_nat.mem_cylinder_iff_dist_le PiNat.mem_cylinder_iff_dist_le

theorem apply_eq_of_dist_lt {x y : ∀ n, E n} {n : ℕ} (h : dist x y < (1 / 2) ^ n) {i : ℕ}
    (hi : i ≤ n) : x i = y i := by
  rcases eq_or_ne x y with (rfl | hne)
  · rfl
  have : n < firstDiff x y := by
    simpa [dist_eq_of_ne hne, inv_lt_inv, pow_lt_pow_iff_right, one_lt_two] using h
  exact apply_eq_of_lt_firstDiff (hi.trans_lt this)
#align pi_nat.apply_eq_of_dist_lt PiNat.apply_eq_of_dist_lt

/-- A function to a pseudo-metric-space is `1`-Lipschitz if and only if points in the same cylinder
of length `n` are sent to points within distance `(1/2)^n`.
Not expressed using `LipschitzWith` as we don't have a metric space structure -/
theorem lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder {α : Type*}
    [PseudoMetricSpace α] {f : (∀ n, E n) → α} :
    (∀ x y : ∀ n, E n, dist (f x) (f y) ≤ dist x y) ↔
      ∀ x y n, y ∈ cylinder x n → dist (f x) (f y) ≤ (1 / 2) ^ n := by
  constructor
  · intro H x y n hxy
    apply (H x y).trans
    rw [PiNat.dist_comm]
    exact mem_cylinder_iff_dist_le.1 hxy
  · intro H x y
    rcases eq_or_ne x y with (rfl | hne)
    · simp [PiNat.dist_nonneg]
    rw [dist_eq_of_ne hne]
    apply H x y (firstDiff x y)
    rw [firstDiff_comm]
    exact mem_cylinder_firstDiff _ _
#align pi_nat.lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder PiNat.lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder

variable (E)
variable [∀ n, TopologicalSpace (E n)] [∀ n, DiscreteTopology (E n)]

theorem isOpen_cylinder (x : ∀ n, E n) (n : ℕ) : IsOpen (cylinder x n) := by
  rw [PiNat.cylinder_eq_pi]
  exact isOpen_set_pi (Finset.range n).finite_toSet fun a _ => isOpen_discrete _
#align pi_nat.is_open_cylinder PiNat.isOpen_cylinder

theorem isTopologicalBasis_cylinders :
    IsTopologicalBasis { s : Set (∀ n, E n) | ∃ (x : ∀ n, E n) (n : ℕ), s = cylinder x n } := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro u ⟨x, n, rfl⟩
    apply isOpen_cylinder
  · intro x u hx u_open
    obtain ⟨v, ⟨U, F, -, rfl⟩, xU, Uu⟩ :
        ∃ v ∈ { S : Set (∀ i : ℕ, E i) | ∃ (U : ∀ i : ℕ, Set (E i)) (F : Finset ℕ),
          (∀ i : ℕ, i ∈ F → U i ∈ { s : Set (E i) | IsOpen s }) ∧ S = (F : Set ℕ).pi U },
        x ∈ v ∧ v ⊆ u :=
      (isTopologicalBasis_pi fun n : ℕ => isTopologicalBasis_opens).exists_subset_of_mem_open hx
        u_open
    rcases Finset.bddAbove F with ⟨n, hn⟩
    refine ⟨cylinder x (n + 1), ⟨x, n + 1, rfl⟩, self_mem_cylinder _ _, Subset.trans ?_ Uu⟩
    intro y hy
    suffices ∀ i : ℕ, i ∈ F → y i ∈ U i by simpa
    intro i hi
    have : y i = x i := mem_cylinder_iff.1 hy i ((hn hi).trans_lt (lt_add_one n))
    rw [this]
    simp only [Set.mem_pi, Finset.mem_coe] at xU
    exact xU i hi
#align pi_nat.is_topological_basis_cylinders PiNat.isTopologicalBasis_cylinders

variable {E}

theorem isOpen_iff_dist (s : Set (∀ n, E n)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s := by
  constructor
  · intro hs x hx
    obtain ⟨v, ⟨y, n, rfl⟩, h'x, h's⟩ :
        ∃ v ∈ { s | ∃ (x : ∀ n : ℕ, E n) (n : ℕ), s = cylinder x n }, x ∈ v ∧ v ⊆ s :=
      (isTopologicalBasis_cylinders E).exists_subset_of_mem_open hx hs
    rw [← mem_cylinder_iff_eq.1 h'x] at h's
    exact
      ⟨(1 / 2 : ℝ) ^ n, by simp, fun y hy => h's fun i hi => (apply_eq_of_dist_lt hy hi.le).symm⟩
  · intro h
    refine (isTopologicalBasis_cylinders E).isOpen_iff.2 fun x hx => ?_
    rcases h x hx with ⟨ε, εpos, hε⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < ε := exists_pow_lt_of_lt_one εpos one_half_lt_one
    refine ⟨cylinder x n, ⟨x, n, rfl⟩, self_mem_cylinder x n, fun y hy => hε y ?_⟩
    rw [PiNat.dist_comm]
    exact (mem_cylinder_iff_dist_le.1 hy).trans_lt hn
#align pi_nat.is_open_iff_dist PiNat.isOpen_iff_dist

/-- Metric space structure on `Π (n : ℕ), E n` when the spaces `E n` have the discrete topology,
where the distance is given by `dist x y = (1/2)^n`, where `n` is the smallest index where `x` and
`y` differ. Not registered as a global instance by default.
Warning: this definition makes sure that the topology is defeq to the original product topology,
but it does not take care of a possible uniformity. If the `E n` have a uniform structure, then
there will be two non-defeq uniform structures on `Π n, E n`, the product one and the one coming
from the metric structure. In this case, use `metricSpaceOfDiscreteUniformity` instead. -/
protected def metricSpace : MetricSpace (∀ n, E n) :=
  MetricSpace.ofDistTopology dist PiNat.dist_self PiNat.dist_comm PiNat.dist_triangle
    isOpen_iff_dist PiNat.eq_of_dist_eq_zero
#align pi_nat.metric_space PiNat.metricSpace

/-- Metric space structure on `Π (n : ℕ), E n` when the spaces `E n` have the discrete uniformity,
where the distance is given by `dist x y = (1/2)^n`, where `n` is the smallest index where `x` and
`y` differ. Not registered as a global instance by default. -/
protected def metricSpaceOfDiscreteUniformity {E : ℕ → Type*} [∀ n, UniformSpace (E n)]
    (h : ∀ n, uniformity (E n) = 𝓟 idRel) : MetricSpace (∀ n, E n) :=
  haveI : ∀ n, DiscreteTopology (E n) := fun n => discreteTopology_of_discrete_uniformity (h n)
  { dist_triangle := PiNat.dist_triangle
    dist_comm := PiNat.dist_comm
    dist_self := PiNat.dist_self
    eq_of_dist_eq_zero := PiNat.eq_of_dist_eq_zero _ _
    edist_dist := fun _ _ ↦ by exact ENNReal.coe_nnreal_eq _
    toUniformSpace := Pi.uniformSpace _
    uniformity_dist := by
      simp [Pi.uniformity, comap_iInf, gt_iff_lt, preimage_setOf_eq, comap_principal,
        PseudoMetricSpace.uniformity_dist, h, idRel]
      apply le_antisymm
      · simp only [le_iInf_iff, le_principal_iff]
        intro ε εpos
        obtain ⟨n, hn⟩ : ∃ n, (1 / 2 : ℝ) ^ n < ε := exists_pow_lt_of_lt_one εpos (by norm_num)
        apply
          @mem_iInf_of_iInter _ _ _ _ _ (Finset.range n).finite_toSet fun i =>
            { p : (∀ n : ℕ, E n) × ∀ n : ℕ, E n | p.fst i = p.snd i }
        · simp only [mem_principal, setOf_subset_setOf, imp_self, imp_true_iff]
        · rintro ⟨x, y⟩ hxy
          simp only [Finset.mem_coe, Finset.mem_range, iInter_coe_set, mem_iInter, mem_setOf_eq]
            at hxy
          apply lt_of_le_of_lt _ hn
          rw [← mem_cylinder_iff_dist_le, mem_cylinder_iff]
          exact hxy
      · simp only [le_iInf_iff, le_principal_iff]
        intro n
        refine mem_iInf_of_mem ((1 / 2) ^ n : ℝ) ?_
        refine mem_iInf_of_mem (by positivity) ?_
        simp only [mem_principal, setOf_subset_setOf, Prod.forall]
        intro x y hxy
        exact apply_eq_of_dist_lt hxy le_rfl }
#align pi_nat.metric_space_of_discrete_uniformity PiNat.metricSpaceOfDiscreteUniformity

/-- Metric space structure on `ℕ → ℕ` where the distance is given by `dist x y = (1/2)^n`,
where `n` is the smallest index where `x` and `y` differ.
Not registered as a global instance by default. -/
def metricSpaceNatNat : MetricSpace (ℕ → ℕ) :=
  PiNat.metricSpaceOfDiscreteUniformity fun _ => rfl
#align pi_nat.metric_space_nat_nat PiNat.metricSpaceNatNat

attribute [local instance] PiNat.metricSpace

protected theorem completeSpace : CompleteSpace (∀ n, E n) := by
  refine Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2) ^ n) (by simp) ?_
  intro u hu
  refine ⟨fun n => u n n, tendsto_pi_nhds.2 fun i => ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.Ici_mem_atTop i] with n hn
  exact apply_eq_of_dist_lt (hu i i n le_rfl hn) le_rfl
#align pi_nat.complete_space PiNat.completeSpace

/-!
### Retractions inside product spaces

We show that, in a space `Π (n : ℕ), E n` where each `E n` is discrete, there is a retraction on
any closed nonempty subset `s`, i.e., a continuous map `f` from the whole space to `s` restricting
to the identity on `s`. The map `f` is defined as follows. For `x ∈ s`, let `f x = x`. Otherwise,
consider the longest prefix `w` that `x` shares with an element of `s`, and let `f x = z_w`
where `z_w` is an element of `s` starting with `w`.
-/

theorem exists_disjoint_cylinder {s : Set (∀ n, E n)} (hs : IsClosed s) {x : ∀ n, E n}
    (hx : x ∉ s) : ∃ n, Disjoint s (cylinder x n) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · exact ⟨0, by simp⟩
  have A : 0 < infDist x s := (hs.not_mem_iff_infDist_pos hne).1 hx
  obtain ⟨n, hn⟩ : ∃ n, (1 / 2 : ℝ) ^ n < infDist x s := exists_pow_lt_of_lt_one A one_half_lt_one
  refine ⟨n, disjoint_left.2 fun y ys hy => ?_⟩
  apply lt_irrefl (infDist x s)
  calc
    infDist x s ≤ dist x y := infDist_le_dist_of_mem ys
    _ ≤ (1 / 2) ^ n := by
      rw [mem_cylinder_comm] at hy
      exact mem_cylinder_iff_dist_le.1 hy
    _ < infDist x s := hn
#align pi_nat.exists_disjoint_cylinder PiNat.exists_disjoint_cylinder

/-- Given a point `x` in a product space `Π (n : ℕ), E n`, and `s` a subset of this space, then
`shortestPrefixDiff x s` if the smallest `n` for which there is no element of `s` having the same
prefix of length `n` as `x`. If there is no such `n`, then use `0` by convention. -/
def shortestPrefixDiff {E : ℕ → Type*} (x : ∀ n, E n) (s : Set (∀ n, E n)) : ℕ :=
  if h : ∃ n, Disjoint s (cylinder x n) then Nat.find h else 0
#align pi_nat.shortest_prefix_diff PiNat.shortestPrefixDiff

theorem firstDiff_lt_shortestPrefixDiff {s : Set (∀ n, E n)} (hs : IsClosed s) {x y : ∀ n, E n}
    (hx : x ∉ s) (hy : y ∈ s) : firstDiff x y < shortestPrefixDiff x s := by
  have A := exists_disjoint_cylinder hs hx
  rw [shortestPrefixDiff, dif_pos A]
  have B := Nat.find_spec A
  contrapose! B
  rw [not_disjoint_iff_nonempty_inter]
  refine ⟨y, hy, ?_⟩
  rw [mem_cylinder_comm]
  exact cylinder_anti y B (mem_cylinder_firstDiff x y)
#align pi_nat.first_diff_lt_shortest_prefix_diff PiNat.firstDiff_lt_shortestPrefixDiff

theorem shortestPrefixDiff_pos {s : Set (∀ n, E n)} (hs : IsClosed s) (hne : s.Nonempty)
    {x : ∀ n, E n} (hx : x ∉ s) : 0 < shortestPrefixDiff x s := by
  rcases hne with ⟨y, hy⟩
  exact (zero_le _).trans_lt (firstDiff_lt_shortestPrefixDiff hs hx hy)
#align pi_nat.shortest_prefix_diff_pos PiNat.shortestPrefixDiff_pos

/-- Given a point `x` in a product space `Π (n : ℕ), E n`, and `s` a subset of this space, then
`longestPrefix x s` if the largest `n` for which there is an element of `s` having the same
prefix of length `n` as `x`. If there is no such `n`, use `0` by convention. -/
def longestPrefix {E : ℕ → Type*} (x : ∀ n, E n) (s : Set (∀ n, E n)) : ℕ :=
  shortestPrefixDiff x s - 1
#align pi_nat.longest_prefix PiNat.longestPrefix

theorem firstDiff_le_longestPrefix {s : Set (∀ n, E n)} (hs : IsClosed s) {x y : ∀ n, E n}
    (hx : x ∉ s) (hy : y ∈ s) : firstDiff x y ≤ longestPrefix x s := by
  rw [longestPrefix, le_tsub_iff_right]
  · exact firstDiff_lt_shortestPrefixDiff hs hx hy
  · exact shortestPrefixDiff_pos hs ⟨y, hy⟩ hx
#align pi_nat.first_diff_le_longest_prefix PiNat.firstDiff_le_longestPrefix

theorem inter_cylinder_longestPrefix_nonempty {s : Set (∀ n, E n)} (hs : IsClosed s)
    (hne : s.Nonempty) (x : ∀ n, E n) : (s ∩ cylinder x (longestPrefix x s)).Nonempty := by
  by_cases hx : x ∈ s
  · exact ⟨x, hx, self_mem_cylinder _ _⟩
  have A := exists_disjoint_cylinder hs hx
  have B : longestPrefix x s < shortestPrefixDiff x s :=
    Nat.pred_lt (shortestPrefixDiff_pos hs hne hx).ne'
  rw [longestPrefix, shortestPrefixDiff, dif_pos A] at B ⊢
  obtain ⟨y, ys, hy⟩ : ∃ y : ∀ n : ℕ, E n, y ∈ s ∧ x ∈ cylinder y (Nat.find A - 1) := by
    simpa only [not_disjoint_iff, mem_cylinder_comm] using Nat.find_min A B
  refine ⟨y, ys, ?_⟩
  rw [mem_cylinder_iff_eq] at hy ⊢
  rw [hy]
#align pi_nat.inter_cylinder_longest_prefix_nonempty PiNat.inter_cylinder_longestPrefix_nonempty

theorem disjoint_cylinder_of_longestPrefix_lt {s : Set (∀ n, E n)} (hs : IsClosed s) {x : ∀ n, E n}
    (hx : x ∉ s) {n : ℕ} (hn : longestPrefix x s < n) : Disjoint s (cylinder x n) := by
  contrapose! hn
  rcases not_disjoint_iff_nonempty_inter.1 hn with ⟨y, ys, hy⟩
  apply le_trans _ (firstDiff_le_longestPrefix hs hx ys)
  apply (mem_cylinder_iff_le_firstDiff (ne_of_mem_of_not_mem ys hx).symm _).1
  rwa [mem_cylinder_comm]
#align pi_nat.disjoint_cylinder_of_longest_prefix_lt PiNat.disjoint_cylinder_of_longestPrefix_lt

/-- If two points `x, y` coincide up to length `n`, and the longest common prefix of `x` with `s`
is strictly shorter than `n`, then the longest common prefix of `y` with `s` is the same, and both
cylinders of this length based at `x` and `y` coincide. -/
theorem cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff {x y : ∀ n, E n}
    {s : Set (∀ n, E n)} (hs : IsClosed s) (hne : s.Nonempty)
    (H : longestPrefix x s < firstDiff x y) (xs : x ∉ s) (ys : y ∉ s) :
    cylinder x (longestPrefix x s) = cylinder y (longestPrefix y s) := by
  have l_eq : longestPrefix y s = longestPrefix x s := by
    rcases lt_trichotomy (longestPrefix y s) (longestPrefix x s) with (L | L | L)
    · have Ax : (s ∩ cylinder x (longestPrefix x s)).Nonempty :=
        inter_cylinder_longestPrefix_nonempty hs hne x
      have Z := disjoint_cylinder_of_longestPrefix_lt hs ys L
      rw [firstDiff_comm] at H
      rw [cylinder_eq_cylinder_of_le_firstDiff _ _ H.le] at Z
      exact (Ax.not_disjoint Z).elim
    · exact L
    · have Ay : (s ∩ cylinder y (longestPrefix y s)).Nonempty :=
        inter_cylinder_longestPrefix_nonempty hs hne y
      have A'y : (s ∩ cylinder y (longestPrefix x s).succ).Nonempty :=
        Ay.mono (inter_subset_inter_right s (cylinder_anti _ L))
      have Z := disjoint_cylinder_of_longestPrefix_lt hs xs (Nat.lt_succ_self _)
      rw [cylinder_eq_cylinder_of_le_firstDiff _ _ H] at Z
      exact (A'y.not_disjoint Z).elim
  rw [l_eq, ← mem_cylinder_iff_eq]
  exact cylinder_anti y H.le (mem_cylinder_firstDiff x y)
#align pi_nat.cylinder_longest_prefix_eq_of_longest_prefix_lt_first_diff PiNat.cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff

/-- Given a closed nonempty subset `s` of `Π (n : ℕ), E n`, there exists a Lipschitz retraction
onto this set, i.e., a Lipschitz map with range equal to `s`, equal to the identity on `s`. -/
theorem exists_lipschitz_retraction_of_isClosed {s : Set (∀ n, E n)} (hs : IsClosed s)
    (hne : s.Nonempty) :
    ∃ f : (∀ n, E n) → ∀ n, E n, (∀ x ∈ s, f x = x) ∧ range f = s ∧ LipschitzWith 1 f := by
  /- The map `f` is defined as follows. For `x ∈ s`, let `f x = x`. Otherwise, consider the longest
    prefix `w` that `x` shares with an element of `s`, and let `f x = z_w` where `z_w` is an element
    of `s` starting with `w`. All the desired properties are clear, except the fact that `f` is
    `1`-Lipschitz: if two points `x, y` belong to a common cylinder of length `n`, one should show
    that their images also belong to a common cylinder of length `n`. This is a case analysis:
    * if both `x, y ∈ s`, then this is clear.
    * if `x ∈ s` but `y ∉ s`, then the longest prefix `w` of `y` shared by an element of `s` is of
    length at least `n` (because of `x`), and then `f y` starts with `w` and therefore stays in the
    same length `n` cylinder.
    * if `x ∉ s`, `y ∉ s`, let `w` be the longest prefix of `x` shared by an element of `s`. If its
    length is `< n`, then it is also the longest prefix of `y`, and we get `f x = f y = z_w`.
    Otherwise, `f x` remains in the same `n`-cylinder as `x`. Similarly for `y`. Finally, `f x` and
    `f y` are again in the same `n`-cylinder, as desired. -/
  set f := fun x => if x ∈ s then x else (inter_cylinder_longestPrefix_nonempty hs hne x).some
  have fs : ∀ x ∈ s, f x = x := fun x xs => by simp [f, xs]
  refine ⟨f, fs, ?_, ?_⟩
  -- check that the range of `f` is `s`.
  · apply Subset.antisymm
    · rintro x ⟨y, rfl⟩
      by_cases hy : y ∈ s
      · rwa [fs y hy]
      simpa [f, if_neg hy] using (inter_cylinder_longestPrefix_nonempty hs hne y).choose_spec.1
    · intro x hx
      rw [← fs x hx]
      exact mem_range_self _
  -- check that `f` is `1`-Lipschitz, by a case analysis.
  · refine LipschitzWith.mk_one fun x y => ?_
    -- exclude the trivial cases where `x = y`, or `f x = f y`.
    rcases eq_or_ne x y with (rfl | hxy)
    · simp
    rcases eq_or_ne (f x) (f y) with (h' | hfxfy)
    · simp [h', dist_nonneg]
    have I2 : cylinder x (firstDiff x y) = cylinder y (firstDiff x y) := by
      rw [← mem_cylinder_iff_eq]
      apply mem_cylinder_firstDiff
    suffices firstDiff x y ≤ firstDiff (f x) (f y) by
      simpa [dist_eq_of_ne hxy, dist_eq_of_ne hfxfy]
    -- case where `x ∈ s`
    by_cases xs : x ∈ s
    · rw [fs x xs] at hfxfy ⊢
      -- case where `y ∈ s`, trivial
      by_cases ys : y ∈ s
      · rw [fs y ys]
      -- case where `y ∉ s`
      have A : (s ∩ cylinder y (longestPrefix y s)).Nonempty :=
        inter_cylinder_longestPrefix_nonempty hs hne y
      have fy : f y = A.some := by simp_rw [f, if_neg ys]
      have I : cylinder A.some (firstDiff x y) = cylinder y (firstDiff x y) := by
        rw [← mem_cylinder_iff_eq, firstDiff_comm]
        apply cylinder_anti y _ A.some_mem.2
        exact firstDiff_le_longestPrefix hs ys xs
      rwa [← fy, ← I2, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_firstDiff hfxfy.symm,
        firstDiff_comm _ x] at I
    -- case where `x ∉ s`
    · by_cases ys : y ∈ s
      -- case where `y ∈ s` (similar to the above)
      · have A : (s ∩ cylinder x (longestPrefix x s)).Nonempty :=
          inter_cylinder_longestPrefix_nonempty hs hne x
        have fx : f x = A.some := by simp_rw [f, if_neg xs]
        have I : cylinder A.some (firstDiff x y) = cylinder x (firstDiff x y) := by
          rw [← mem_cylinder_iff_eq]
          apply cylinder_anti x _ A.some_mem.2
          apply firstDiff_le_longestPrefix hs xs ys
        rw [fs y ys] at hfxfy ⊢
        rwa [← fx, I2, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_firstDiff hfxfy] at I
      -- case where `y ∉ s`
      · have Ax : (s ∩ cylinder x (longestPrefix x s)).Nonempty :=
          inter_cylinder_longestPrefix_nonempty hs hne x
        have fx : f x = Ax.some := by simp_rw [f, if_neg xs]
        have Ay : (s ∩ cylinder y (longestPrefix y s)).Nonempty :=
          inter_cylinder_longestPrefix_nonempty hs hne y
        have fy : f y = Ay.some := by simp_rw [f, if_neg ys]
        -- case where the common prefix to `x` and `s`, or `y` and `s`, is shorter than the
        -- common part to `x` and `y` -- then `f x = f y`.
        by_cases H : longestPrefix x s < firstDiff x y ∨ longestPrefix y s < firstDiff x y
        · have : cylinder x (longestPrefix x s) = cylinder y (longestPrefix y s) := by
            cases' H with H H
            · exact cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff hs hne H xs ys
            · symm
              rw [firstDiff_comm] at H
              exact cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff hs hne H ys xs
          rw [fx, fy] at hfxfy
          apply (hfxfy _).elim
          congr
        -- case where the common prefix to `x` and `s` is long, as well as the common prefix to
        -- `y` and `s`. Then all points remain in the same cylinders.
        · push_neg at H
          have I1 : cylinder Ax.some (firstDiff x y) = cylinder x (firstDiff x y) := by
            rw [← mem_cylinder_iff_eq]
            exact cylinder_anti x H.1 Ax.some_mem.2
          have I3 : cylinder y (firstDiff x y) = cylinder Ay.some (firstDiff x y) := by
            rw [eq_comm, ← mem_cylinder_iff_eq]
            exact cylinder_anti y H.2 Ay.some_mem.2
          have : cylinder Ax.some (firstDiff x y) = cylinder Ay.some (firstDiff x y) := by
            rw [I1, I2, I3]
          rw [← fx, ← fy, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_firstDiff hfxfy] at this
          exact this
#align pi_nat.exists_lipschitz_retraction_of_is_closed PiNat.exists_lipschitz_retraction_of_isClosed

/-- Given a closed nonempty subset `s` of `Π (n : ℕ), E n`, there exists a retraction onto this
set, i.e., a continuous map with range equal to `s`, equal to the identity on `s`. -/
theorem exists_retraction_of_isClosed {s : Set (∀ n, E n)} (hs : IsClosed s) (hne : s.Nonempty) :
    ∃ f : (∀ n, E n) → ∀ n, E n, (∀ x ∈ s, f x = x) ∧ range f = s ∧ Continuous f := by
  rcases exists_lipschitz_retraction_of_isClosed hs hne with ⟨f, fs, frange, hf⟩
  exact ⟨f, fs, frange, hf.continuous⟩
#align pi_nat.exists_retraction_of_is_closed PiNat.exists_retraction_of_isClosed

theorem exists_retraction_subtype_of_isClosed {s : Set (∀ n, E n)} (hs : IsClosed s)
    (hne : s.Nonempty) :
    ∃ f : (∀ n, E n) → s, (∀ x : s, f x = x) ∧ Surjective f ∧ Continuous f := by
  obtain ⟨f, fs, rfl, f_cont⟩ :
    ∃ f : (∀ n, E n) → ∀ n, E n, (∀ x ∈ s, f x = x) ∧ range f = s ∧ Continuous f :=
    exists_retraction_of_isClosed hs hne
  have A : ∀ x : range f, rangeFactorization f x = x := fun x ↦ Subtype.eq <| fs x x.2
  exact ⟨rangeFactorization f, A, fun x => ⟨x, A x⟩, f_cont.subtype_mk _⟩
#align pi_nat.exists_retraction_subtype_of_is_closed PiNat.exists_retraction_subtype_of_isClosed

end PiNat

open PiNat

/-- Any nonempty complete second countable metric space is the continuous image of the
fundamental space `ℕ → ℕ`. For a version of this theorem in the context of Polish spaces, see
`exists_nat_nat_continuous_surjective_of_polishSpace`. -/
theorem exists_nat_nat_continuous_surjective_of_completeSpace (α : Type*) [MetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] [Nonempty α] :
    ∃ f : (ℕ → ℕ) → α, Continuous f ∧ Surjective f := by
  /- First, we define a surjective map from a closed subset `s` of `ℕ → ℕ`. Then, we compose
    this map with a retraction of `ℕ → ℕ` onto `s` to obtain the desired map.
    Let us consider a dense sequence `u` in `α`. Then `s` is the set of sequences `xₙ` such that the
    balls `closedBall (u xₙ) (1/2^n)` have a nonempty intersection. This set is closed,
    and we define `f x` there to be the unique point in the intersection.
    This function is continuous and surjective by design. -/
  letI : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  have I0 : (0 : ℝ) < 1 / 2 := by norm_num
  have I1 : (1 / 2 : ℝ) < 1 := by norm_num
  rcases exists_dense_seq α with ⟨u, hu⟩
  let s : Set (ℕ → ℕ) := { x | (⋂ n : ℕ, closedBall (u (x n)) ((1 / 2) ^ n)).Nonempty }
  let g : s → α := fun x => x.2.some
  have A : ∀ (x : s) (n : ℕ), dist (g x) (u ((x : ℕ → ℕ) n)) ≤ (1 / 2) ^ n := fun x n =>
    (mem_iInter.1 x.2.some_mem n : _)
  have g_cont : Continuous g := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    refine continuousAt_of_locally_lipschitz zero_lt_one 4 fun x hxy => ?_
    rcases eq_or_ne x y with (rfl | hne)
    · simp
    have hne' : x.1 ≠ y.1 := Subtype.coe_injective.ne hne
    have dist' : dist x y = dist x.1 y.1 := rfl
    let n := firstDiff x.1 y.1 - 1
    have diff_pos : 0 < firstDiff x.1 y.1 := by
      by_contra! h
      apply apply_firstDiff_ne hne'
      rw [Nat.le_zero.1 h]
      apply apply_eq_of_dist_lt _ le_rfl
      rw [pow_zero]
      exact hxy
    have hn : firstDiff x.1 y.1 = n + 1 := (Nat.succ_pred_eq_of_pos diff_pos).symm
    rw [dist', dist_eq_of_ne hne', hn]
    have B : x.1 n = y.1 n := mem_cylinder_firstDiff x.1 y.1 n (Nat.pred_lt diff_pos.ne')
    calc
      dist (g x) (g y) ≤ dist (g x) (u (x.1 n)) + dist (g y) (u (x.1 n)) :=
        dist_triangle_right _ _ _
      _ = dist (g x) (u (x.1 n)) + dist (g y) (u (y.1 n)) := by rw [← B]
      _ ≤ (1 / 2) ^ n + (1 / 2) ^ n := add_le_add (A x n) (A y n)
      _ = 4 * (1 / 2) ^ (n + 1) := by ring
  have g_surj : Surjective g := fun y ↦ by
    have : ∀ n : ℕ, ∃ j, y ∈ closedBall (u j) ((1 / 2) ^ n) := fun n ↦ by
      rcases hu.exists_dist_lt y (by simp : (0 : ℝ) < (1 / 2) ^ n) with ⟨j, hj⟩
      exact ⟨j, hj.le⟩
    choose x hx using this
    have I : (⋂ n : ℕ, closedBall (u (x n)) ((1 / 2) ^ n)).Nonempty := ⟨y, mem_iInter.2 hx⟩
    refine ⟨⟨x, I⟩, ?_⟩
    refine dist_le_zero.1 ?_
    have J : ∀ n : ℕ, dist (g ⟨x, I⟩) y ≤ (1 / 2) ^ n + (1 / 2) ^ n := fun n =>
      calc
        dist (g ⟨x, I⟩) y ≤ dist (g ⟨x, I⟩) (u (x n)) + dist y (u (x n)) :=
          dist_triangle_right _ _ _
        _ ≤ (1 / 2) ^ n + (1 / 2) ^ n := add_le_add (A ⟨x, I⟩ n) (hx n)
    have L : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n + (1 / 2) ^ n) atTop (𝓝 (0 + 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one I0.le I1).add
        (tendsto_pow_atTop_nhds_zero_of_lt_one I0.le I1)
    rw [add_zero] at L
    exact ge_of_tendsto' L J
  have s_closed : IsClosed s := by
    refine isClosed_iff_clusterPt.mpr fun x hx ↦ ?_
    have L : Tendsto (fun n : ℕ => diam (closedBall (u (x n)) ((1 / 2) ^ n))) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => (2 : ℝ) * (1 / 2) ^ n) atTop (𝓝 (2 * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one I0.le I1).const_mul _
      rw [mul_zero] at this
      exact
        squeeze_zero (fun n => diam_nonneg) (fun n => diam_closedBall (pow_nonneg I0.le _)) this
    refine nonempty_iInter_of_nonempty_biInter (fun n => isClosed_ball)
      (fun n => isBounded_closedBall) (fun N ↦ ?_) L
    obtain ⟨y, hxy, ys⟩ : ∃ y, y ∈ ball x ((1 / 2) ^ N) ∩ s :=
      clusterPt_principal_iff.1 hx _ (ball_mem_nhds x (pow_pos I0 N))
    have E :
      ⋂ (n : ℕ) (H : n ≤ N), closedBall (u (x n)) ((1 / 2) ^ n) =
        ⋂ (n : ℕ) (H : n ≤ N), closedBall (u (y n)) ((1 / 2) ^ n) := by
      refine iInter_congr fun n ↦ iInter_congr fun hn ↦ ?_
      have : x n = y n := apply_eq_of_dist_lt (mem_ball'.1 hxy) hn
      rw [this]
    rw [E]
    apply Nonempty.mono _ ys
    apply iInter_subset_iInter₂
  obtain ⟨f, -, f_surj, f_cont⟩ :
    ∃ f : (ℕ → ℕ) → s, (∀ x : s, f x = x) ∧ Surjective f ∧ Continuous f := by
    apply exists_retraction_subtype_of_isClosed s_closed
    simpa only [nonempty_coe_sort] using g_surj.nonempty
  exact ⟨g ∘ f, g_cont.comp f_cont, g_surj.comp f_surj⟩
#align exists_nat_nat_continuous_surjective_of_complete_space exists_nat_nat_continuous_surjective_of_completeSpace

namespace PiCountable

/-!
### Products of (possibly non-discrete) metric spaces
-/


variable {ι : Type*} [Encodable ι] {F : ι → Type*} [∀ i, MetricSpace (F i)]

open Encodable

/-- Given a countable family of metric spaces, one may put a distance on their product `Π i, E i`.
It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `dist x y = ∑' i, min (1/2)^(encode i) (dist (x i) (y i))`. -/
protected def dist : Dist (∀ i, F i) :=
  ⟨fun x y => ∑' i : ι, min ((1 / 2) ^ encode i) (dist (x i) (y i))⟩
#align pi_countable.has_dist PiCountable.dist

attribute [local instance] PiCountable.dist

theorem dist_eq_tsum (x y : ∀ i, F i) :
    dist x y = ∑' i : ι, min ((1 / 2) ^ encode i : ℝ) (dist (x i) (y i)) :=
  rfl
#align pi_countable.dist_eq_tsum PiCountable.dist_eq_tsum

theorem dist_summable (x y : ∀ i, F i) :
    Summable fun i : ι => min ((1 / 2) ^ encode i : ℝ) (dist (x i) (y i)) := by
  refine .of_nonneg_of_le (fun i => ?_) (fun i => min_le_left _ _)
    summable_geometric_two_encode
  exact le_min (pow_nonneg (by norm_num) _) dist_nonneg
#align pi_countable.dist_summable PiCountable.dist_summable

theorem min_dist_le_dist_pi (x y : ∀ i, F i) (i : ι) :
    min ((1 / 2) ^ encode i : ℝ) (dist (x i) (y i)) ≤ dist x y :=
  le_tsum (dist_summable x y) i fun j _ => le_min (by simp) dist_nonneg
#align pi_countable.min_dist_le_dist_pi PiCountable.min_dist_le_dist_pi

theorem dist_le_dist_pi_of_dist_lt {x y : ∀ i, F i} {i : ι} (h : dist x y < (1 / 2) ^ encode i) :
    dist (x i) (y i) ≤ dist x y := by
  simpa only [not_le.2 h, false_or_iff] using min_le_iff.1 (min_dist_le_dist_pi x y i)
#align pi_countable.dist_le_dist_pi_of_dist_lt PiCountable.dist_le_dist_pi_of_dist_lt

open Topology Filter NNReal

variable (E)

/-- Given a countable family of metric spaces, one may put a distance on their product `Π i, E i`,
defining the right topology and uniform structure. It is highly non-canonical, though, and therefore
not registered as a global instance.
The distance we use here is `dist x y = ∑' n, min (1/2)^(encode i) (dist (x n) (y n))`. -/
protected def metricSpace : MetricSpace (∀ i, F i) where
  dist_self x := by simp [dist_eq_tsum]
  dist_comm x y := by simp [dist_eq_tsum, dist_comm]
  dist_triangle x y z :=
    have I : ∀ i, min ((1 / 2) ^ encode i : ℝ) (dist (x i) (z i)) ≤
        min ((1 / 2) ^ encode i : ℝ) (dist (x i) (y i)) +
          min ((1 / 2) ^ encode i : ℝ) (dist (y i) (z i)) := fun i =>
      calc
        min ((1 / 2) ^ encode i : ℝ) (dist (x i) (z i)) ≤
            min ((1 / 2) ^ encode i : ℝ) (dist (x i) (y i) + dist (y i) (z i)) :=
          min_le_min le_rfl (dist_triangle _ _ _)
        _ = min ((1 / 2) ^ encode i : ℝ) (min ((1 / 2) ^ encode i : ℝ) (dist (x i) (y i)) +
              min ((1 / 2) ^ encode i : ℝ) (dist (y i) (z i))) := by
          convert congr_arg ((↑) : ℝ≥0 → ℝ)
            (min_add_distrib ((1 / 2 : ℝ≥0) ^ encode i) (nndist (x i) (y i))
              (nndist (y i) (z i)))
        _ ≤ min ((1 / 2) ^ encode i : ℝ) (dist (x i) (y i)) +
              min ((1 / 2) ^ encode i : ℝ) (dist (y i) (z i)) :=
          min_le_right _ _
    calc dist x z ≤ ∑' i, (min ((1 / 2) ^ encode i : ℝ) (dist (x i) (y i)) +
          min ((1 / 2) ^ encode i : ℝ) (dist (y i) (z i))) :=
        tsum_le_tsum I (dist_summable x z) ((dist_summable x y).add (dist_summable y z))
      _ = dist x y + dist y z := tsum_add (dist_summable x y) (dist_summable y z)
  edist_dist _ _ := by exact ENNReal.coe_nnreal_eq _
  eq_of_dist_eq_zero hxy := by
    ext1 n
    rw [← dist_le_zero, ← hxy]
    apply dist_le_dist_pi_of_dist_lt
    rw [hxy]
    simp
  toUniformSpace := Pi.uniformSpace _
  uniformity_dist := by
    simp only [Pi.uniformity, comap_iInf, gt_iff_lt, preimage_setOf_eq, comap_principal,
      PseudoMetricSpace.uniformity_dist]
    apply le_antisymm
    · simp only [le_iInf_iff, le_principal_iff]
      intro ε εpos
      obtain ⟨K, hK⟩ :
        ∃ K : Finset ι, (∑' i : { j // j ∉ K }, (1 / 2 : ℝ) ^ encode (i : ι)) < ε / 2 :=
        ((tendsto_order.1 (tendsto_tsum_compl_atTop_zero fun i : ι => (1 / 2 : ℝ) ^ encode i)).2 _
            (half_pos εpos)).exists
      obtain ⟨δ, δpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ (K.card : ℝ) * δ < ε / 2 :=
        exists_pos_mul_lt (half_pos εpos) _
      apply @mem_iInf_of_iInter _ _ _ _ _ K.finite_toSet fun i =>
          { p : (∀ i : ι, F i) × ∀ i : ι, F i | dist (p.fst i) (p.snd i) < δ }
      · rintro ⟨i, hi⟩
        refine mem_iInf_of_mem δ (mem_iInf_of_mem δpos ?_)
        simp only [Prod.forall, imp_self, mem_principal, Subset.rfl]
      · rintro ⟨x, y⟩ hxy
        simp only [mem_iInter, mem_setOf_eq, SetCoe.forall, Finset.mem_range, Finset.mem_coe] at hxy
        calc
          dist x y = ∑' i : ι, min ((1 / 2) ^ encode i : ℝ) (dist (x i) (y i)) := rfl
          _ = (∑ i ∈ K, min ((1 / 2) ^ encode i : ℝ) (dist (x i) (y i))) +
                ∑' i : ↑(K : Set ι)ᶜ, min ((1 / 2) ^ encode (i : ι) : ℝ) (dist (x i) (y i)) :=
            (sum_add_tsum_compl (dist_summable _ _)).symm
          _ ≤ (∑ i ∈ K, dist (x i) (y i)) +
                ∑' i : ↑(K : Set ι)ᶜ, ((1 / 2) ^ encode (i : ι) : ℝ) := by
            refine add_le_add (Finset.sum_le_sum fun i _ => min_le_right _ _) ?_
            refine tsum_le_tsum (fun i => min_le_left _ _) ?_ ?_
            · apply Summable.subtype (dist_summable x y) (↑K : Set ι)ᶜ
            · apply Summable.subtype summable_geometric_two_encode (↑K : Set ι)ᶜ
          _ < (∑ _i ∈ K, δ) + ε / 2 := by
            apply add_lt_add_of_le_of_lt _ hK
            refine Finset.sum_le_sum fun i hi => (hxy i ?_).le
            simpa using hi
          _ ≤ ε / 2 + ε / 2 :=
            (add_le_add_right (by simpa only [Finset.sum_const, nsmul_eq_mul] using hδ.le) _)
          _ = ε := add_halves _
    · simp only [le_iInf_iff, le_principal_iff]
      intro i ε εpos
      refine mem_iInf_of_mem (min ((1 / 2) ^ encode i : ℝ) ε) ?_
      have : 0 < min ((1 / 2) ^ encode i : ℝ) ε := lt_min (by simp) εpos
      refine mem_iInf_of_mem this ?_
      simp only [and_imp, Prod.forall, setOf_subset_setOf, lt_min_iff, mem_principal]
      intro x y hn hε
      calc
        dist (x i) (y i) ≤ dist x y := dist_le_dist_pi_of_dist_lt hn
        _ < ε := hε
#align pi_countable.metric_space PiCountable.metricSpace

end PiCountable
