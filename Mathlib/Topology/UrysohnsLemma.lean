/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.NormedSpace.AddTorsor
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.GDelta
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.ContinuousFunction.Bounded

#align_import topology.urysohns_lemma from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Urysohn's lemma

In this file we prove Urysohn's lemma `exists_continuous_zero_one_of_isClosed`: for any two disjoint
closed sets `s` and `t` in a normal topological space `X` there exists a continuous function
`f : X → ℝ` such that

* `f` equals zero on `s`;
* `f` equals one on `t`;
* `0 ≤ f x ≤ 1` for all `x`.

We also give versions in a regular locally compact space where one assumes that `s` is compact
and `t` is closed, in `exists_continuous_zero_one_of_isCompact`
and `exists_continuous_one_zero_of_isCompact` (the latter providing additionally a function with
compact support).

We write a generic proof so that it applies both to normal spaces and to regular locally
compact spaces.

## Implementation notes

Most paper sources prove Urysohn's lemma using a family of open sets indexed by dyadic rational
numbers on `[0, 1]`. There are many technical difficulties with formalizing this proof (e.g., one
needs to formalize the "dyadic induction", then prove that the resulting family of open sets is
monotone). So, we formalize a slightly different proof.

Let `Urysohns.CU` be the type of pairs `(C, U)` of a closed set `C` and an open set `U` such that
`C ⊆ U`. Since `X` is a normal topological space, for each `c : CU` there exists an open set `u`
such that `c.C ⊆ u ∧ closure u ⊆ c.U`. We define `c.left` and `c.right` to be `(c.C, u)` and
`(closure u, c.U)`, respectively. Then we define a family of functions
`Urysohns.CU.approx (c : Urysohns.CU) (n : ℕ) : X → ℝ` by recursion on `n`:

* `c.approx 0` is the indicator of `c.Uᶜ`;
* `c.approx (n + 1) x = (c.left.approx n x + c.right.approx n x) / 2`.

For each `x` this is a monotone family of functions that are equal to zero on `c.C` and are equal to
one outside of `c.U`. We also have `c.approx n x ∈ [0, 1]` for all `c`, `n`, and `x`.

Let `Urysohns.CU.lim c` be the supremum (or equivalently, the limit) of `c.approx n`. Then
properties of `Urysohns.CU.approx` immediately imply that

* `c.lim x ∈ [0, 1]` for all `x`;
* `c.lim` equals zero on `c.C` and equals one outside of `c.U`;
* `c.lim x = (c.left.lim x + c.right.lim x) / 2`.

In order to prove that `c.lim` is continuous at `x`, we prove by induction on `n : ℕ` that for `y`
in a small neighborhood of `x` we have `|c.lim y - c.lim x| ≤ (3 / 4) ^ n`. Induction base follows
from `c.lim x ∈ [0, 1]`, `c.lim y ∈ [0, 1]`. For the induction step, consider two cases:

* `x ∈ c.left.U`; then for `y` in a small neighborhood of `x` we have `y ∈ c.left.U ⊆ c.right.C`
  (hence `c.right.lim x = c.right.lim y = 0`) and `|c.left.lim y - c.left.lim x| ≤ (3 / 4) ^ n`.
  Then
  `|c.lim y - c.lim x| = |c.left.lim y - c.left.lim x| / 2 ≤ (3 / 4) ^ n / 2 < (3 / 4) ^ (n + 1)`.
* otherwise, `x ∉ c.left.right.C`; then for `y` in a small neighborhood of `x` we have
  `y ∉ c.left.right.C ⊇ c.left.left.U` (hence `c.left.left.lim x = c.left.left.lim y = 1`),
  `|c.left.right.lim y - c.left.right.lim x| ≤ (3 / 4) ^ n`, and
  `|c.right.lim y - c.right.lim x| ≤ (3 / 4) ^ n`. Combining these inequalities, the triangle
  inequality, and the recurrence formula for `c.lim`, we get
  `|c.lim x - c.lim y| ≤ (3 / 4) ^ (n + 1)`.

The actual formalization uses `midpoint ℝ x y` instead of `(x + y) / 2` because we have more API
lemmas about `midpoint`.

## Tags

Urysohn's lemma, normal topological space, locally compact topological space
-/


variable {X : Type*} [TopologicalSpace X]

open Set Filter TopologicalSpace Topology Filter
open scoped Pointwise

namespace Urysohns

set_option linter.uppercaseLean3 false

/-- An auxiliary type for the proof of Urysohn's lemma: a pair of a closed set `C` and its
open neighborhood `U`, together with the assumption that `C` satisfies the property `P C`. The
latter assumption will make it possible to prove simultaneously both versions of Urysohn's lemma,
in normal spaces (with `P` always true) and in locally compact spaces (with `P = IsCompact`).
We put also in the structure the assumption that, for any such pair, one may find an intermediate
pair inbetween satisfying `P`, to avoid carrying it around in the argument. -/
structure CU {X : Type*} [TopologicalSpace X] (P : Set X → Prop) where
  /-- The inner set in the inductive construction towards Urysohn's lemma -/
  protected C : Set X
  /-- The outer set in the inductive construction towards Urysohn's lemma -/
  protected U : Set X
  protected P_C : P C
  protected closed_C : IsClosed C
  protected open_U : IsOpen U
  protected subset : C ⊆ U
  protected hP : ∀ {c u : Set X}, IsClosed c → P c → IsOpen u → c ⊆ u →
    ∃ v, IsOpen v ∧ c ⊆ v ∧ closure v ⊆ u ∧ P (closure v)
#align urysohns.CU Urysohns.CU

namespace CU

variable {P : Set X → Prop}

/-- By assumption, for each `c : CU P` there exists an open set `u`
such that `c.C ⊆ u` and `closure u ⊆ c.U`. `c.left` is the pair `(c.C, u)`. -/
@[simps C]
def left (c : CU P) : CU P where
  C := c.C
  U := (c.hP c.closed_C c.P_C c.open_U c.subset).choose
  closed_C := c.closed_C
  P_C := c.P_C
  open_U := (c.hP c.closed_C c.P_C c.open_U c.subset).choose_spec.1
  subset := (c.hP c.closed_C c.P_C c.open_U c.subset).choose_spec.2.1
  hP := c.hP
#align urysohns.CU.left Urysohns.CU.left

/-- By assumption, for each `c : CU P` there exists an open set `u`
such that `c.C ⊆ u` and `closure u ⊆ c.U`. `c.right` is the pair `(closure u, c.U)`. -/
@[simps U]
def right (c : CU P) : CU P where
  C := closure (c.hP c.closed_C c.P_C c.open_U c.subset).choose
  U := c.U
  closed_C := isClosed_closure
  P_C := (c.hP c.closed_C c.P_C c.open_U c.subset).choose_spec.2.2.2
  open_U := c.open_U
  subset := (c.hP c.closed_C c.P_C c.open_U c.subset).choose_spec.2.2.1
  hP := c.hP
#align urysohns.CU.right Urysohns.CU.right

theorem left_U_subset_right_C (c : CU P) : c.left.U ⊆ c.right.C :=
  subset_closure
#align urysohns.CU.left_U_subset_right_C Urysohns.CU.left_U_subset_right_C

theorem left_U_subset (c : CU P) : c.left.U ⊆ c.U :=
  Subset.trans c.left_U_subset_right_C c.right.subset
#align urysohns.CU.left_U_subset Urysohns.CU.left_U_subset

theorem subset_right_C (c : CU P) : c.C ⊆ c.right.C :=
  Subset.trans c.left.subset c.left_U_subset_right_C
#align urysohns.CU.subset_right_C Urysohns.CU.subset_right_C

/-- `n`-th approximation to a continuous function `f : X → ℝ` such that `f = 0` on `c.C` and `f = 1`
outside of `c.U`. -/
noncomputable def approx : ℕ → CU P → X → ℝ
  | 0, c, x => indicator c.Uᶜ 1 x
  | n + 1, c, x => midpoint ℝ (approx n c.left x) (approx n c.right x)
#align urysohns.CU.approx Urysohns.CU.approx

theorem approx_of_mem_C (c : CU P) (n : ℕ) {x : X} (hx : x ∈ c.C) : c.approx n x = 0 := by
  induction' n with n ihn generalizing c
  · exact indicator_of_not_mem (fun (hU : x ∈ c.Uᶜ) => hU <| c.subset hx) _
  · simp only [approx]
    rw [ihn, ihn, midpoint_self]
    exacts [c.subset_right_C hx, hx]
#align urysohns.CU.approx_of_mem_C Urysohns.CU.approx_of_mem_C

theorem approx_of_nmem_U (c : CU P) (n : ℕ) {x : X} (hx : x ∉ c.U) : c.approx n x = 1 := by
  induction' n with n ihn generalizing c
  · rw [← mem_compl_iff] at hx
    exact indicator_of_mem hx _
  · simp only [approx]
    rw [ihn, ihn, midpoint_self]
    exacts [hx, fun hU => hx <| c.left_U_subset hU]
#align urysohns.CU.approx_of_nmem_U Urysohns.CU.approx_of_nmem_U

theorem approx_nonneg (c : CU P) (n : ℕ) (x : X) : 0 ≤ c.approx n x := by
  induction' n with n ihn generalizing c
  · exact indicator_nonneg (fun _ _ => zero_le_one) _
  · simp only [approx, midpoint_eq_smul_add, invOf_eq_inv]
    refine' mul_nonneg (inv_nonneg.2 zero_le_two) (add_nonneg _ _) <;> apply ihn
#align urysohns.CU.approx_nonneg Urysohns.CU.approx_nonneg

theorem approx_le_one (c : CU P) (n : ℕ) (x : X) : c.approx n x ≤ 1 := by
  induction' n with n ihn generalizing c
  · exact indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
  · simp only [approx, midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul, ← div_eq_inv_mul]
    have := add_le_add (ihn (left c)) (ihn (right c))
    set_option tactic.skipAssignedInstances false in
    norm_num at this
    exact Iff.mpr (div_le_one zero_lt_two) this
#align urysohns.CU.approx_le_one Urysohns.CU.approx_le_one

theorem bddAbove_range_approx (c : CU P) (x : X) : BddAbove (range fun n => c.approx n x) :=
  ⟨1, fun _ ⟨n, hn⟩ => hn ▸ c.approx_le_one n x⟩
#align urysohns.CU.bdd_above_range_approx Urysohns.CU.bddAbove_range_approx

theorem approx_le_approx_of_U_sub_C {c₁ c₂ : CU P} (h : c₁.U ⊆ c₂.C) (n₁ n₂ : ℕ) (x : X) :
    c₂.approx n₂ x ≤ c₁.approx n₁ x := by
  by_cases hx : x ∈ c₁.U
  · calc
      approx n₂ c₂ x = 0 := approx_of_mem_C _ _ (h hx)
      _ ≤ approx n₁ c₁ x := approx_nonneg _ _ _
  · calc
      approx n₂ c₂ x ≤ 1 := approx_le_one _ _ _
      _ = approx n₁ c₁ x := (approx_of_nmem_U _ _ hx).symm
#align urysohns.CU.approx_le_approx_of_U_sub_C Urysohns.CU.approx_le_approx_of_U_sub_C

theorem approx_mem_Icc_right_left (c : CU P) (n : ℕ) (x : X) :
    c.approx n x ∈ Icc (c.right.approx n x) (c.left.approx n x) := by
  induction' n with n ihn generalizing c
  · exact ⟨le_rfl, indicator_le_indicator_of_subset (compl_subset_compl.2 c.left_U_subset)
      (fun _ => zero_le_one) _⟩
  · simp only [approx, mem_Icc]
    refine' ⟨midpoint_le_midpoint _ (ihn _).1, midpoint_le_midpoint (ihn _).2 _⟩ <;>
      apply approx_le_approx_of_U_sub_C
    exacts [subset_closure, subset_closure]
#align urysohns.CU.approx_mem_Icc_right_left Urysohns.CU.approx_mem_Icc_right_left

theorem approx_le_succ (c : CU P) (n : ℕ) (x : X) : c.approx n x ≤ c.approx (n + 1) x := by
  induction' n with n ihn generalizing c
  · simp only [approx, right_U, right_le_midpoint]
    exact (approx_mem_Icc_right_left c 0 x).2
  · rw [approx, approx]
    exact midpoint_le_midpoint (ihn _) (ihn _)
#align urysohns.CU.approx_le_succ Urysohns.CU.approx_le_succ

theorem approx_mono (c : CU P) (x : X) : Monotone fun n => c.approx n x :=
  monotone_nat_of_le_succ fun n => c.approx_le_succ n x
#align urysohns.CU.approx_mono Urysohns.CU.approx_mono

/-- A continuous function `f : X → ℝ` such that

* `0 ≤ f x ≤ 1` for all `x`;
* `f` equals zero on `c.C` and equals one outside of `c.U`;
-/
protected noncomputable def lim (c : CU P) (x : X) : ℝ :=
  ⨆ n, c.approx n x
#align urysohns.CU.lim Urysohns.CU.lim

theorem tendsto_approx_atTop (c : CU P) (x : X) :
    Tendsto (fun n => c.approx n x) atTop (𝓝 <| c.lim x) :=
  tendsto_atTop_ciSup (c.approx_mono x) ⟨1, fun _ ⟨_, hn⟩ => hn ▸ c.approx_le_one _ _⟩
#align urysohns.CU.tendsto_approx_at_top Urysohns.CU.tendsto_approx_atTop

theorem lim_of_mem_C (c : CU P) (x : X) (h : x ∈ c.C) : c.lim x = 0 := by
  simp only [CU.lim, approx_of_mem_C, h, ciSup_const]
#align urysohns.CU.lim_of_mem_C Urysohns.CU.lim_of_mem_C

theorem lim_of_nmem_U (c : CU P) (x : X) (h : x ∉ c.U) : c.lim x = 1 := by
  simp only [CU.lim, approx_of_nmem_U c _ h, ciSup_const]
#align urysohns.CU.lim_of_nmem_U Urysohns.CU.lim_of_nmem_U

theorem lim_eq_midpoint (c : CU P) (x : X) :
    c.lim x = midpoint ℝ (c.left.lim x) (c.right.lim x) := by
  refine' tendsto_nhds_unique (c.tendsto_approx_atTop x) ((tendsto_add_atTop_iff_nat 1).1 _)
  simp only [approx]
  exact (c.left.tendsto_approx_atTop x).midpoint (c.right.tendsto_approx_atTop x)
#align urysohns.CU.lim_eq_midpoint Urysohns.CU.lim_eq_midpoint

theorem approx_le_lim (c : CU P) (x : X) (n : ℕ) : c.approx n x ≤ c.lim x :=
  le_ciSup (c.bddAbove_range_approx x) _
#align urysohns.CU.approx_le_lim Urysohns.CU.approx_le_lim

theorem lim_nonneg (c : CU P) (x : X) : 0 ≤ c.lim x :=
  (c.approx_nonneg 0 x).trans (c.approx_le_lim x 0)
#align urysohns.CU.lim_nonneg Urysohns.CU.lim_nonneg

theorem lim_le_one (c : CU P) (x : X) : c.lim x ≤ 1 :=
  ciSup_le fun _ => c.approx_le_one _ _
#align urysohns.CU.lim_le_one Urysohns.CU.lim_le_one

theorem lim_mem_Icc (c : CU P) (x : X) : c.lim x ∈ Icc (0 : ℝ) 1 :=
  ⟨c.lim_nonneg x, c.lim_le_one x⟩
#align urysohns.CU.lim_mem_Icc Urysohns.CU.lim_mem_Icc

/-- Continuity of `Urysohns.CU.lim`. See module docstring for a sketch of the proofs. -/
theorem continuous_lim (c : CU P) : Continuous c.lim := by
  obtain ⟨h0, h1234, h1⟩ : 0 < (2⁻¹ : ℝ) ∧ (2⁻¹ : ℝ) < 3 / 4 ∧ (3 / 4 : ℝ) < 1 := by norm_num
  refine'
    continuous_iff_continuousAt.2 fun x =>
      (Metric.nhds_basis_closedBall_pow (h0.trans h1234) h1).tendsto_right_iff.2 fun n _ => _
  simp only [Metric.mem_closedBall]
  induction' n with n ihn generalizing c
  · filter_upwards with y
    rw [pow_zero]
    exact Real.dist_le_of_mem_Icc_01 (c.lim_mem_Icc _) (c.lim_mem_Icc _)
  · by_cases hxl : x ∈ c.left.U
    · filter_upwards [IsOpen.mem_nhds c.left.open_U hxl, ihn c.left] with _ hyl hyd
      rw [pow_succ', c.lim_eq_midpoint, c.lim_eq_midpoint,
        c.right.lim_of_mem_C _ (c.left_U_subset_right_C hyl),
        c.right.lim_of_mem_C _ (c.left_U_subset_right_C hxl)]
      refine' (dist_midpoint_midpoint_le _ _ _ _).trans _
      rw [dist_self, add_zero, div_eq_inv_mul]
      gcongr
    · replace hxl : x ∈ c.left.right.Cᶜ :=
        compl_subset_compl.2 c.left.right.subset hxl
      filter_upwards [IsOpen.mem_nhds (isOpen_compl_iff.2 c.left.right.closed_C) hxl,
        ihn c.left.right, ihn c.right] with y hyl hydl hydr
      replace hxl : x ∉ c.left.left.U :=
        compl_subset_compl.2 c.left.left_U_subset_right_C hxl
      replace hyl : y ∉ c.left.left.U :=
        compl_subset_compl.2 c.left.left_U_subset_right_C hyl
      simp only [pow_succ, c.lim_eq_midpoint, c.left.lim_eq_midpoint,
        c.left.left.lim_of_nmem_U _ hxl, c.left.left.lim_of_nmem_U _ hyl]
      refine' (dist_midpoint_midpoint_le _ _ _ _).trans _
      refine' (div_le_div_of_nonneg_right (add_le_add_right (dist_midpoint_midpoint_le _ _ _ _) _)
        zero_le_two).trans _
      rw [dist_self, zero_add]
      set r := (3 / 4 : ℝ) ^ n
      calc _ ≤ (r / 2 + r) / 2 := by gcongr
        _ = _ := by field_simp; ring
#align urysohns.CU.continuous_lim Urysohns.CU.continuous_lim

end CU

end Urysohns

/-- Urysohn's lemma: if `s` and `t` are two disjoint closed sets in a normal topological space `X`,
then there exists a continuous function `f : X → ℝ` such that

* `f` equals zero on `s`;
* `f` equals one on `t`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
theorem exists_continuous_zero_one_of_isClosed [NormalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hd : Disjoint s t) : ∃ f : C(X, ℝ), EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  -- The actual proof is in the code above. Here we just repack it into the expected format.
  let P : Set X → Prop := fun _ ↦ True
  set c : Urysohns.CU P :=
  { C := s
    U := tᶜ
    P_C := trivial
    closed_C := hs
    open_U := ht.isOpen_compl
    subset := disjoint_left.1 hd
    hP := by
      rintro c u c_closed - u_open cu
      rcases normal_exists_closure_subset c_closed u_open cu with ⟨v, v_open, cv, hv⟩
      exact ⟨v, v_open, cv, hv, trivial⟩ }
  exact ⟨⟨c.lim, c.continuous_lim⟩, c.lim_of_mem_C, fun x hx => c.lim_of_nmem_U _ fun h => h hx,
    c.lim_mem_Icc⟩
#align exists_continuous_zero_one_of_closed exists_continuous_zero_one_of_isClosed

/-- Urysohn's lemma: if `s` and `t` are two disjoint sets in a regular locally compact topological
space `X`, with `s` compact and `t` closed, then there exists a continuous
function `f : X → ℝ` such that

* `f` equals zero on `s`;
* `f` equals one on `t`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
theorem exists_continuous_zero_one_of_isCompact [RegularSpace X] [LocallyCompactSpace X]
    {s t : Set X} (hs : IsCompact s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C(X, ℝ), EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨k, k_comp, k_closed, sk, kt⟩ : ∃ k, IsCompact k ∧ IsClosed k ∧ s ⊆ interior k ∧ k ⊆ tᶜ :=
    exists_compact_closed_between hs ht.isOpen_compl hd.symm.subset_compl_left
  let P : Set X → Prop := IsCompact
  set c : Urysohns.CU P :=
  { C := k
    U := tᶜ
    P_C := k_comp
    closed_C := k_closed
    open_U := ht.isOpen_compl
    subset := kt
    hP := by
      rintro c u - c_comp u_open cu
      rcases exists_compact_closed_between c_comp u_open cu with ⟨k, k_comp, k_closed, ck, ku⟩
      have A : closure (interior k) ⊆ k :=
        (IsClosed.closure_subset_iff k_closed).2 interior_subset
      refine ⟨interior k, isOpen_interior, ck, A.trans ku,
        k_comp.of_isClosed_subset isClosed_closure A⟩ }
  exact ⟨⟨c.lim, c.continuous_lim⟩, fun x hx ↦ c.lim_of_mem_C _ (sk.trans interior_subset hx),
    fun x hx => c.lim_of_nmem_U _ fun h => h hx, c.lim_mem_Icc⟩

/-- Urysohn's lemma: if `s` and `t` are two disjoint sets in a regular locally compact topological
space `X`, with `s` compact and `t` closed, then there exists a continuous compactly supported
function `f : X → ℝ` such that

* `f` equals one on `s`;
* `f` equals zero on `t`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
theorem exists_continuous_one_zero_of_isCompact [RegularSpace X] [LocallyCompactSpace X]
    {s t : Set X} (hs : IsCompact s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C(X, ℝ), EqOn f 1 s ∧ EqOn f 0 t ∧ HasCompactSupport f ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨k, k_comp, k_closed, sk, kt⟩ : ∃ k, IsCompact k ∧ IsClosed k ∧ s ⊆ interior k ∧ k ⊆ tᶜ :=
    exists_compact_closed_between hs ht.isOpen_compl hd.symm.subset_compl_left
  rcases exists_continuous_zero_one_of_isCompact hs isOpen_interior.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr sk) with ⟨⟨f, hf⟩, hfs, hft, h'f⟩
  have A : t ⊆ (interior k)ᶜ := subset_compl_comm.mpr (interior_subset.trans kt)
  refine ⟨⟨fun x ↦ 1 - f x, continuous_const.sub hf⟩, fun x hx ↦ by simpa using hfs hx,
    fun x hx ↦ by simpa [sub_eq_zero] using (hft (A hx)).symm, ?_, fun x ↦ ?_⟩
  · apply HasCompactSupport.intro' k_comp k_closed (fun x hx ↦ ?_)
    simp only [ContinuousMap.coe_mk, sub_eq_zero]
    apply (hft _).symm
    contrapose! hx
    simp only [mem_compl_iff, not_not] at hx
    exact interior_subset hx
  · have : 0 ≤ f x ∧ f x ≤ 1 := by simpa using h'f x
    simp [this]

/-- Urysohn's lemma: if `s` and `t` are two disjoint sets in a regular locally compact topological
space `X`, with `s` compact and `t` closed, then there exists a continuous compactly supported
function `f : X → ℝ` such that

* `f` equals one on `s`;
* `f` equals zero on `t`;
* `0 ≤ f x ≤ 1` for all `x`.

Moreover, if `s` is Gδ, one can ensure that `f ⁻¹ {1}` is exactly `s`.
-/
theorem exists_continuous_one_zero_of_isCompact_of_isGδ [RegularSpace X] [LocallyCompactSpace X]
    {s t : Set X} (hs : IsCompact s) (h's : IsGδ s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C(X, ℝ), s = f ⁻¹' {1} ∧ EqOn f 0 t ∧ HasCompactSupport f
      ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  rcases h's.eq_iInter_nat with ⟨U, U_open, hU⟩
  obtain ⟨m, m_comp, -, sm, mt⟩ : ∃ m, IsCompact m ∧ IsClosed m ∧ s ⊆ interior m ∧ m ⊆ tᶜ :=
    exists_compact_closed_between hs ht.isOpen_compl hd.symm.subset_compl_left
  have A n : ∃ f : C(X, ℝ), EqOn f 1 s ∧ EqOn f 0 (U n ∩ interior m)ᶜ ∧ HasCompactSupport f
      ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
    apply exists_continuous_one_zero_of_isCompact hs
      ((U_open n).inter isOpen_interior).isClosed_compl
    rw [disjoint_compl_right_iff_subset]
    exact subset_inter ((hU.subset.trans (iInter_subset U n))) sm
  choose f fs fm _hf f_range using A
  obtain ⟨u, u_pos, u_sum, hu⟩ : ∃ (u : ℕ → ℝ), (∀ i, 0 < u i) ∧ Summable u ∧ ∑' i, u i = 1 :=
    ⟨fun n ↦ 1/2/2^n, fun n ↦ by positivity, summable_geometric_two' 1, tsum_geometric_two' 1⟩
  let g : X → ℝ := fun x ↦ ∑' n, u n * f n x
  have hgmc : EqOn g 0 mᶜ := by
    intro x hx
    have B n : f n x = 0 := by
      have : mᶜ ⊆ (U n ∩ interior m)ᶜ := by
        simpa using (inter_subset_right _ _).trans interior_subset
      exact fm n (this hx)
    simp [g, B]
  have I n x : u n * f n x ≤ u n := mul_le_of_le_one_right (u_pos n).le (f_range n x).2
  have S x : Summable (fun n ↦ u n * f n x) := Summable.of_nonneg_of_le
      (fun n ↦ mul_nonneg (u_pos n).le (f_range n x).1) (fun n ↦ I n x) u_sum
  refine ⟨⟨g, ?_⟩, ?_, hgmc.mono (subset_compl_comm.mp mt), ?_, fun x ↦ ⟨?_, ?_⟩⟩
  · apply continuous_tsum (fun n ↦ continuous_const.mul (f n).continuous) u_sum (fun n x ↦ ?_)
    simpa [abs_of_nonneg, (u_pos n).le, (f_range n x).1] using I n x
  · apply Subset.antisymm (fun x hx ↦ by simp [g, fs _ hx, hu]) ?_
    apply compl_subset_compl.1
    intro x hx
    obtain ⟨n, hn⟩ : ∃ n, x ∉ U n := by simpa [hU] using hx
    have fnx : f n x = 0 := fm _ (by simp [hn])
    have : g x < 1 := by
      apply lt_of_lt_of_le ?_ hu.le
      exact tsum_lt_tsum (i := n) (fun i ↦ I i x) (by simp [fnx, u_pos n]) (S x) u_sum
    simpa using this.ne
  · exact HasCompactSupport.of_support_subset_isCompact m_comp
      (Function.support_subset_iff'.mpr hgmc)
  · exact tsum_nonneg (fun n ↦ mul_nonneg (u_pos n).le (f_range n x).1)
  · apply le_trans _ hu.le
    exact tsum_le_tsum (fun n ↦ I n x) (S x) u_sum

theorem exists_continuous_nonneg_pos [RegularSpace X] [LocallyCompactSpace X] (x : X) :
    ∃ f : C(X, ℝ), HasCompactSupport f ∧ 0 ≤ (f : X → ℝ) ∧ f x ≠ 0 := by
  rcases exists_compact_mem_nhds x with ⟨k, hk, k_mem⟩
  rcases exists_continuous_one_zero_of_isCompact hk isClosed_empty (disjoint_empty k)
    with ⟨f, fk, -, f_comp, hf⟩
  refine ⟨f, f_comp, fun x ↦ (hf x).1, ?_⟩
  have := fk (mem_of_mem_nhds k_mem)
  simp only [ContinuousMap.coe_mk, Pi.one_apply] at this
  simp [this]

/-- A variation of Urysohn's lemma. In a normal space `X`, for a closed set `t` and an open set `s`
such that `t ⊆ s`, there is a continuous function `f` supported in `s`, `f x = 1` on `t` and
`0 ≤ f x ≤ 1`. -/
lemma exists_tsupport_one_of_isOpen_isClosed [NormalSpace X] {s t : Set X}
    (hs : IsOpen s) (ht : IsClosed t) (hst : t ⊆ s) : ∃ f : C(X, ℝ), tsupport f ⊆ s ∧ EqOn f 1 t
    ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨U, V, hUV⟩ := normal_separation (IsOpen.isClosed_compl hs) ht
      (HasSubset.Subset.disjoint_compl_left hst)
    have hDisjoint : Disjoint (closure U) t := by
      apply le_compl_iff_disjoint_right.mp
      apply _root_.subset_trans _ (Set.compl_subset_compl.mpr hUV.2.2.2.1)
      apply (IsClosed.closure_subset_iff (IsOpen.isClosed_compl hUV.2.1)).mpr
      exact Set.subset_compl_iff_disjoint_right.mpr hUV.2.2.2.2
    obtain ⟨f, hf⟩ := exists_continuous_zero_one_of_isClosed isClosed_closure ht hDisjoint
    use f
    constructor
    · apply _root_.subset_trans _ (Set.compl_subset_comm.mp hUV.2.2.1)
      rw [← IsClosed.closure_eq (IsOpen.isClosed_compl hUV.1)]
      apply closure_mono
      rw [Set.subset_compl_iff_disjoint_left, Function.disjoint_support_iff]
      exact Set.EqOn.mono subset_closure hf.1
    · exact hf.2

open Classical BigOperators

/-- A variation of Urysohn's lemma. In a normal T2 space `X`, for a compact set `t` and a finite
family of open sets `{s i}` such that `t ⊆ ⋃ i, s i`, there is a family of continuous function
`{f i}` supported in `s i`, `∑ i, f i x = 1` on `t` and `0 ≤ f x ≤ 1`. -/
lemma exists_forall_tsupport_iUnion_one_iUnion_of_isOpen_isClosed [NormalSpace X] [T2Space X]
    [LocallyCompactSpace X] {n : ℕ} {t : Set X} {s : Fin n → Set X}
    (hs : ∀ (i : Fin n), IsOpen (s i))
    (htcp : IsCompact t) (hst : t ⊆ ⋃ i, s i) :
    ∃ f : Fin n → C(X, ℝ), (∀ (i : Fin n), tsupport (f i) ⊆ s i) ∧ EqOn (∑ i, f i) 1 t
    ∧ ∀ (i : Fin n), ∀ (x : X), f i x ∈ Icc (0 : ℝ) 1 := by
  rcases n with _ | n
  · simp only [Nat.zero_eq, Finset.univ_eq_empty, Finset.sum_empty, mem_Icc, IsEmpty.forall_iff,
    and_true, exists_const]
    have : t = ∅ := by
      rw [Set.iUnion_of_empty s] at hst
      exact subset_eq_empty hst rfl
    constructor
    · exact trivial
    · intro x
      rw [this]
      exact fun a => a.elim
  · have htW : ∀ (x : X), x ∈ t → ∃ (Wx : Set X), x ∈ Wx ∧ IsOpen Wx ∧ IsCompact (closure Wx)
        ∧ ∃ (i : Fin (Nat.succ n)), (closure Wx) ⊆ s i := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ((Set.mem_of_subset_of_mem hst) hx)
      obtain ⟨cWx, hWx⟩ := exists_compact_subset (hs i) hi
      use interior cWx
      constructor
      · exact hWx.2.1
      constructor
      · simp only [isOpen_interior]
      constructor
      · apply IsCompact.of_isClosed_subset hWx.1 isClosed_closure
        nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hWx.1)]
        exact closure_mono interior_subset
      · use i
        apply _root_.subset_trans _ hWx.2.2
        nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hWx.1)]
        exact closure_mono interior_subset
    set W : X → Set X := fun x => if hx : x ∈ t then Classical.choose (htW x hx) else default
      with hW
    have htWnhds : ∀ (x : X), x ∈ t → W x ∈ nhds x := by
      intro x hx
      apply mem_nhds_iff.mpr
      use W x
      constructor
      · exact subset_refl (W x)
      · rw [hW]
        simp only
        rw [dif_pos hx]
        exact And.intro (Classical.choose_spec (htW x hx)).2.1 (Classical.choose_spec (htW x hx)).1
    obtain ⟨ι, hι⟩ := IsCompact.elim_nhds_subcover htcp W htWnhds
    set Wx : Fin (Nat.succ n) → ι → Set X := fun i xj =>
      if closure (W xj) ⊆ s i then closure (W xj) else ∅
      with hWx
    set H : Fin (Nat.succ n) → Set X := fun i => ⋃ xj, closure (Wx i xj)
      with hH
    have IsClosedH : ∀ (i : Fin (Nat.succ n)), IsClosed (H i) := by
      intro i
      rw [hH]
      simp only
      exact isClosed_iUnion_of_finite (fun (xj : ι) => isClosed_closure)
    have IsHSubS : ∀ (i : Fin (Nat.succ n)), H i ⊆ s i := by
      intro i
      rw [hH]
      simp only
      apply Set.iUnion_subset
      intro xj
      rw [hWx]
      simp only
      by_cases hmV : closure (W xj) ⊆ s i
      · rw [if_pos hmV, closure_closure]
        exact hmV
      · rw [if_neg hmV, closure_empty]
        exact Set.empty_subset _
    set g : Fin (Nat.succ n) → C(X, ℝ) := fun i => Classical.choose
      (exists_tsupport_one_of_isOpen_isClosed (hs i) (IsClosedH i) (IsHSubS i))
      with hg
    set f : Fin (Nat.succ n) → C(X, ℝ) :=
      fun i => (∏ j in { j : Fin (Nat.succ n) | j < i }.toFinset, (1 - g j)) * g i
      with hf
    use f
    constructor
    · rw [hf]
      simp only
      intro i
      apply _root_.subset_trans tsupport_mul_subset_right
      exact (Classical.choose_spec
        (exists_tsupport_one_of_isOpen_isClosed (hs i) (IsClosedH i) (IsHSubS i))).1
    constructor
    · have hsumf (m : ℕ) (hm : m < Nat.succ n) :
          ∑ j in { j : Fin (Nat.succ n) | j ≤ ⟨m, hm⟩ }.toFinset, f j
          = 1 - (∏ j in { j : Fin (Nat.succ n) | j ≤ ⟨m, hm⟩ }.toFinset, (1 - g j)) := by
        induction' m with m ihm
        · simp only [Nat.zero_eq, Fin.zero_eta, Fin.le_zero_iff, setOf_eq_eq_singleton,
          toFinset_singleton, Finset.sum_singleton, Finset.prod_singleton, sub_sub_cancel]
          rw [hf]
          simp only [Fin.not_lt_zero, setOf_false, toFinset_empty, Finset.prod_empty, one_mul]
        · have hmlt : m < Nat.succ n := by
            exact Nat.lt_of_succ_lt hm
          have hUnion: { j : Fin (Nat.succ n) | j ≤ ⟨m + 1, hm⟩}
              = { j : Fin (Nat.succ n) | j ≤ ⟨m, hmlt⟩ } ∪ {⟨m+1, hm⟩} := by
            simp only [union_singleton]
            ext j
            simp only [Nat.cast_add, Nat.cast_one, mem_setOf_eq, mem_insert_iff]
            constructor
            · intro hj
              by_cases hjm : j.1 ≤ m
              · right
                exact hjm
              · push_neg at hjm
                left
                rw [Fin.ext_iff]
                simp only
                rw [Fin.le_def] at hj
                exact (Nat.le_antisymm hjm hj).symm
            · intro hj
              rcases hj with hjmone | hjmle
              · exact le_of_eq hjmone
              · rw [Fin.le_def]
                simp only
                rw [Fin.le_def] at hjmle
                simp only at hjmle
                rw [Nat.le_add_one_iff]
                left
                exact hjmle
          simp_rw [hUnion]
          simp only [union_singleton, toFinset_insert, mem_setOf_eq, toFinset_setOf]
          rw [Finset.sum_insert _, Finset.prod_insert _]
          simp only [mem_setOf_eq, toFinset_setOf] at ihm
          rw [ihm hmlt, sub_mul, one_mul, hf]
          ring_nf
          simp only [mem_setOf_eq, toFinset_setOf]
          have honeaddm: 1+m < Nat.succ n := by
            rw [add_comm 1 m]
            exact hm
          have hxlem : Finset.filter (fun (x : Fin (Nat.succ n)) => x < { val := 1+m, isLt := honeaddm })
              = Finset.filter (fun (x : Fin (Nat.succ n)) => x ≤ { val := m, isLt := hmlt }) := by
            ext Finset.univ a
            simp only [Finset.mem_filter, and_congr_right_iff]
            intro _
            rw [Fin.le_def, Fin.lt_def]
            simp only
            rw [add_comm 1 m]
            exact Nat.lt_add_one_iff
          rw [hxlem]
          ring
          all_goals
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
            rw [Fin.lt_def]
            simp only [Fin.val_nat_cast]
            exact lt_add_one m
      intro x hx
      have huniv : {j : Fin (Nat.succ n) | j ≤ ⟨n, (lt_add_one n)⟩ }.toFinset = Finset.univ := by
        ext j
        simp only [Nat.zero_eq, mem_setOf_eq, toFinset_setOf, Finset.mem_filter, Finset.mem_univ,
          true_and, iff_true]
        apply Fin.mk_le_of_le_val
        simp only
        exact Nat.lt_succ_iff.mp j.isLt
      rw [← huniv]
      have heqfun (x : X) :
          (∑ j in { j : Fin (Nat.succ n) | j ≤ ⟨n, (lt_add_one n)⟩ }.toFinset, f j) x
          = (1 - (∏ j in { j : Fin (Nat.succ n) | j ≤ ⟨n, (lt_add_one n)⟩ }.toFinset, (1 - g j)))
          x := by
        apply Function.funext_iff.mp
        ext z
        exact congrFun (congrArg DFunLike.coe (hsumf n (lt_add_one n))) z
      simp only [Nat.zero_eq, mem_setOf_eq, toFinset_setOf, ContinuousMap.coe_sum, Finset.sum_apply,
        ContinuousMap.sub_apply, ContinuousMap.one_apply, ContinuousMap.coe_prod,
        ContinuousMap.coe_sub, ContinuousMap.coe_one, Finset.prod_apply, Pi.sub_apply,
        Pi.one_apply] at heqfun
      simp only [Nat.zero_eq, mem_setOf_eq, toFinset_setOf, Finset.sum_apply, Pi.one_apply]
      rw [heqfun]
      simp only [sub_eq_self]
      obtain ⟨xj, hxj⟩ := exists_exists_eq_and.mp (hι.2 hx)
      simp only [mem_iUnion, exists_prop] at hxj
      rw [hW] at hxj
      simp at hxj
      rw [dif_pos (hι.1 xj hxj.1)] at hxj
      obtain ⟨i, hi⟩ := (Classical.choose_spec (htW xj (hι.1 xj hxj.1))).2.2.2
      have hxHi : x ∈ H i := by
        rw [hH]
        simp only [mem_iUnion]
        use ⟨xj, hxj.1⟩
        rw [hWx]
        simp only [dite_eq_ite]
        rw [hW]
        simp only
        rw [dif_pos (hι.1 xj hxj.1)]
        apply Set.mem_of_mem_of_subset _ subset_closure
        simp only [mem_ite_empty_right]
        exact And.intro hi (Set.mem_of_mem_of_subset hxj.2 subset_closure)
      simp at huniv
      rw [huniv]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hg]
      simp only [mem_Icc]
      rw [(Classical.choose_spec (exists_tsupport_one_of_isOpen_isClosed
        (hs i) (IsClosedH i) (IsHSubS i))).2.1 hxHi]
      simp only [Pi.one_apply, sub_self]
    · intro i x
      rw [hf]
      simp only [mem_setOf_eq, toFinset_setOf, ContinuousMap.mul_apply, ContinuousMap.coe_prod,
        ContinuousMap.coe_sub, ContinuousMap.coe_one, Finset.prod_apply]
      apply unitInterval.mul_mem
      · sorry
      -- apply prod_mem  gives an error "tactic 'apply' failed, failed to unify". `(1 - g c) x` needs to be understood as `fun c => (1 - g c) x
      -- leaving a code using an ad hoc lemma icc_prod_Icc in https://github.com/yoh-tanimoto/mathlib4/blob/yoh/yoh/RMK/urysohn.lean
      -- · apply icc_prod_Icc i.val
      --   constructor
      --   · rw [hg]
      --     simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_nonneg,
      --       tsub_le_iff_right, le_add_iff_nonneg_right]
      --     intro j _
      --     apply Set.Icc.one_sub_mem
      --     exact (Classical.choose_spec (exists_tsupport_one_of_isOpen_isClosed
      --       (hs j) (IsClosedH j) (IsHSubS j))).2.2 x
      --   · have hFinIcc: Finset.filter (fun x => x < i) Finset.univ = Finset.Ico 0 i := by
      --       ext j
      --       simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico, Fin.zero_le]
      --     rw [hFinIcc]
      --     simp only [Fin.card_Ico, Fin.val_zero, tsub_zero]
      · rw [hg]
        simp only
        exact (Classical.choose_spec (exists_tsupport_one_of_isOpen_isClosed (hs i) (IsClosedH i) (IsHSubS i))).2.2 x
