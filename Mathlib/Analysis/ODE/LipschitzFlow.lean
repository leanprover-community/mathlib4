/-
Copyright (c) 2026 Alireza Behtash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alireza Behtash
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Dynamics.Flow

import Mathlib.Analysis.ODE.Gronwall

/-!
# Flows of globally Lipschitz vector fields

A globally Lipschitz vector field `v` on a Banach space `E` has, through every point, a unique
solution `γ : ℝ → E` of `γ' = v ∘ γ` defined for all times. These solutions form a continuous flow
`LipschitzWith.flow : Flow ℝ E`.

## Main results

* `LipschitzWith.exists_forall_hasDerivAt`: global existence of solutions.
* `LipschitzWith.dist_le_of_forall_hasDerivAt`: two solutions diverge at most exponentially.
* `LipschitzWith.flow`: the flow of `v`.
* `LipschitzWith.hasDerivAt_flow`: the orbits of the flow solve `γ' = v ∘ γ`.
* `LipschitzWith.flow_eq_of_hasDerivAt`: every solution is an orbit of the flow.

## Implementation notes

The Picard–Lindelöf theorem gives solutions of a bounded Lipschitz field on every compact time
interval, and these glue to a global solution. A general Lipschitz field is reduced to this case by
a cutoff. By Grönwall's inequality, the solutions starting at `x` stay, on a time interval
`[-T, T]`, in a ball whose radius depends only on `x` and `T`. Cutting the field off outside a
larger ball does not change these solutions.
-/

public section

open Set Filter Topology Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] {v : E → E} {K : ℝ≥0}

namespace LipschitzWith

private lemma norm_le_add_mul_norm (hv : LipschitzWith K v) (y : E) :
    ‖v y‖ ≤ ‖v 0‖ + K * ‖y‖ := by
  have h := hv.dist_le_mul y 0
  rw [dist_eq_norm, dist_zero_right] at h
  linarith [norm_le_insert' (v y) (v 0)]

/-- A cutoff function equal to `1` on `closedBall 0 R` and to `0` outside `ball 0 (R + 1)`. -/
private noncomputable def cutoff (R : ℝ) (y : E) : ℝ := min 1 (max 0 (R + 1 - ‖y‖))

private lemma lipschitzWith_cutoff (R : ℝ) : LipschitzWith 1 (cutoff (E := E) R) := by
  have hg : LipschitzWith 1 fun y : E ↦ R + 1 - ‖y‖ := LipschitzWith.of_dist_le_mul fun x y ↦ by
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul,
      show R + 1 - ‖x‖ - (R + 1 - ‖y‖) = ‖y‖ - ‖x‖ by ring, abs_sub_comm]
    exact abs_norm_sub_norm_le x y
  exact (hg.const_max 0).const_min 1

private lemma cutoff_nonneg (R : ℝ) (y : E) : 0 ≤ cutoff R y :=
  le_min zero_le_one (le_max_left _ _)

private lemma cutoff_le_one (R : ℝ) (y : E) : cutoff R y ≤ 1 :=
  min_le_left _ _

private lemma cutoff_of_norm_le {R : ℝ} {y : E} (hy : ‖y‖ ≤ R) : cutoff R y = 1 :=
  min_eq_left (le_max_of_le_right (by linarith))

private lemma cutoff_of_le_norm {R : ℝ} {y : E} (hy : R + 1 ≤ ‖y‖) : cutoff R y = 0 := by
  rw [cutoff, max_eq_left (by linarith), min_eq_right zero_le_one]

variable [NormedSpace ℝ E]

/-- Solutions on the intervals `(-(n + 1), n + 1)` glue to a global solution. -/
private lemma exists_forall_hasDerivAt_of_forall_Ioo (hv : LipschitzWith K v) {x : E}
    (h : ∀ n : ℕ, ∃ α : ℝ → E, α 0 = x ∧
      ∀ t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1), HasDerivAt α (v (α t)) t) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (v (γ t)) t := by
  choose α hα0 hα using h
  have key : ∀ n m : ℕ, n ≤ m → EqOn (α n) (α m) (Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1)) := by
    intro n m hnm
    have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by gcongr
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    exact ODE_solution_unique_of_mem_Ioo (v := fun _ ↦ v) (s := fun _ ↦ univ) (t₀ := 0)
      (fun _ _ ↦ hv.lipschitzOnWith) ⟨by linarith, by linarith⟩
      (fun t ht ↦ ⟨hα n t ht, trivial⟩)
      (fun t ht ↦ ⟨hα m t ⟨by linarith [ht.1], by linarith [ht.2]⟩, trivial⟩) (by rw [hα0, hα0])
  have hagree : ∀ n m : ℕ, ∀ t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      t ∈ Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1) → α n t = α m t := by
    intro n m t hn hm
    rcases le_total n m with h | h
    · exact key n m h hn
    · exact (key m n h hm).symm
  have hmem : ∀ t : ℝ, t ∈ Ioo (-((⌈|t|⌉₊ : ℝ) + 1)) ((⌈|t|⌉₊ : ℝ) + 1) := fun t ↦ by
    have := Nat.le_ceil |t|
    constructor <;> linarith [neg_abs_le t, le_abs_self t]
  refine ⟨fun t ↦ α ⌈|t|⌉₊ t, by simp [hα0], fun t ↦ ?_⟩
  refine (hα _ t (hmem t)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (hmem t).1 (hmem t).2] with s hs
  exact hagree _ _ s (hmem s) hs

/-- A bounded Lipschitz vector field has global solutions. -/
private lemma exists_forall_hasDerivAt_of_norm_le [CompleteSpace E] (hv : LipschitzWith K v)
    {L : ℝ≥0} (hb : ∀ y, ‖v y‖ ≤ L) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (v (γ t)) t := by
  refine hv.exists_forall_hasDerivAt_of_forall_Ioo fun n ↦ ?_
  let T : ℝ≥0 := ⟨(n : ℝ) + 1, by positivity⟩
  have h0 : (0 : ℝ) ∈ Icc (-(T : ℝ)) T := ⟨by simp, T.2⟩
  have hPL : IsPicardLindelof (fun _ ↦ v) (⟨0, h0⟩ : Icc (-(T : ℝ)) T) x (L * T) 0 L K :=
    { lipschitzOnWith := fun _ _ ↦ hv.lipschitzOnWith
      continuousOn := fun _ _ ↦ continuousOn_const
      norm_le := fun _ _ y _ ↦ hb y
      mul_max_le := by simp }
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, fun t ht ↦ (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

private lemma norm_cutoff_smul_le (hv : LipschitzWith K v) (R : ℝ) (y : E) :
    ‖cutoff R y • v y‖ ≤ ‖v 0‖ + K * ‖y‖ := by
  rw [norm_smul, Real.norm_of_nonneg (cutoff_nonneg R y)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one R y)).trans
    (hv.norm_le_add_mul_norm y)

private lemma norm_cutoff_smul_le_of_nonneg (hv : LipschitzWith K v) {R : ℝ} (hR : 0 ≤ R)
    (y : E) : ‖cutoff R y • v y‖ ≤ ‖v 0‖ + K * (R + 1) := by
  rcases le_or_gt ‖y‖ (R + 1) with hy | hy
  · exact (hv.norm_cutoff_smul_le R y).trans (by gcongr)
  · rw [cutoff_of_le_norm hy.le, zero_smul, norm_zero]
    exact add_nonneg (norm_nonneg _) (mul_nonneg K.coe_nonneg (by linarith))

private lemma lipschitzWith_cutoff_smul (hv : LipschitzWith K v) {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith (‖v 0‖ + K * (R + 1) + K).toNNReal fun y ↦ cutoff R y • v y := by
  have hM : 0 ≤ ‖v 0‖ + K * (R + 1) := add_nonneg (norm_nonneg _) (mul_nonneg K.coe_nonneg
    (by linarith))
  have key : ∀ x y : E, ‖x‖ ≤ R + 1 → ‖cutoff R x • v x - cutoff R y • v y‖ ≤
      (‖v 0‖ + K * (R + 1) + K) * ‖x - y‖ := by
    intro x y hx
    have hc : |cutoff R x - cutoff R y| ≤ ‖x - y‖ := by
      simpa [Real.dist_eq, dist_eq_norm] using (lipschitzWith_cutoff (E := E) R).dist_le_mul x y
    have hvx : ‖v x‖ ≤ ‖v 0‖ + K * (R + 1) := (hv.norm_le_add_mul_norm x).trans (by gcongr)
    have hvxy : ‖v x - v y‖ ≤ K * ‖x - y‖ := by simpa [dist_eq_norm] using hv.dist_le_mul x y
    calc ‖cutoff R x • v x - cutoff R y • v y‖
        = ‖(cutoff R x - cutoff R y) • v x + cutoff R y • (v x - v y)‖ := by
          rw [sub_smul, smul_sub]
          abel_nf
      _ ≤ |cutoff R x - cutoff R y| * ‖v x‖ + cutoff R y * ‖v x - v y‖ := by
          refine (norm_add_le _ _).trans_eq ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (cutoff_nonneg R y)]
      _ ≤ ‖x - y‖ * (‖v 0‖ + K * (R + 1)) + 1 * (K * ‖x - y‖) :=
          add_le_add (mul_le_mul hc hvx (norm_nonneg _) (norm_nonneg _))
            (mul_le_mul (cutoff_le_one R y) hvxy (norm_nonneg _) zero_le_one)
      _ = (‖v 0‖ + K * (R + 1) + K) * ‖x - y‖ := by ring
  refine LipschitzWith.of_dist_le' fun x y ↦ ?_
  rw [dist_eq_norm, dist_eq_norm]
  rcases le_or_gt ‖x‖ (R + 1) with hx | hx
  · exact key x y hx
  rcases le_or_gt ‖y‖ (R + 1) with hy | hy
  · rw [norm_sub_rev, norm_sub_rev x]
    exact key y x hy
  · simp only [cutoff_of_le_norm hx.le, cutoff_of_le_norm hy.le, zero_smul, sub_zero, norm_zero]
    exact mul_nonneg (add_nonneg hM K.coe_nonneg) (norm_nonneg _)

/-- If `‖u y‖ ≤ c + K * ‖y‖`, a solution of `γ' = u ∘ γ` stays in the ball of radius
`gronwallBound ‖γ 0‖ K c T` on the time interval `[-T, T]`. -/
private lemma norm_le_gronwallBound {u : E → E} {c : ℝ} (hc : 0 ≤ c)
    (hu : ∀ y, ‖u y‖ ≤ c + K * ‖y‖) {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (u (γ t)) t) {T t : ℝ}
    (ht : t ∈ Icc (-T) T) : ‖γ t‖ ≤ gronwallBound ‖γ 0‖ K c T := by
  have fwd : ∀ {u : E → E}, (∀ y, ‖u y‖ ≤ c + K * ‖y‖) → ∀ {γ : ℝ → E},
      (∀ t, HasDerivAt γ (u (γ t)) t) → ∀ t ∈ Icc 0 T, ‖γ t‖ ≤ gronwallBound ‖γ 0‖ K c T := by
    intro u hu γ hγ t ht
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (f' := fun s ↦ u (γ s)) (K := K)
      (ε := c) (continuous_iff_continuousAt.2 fun s ↦ (hγ s).continuousAt).continuousOn
      (fun s _ ↦ (hγ s).hasDerivWithinAt) le_rfl (fun s _ ↦ by linarith [hu (γ s)]) t ht
    rw [sub_zero] at h
    exact h.trans (gronwallBound_mono (norm_nonneg _) hc K.coe_nonneg ht.2)
  rcases le_total 0 t with h0 | h0
  · exact fwd hu hγ t ⟨h0, ht.2⟩
  · have hγ' : ∀ s, HasDerivAt (fun s ↦ γ (-s)) (-u (γ (-s))) s := fun s ↦ by
      simpa [Function.comp_def] using (hγ (-s)).scomp s (hasDerivAt_neg s)
    simpa using fwd (u := fun y ↦ -u y) (fun y ↦ by simpa using hu y) hγ' (-t)
      ⟨by linarith, by linarith [ht.1]⟩

/-- A globally Lipschitz vector field on a Banach space has a solution through every point,
defined for all times. -/
theorem exists_forall_hasDerivAt [CompleteSpace E] (hv : LipschitzWith K v) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (v (γ t)) t := by
  refine hv.exists_forall_hasDerivAt_of_forall_Ioo fun n ↦ ?_
  let R := gronwallBound ‖x‖ K ‖v 0‖ ((n : ℝ) + 1)
  have hR : 0 ≤ R := by
    have h := gronwallBound_mono (norm_nonneg x) (norm_nonneg (v 0)) K.coe_nonneg
      (by positivity : (0 : ℝ) ≤ n + 1)
    rw [gronwallBound_x0] at h
    exact (norm_nonneg x).trans h
  obtain ⟨γ, hγ0, hγ⟩ := (hv.lipschitzWith_cutoff_smul hR).exists_forall_hasDerivAt_of_norm_le
    (L := ⟨‖v 0‖ + K * (R + 1), add_nonneg (norm_nonneg _) (mul_nonneg K.coe_nonneg
      (by linarith))⟩) (hv.norm_cutoff_smul_le_of_nonneg hR) x
  refine ⟨γ, hγ0, fun t ht ↦ ?_⟩
  have hγt : ‖γ t‖ ≤ R := by
    have h := norm_le_gronwallBound (norm_nonneg (v 0)) (hv.norm_cutoff_smul_le R) hγ
      (T := (n : ℝ) + 1) ⟨ht.1.le, ht.2.le⟩
    rwa [hγ0] at h
  simpa [cutoff_of_norm_le hγt] using hγ t

/-- Two solutions of `γ' = v ∘ γ` diverge at most exponentially. -/
theorem dist_le_of_forall_hasDerivAt (hv : LipschitzWith K v) {γ δ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (hδ : ∀ t, HasDerivAt δ (v (δ t)) t) (t : ℝ) :
    dist (γ t) (δ t) ≤ dist (γ 0) (δ 0) * Real.exp (K * |t|) := by
  have fwd : ∀ {u : E → E}, LipschitzWith K u → ∀ {γ δ : ℝ → E},
      (∀ t, HasDerivAt γ (u (γ t)) t) → (∀ t, HasDerivAt δ (u (δ t)) t) → ∀ t, 0 ≤ t →
        dist (γ t) (δ t) ≤ dist (γ 0) (δ 0) * Real.exp (K * t) := by
    intro u hu γ δ hγ hδ t ht
    simpa using dist_le_of_trajectories_ODE (v := fun _ ↦ u) (K := K) (a := 0) (b := t)
      (fun _ ↦ hu) (fun s _ ↦ (hγ s).continuousAt.continuousWithinAt)
      (fun s _ ↦ (hγ s).hasDerivWithinAt) (fun s _ ↦ (hδ s).continuousAt.continuousWithinAt)
      (fun s _ ↦ (hδ s).hasDerivWithinAt) le_rfl t ⟨ht, le_rfl⟩
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact fwd hv hγ hδ t ht
  · have hrev : ∀ {γ : ℝ → E}, (∀ t, HasDerivAt γ (v (γ t)) t) →
        ∀ s, HasDerivAt (fun s ↦ γ (-s)) (-v (γ (-s))) s := fun hγ s ↦ by
      simpa [Function.comp_def] using (hγ (-s)).scomp s (hasDerivAt_neg s)
    have hv' : LipschitzWith K fun y ↦ -v y := by
      simpa [Function.comp_def] using LipschitzWith.id.neg.comp hv
    rw [abs_of_nonpos ht]
    simpa using fwd hv' (hrev hγ) (hrev hδ) (-t) (by linarith)

variable [CompleteSpace E]

/-- The flow of a globally Lipschitz vector field `v` on a Banach space: `hv.flow t x` is the
value at time `t` of the solution of `γ' = v ∘ γ` with `γ 0 = x`. -/
noncomputable def flow (hv : LipschitzWith K v) : Flow ℝ E where
  toFun t x := (hv.exists_forall_hasDerivAt x).choose t
  cont' := by
    have hγ := fun x ↦ (hv.exists_forall_hasDerivAt x).choose_spec
    refine continuous_iff_continuousAt.2 fun p ↦ ?_
    have hp : p ∈ Ioo (-(|p.1| + 1)) (|p.1| + 1) ×ˢ (univ : Set E) :=
      ⟨⟨by linarith [neg_abs_le p.1], by linarith [le_abs_self p.1]⟩, trivial⟩
    refine ContinuousOn.continuousAt ?_ ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)
    refine continuousOn_prod_of_continuousOn_lipschitzOnWith' _
      (Real.exp (K * (|p.1| + 1))).toNNReal (fun t ht ↦ ?_) (fun x _ ↦ ?_)
    · refine (LipschitzWith.of_dist_le' fun x y ↦ ?_).lipschitzOnWith
      have ht' : |t| ≤ |p.1| + 1 := abs_le.2 ⟨ht.1.le, ht.2.le⟩
      refine (hv.dist_le_of_forall_hasDerivAt (hγ x).2 (hγ y).2 t).trans ?_
      rw [(hγ x).1, (hγ y).1, mul_comm (dist x y)]
      gcongr
    · exact (continuous_iff_continuousAt.2 fun t ↦ ((hγ x).2 t).continuousAt).continuousOn
  map_add' t₁ t₂ x := by
    have h := (hv.exists_forall_hasDerivAt x).choose_spec
    have h' := (hv.exists_forall_hasDerivAt ((hv.exists_forall_hasDerivAt x).choose t₂)).choose_spec
    have := ODE_solution_unique_univ (v := fun _ ↦ v) (s := fun _ ↦ univ)
      (fun _ ↦ hv.lipschitzOnWith) (fun s ↦ ⟨h'.2 s, trivial⟩)
      (fun s ↦ ⟨(h.2 (s + t₂)).comp_add_const s t₂, trivial⟩) (t₀ := 0) (by simp [h'.1])
    exact (congrFun this t₁).symm
  map_zero' x := (hv.exists_forall_hasDerivAt x).choose_spec.1

/-- The orbits of `hv.flow` are solutions of `γ' = v ∘ γ`. -/
theorem hasDerivAt_flow (hv : LipschitzWith K v) (x : E) (t : ℝ) :
    HasDerivAt (fun s ↦ hv.flow s x) (v (hv.flow t x)) t :=
  (hv.exists_forall_hasDerivAt x).choose_spec.2 t

/-- Every solution of `γ' = v ∘ γ` is an orbit of `hv.flow`. -/
theorem flow_eq_of_hasDerivAt (hv : LipschitzWith K v) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (t₀ t : ℝ) : hv.flow t (γ t₀) = γ (t + t₀) :=
  congrFun (ODE_solution_unique_univ (v := fun _ ↦ v) (s := fun _ ↦ univ)
    (fun _ ↦ hv.lipschitzOnWith) (fun s ↦ ⟨hv.hasDerivAt_flow _ s, trivial⟩)
    (fun s ↦ ⟨(hγ (s + t₀)).comp_add_const s t₀, trivial⟩) (t₀ := 0)
    (by rw [Flow.map_zero_apply, zero_add])) t

theorem dist_flow_le (hv : LipschitzWith K v) (x y : E) (t : ℝ) :
    dist (hv.flow t x) (hv.flow t y) ≤ dist x y * Real.exp (K * |t|) := by
  simpa [Flow.map_zero_apply] using
    hv.dist_le_of_forall_hasDerivAt (hv.hasDerivAt_flow x) (hv.hasDerivAt_flow y) t

end LipschitzWith
