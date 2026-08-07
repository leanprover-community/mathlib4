/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Stream.Defs
public import Mathlib.Order.WithBotTop
public import Mathlib.Data.Seq.Basic

/-!
# Constructing a Newton Polygon

This file gives a way to construct a one sided Newton polygon given a sequence
`(v : ℕ → WithTop Γ)`, this is our way of packaging a set in `ℕ × Γ`.

We follow a rotating line algorithm found in Gouvêa's "P-adic Numbers: An Introduction".

## References
P-adic Numbers: An Introduction - Fernando Q. Gouvêa

-/

namespace NewtonPolygon₀.Construction


@[expose] public section

variable {Γ : Type*} [CommSemiring Γ] [Algebra Γ ℝ]

variable (Γ) in
/-- The result of one step of the Newton polygon algorithm. -/
inductive Step where
  /-- No more finite values. -/
  | tail
  /-- The set of minimum slopes is unbounded below. -/
  | unboundedBelow
  /-- The infimum is not attained (all later points are strictly above the limiting line):
      final ray with no further lattice points. -/
  | limitingRay (m : ℝ)
  /-- Infinitely many points achieve the minimum slope m: final ray with infinitely many points. -/
  | infiniteRay (m : ℝ)
  /-- The minimum slope is achieved by finitely many points;
      move to the rightmost point (j₀, j₁). -/
  | nextVertex (j₀ : ℕ) (j₁ : Γ) (l : ℕ) (m : ℝ)

variable (v : ℕ → WithTop Γ)

/-- Predicate saying the valuation of the `i`-th coefficient is not `⊤`. -/
def finite (i : ℕ) : Prop := v i ≠ ⊤

/-- The set of indices with finite coefficients. -/
def support : Set ℕ := {i | finite v i}

/-- The slope from a point `(x₀, y₀)` to `(x₁, y₁)` as a real number. -/
noncomputable
def slopeReal (x₀ x₁ : ℕ) (y₀ y₁ : Γ) : ℝ :=
  (algebraMap Γ ℝ y₁ - algebraMap Γ ℝ y₀) / (x₁ - x₀)

/-- The set of slopes out of a point `(i₀, i₁)`. -/
def slopeSet (i₀ : ℕ) (i₁ : Γ) : Set ℝ :=
  {m | ∃ j₀ : ℕ, j₀ > i₀ ∧ finite v j₀ ∧ ∃ j₁ : Γ, v j₀ = j₁ ∧ m = slopeReal i₀ j₀ i₁ j₁}


/-- The set of points that achieves a slope of `m` from a point `(i₀, i₁)`. -/
def achievingSet (i₀ : ℕ) (i₁ : Γ) (m : ℝ) : Set ℕ :=
  {j : ℕ | j > i₀ ∧ finite v j ∧ ∃ j₁ : Γ, v j = j₁ ∧ m = slopeReal i₀ j i₁ j₁}

/-- Given a point `(i₀, i₁)` returns the result of applying the Newton polygon algorithm. -/
noncomputable
def nextStep (i₀ : ℕ) (i₁ : Γ) : Step Γ :=
  open Classical in
  if slopeSet v i₀ i₁ = ∅ then
    .tail
  else if ¬ (BddBelow (slopeSet v i₀ i₁)) then
    .unboundedBelow
  else if hm : ¬ ∃ m ∈ slopeSet v i₀ i₁, m = sInf (slopeSet v i₀ i₁) then
    .limitingRay (sInf (slopeSet v i₀ i₁))
  else if hInf : (achievingSet v i₀ i₁ (of_not_not hm).choose).Infinite then
    .infiniteRay (of_not_not hm).choose
  else
    have hNonempty : (achievingSet v i₀ i₁ (of_not_not hm).choose).Nonempty := by
      simp only [↓existsAndEq, and_true] at hm
      use (of_not_not hm).choose
      grind [achievingSet]
    let j₀ := (Set.not_infinite.mp hInf).toFinset.max'
      ((Set.not_infinite.mp hInf).toFinset_nonempty.mpr hNonempty)
    match v j₀ with
      | ⊤ => .tail
      | (j₁ : Γ) => .nextVertex j₀ j₁ (j₀ - i₀) ((of_not_not hm).choose)

/-- Find the first index with finite valuation, starting from a given position. -/
noncomputable
def findFirstFinite (startIdx : ℕ) : Option (ℕ × Γ) := open Classical in
  if h : ∃ i ≥ startIdx, finite v i then
    some (Nat.find h, (Option.ne_none_iff_exists.mp (Nat.find_spec h).2).choose)
  else
    none

/-- The full Newton Polygon. -/
noncomputable
def stream' : Stream' (Option (Step Γ))
  | 0 => match findFirstFinite v 0 with
    | none => some .tail
    | some (i, v_i) => nextStep v i v_i
  | n + 1 =>
    open Classical in
    match stream' n with
      | some (.nextVertex j₀ j₁ _ _) => nextStep v j₀ j₁
      | _ => none

section NewtonPolygon₀.ConstructionAPI

lemma nextStep_none (a : ℕ) (ha : stream' v a = none) :
    stream' v (a + 1) = none := by
  simp [stream', ha]

lemma nextStep_limitingRay (a : ℕ) (m : ℝ) (ha : stream' v a =
    some (.limitingRay m)) : stream' v (a + 1) = none := by
  simp [stream', ha]

lemma nextStep_limitingRay' {a : ℕ} {m : ℝ} (ha : stream' v (a + 1) =
    some (.limitingRay m)) : ∃ i₀ i₁ l m, stream' v a =
    some (.nextVertex i₀ i₁ l m) := by
  unfold stream' at ha
  split at ha
  · rename_i _ i₀ i₁ m hm
    grind
  · trivial

lemma nextStep_limitingRay'' {a i₀ l : ℕ} {i₁ : Γ} {m n : ℝ}
    (ha : stream' v (a + 1) = some (.limitingRay m))
    (h : stream' v a = some (.nextVertex i₀ i₁ l n)) : nextStep v i₀ i₁ =
    .limitingRay m := by
  unfold stream' at ha
  simp_rw [h, Option.some.injEq] at ha
  exact ha

lemma nextStep_infiniteRay (a : ℕ) (m : ℝ) (ha : stream' v a =
    some (.infiniteRay m)) : stream' v (a + 1) = none := by
  simp [stream', ha]

lemma nextStep_infiniteRay' {a : ℕ} {m : ℝ} (ha : stream' v (a + 1) =
    some (.infiniteRay m)) :  ∃ i₀ i₁ l n, stream' v a =
    some (.nextVertex i₀ i₁ l n) := by
  unfold stream' at ha
  split at ha
  · rename_i _ i₀ i₁ m hm
    grind
  · trivial

lemma nextStep_infiniteRay'' {a i₀ l : ℕ} {i₁ : Γ} {m n : ℝ}
    (ha : stream' v (a + 1) = some (.infiniteRay m))
    (h : stream' v a = some (.nextVertex i₀ i₁ l n)) : nextStep v i₀ i₁ =
    .infiniteRay m := by
  unfold stream' at ha
  simp_rw [h, Option.some.injEq] at ha
  exact ha

lemma nextStep_tail (a : ℕ) (ha : stream' v a = some .tail) :
    stream' v (a + 1) = none := by
  simp [stream', ha]

lemma nextStep_tail' {a : ℕ} (ha : stream' v (a + 1) = some .tail) :
    ∃ i₀ i₁ l m, stream' v a = some (.nextVertex i₀ i₁ l m) := by
  unfold stream' at ha
  split at ha
  · rename_i _ i₀ i₁ m hm
    grind
  · trivial

lemma nextStep_nextVertex {a j₀ l : ℕ} {j₁} {m : ℝ}
    (ha : stream' v a = some (.nextVertex j₀ j₁ l m)) :
    ∃ i₀ i₁, nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m := by
  unfold stream' at ha
  split at ha
  · split at ha
    · simp only [Option.some.injEq, reduceCtorEq] at ha
    · simp only [Option.some.injEq] at ha
      exact ⟨_, _, ha⟩
  · split at ha
    · simp only [Option.some.injEq] at ha
      exact ⟨_, _, ha⟩
    · trivial

lemma nextStep_nextVertex' {a j₀ l' : ℕ} {j₁ : Γ} {m' : ℝ}
    (ha : stream' v (a + 1) = some (.nextVertex j₀ j₁ l' m')) :
    ∃ i₀ i₁ l m, stream' v a = some (.nextVertex i₀ i₁ l m) := by
  unfold stream' at ha
  split at ha
  · rename_i _ i₀ i₁ m hm
    grind
  · trivial

lemma nextStep_nextVertex'' {a i₀ j₀ l l' : ℕ} {i₁ j₁ : Γ} {m m' : ℝ}
    (ha : stream' v (a + 1) = some (.nextVertex j₀ j₁ l' m'))
    (h : stream' v a = some (.nextVertex i₀ i₁ l m)) :
  nextStep v i₀ i₁ = .nextVertex j₀ j₁ l' m' := by
  unfold stream' at ha
  simp only [h, Option.some.injEq] at ha
  exact ha

end NewtonPolygon₀.ConstructionAPI

/-- Corresponding slopes to `Step Γ`. -/
def slopes : Step Γ → WithBotTop ℝ
  | .tail => ⊤
  | .unboundedBelow => ⊥
  | .limitingRay m => m
  | .infiniteRay m => m
  | .nextVertex _ _ _ m => m

/-- Raising slopes to `Option (Step Γ)`. -/
def slopes' : Option (Step Γ) → WithBotTop ℝ
  | some S => slopes S
  | none => ⊤

/-- The sequence of slopes of a `stream'`. -/
noncomputable
def stream'_slopes : ℕ → WithBotTop ℝ :=
  fun a => slopes' (stream' (Γ := Γ) v a)

/-- The sequence of lengths of a `stream'`. -/
noncomputable
def stream'_lengths : ℕ → WithTop ℕ :=
  fun a => match stream' v a with
    | none => 0
    | some step => match step with
      | .tail => 0
      | .unboundedBelow => 0
      | .limitingRay _ => ⊤
      | .infiniteRay _ => ⊤
      | .nextVertex _ _ l _ => l

section nextVertexAPI

lemma nextVertex_bddBelow (v : ℕ → WithTop Γ) {i₀ j₀ l : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) :
    BddBelow (slopeSet v i₀ i₁) := by
  simp_rw [nextStep] at h
  grind

lemma nextVertex_finite (v : ℕ → WithTop Γ) {i₀ j₀ l : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) :
    (achievingSet v i₀ i₁ (sInf (slopeSet v i₀ i₁))).Finite := by
  rw [nextStep] at h
  split_ifs at h with _ _ h1 h2
  grind

lemma nextVertex_nonEmpty (v : ℕ → WithTop Γ) {i₀ j₀ l : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) :
    (achievingSet v i₀ i₁ (sInf (slopeSet v i₀ i₁))).Nonempty := by
  rw [nextStep] at h
  split_ifs at h with _ _ hm
  simp only [↓existsAndEq, and_true] at hm
  use Classical.choose hm
  simp_rw [achievingSet]
  grind

lemma nextVertex_j₀_eq_max (v : ℕ → WithTop Γ) {i₀ j₀ l : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) : j₀ =
    (nextVertex_finite v h).toFinset.max' ((nextVertex_finite v  h).toFinset_nonempty.mpr
    (nextVertex_nonEmpty v h)) := by
  simp_rw [nextStep] at h
  split_ifs at h with _ _ H
  split at h
  · trivial
  · grind

lemma nextVertex_j₀Mem (v : ℕ → WithTop Γ) {i₀ j₀ l : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) :
    j₀ ∈ achievingSet v i₀ i₁ (sInf (slopeSet v i₀ i₁)) := by
  have : j₀ ∈ (nextVertex_finite v h).toFinset := by
    simp_rw [nextVertex_j₀_eq_max v h]
    exact Finset.max'_mem _ _
  simp only [Set.Finite.mem_toFinset] at this
  exact this

lemma nextVertex_l_eq (v : ℕ → WithTop Γ) {i₀ j₀ l : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) : l = j₀ - i₀ := by
  simp_rw [nextStep] at h
  grind

lemma nextVertex_lt (v : ℕ → WithTop Γ) {i₀ j₀ l : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) : i₀ < j₀ := by
  have := nextVertex_j₀Mem v h
  simp_rw [achievingSet] at this
  grind

lemma nextVertex_j₁_eq (v : ℕ → WithTop Γ) {i₀ j₀ l : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) : v j₀ = j₁ := by
  simp_rw [nextStep] at h
  split_ifs at h
  aesop

lemma nextVertex_j₀Finite (v : ℕ → WithTop Γ) {i₀ j₀ l : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) : finite v j₀ := by
  have := nextVertex_j₁_eq v h
  simp_all [finite]

lemma nextVertex_slope_eq_sInf (v : ℕ → WithTop Γ) {i₀ j₀ l : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) :
    slopeReal i₀ j₀ i₁ j₁ = sInf (slopeSet v i₀ i₁) := by
  obtain ⟨hij, finj, j', hj', fin⟩ := nextVertex_j₀Mem v h
  simp_all [nextVertex_j₁_eq v h]

lemma nextVertex_slope_eq_sInf' (v : ℕ → WithTop Γ) {i₀ j₀ l : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) :
    m = slopeReal i₀ j₀ i₁ j₁ := by
  have := nextVertex_slope_eq_sInf v h
  simp_rw [nextStep] at h
  split_ifs at h with _ _ H
  grind

lemma nextVertex_slope_eq_sInf'' (v : ℕ → WithTop Γ) {i₀ j₀ l : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) :
    m = sInf (slopeSet v i₀ i₁) := by
  simpa [← nextVertex_slope_eq_sInf v h] using nextVertex_slope_eq_sInf' v h

end nextVertexAPI

section infiniteRayAPI

lemma infiniteRay_bddBelow (v : ℕ → WithTop Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .infiniteRay m) :
    BddBelow (slopeSet v i₀ i₁) := by
  simp_rw [nextStep] at h
  grind

lemma infiniteRay_nonempty (v : ℕ → WithTop Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .infiniteRay m) :
    (achievingSet v i₀ i₁ m).Nonempty := by
  simp_rw [nextStep] at h
  split_ifs at h
  · simp_all only [Step.infiniteRay.injEq]
    rename_i _ _ _ fin
    exact Set.Infinite.nonempty fin
  · aesop

lemma infiniteRay_slope_eq_sInf (v : ℕ → WithTop Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .infiniteRay m) :
    m = sInf (slopeSet v i₀ i₁) := by
  simp_rw [nextStep] at h
  split_ifs at h
  · simp only [Step.infiniteRay.injEq] at h
    rename_i _ _ t _
    convert Classical.choose_spec t
    aesop
  · aesop

lemma infiniteRay_ex (v : ℕ → WithTop Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .infiniteRay m) :
    ∃ j₀ : ℕ, j₀ > i₀ ∧ finite v j₀ ∧ ∃ j₁ : Γ, v j₀ = j₁ ∧  m = slopeReal i₀ j₀ i₁ j₁ := by
  obtain ⟨_, b⟩ := infiniteRay_nonempty v h
  simp_rw [achievingSet] at b
  aesop

end infiniteRayAPI

section limitingRayAPI

lemma limitingRay_bddBelow (v : ℕ → WithTop Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .limitingRay m) :
    BddBelow (slopeSet v i₀ i₁) := by
  simp_rw [nextStep] at h
  grind

lemma limitingRay_nonempty (v : ℕ → WithTop Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .limitingRay m) : (slopeSet v i₀ i₁).Nonempty := by
  simp_rw [nextStep] at h
  split at h
  · trivial
  · rename_i fin
    exact Set.nonempty_iff_ne_empty.mpr fin

lemma limitingRay_slope_eq_sInf (v : ℕ → WithTop Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .limitingRay m) : m = sInf (slopeSet v i₀ i₁) := by
  simp_rw [nextStep] at h
  split_ifs at h
  all_goals aesop

end limitingRayAPI

lemma succSlope_le_Slope {a₀ a₁ a₂ : ℝ} {b₀ b₁ b₂ : ℝ} (ha1 : a₀ < a₁) (ha2 : a₁ < a₂)
    (hab : (b₂ - b₁) / (a₂ - a₁) ≤ (b₁ - b₀) / (a₁ - a₀)) :
    (b₂ - b₀) / (a₂ - a₀) ≤ (b₁ - b₀) / (a₁ - a₀) := by
  have : b₂ ≤ b₀ + (b₁ - b₀) / (a₁ - a₀) * (a₂ - a₀) := by
    have h : b₂ = b₁ + (b₂ - b₁) / (a₂ - a₁) * (a₂ - a₁) := by grind
    have : b₀ + (b₁ - b₀) / (a₁ - a₀) * (a₂ - a₀) = b₁ + (b₁ - b₀) / (a₁ - a₀) * (a₂ - a₁) := by
      grind
    rw [this, h]
    simp only [add_le_add_iff_left, ge_iff_le]
    exact mul_le_mul_of_nonneg_right hab (by grind)
  rw [add_comm, ← tsub_le_iff_right] at this
  rw [div_le_iff₀' (by grind), mul_comm]
  grind

lemma succSlope_lt_Slope {a₀ a₁ a₂ : ℝ} {b₀ b₁ b₂ : ℝ} (ha1 : a₀ < a₁) (hb2 : a₁ < a₂)
    (hab : (b₂ - b₁) / (a₂ - a₁) < (b₁ - b₀) / (a₁ - a₀)) :
    (b₂ - b₀) / (a₂ - a₀) < (b₁ - b₀) / (a₁ - a₀) := by
  have : b₂ < b₀ + (b₁ - b₀) / (a₁ - a₀) * (a₂ - a₀) := by
    have h : b₂ = b₁ + (b₂ - b₁) / (a₂ - a₁) * (a₂ - a₁) := by grind
    have : b₀ + (b₁ - b₀) / (a₁ - a₀) * (a₂ - a₀) = b₁ + (b₁ - b₀) / (a₁ - a₀) * (a₂ - a₁) := by
      grind
    rw [this, h]
    simp only [add_lt_add_iff_left, gt_iff_lt]
    exact mul_lt_mul_of_pos_right hab (by grind)
  rw [div_lt_iff₀' (by grind), mul_comm]
  grind

lemma slopes_increasing_limitingRay {i₀ j₀ l : ℕ} {i₁ j₁ : Γ} {m m' : ℝ}
    (h1 : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m)
    (h2 : nextStep v j₀ j₁ = .limitingRay m') : m ≤ m':= by
  simp_rw [nextVertex_slope_eq_sInf'' v h1, limitingRay_slope_eq_sInf v h2]
  refine le_csInf (limitingRay_nonempty v h2) ?_
  by_contra
  simp only [not_forall, not_le] at this
  obtain ⟨n, ⟨k₀, hk₀, k₀_fin, k₁, hk₁, hn⟩, n_lt⟩ := this
  suffices slopeReal i₀ k₀ i₁ k₁ < sInf (slopeSet v i₀ i₁) by
    have k₀_in : k₀ ∈ achievingSet v i₀ i₁ (sInf (slopeSet v i₀ i₁)) := by
      refine ⟨(nextVertex_lt v h1).trans hk₀, k₀_fin, k₁, hk₁, ?_⟩
      have : slopeReal i₀ k₀ i₁ k₁ ∈ (slopeSet v i₀ i₁) := by
        exact ⟨k₀, (nextVertex_lt v h1).trans hk₀, k₀_fin, k₁, hk₁, rfl⟩
      grind [csInf_le (nextVertex_bddBelow v h1) this]
    have : k₀ ≤ j₀ := by
      simpa [nextVertex_j₀_eq_max v h1] using Finset.le_max' _ _
        ((nextVertex_finite v h1).mem_toFinset.mpr k₀_in)
    grind
  simp_rw [hn, ← nextVertex_slope_eq_sInf v h1, slopeReal] at n_lt ⊢
  exact succSlope_lt_Slope (Nat.cast_lt.mpr (nextVertex_lt v h1)) (Nat.cast_lt.mpr hk₀) n_lt

lemma slopes_increasing_infiniteRay {i₀ j₀ l : ℕ} {i₁ j₁ : Γ} {m m' : ℝ}
    (h1 : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) (h2 : nextStep v j₀ j₁ = .infiniteRay m') :
    m < m' := by
  obtain ⟨k₀, hk₀, k₀_fin, k₁, hk₁, rfl⟩ := infiniteRay_ex v h2
  simp_rw [nextVertex_slope_eq_sInf' v h1, slopeReal]
  by_contra
  simp only [not_lt] at this
  suffices h : slopeReal i₀ k₀ i₁ k₁ ≤ sInf (slopeSet v i₀ i₁) by
    have k₀_in : k₀ ∈ achievingSet v i₀ i₁ (sInf (slopeSet v i₀ i₁)) := by
      refine ⟨(nextVertex_lt v h1).trans hk₀, k₀_fin, k₁, hk₁, ?_⟩
      have : slopeReal i₀ k₀ i₁ k₁ ∈ (slopeSet v i₀ i₁) := by
        exact ⟨k₀, (nextVertex_lt v h1).trans hk₀, k₀_fin, k₁, hk₁, rfl⟩
      grind [csInf_le (nextVertex_bddBelow v h1) this]
    have : k₀ ≤ j₀ := by
      simpa [nextVertex_j₀_eq_max v h1] using Finset.le_max' _ _
        ((nextVertex_finite v h1).mem_toFinset.mpr k₀_in)
    grind
  simpa [← nextVertex_slope_eq_sInf v h1, slopeReal] using succSlope_le_Slope
    (Nat.cast_lt.mpr (nextVertex_lt v h1)) (Nat.cast_lt.mpr hk₀) this

lemma slopes_increasing_nextVertex {i₀ j₀ k₀ l l' : ℕ} {i₁ j₁ k₁ : Γ} {m m' : ℝ}
    (h1 : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m)
    (h2 : nextStep v j₀ j₁ = .nextVertex k₀ k₁ l' m') : m < m' := by
  by_contra
  suffices slopeReal i₀ k₀ i₁ k₁ ≤ sInf (slopeSet v i₀ i₁) by
    have k₀_in : k₀ ∈ achievingSet v i₀ i₁ (sInf (slopeSet v i₀ i₁)) := by
      refine ⟨(nextVertex_lt v h1).trans (Nat.cast_lt.mpr (nextVertex_lt v h2)),
        nextVertex_j₀Finite v h2, k₁, nextVertex_j₁_eq v h2, ?_⟩
      have : slopeReal i₀ k₀ i₁ k₁ ∈ (slopeSet v i₀ i₁) := by
        exact ⟨k₀, (nextVertex_lt v h1).trans (Nat.cast_lt.mpr (nextVertex_lt v h2)),
          nextVertex_j₀Finite v h2, k₁, nextVertex_j₁_eq v h2, rfl⟩
      grind [csInf_le (nextVertex_bddBelow v h1) this]
    have : k₀ ≤ j₀ := by
      simpa [nextVertex_j₀_eq_max v h1] using Finset.le_max' _ _
        ((nextVertex_finite v h1).mem_toFinset.mpr k₀_in)
    grind [nextVertex_lt v h2]
  simp_rw [not_lt, ← nextVertex_slope_eq_sInf v h1, nextVertex_slope_eq_sInf' v h1,
    nextVertex_slope_eq_sInf' v h2, slopeReal] at ⊢ this
  exact succSlope_le_Slope (Nat.cast_lt.mpr (nextVertex_lt v h1))
    (Nat.cast_lt.mpr (nextVertex_lt v h2)) this

section unboundedBelowAPI

lemma nextStep_unboundedBelow (a : ℕ) (ha : stream' v a = some .unboundedBelow)
    : stream' v (a + 1) = none := by
  simp [stream', ha]

lemma unboundedBelow {i₀ : ℕ} {i₁ : Γ} (h : nextStep v i₀ i₁ = Step.unboundedBelow) :
    ¬ (BddBelow (slopeSet v i₀ i₁)) := by
  simp_rw [nextStep] at h
  split at h
  · trivial
  split at h
  · rename_i _ fin
    exact fin
  · split_ifs at h
    grind

lemma nextStep_unboundedBelow' (a : ℕ) : stream' v (a + 1) ≠
    some (.unboundedBelow) := by
  unfold stream'
  split
  · rename_i _ i₀ i₁ l m h
    by_contra
    simp only [Option.some.injEq] at this
    obtain ⟨p₀, p₁, T⟩ := nextStep_nextVertex v h
    apply unboundedBelow v this
    refine ⟨m, ?_⟩
    rintro x ⟨k₀, hk₀, k₀_fin, k₁, hk₁, rfl⟩
    by_contra hlt
    simp_rw [nextVertex_slope_eq_sInf' v T, not_le] at hlt
    have : slopeReal p₀ k₀ p₁ k₁ < slopeReal p₀ i₀ p₁ i₁ :=
      succSlope_lt_Slope (Nat.cast_lt.mpr (nextVertex_lt v T)) (Nat.cast_lt.mpr hk₀) hlt
    have : slopeReal p₀ i₀ p₁ i₁ ≤ slopeReal p₀ k₀ p₁ k₁ := by
      simpa [← nextVertex_slope_eq_sInf v T] using csInf_le (nextVertex_bddBelow v T)
        ⟨k₀, (nextVertex_lt v T).trans hk₀, k₀_fin, k₁, hk₁, rfl⟩
    grind
  · simp

end unboundedBelowAPI

section stream'API

lemma stream'_none_of_le {a b : ℕ} (hab : a ≤ b) (ha : stream' v a = none) :
    stream' v b = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction k with
  | zero => exact ha
  | succ k ih => exact nextStep_none v (a + k) ih

lemma stream'_ne_none_of_le {a b : ℕ} (hab : a ≤ b) (hb : stream' v b ≠ none) :
    stream' v a ≠ none :=
  fun ha ↦ hb (stream'_none_of_le v hab ha)

lemma stream'_nextVertex_of_succ_ne_none {a : ℕ} (ha : stream' v (a + 1) ≠ none) :
    ∃ i₀ i₁ l m, stream' v a = some (.nextVertex i₀ i₁ l m) := by
  cases t : stream' v (a + 1) with
  | none => exact absurd t ha
  | some S =>
    cases S with
    | tail => exact nextStep_tail' v t
    | unboundedBelow => exact absurd t (nextStep_unboundedBelow' v a)
    | limitingRay m => exact nextStep_limitingRay' v t
    | infiniteRay m => exact nextStep_infiniteRay' v t
    | nextVertex j₀ j₁ l m => exact nextStep_nextVertex' v t

lemma stream'_nextVertex_of_lt {b a : ℕ} (hb : b < a) (ha : stream' v a ≠ none) :
    ∃ i₀ i₁ l m, stream' v b = some (.nextVertex i₀ i₁ l m) :=
  stream'_nextVertex_of_succ_ne_none v (stream'_ne_none_of_le v hb ha)

open Classical in
/-- The sequence of slopes are strictly increasing while they exist -
  except possibly when the final output is a limiting ray, where equality is possible:
  e.g. f(x) = 1 + x + p⁻¹ ∑_{n = 2}^∞ x^n has two slopes of gradient 0. -/
lemma stream'_slopes_increasing (a : ℕ) :
    if stream' v (a + 1) = none then true
    else if ∃ m, stream' v (a + 1) = some (.limitingRay m) then
      stream'_slopes v a ≤ stream'_slopes v (a + 1)
    else
      stream'_slopes v a < stream'_slopes v (a + 1) := by
  split_ifs with h hh
  · trivial
  · obtain ⟨_, hm'⟩ := hh
    obtain ⟨_, _, _, _, hm⟩ := nextStep_limitingRay' v hm'
    simp_rw [stream'_slopes, slopes', hm', hm, slopes, WithBotTop.coe_le_coe]
    obtain ⟨_, _, h1⟩ := nextStep_nextVertex v hm
    exact slopes_increasing_limitingRay v h1 (nextStep_limitingRay'' v hm' hm)
  · simp_rw [stream'_slopes]
    cases t : (stream' v (a + 1))
    · grind
    · rename_i val
      cases val
      · obtain ⟨_, _, _, _, hm⟩ := nextStep_tail' v t
        simpa [hm, slopes', slopes] using compareOfLessAndEq_eq_lt.mp rfl
      · grind [nextStep_unboundedBelow' v a]
      · grind
      · obtain ⟨_, _, _, _, hm⟩ := nextStep_infiniteRay' v t
        obtain ⟨_, _, h1⟩ := nextStep_nextVertex v hm
        simp_rw [slopes', hm, slopes, WithBotTop.coe_lt_coe]
        exact slopes_increasing_infiniteRay v h1 (nextStep_infiniteRay'' v t hm)
      · rename_i k₀ k₁ l m
        obtain ⟨_, _, _, _, hm⟩ := nextStep_nextVertex' v t
        obtain ⟨_, _, h1⟩ := nextStep_nextVertex v hm
        simp_rw [slopes', hm, slopes, WithBotTop.coe_lt_coe]
        exact slopes_increasing_nextVertex v h1 (nextStep_nextVertex'' v t hm)

lemma stream'_slopes_mono (n : ℕ) : stream'_slopes v n ≤ stream'_slopes v (n + 1) := by
  have := stream'_slopes_increasing v n
  split_ifs at this with h1 h2
  · unfold stream'_slopes
    rw [h1]
    exact le_top
  · exact this
  · exact le_of_lt this

open Classical in
/-- The number of genuine segments of stream'. -/
noncomputable
def stream'_numSegments : WithTop ℕ :=
  if h : ∃ a, stream' v a = some .tail then (Nat.find h : WithTop ℕ)
  else if h' : ∃ a, stream' v a = none then (Nat.find h' : WithTop ℕ)
  else ⊤

lemma stream'_nextVertex_of_lt_numSegments {n : ℕ} (h : (n : WithTop ℕ) + 1 < stream'_numSegments v)
    : ∃ i₀ i₁ l m, stream' v n = some (.nextVertex i₀ i₁ l m) := by
  classical
  unfold stream'_numSegments at h
  split_ifs at h with ht hn
  · have hfn : n + 1 < Nat.find ht := by exact_mod_cast h
    exact stream'_nextVertex_of_lt v (show n < Nat.find ht by exact Nat.lt_of_succ_lt hfn)
      (by simp [Nat.find_spec ht])
  · have hfn : n + 1 < Nat.find hn := by exact_mod_cast h
    exact stream'_nextVertex_of_succ_ne_none v
      (Nat.find_min hn (show n + 1 < Nat.find hn by omega))
  · exact stream'_nextVertex_of_succ_ne_none v (fun hh ↦ hn ⟨n + 1, hh⟩)

lemma stream'_slopes_junk {n : ℕ} (h : stream'_numSegments v ≤ (n : WithTop ℕ)) :
    stream'_slopes v n = ⊤ := by
  classical
  rw [stream'_numSegments] at h
  split_ifs at h with ht hn
  · rcases eq_or_lt_of_le (by exact_mod_cast h) with rfl | hlt
    · simp [stream'_slopes, Nat.find_spec ht, slopes', slopes]
    · simp [stream'_slopes, stream'_none_of_le _ hlt (nextStep_tail v _ (Nat.find_spec ht)),
        slopes']
  · simp [stream'_slopes, stream'_none_of_le v (by exact_mod_cast h) (Nat.find_spec hn), slopes']
  · exact absurd (top_le_iff.mp h) WithTop.coe_ne_top

lemma stream'_lengths_junk {n : ℕ} (h : stream'_numSegments v ≤ (n : WithTop ℕ)) :
    stream'_lengths v n = 0 := by
  classical
  rw [stream'_numSegments] at h
  split_ifs at h with ht hn
  · rcases eq_or_lt_of_le (by exact_mod_cast h) with rfl | hlt
    · simp [stream'_lengths, Nat.find_spec ht]
    · simp [stream'_lengths, stream'_none_of_le v hlt (nextStep_tail v _ (Nat.find_spec ht))]
  · simp [stream'_lengths, stream'_none_of_le v (by exact_mod_cast h) (Nat.find_spec hn)]
  · exact absurd (top_le_iff.mp h) WithTop.coe_ne_top

lemma stream'_slopes_nonFinal {n : ℕ} (h : (n : WithTop ℕ) + 1 < stream'_numSegments v) :
    ∃ a : ℝ, stream'_slopes v n = some (some a) := by
  obtain ⟨_, _, _, m, hm⟩ := stream'_nextVertex_of_lt_numSegments v h
  exact ⟨m, by rw [stream'_slopes, hm]; rfl⟩

lemma stream'_lengths_nonFinal {n : ℕ} (h : (n : WithTop ℕ) + 1 < stream'_numSegments v) :
    ∃ a : ℕ, a ≠ 0 ∧ stream'_lengths v n = some a := by
  obtain ⟨_, _, l, _, hm⟩ := stream'_nextVertex_of_lt_numSegments v h
  obtain ⟨_, _, hp⟩ := nextStep_nextVertex v hm
  exact ⟨l, by grind [nextVertex_l_eq v hp, nextVertex_lt v hp], by rw [stream'_lengths, hm]; rfl⟩

lemma stream'_slopes_final {n : ℕ} (h1 : (n : WithTop ℕ) + 1 = stream'_numSegments v)
    (h2 : stream'_slopes v n = ⊤ ∨ stream'_slopes v n = ⊥) : stream'_numSegments v = 1 := by
  classical
  rw [← h1]
  suffices n = 0 by simp [this]
  rw [stream'_numSegments] at h1
  split_ifs at h1 with ht hn
  · have := by exact_mod_cast h1
    obtain ⟨_, _, _, _, hm⟩ := stream'_nextVertex_of_lt v
      (show n < Nat.find ht by grind) (by simp [Nat.find_spec ht])
    simp [stream'_slopes, hm, slopes', slopes] at h2
  · have := by exact_mod_cast h1
    cases t : stream' v n with
    | none => exact absurd t (Nat.find_min hn (show n < Nat.find hn by omega))
    | some S =>
      cases S with
      | tail => exact absurd ⟨n, t⟩ ht
      | unboundedBelow =>
        cases n with
        | zero => rfl
        | succ a => exact absurd t (nextStep_unboundedBelow' v a)
      | limitingRay m => simp [stream'_slopes, t, slopes', slopes] at h2
      | infiniteRay m => simp [stream'_slopes, t, slopes', slopes] at h2
      | nextVertex i₀ i₁ l m => simp [stream'_slopes, t, slopes', slopes] at h2
  · simp at h1

lemma stream'_lengths_final {n : ℕ} (h1 : (n : WithTop ℕ) + 1 = stream'_numSegments v)
    (h2 : stream'_lengths v n = 0) : stream'_numSegments v = 1 := by
  classical
  rw [← h1]
  suffices n = 0 by simp [this]
  rw [stream'_numSegments] at h1
  split_ifs at h1 with ht hn
  · have := by exact_mod_cast h1
    obtain ⟨_, _, l, _, hm⟩ := stream'_nextVertex_of_lt v
      (show n < Nat.find ht by omega) (by simp [Nat.find_spec ht])
    obtain ⟨p₀, p₁, hp⟩ := nextStep_nextVertex v hm
    simp only [stream'_lengths, hm] at h2
    have := by exact_mod_cast h2
    grind [nextVertex_l_eq v hp, nextVertex_lt v hp]
  · have := by exact_mod_cast h1
    cases t : stream' v n with
    | none => exact absurd t (Nat.find_min hn (show n < Nat.find hn by omega))
    | some S =>
      cases S with
      | tail => exact absurd ⟨n, t⟩ ht
      | unboundedBelow =>
        cases n with
        | zero => rfl
        | succ a => exact absurd t (nextStep_unboundedBelow' v a)
      | limitingRay m =>
        simp only [stream'_lengths, t] at h2
        exact absurd h2 (by decide)
      | infiniteRay m =>
        simp only [stream'_lengths, t] at h2
        exact absurd h2 (by decide)
      | nextVertex i₀ i₁ l m =>
        obtain ⟨p₀, p₁, hp⟩ := nextStep_nextVertex v t
        simp only [stream'_lengths, t] at h2
        have := by exact_mod_cast h2
        grind [nextVertex_l_eq v hp, nextVertex_lt v hp]
  · simp at h1

end stream'API

theorem IsSeq : Stream'.IsSeq (stream' v) :=
  fun _ ↦ by grind [stream']

/-- The `NewtonPolygon₀.Construction.stream'` packaged as a Seq. -/
noncomputable
def seq : Stream'.Seq (Step Γ) :=
  ⟨stream' v, IsSeq v⟩

lemma stream'_lt_length_neq_none (n : ℕ) (h : ↑n + 1 < (seq v).length') :
    stream' v (n + 1) ≠ none := by
  by_contra
  suffices (seq v).length' ≤ n + 1 by
    grind
  have h : (seq v).Terminates := by
    use n + 1
    aesop
  simp only [Stream'.Seq.length', h, ↓reduceDIte, ge_iff_le]
  suffices (seq v).length h ≤ n + 1 by
    rw [← Nat.cast_one, ← Nat.cast_add]
    exact ENat.natCast_le_natCast.mpr this
  exact Stream'.Seq.length_le_iff.mpr this

lemma stream'_ge_length_eq_none (n : ℕ) (h : (seq v).length' ≤ ↑n) :
    stream' v n = none := by
  simp_rw [Stream'.Seq.length'] at h
  split_ifs at h
  · simp only [Nat.cast_le] at h
    exact Stream'.Seq.length_le_iff.mp h
  · aesop

/-- The Newton polygon construction for `v` terminates after finitely many steps. -/
def IsFinite : Prop := (seq v).Terminates

/-- Finite `NewtonPolygon₀.Construction.seq` packaged as a list. -/
noncomputable
def list (h : IsFinite v) : List (Step Γ) :=
    Stream'.Seq.toList (seq v) h

end

end NewtonPolygon₀.Construction
