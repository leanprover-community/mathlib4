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
  else if hInf : (achievingSet v i₀ i₁ (Classical.choose (of_not_not hm))).Infinite then
    .infiniteRay (Classical.choose (of_not_not hm))
  else
    have hNonempty : (achievingSet v i₀ i₁ (Classical.choose (of_not_not hm))).Nonempty := by
      simp only [↓existsAndEq, and_true] at hm
      use Classical.choose (of_not_not hm)
      simp_rw [achievingSet]
      grind
    let j₀ := (Set.not_infinite.mp hInf).toFinset.max'
      ((Set.not_infinite.mp hInf).toFinset_nonempty.mpr hNonempty)
    match v j₀ with
      | ⊤ => .tail
      | (j₁ : Γ) => .nextVertex j₀ j₁ (j₀ - i₀) (Classical.choose (of_not_not hm))

/-- Find the first index with finite valuation, starting from a given position. -/
noncomputable
def findFirstFinite (startIdx : ℕ) : Option (ℕ × Γ) := open Classical in
  if h : ∃ i ≥ startIdx, finite v i then
    let i := Nat.find h
    match v i with
    | ⊤ => none  -- contradicts finiteness
    | (val : Γ) => some (i, val)
  else
    none

/-- The full Newton Polygon. -/
noncomputable
def newtonPolygon : Stream' (Option (Step Γ))
  | 0 => match findFirstFinite v 0 with
    | none => some .tail
    | some (i, v_i) => nextStep v i v_i
  | n + 1 =>
    open Classical in
    match newtonPolygon n with
      | some (.nextVertex j₀ j₁ _ _) => nextStep v j₀ j₁
      | _ => none

section newtonPolygonAPI

lemma nextStep_none (a : ℕ) (ha : newtonPolygon v a = none) :
    newtonPolygon v (a + 1) = none := by
  simp [newtonPolygon, ha]

lemma nextStep_limitingRay (a : ℕ) (m : ℝ) (ha : newtonPolygon v a = some (.limitingRay m)) :
    newtonPolygon v (a + 1) = none := by
  simp [newtonPolygon, ha]

lemma nextStep_limitingRay' {a : ℕ} {m : ℝ} (ha : newtonPolygon v (a + 1) = some (.limitingRay m)) :
    ∃ i₀ i₁ l m, newtonPolygon v a = some (.nextVertex i₀ i₁ l m) := by
  unfold newtonPolygon at ha
  split at ha
  · rename_i _ i₀ i₁ m hm
    grind
  · trivial

lemma nextStep_limitingRay'' {a i₀ l : ℕ} {i₁ : Γ} {m n : ℝ}
    (ha : newtonPolygon v (a + 1) = some (.limitingRay m))
    (h : newtonPolygon v a = some (.nextVertex i₀ i₁ l n)) : nextStep v i₀ i₁ = .limitingRay m := by
  unfold newtonPolygon at ha
  simp_rw [h, Option.some.injEq] at ha
  exact ha

lemma nextStep_infiniteRay (a : ℕ) (m : ℝ) (ha : newtonPolygon v a = some (.infiniteRay m)) :
    newtonPolygon v (a + 1) = none := by
  simp [newtonPolygon, ha]

lemma nextStep_infiniteRay' {a : ℕ} {m : ℝ} (ha : newtonPolygon v (a + 1) = some (.infiniteRay m)) :
    ∃ i₀ i₁ l n, newtonPolygon v a = some (.nextVertex i₀ i₁ l n) := by
  unfold newtonPolygon at ha
  split at ha
  · rename_i _ i₀ i₁ m hm
    grind
  · trivial

lemma nextStep_infiniteRay'' {a i₀ l : ℕ} {i₁ : Γ} {m n : ℝ}
    (ha : newtonPolygon v (a + 1) = some (.infiniteRay m))
    (h : newtonPolygon v a = some (.nextVertex i₀ i₁ l n)) : nextStep v i₀ i₁ = .infiniteRay m := by
  unfold newtonPolygon at ha
  simp_rw [h, Option.some.injEq] at ha
  exact ha

lemma nextStep_tail (a : ℕ) (ha : newtonPolygon v a = some .tail) :
    newtonPolygon v (a + 1) = none := by
  simp [newtonPolygon, ha]

lemma nextStep_tail' {a : ℕ} (ha : newtonPolygon v (a + 1) = some .tail) :
    ∃ i₀ i₁ l m, newtonPolygon v a = some (.nextVertex i₀ i₁ l m) := by
  unfold newtonPolygon at ha
  split at ha
  · rename_i _ i₀ i₁ m hm
    grind
  · trivial

lemma nextStep_nextVertex {a j₀ l : ℕ} {j₁} {m : ℝ}
    (ha : newtonPolygon v a = some (.nextVertex j₀ j₁ l m)) :
    ∃ i₀ i₁, nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m := by
  unfold newtonPolygon at ha
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
    (ha : newtonPolygon v (a + 1) = some (.nextVertex j₀ j₁ l' m')) :
    ∃ i₀ i₁ l m, newtonPolygon v a = some (.nextVertex i₀ i₁ l m) := by
  unfold newtonPolygon at ha
  split at ha
  · rename_i _ i₀ i₁ m hm
    grind
  · trivial

lemma nextStep_nextVertex'' {a i₀ j₀ l l' : ℕ} {i₁ j₁ : Γ} {m m' : ℝ}
    (ha : newtonPolygon v (a + 1) = some (.nextVertex j₀ j₁ l' m'))
    (h : newtonPolygon v a = some (.nextVertex i₀ i₁ l m)) :
  nextStep v i₀ i₁ = .nextVertex j₀ j₁ l' m' := by
  unfold newtonPolygon at ha
  simp only [h, Option.some.injEq] at ha
  exact ha

end newtonPolygonAPI

/-- Corresponding slopes to `Step Γ`. -/
def slopes : Step Γ → WithTopBot ℝ
  | .tail => ⊤
  | .unboundedBelow => ⊥
  | .limitingRay m => m
  | .infiniteRay m => m
  | .nextVertex _ _ _ m => m

/-- Raising slopes to `Option (Step Γ)`. -/
def slopes' : Option (Step Γ) → WithTopBot ℝ
  | some S => slopes S
  | none => ⊥

/-- The sequence of slopes of a Newton polygon. -/
noncomputable
def newtonPolygon_slopes : ℕ → WithTopBot ℝ :=
  fun a => slopes' (newtonPolygon (Γ := Γ) v a)

/-- The sequence of lengths of a Newton polygon. -/
noncomputable
def newtonPolygon_lengths : ℕ → WithTop ℕ :=
  fun a => match newtonPolygon v a with
    | none => 0
    | some step => match step with
      | .tail => 0
      | .unboundedBelow => 0
      | .limitingRay _ => ⊤
      | .infiniteRay _ => ⊤
      | .nextVertex _ _ l _ => l


open Classical in
/-- The sequence of slopes of a Newton polygon are strictly increasing - except when the final
  output is a limiting ray, then equality is possible: e.g.
  f(x) = 1 + x + p⁻¹ ∑_{n = 2}^∞ x^n. -/
def newtonPolygon_slopes_increasing : Prop :=
  ∀ a : ℕ, if newtonPolygon v (a + 1) = none then
    true
  else if ∃ m, newtonPolygon v (a + 1) = some (.limitingRay m) then
    newtonPolygon_slopes v a ≤ newtonPolygon_slopes v (a + 1)
  else
    newtonPolygon_slopes v a < newtonPolygon_slopes v (a + 1)

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

lemma nextStep_unboundedBelow (a : ℕ) (ha : newtonPolygon v a = some .unboundedBelow) :
    newtonPolygon v (a + 1) = none := by
  simp [newtonPolygon, ha]

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

lemma nextStep_unboundedBelow' (a : ℕ) : newtonPolygon v (a + 1) ≠ some (.unboundedBelow) := by
  unfold newtonPolygon
  split
  · rename_i _ i₀ i₁ l m h
    by_contra
    simp only [Option.some.injEq] at this
    have := unboundedBelow v this
    have h := nextStep_nextVertex v h
    obtain ⟨_, _, T⟩ := h
    have contra := nextVertex_bddBelow v T

    sorry
  · simp

end unboundedBelowAPI

lemma newtonPolygon_slopes_increasing' : newtonPolygon_slopes_increasing v := by
  simp_rw [newtonPolygon_slopes_increasing]
  intro a
  split_ifs with h hh
  · obtain ⟨_, hm'⟩ := hh
    obtain ⟨_, _, _, _, hm⟩ := nextStep_limitingRay' v hm'
    simp_rw [newtonPolygon_slopes, slopes', hm', hm, slopes, WithTop.coe_le_coe, WithBot.coe_le_coe]
    obtain ⟨_, _, h1⟩ := nextStep_nextVertex v hm
    exact slopes_increasing_limitingRay v h1 (nextStep_limitingRay'' v hm' hm)
  · simp_rw [newtonPolygon_slopes]
    cases t : (newtonPolygon v (a + 1))
    · grind
    · rename_i val
      cases val
      · obtain ⟨_, _, _, _, hm⟩ := nextStep_tail' v t
        simp [hm, slopes', slopes]
      · grind [nextStep_unboundedBelow' v a] -- this is sorry'd for now
      · grind
      · obtain ⟨_, _, _, _, hm⟩ := nextStep_infiniteRay' v t
        obtain ⟨_, _, h1⟩ := nextStep_nextVertex v hm
        simp_rw [slopes', hm, slopes, WithTop.coe_lt_coe, WithBot.coe_lt_coe]
        exact slopes_increasing_infiniteRay v h1 (nextStep_infiniteRay'' v t hm)
      · rename_i k₀ k₁ l m
        obtain ⟨_, _, _, _, hm⟩ := nextStep_nextVertex' v t
        obtain ⟨_, _, h1⟩ := nextStep_nextVertex v hm
        simp_rw [slopes', hm, slopes, WithTop.coe_lt_coe, WithBot.coe_lt_coe]
        exact slopes_increasing_nextVertex v h1 (nextStep_nextVertex'' v t hm)



/- How we construct a `v` from a power series...

section PowerSeries

variable {R : Type*} [Semiring R]

noncomputable
def coeff_seq (f : PowerSeries R) (v : R → WithTop Γ) : ℕ → WithTop Γ :=
  fun i => v (PowerSeries.coeff i f)

end PowerSeries

-/

-- Post Zulip discussion

def newtonPolygon_IsSeq : Stream'.IsSeq (newtonPolygon v) := fun _ ↦ by grind [newtonPolygon]

noncomputable
def newtonPolygon_seq : Stream'.Seq (Step Γ) := ⟨newtonPolygon v, newtonPolygon_IsSeq v⟩

class FiniteNewtonPolygon where
  Terminates : Stream'.Seq.Terminates (newtonPolygon_seq v)

noncomputable
def finite_newtonPolygon (h : FiniteNewtonPolygon v) : List (Step Γ) :=
    Stream'.Seq.toList (newtonPolygon_seq v) h.Terminates

structure NewtonPolygon where
  support : WithTop ℕ
  slopes : ℕ → WithTopBot ℝ
  slopes_junk : ∀ n : ℕ, support ≤ n → slopes n = ⊥
  -- could choose ⊤, then increasing could just be for all n
  -- and the proof relies on seperating cases of n + 1 < support and not
  -- when not its _ ≤ ⊤ so true
  lengths : ℕ → WithTop ℕ
  lengths_junk : ∀ n : ℕ, support ≤ n → lengths n = 0
  increasing : ∀ n : ℕ, n + 1 < support → slopes n ≤ slopes (n + 1)

lemma newtonPolygon_lt_length_neq_none (n : ℕ) (h : ↑n + 1 < (newtonPolygon_seq v).length') :
    newtonPolygon v (n + 1) ≠ none := by
  by_contra
  suffices (newtonPolygon_seq v).length' ≤ n + 1 by
    grind
  have h : (newtonPolygon_seq v).Terminates := by
    use n + 1
    aesop
  simp only [Stream'.Seq.length', h, ↓reduceDIte, ge_iff_le]
  suffices (newtonPolygon_seq v).length h ≤ n + 1 by
    rw [← Nat.cast_one, ← Nat.cast_add]
    exact ENat.coe_le_coe.mpr this
  exact Stream'.Seq.length_le_iff.mpr this

lemma newtonPolygon_ge_length_eq_none (n : ℕ) (h : (newtonPolygon_seq v).length' ≤ ↑n) :
    newtonPolygon v n = none := by
  simp_rw [Stream'.Seq.length'] at h
  split_ifs at h
  · simp only [Nat.cast_le] at h
    exact Stream'.Seq.length_le_iff.mp h
  · aesop

noncomputable
def NP' : NewtonPolygon where
  support := Stream'.Seq.length' (newtonPolygon_seq v)
  slopes := newtonPolygon_slopes v
  slopes_junk :=
    fun n hn ↦ by simp [newtonPolygon_slopes, slopes', newtonPolygon_ge_length_eq_none v n hn]
  lengths := newtonPolygon_lengths v
  lengths_junk :=
    fun n hn ↦ by simp [newtonPolygon_lengths, newtonPolygon_ge_length_eq_none v n hn]
  increasing := by
    intro n hn
    have := newtonPolygon_slopes_increasing' v
    simp_rw [newtonPolygon_slopes_increasing] at this
    specialize this n
    simp only [(newtonPolygon_lt_length_neq_none v n hn), ↓reduceIte] at this
    split_ifs at this
    · exact this
    · exact le_of_lt this

variable (Γ) in
def IsNewtonPolygon (NP : NewtonPolygon) : Prop :=
  ∃ (v : ℕ → WithTop Γ), NP.slopes = newtonPolygon_slopes v ∧ NP.lengths = newtonPolygon_lengths v
