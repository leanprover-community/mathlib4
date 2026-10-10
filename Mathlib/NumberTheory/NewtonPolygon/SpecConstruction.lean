/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.NumberTheory.NewtonPolygon.OfSeq
public import Mathlib.NumberTheory.NewtonPolygon.Construction

/-!
# The constructed Newton polygon satisfies the geometric specification

**Existence** for `IsNewtonPolygonOf`: the polygon produced by the step algorithm of
`Mathlib/NumberTheory/NewtonPolygon/Construction.lean` (packaged as `NewtonPolygon₀.construction`)
is the lower convex hull of the points `(k, v k)`.

Two hypotheses are genuinely needed:

* `∃ i, v i ≠ ⊤` — there is at least one point (otherwise no anchored polygon exists);
* `IsAdmissible v` — every slope set is bounded below. Without it no polygon lies below the
  points at all (e.g. `v k = -k²` over `Γ = ℝ`): the hull "is vertical". The algorithm then
  returns the junk `unboundedBelow` step and the spec is unsatisfiable
  (`IsNewtonPolygonOf.bddBelow` below is the converse: the spec forces admissibility at the
  anchor).

The proof of `height_le` ("below the points") is the segment-by-segment line bound. The proof of
`isGreatest` is the chord argument: a competitor is convex (`NewtonPolygon₀.heightFun_chord`),
sits below the points, and the constructed polygon touches the points at its vertices, so on each
segment the competitor is below its own chord, which is below the constructed segment; final rays
are handled by an ε-approximation along slopes tending to the infimum.
-/

@[expose] public section

namespace NewtonPolygon₀.construction

variable {Γ : Type*} [CommSemiring Γ] [Algebra Γ ℝ] (v : ℕ → WithTop Γ)

/-! ### Admissibility -/

/-- A point sequence is *admissible* when every slope set out of one of its points is bounded
below. This is exactly the condition for a lower convex hull (equivalently, a nonvertical
supporting line) to exist. -/
def IsAdmissible : Prop :=
  ∀ (i₀ : ℕ) (i₁ : Γ), v i₀ = (i₁ : WithTop Γ) → BddBelow (slopeSet v i₀ i₁)

/-- Points lying on/above a single affine line form an admissible sequence. -/
lemma isAdmissible_of_affine_bound {m b : ℝ}
    (h : ∀ (k : ℕ) (a : Γ), v k = (a : WithTop Γ) → m * k + b ≤ algebraMap Γ ℝ a) :
    IsAdmissible v := by
  intro i₀ i₁ hvi
  -- the vertex itself lies on/above the line, at some height `m * i₀ + b + C` with `C ≥ 0`
  obtain ⟨C, hC0, hCeq⟩ : ∃ C : ℝ, 0 ≤ C ∧ algebraMap Γ ℝ i₁ = m * i₀ + b + C :=
    ⟨algebraMap Γ ℝ i₁ - (m * i₀ + b), by linarith [h i₀ i₁ hvi], by ring⟩
  -- every later point is at least `m * (k - i₀) - C` higher, and `k - i₀ ≥ 1`
  refine ⟨m - C, ?_⟩
  rintro s ⟨k, hk, -, a, hva, rfl⟩
  have hki : (0 : ℝ) < (k : ℝ) - i₀ := sub_pos.mpr (by exact_mod_cast hk)
  have h1 : (1 : ℝ) ≤ (k : ℝ) - (i₀ : ℝ) := by
    have : ((i₀ + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    push_cast at this
    linarith
  rw [slopeReal, le_div_iff₀ hki]
  have hkey : (m - C) * ((k : ℝ) - (i₀ : ℝ)) ≤ m * ((k : ℝ) - (i₀ : ℝ)) - C := by
    nlinarith [mul_nonneg hC0 (show (0 : ℝ) ≤ ((k : ℝ) - (i₀ : ℝ)) - 1 by linarith)]
  linarith [h k a hva]

/-- The specification forces admissibility at the anchor: slopes out of the starting vertex are
bounded below by the first unit slope. -/
lemma IsNewtonPolygonOf.bddBelow {P : NewtonPolygon₀ (Γ := Γ)} (h : IsNewtonPolygonOf v P)
    {k : ℕ} (hk : (k : ℤ) = P.starting_point.1) :
    BddBelow (slopeSet v k P.starting_point.2) := by
  refine ⟨WithBotTop.toReal (P.unitSlope 0), ?_⟩
  rintro s ⟨k', hk', -, a, hva, rfl⟩
  have hlt : P.starting_point.1 < (k' : ℤ) := by
    rw [← hk]
    exact_mod_cast hk'
  have hb := h.unitSlope_zero_mul_le hlt hva
  rw [show ((P.starting_point.1 : ℤ) : ℝ) = (k : ℝ) by rw [← hk]; push_cast; ring] at hb
  have hki : (0 : ℝ) < (k' : ℝ) - (k : ℝ) := sub_pos.mpr (by exact_mod_cast hk')
  rw [slopeReal, le_div_iff₀ hki]
  exact hb

/-! ### Line bounds out of an algorithm step

The geometric content of each step output: all later points lie on/above the line of the output
slope through the current vertex — strictly above beyond the chosen vertex (`nextVertex`), and
strictly above everywhere for a `limitingRay` (the infimum is not attained). These are the
`Construction.lean`-level generalisations of `step_slope_le` from `Test/test.lean`. -/

/-- Every point to the right of the current vertex contributes its slope to the slope set. -/
private lemma mem_slopeSet {i₀ k : ℕ} {i₁ a : Γ} (hk : i₀ < k) (ha : v k = (a : WithTop Γ)) :
    slopeReal i₀ k i₁ a ∈ slopeSet v i₀ i₁ :=
  ⟨k, hk, by simp [finite, ha], a, ha, rfl⟩

/-- Every point to the right of the current vertex lies on/above the line of the output slope
through that vertex. -/
lemma nextStep_slope_le {i₀ : ℕ} {i₁ : Γ} {j₀ l : ℕ} {j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) {k : ℕ} (hk : i₀ < k) {a : Γ}
    (ha : v k = (a : WithTop Γ)) :
    m * ((k : ℝ) - i₀) ≤ algebraMap Γ ℝ a - algebraMap Γ ℝ i₁ := by
  have hki : (0 : ℝ) < (k : ℝ) - i₀ := sub_pos.mpr (by exact_mod_cast hk)
  rw [← le_div_iff₀ hki, nextVertex_slope_eq_sInf'' v h]
  exact csInf_le (nextVertex_bddBelow v h) (mem_slopeSet v hk ha)

/-- Beyond the chosen vertex (the *last* point achieving the minimal slope), points are strictly
above the segment line. -/
lemma nextStep_slope_lt {i₀ : ℕ} {i₁ : Γ} {j₀ l : ℕ} {j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) {k : ℕ} (hk : j₀ < k) {a : Γ}
    (ha : v k = (a : WithTop Γ)) :
    m * ((k : ℝ) - i₀) < algebraMap Γ ℝ a - algebraMap Γ ℝ i₁ := by
  have hik : i₀ < k := (nextVertex_lt v h).trans hk
  -- equality would make `k` achieve the minimal slope, contradicting maximality of `j₀`
  refine (nextStep_slope_le v h hik ha).lt_of_ne fun heq => ?_
  have hki : (0 : ℝ) < (k : ℝ) - i₀ := sub_pos.mpr (by exact_mod_cast hik)
  have hmem : k ∈ achievingSet v i₀ i₁ (sInf (slopeSet v i₀ i₁)) :=
    ⟨hik, by simp [finite, ha], a, ha, by
      rw [← nextVertex_slope_eq_sInf'' v h, slopeReal, eq_div_iff hki.ne']
      exact heq⟩
  have hkj : k ≤ j₀ := nextVertex_j₀_eq_max v h ▸
    Finset.le_max' _ k ((nextVertex_finite v h).mem_toFinset.mpr hmem)
  omega

/-- If a step returns `.limitingRay`, the infimum of the slope set is not attained. -/
private lemma limitingRay_sInf_not_mem {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .limitingRay m) :
    sInf (slopeSet v i₀ i₁) ∉ slopeSet v i₀ i₁ := by
  simp_rw [nextStep] at h
  split_ifs at h with _ _ h3
  · split at h <;> simp at h
  · exact fun hmem => h3 ⟨_, hmem, rfl⟩

/-- Every slope out of the current vertex is strictly above the (unattained) limiting slope. -/
private lemma limitingRay_lt_of_mem_slopeSet {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .limitingRay m) {s : ℝ} (hs : s ∈ slopeSet v i₀ i₁) : m < s := by
  rw [limitingRay_slope_eq_sInf v h]
  exact (csInf_le (limitingRay_bddBelow v h) hs).lt_of_ne
    fun heq => limitingRay_sInf_not_mem v h (by rwa [heq])

/-- For a `limitingRay` the infimum is not attained, so every point to the right of the current
vertex lies strictly above the limiting line. -/
lemma limitingRay_slope_lt {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .limitingRay m) {k : ℕ} (hk : i₀ < k) {a : Γ}
    (ha : v k = (a : WithTop Γ)) :
    m * ((k : ℝ) - i₀) < algebraMap Γ ℝ a - algebraMap Γ ℝ i₁ := by
  have hki : (0 : ℝ) < (k : ℝ) - i₀ := sub_pos.mpr (by exact_mod_cast hk)
  rw [← lt_div_iff₀ hki]
  exact limitingRay_lt_of_mem_slopeSet v h (mem_slopeSet v hk ha)

/-- Every point to the right of the current vertex lies on/above the line of the `infiniteRay`
slope through that vertex. -/
lemma infiniteRay_slope_le {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .infiniteRay m) {k : ℕ} (hk : i₀ < k) {a : Γ}
    (ha : v k = (a : WithTop Γ)) :
    m * ((k : ℝ) - i₀) ≤ algebraMap Γ ℝ a - algebraMap Γ ℝ i₁ := by
  have hki : (0 : ℝ) < (k : ℝ) - i₀ := sub_pos.mpr (by exact_mod_cast hk)
  rw [← le_div_iff₀ hki, infiniteRay_slope_eq_sInf v h]
  exact csInf_le (infiniteRay_bddBelow v h) (mem_slopeSet v hk ha)

/-- A finite set of reals lying strictly above `m` is uniformly bounded away from `m`. -/
private lemma exists_pos_add_le_of_finite {A : Set ℝ} (hA : A.Finite) {m ε : ℝ} (hε : 0 < ε)
    (hgt : ∀ s ∈ A, m < s) : ∃ δ, 0 < δ ∧ δ ≤ ε ∧ ∀ s ∈ A, m + δ ≤ s := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨ε, hε, le_rfl, by simp⟩
  -- a finite nonempty set attains its infimum, so `δ = min ε (sInf A - m)` works
  exact ⟨min ε (sInf A - m), lt_min hε (by linarith [hgt _ (hne.csInf_mem hA)]), min_le_left _ _,
    fun s hs => by linarith [csInf_le hA.bddBelow hs, min_le_right ε (sInf A - m)]⟩

/-- For a `limitingRay` the infimum slope is approached by points beyond any bound: only
finitely many points lie below any fixed index, each with slope strictly above the unattained
infimum, so slopes within `ε` of the infimum occur arbitrarily far right. -/
lemma limitingRay_exists_slope_lt {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .limitingRay m) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ k > N, ∃ a : Γ, v k = (a : WithTop Γ) ∧ slopeReal i₀ k i₁ a < m + ε := by
  -- the slopes contributed by the finitely many indices `≤ N` are bounded away from `m`
  set g : ℕ → ℝ := fun k => slopeReal i₀ k i₁ ((v k).untopD 0) with hg
  obtain ⟨δ, hδ, hδε, hδle⟩ := exists_pos_add_le_of_finite
    (((Set.finite_Iic N).image g).inter_of_left (slopeSet v i₀ i₁)) hε
    fun s hs => limitingRay_lt_of_mem_slopeSet v h hs.2
  have hlt : sInf (slopeSet v i₀ i₁) < m + δ := by
    rw [← limitingRay_slope_eq_sInf v h]
    exact lt_add_of_pos_right m hδ
  obtain ⟨s, ⟨k, hk, -, a, hva, rfl⟩, hslt⟩ :=
    exists_lt_of_csInf_lt (limitingRay_nonempty v h) hlt
  refine ⟨k, not_le.mp fun hkN => ?_, a, hva, by linarith⟩
  have hgk : g k = slopeReal i₀ k i₁ a := by simp [hg, hva]
  linarith [hδle _ ⟨hgk ▸ Set.mem_image_of_mem g (Set.mem_Iic.mpr hkN), mem_slopeSet v hk hva⟩]

/-- If a step returns `.infiniteRay m`, the set of points achieving the slope `m` is infinite. -/
private lemma infiniteRay_achievingSet_infinite {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .infiniteRay m) : (achievingSet v i₀ i₁ m).Infinite := by
  simp_rw [nextStep] at h
  split_ifs at h with _ _ _ hinf
  · exact Step.infiniteRay.inj h ▸ hinf
  · split at h <;> simp at h

/-- For an `infiniteRay` the achieving set is unbounded. -/
lemma infiniteRay_exists_achieving_gt {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .infiniteRay m) (N : ℕ) :
    ∃ k > N, k ∈ achievingSet v i₀ i₁ m :=
  ((infiniteRay_achievingSet_infinite v h).exists_gt N).imp fun _ hk => ⟨hk.2, hk.1⟩

/-! ### Walk correspondence

Identification of the algorithm's step data with the geometry of the packaged polygon
`NewtonPolygon₀.construction v`: its anchor is the first finite point, and segment `n` carries the
slope
and the length output by step `n`. Carrying this along the walk is the invariant `WalkInv`, whose
consequences are that step `n`'s output vertex is vertex `n + 1` of the polygon, that the polygon's
height there is the point's height, and that on the segment leaving a vertex the polygon *is* the
line of the step's slope. -/

/-- The anchor of the constructed polygon is read off `findFirstFinite`. -/
private lemma startingPoint_eq {i : ℕ} {c : Γ} (hff : findFirstFinite v 0 = some (i, c)) :
    (NewtonPolygon₀.construction v).starting_point = ((i : ℤ), c) := by
  simp only [NewtonPolygon₀.construction, hff]

/-- The anchor data of the sequence: the first finite index `i`, its value `c`, its rôle as the
anchor of the constructed polygon, and the absence of points strictly to its left. -/
private lemma exists_anchor (h1 : ∃ i, v i ≠ ⊤) :
    ∃ (i : ℕ) (c : Γ), findFirstFinite v 0 = some (i, c) ∧
      (NewtonPolygon₀.construction v).starting_point.1 = (i : ℤ) ∧ v i = (c : WithTop Γ) ∧
      ∀ k < i, v k = ⊤ := by
  classical
  obtain ⟨i, hi⟩ := h1
  have hex : ∃ i ≥ 0, finite v i := ⟨i, Nat.zero_le _, hi⟩
  have hff : findFirstFinite v 0 =
      some (Nat.find hex, (Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose) := by
    rw [findFirstFinite, dif_pos hex]
  exact ⟨_, _, hff, by rw [startingPoint_eq v hff],
    ((Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose_spec).symm,
    fun k hk => of_not_not fun hne => Nat.find_min hex hk ⟨Nat.zero_le _, hne⟩⟩

/-- The anchor of the constructed polygon is a point of the sequence. -/
lemma start_mem (h : ∃ i, v i ≠ ⊤) :
    ∃ k : ℕ, (k : ℤ) = (NewtonPolygon₀.construction v).starting_point.1 ∧
      v k = ((NewtonPolygon₀.construction v).starting_point.2 : WithTop Γ) := by
  obtain ⟨i, c, hff, -, hvi, -⟩ := exists_anchor v h
  rw [startingPoint_eq v hff]
  exact ⟨i, rfl, hvi⟩

/-- No points lie strictly left of the anchor of the constructed polygon. -/
lemma start_le (h : ∃ i, v i ≠ ⊤) :
    ∀ k : ℕ, (k : ℤ) < (NewtonPolygon₀.construction v).starting_point.1 → v k = ⊤ := by
  obtain ⟨i, -, -, hstart, -, hleft⟩ := exists_anchor v h
  exact fun k hk => hleft k (by rw [hstart] at hk; exact_mod_cast hk)

/-- Step `0` of the algorithm is the step out of the anchor. -/
private lemma stream'_zero_eq {i : ℕ} {c : Γ} (hff : findFirstFinite v 0 = some (i, c)) :
    stream' v 0 = some (nextStep v i c) := by
  simp only [stream', hff]

/-- Step `n + 1` of the algorithm is the step out of the vertex produced by step `n`. -/
private lemma stream'_succ_eq {n j₀ l : ℕ} {j₁ : Γ} {m : ℝ}
    (h : stream' v n = some (.nextVertex j₀ j₁ l m)) :
    stream' v (n + 1) = some (nextStep v j₀ j₁) := by
  simp only [stream', h]

/-- The slope carried by segment `n` of the constructed polygon is the slope of step `n`. -/
private lemma slopes_eq {n : ℕ} {S : Step Γ} (h : stream' v n = some S) :
    (NewtonPolygon₀.construction v).slopes n = slopes S := by
  change stream'_slopes v n = _
  simp only [stream'_slopes, h, slopes']

/-- The length of segment `n` of the constructed polygon is the length output by step `n`. -/
private lemma lengths_eq {n j₀ l : ℕ} {j₁ : Γ} {m : ℝ}
    (h : stream' v n = some (.nextVertex j₀ j₁ l m)) :
    (NewtonPolygon₀.construction v).lengths n = ((l : ℕ) : WithTop ℕ) := by
  change stream'_lengths v n = _
  simp only [stream'_lengths, h]

/-- A final ray has infinite length, so it is followed by no vertex at all. -/
private lemma vertexX_succ_eq_top_of_ray {n : ℕ} {m : ℝ}
    (h : stream' v n = some (.limitingRay m) ∨ stream' v n = some (.infiniteRay m)) :
    (NewtonPolygon₀.construction v).vertexX (n + 1) = ⊤ := by
  have hlen : (NewtonPolygon₀.construction v).lengths n = ⊤ := by
    change stream'_lengths v n = ⊤
    rcases h with h | h <;> simp only [stream'_lengths, h]
  rw [NewtonPolygon₀.vertexX_succ, hlen, WithTop.map_top, add_top]

/-- Telescoping the height across a stretch of equal unit slopes. -/
private lemma heightFun_add_of_unitSlope_eq (P : NewtonPolygon₀ (Γ := Γ)) {m : ℝ} {a : ℕ} :
    ∀ d : ℕ, (∀ t, a ≤ t → t < a + d → P.unitSlope t = ((m : ℝ) : WithBotTop ℝ)) →
      P.heightFun (a + d) = P.heightFun a + d * m := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro h
    rw [show a + (d + 1) = (a + d) + 1 from rfl, P.heightFun_succ,
      ih fun t ht ht' => h t ht (by omega), h (a + d) (by omega) (by omega),
      WithBotTop.toReal_coe]
    push_cast
    ring

/-- On a stretch of honest unit slopes the height is the real-valued `heightFun`: the junk guard
of the right-hand walk is exactly a `⊤` incoming unit slope. -/
private lemma height_eq_heightFun' (P : NewtonPolygon₀ (Γ := Γ)) {c : ℕ}
    (h : ∀ t < c, P.unitSlope t ≠ ⊤) :
    P.height (P.starting_point.1 + c) = ((P.heightFun c : ℝ) : WithBotTop ℝ) := by
  refine P.height_eq_heightFun c fun hc => ?_
  have hx : P.height (P.starting_point.1 + (c : ℤ)) = P.toNewtonPolygon.rightHeight c := by
    change P.toNewtonPolygon.height _ = _
    rw [NewtonPolygon.height, NewtonPolygon₀.toNewtonPolygon_startingPoint,
      if_pos (show (0 : ℤ) ≤ P.starting_point.1 + (c : ℤ) - P.starting_point.1 by omega)]
    congr 1
    omega
  rw [hx, NewtonPolygon.rightHeight] at hc
  split_ifs at hc with hcond
  · exact h (c - 1) (by have := hcond.1; omega) hcond.2
  · exact absurd hc (by simp)

/-- Inside segment `n` — at offsets `t` from the anchor `i` with `i₀ - i ≤ t` and `i + t` still
left of the next vertex — the unit slope is the slope of that segment. -/
private lemma unitSlope_eq_of_mem_segment {i n i₀ t : ℕ} {m : ℝ}
    (hstart : (NewtonPolygon₀.construction v).starting_point.1 = (i : ℤ))
    (hvx : (NewtonPolygon₀.construction v).vertexX n = ((i₀ : ℤ) : WithTop ℤ))
    (hslope : (NewtonPolygon₀.construction v).slopes n = ((m : ℝ) : WithBotTop ℝ)) (hle : i ≤ i₀)
    (h1 : i₀ - i ≤ t)
    (h2 : (((i : ℤ) + t : ℤ) : WithTop ℤ) < (NewtonPolygon₀.construction v).vertexX (n + 1)) :
    (NewtonPolygon₀.construction v).unitSlope t = ((m : ℝ) : WithBotTop ℝ) := by
  refine ((NewtonPolygon₀.construction v).unitSlope_eq_slopes ?_ (by rwa [hstart])).trans hslope
  rw [hvx, hstart]
  exact WithTop.coe_le_coe.2 (by omega)

/-- The state of the algorithm's walk at step `n`, relative to the anchor index `i`: the polygon's
`n`-th vertex sits at the point `(i₀, i₁)` of the sequence, the polygon's height function touches
it there, and no junk (`⊤`) unit slope occurs to its left. -/
private structure WalkInv (i n i₀ : ℕ) (i₁ : Γ) : Prop where
  /-- The `n`-th vertex of the polygon sits at `i₀`. -/
  vertexX_eq : (NewtonPolygon₀.construction v).vertexX n = ((i₀ : ℤ) : WithTop ℤ)
  /-- The vertex is at or right of the anchor. -/
  le : i ≤ i₀
  /-- The vertex is a point of the sequence. -/
  point : v i₀ = (i₁ : WithTop Γ)
  /-- The polygon touches the point there. -/
  heightFun_eq : (NewtonPolygon₀.construction v).heightFun (i₀ - i) = algebraMap Γ ℝ i₁
  /-- Every unit slope left of the vertex is honest. -/
  unitSlope_ne_top : ∀ t < i₀ - i, (NewtonPolygon₀.construction v).unitSlope t ≠ ⊤

/-- The walk starts at the anchor. -/
private lemma walkInv_zero {i : ℕ} {c : Γ} (hff : findFirstFinite v 0 = some (i, c))
    (hvi : v i = (c : WithTop Γ)) : WalkInv v i 0 i c := by
  have hstart := startingPoint_eq v hff
  refine ⟨by rw [NewtonPolygon₀.vertexX_zero, hstart], le_rfl, hvi, ?_, fun t ht => by omega⟩
  rw [Nat.sub_self, NewtonPolygon₀.heightFun_zero, hstart]

/-- **The induction step of the walk**: a `nextVertex` output moves the invariant to the next
vertex, the polygon having the constant slope `m` on the segment just traversed. -/
private lemma walkInv_succ {i n j₀ l i₀ : ℕ} {j₁ i₁ : Γ} {m : ℝ}
    (hstart : (NewtonPolygon₀.construction v).starting_point.1 = (i : ℤ))
    (hInv : WalkInv v i n i₀ i₁)
    (hnp : stream' v n = some (.nextVertex j₀ j₁ l m))
    (hstep : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) :
    WalkInv v i (n + 1) j₀ j₁ := by
  obtain ⟨hvx, hik, hvi, hhf, hlow⟩ := hInv
  have hlt : i₀ < j₀ := nextVertex_lt v hstep
  have hl : l = j₀ - i₀ := nextVertex_l_eq v hstep
  have hvx1 : (NewtonPolygon₀.construction v).vertexX (n + 1) = ((j₀ : ℤ) : WithTop ℤ) := by
    have hmap : WithTop.map (fun l : ℕ => (l : ℤ)) ((l : ℕ) : WithTop ℕ) =
      (((l : ℤ)) : WithTop ℤ) := rfl
    rw [NewtonPolygon₀.vertexX_succ, hvx, lengths_eq v hnp, hmap,
      ← WithTop.coe_add]
    congr 1
    omega
  have hseg : ∀ t, i₀ - i ≤ t → t < j₀ - i →
      (NewtonPolygon₀.construction v).unitSlope t = ((m : ℝ) : WithBotTop ℝ) := fun t h1 h2 =>
    unitSlope_eq_of_mem_segment v hstart hvx (slopes_eq v hnp) hik h1
      (by rw [hvx1]; exact WithTop.coe_lt_coe.2 (by omega))
  have hhf1 : (NewtonPolygon₀.construction v).heightFun (j₀ - i) = algebraMap Γ ℝ j₁ := by
    have hsum := heightFun_add_of_unitSlope_eq (NewtonPolygon₀.construction v) (m := m)
      (a := i₀ - i)
      (j₀ - i₀) fun t ht ht' => hseg t ht (by omega)
    rw [show j₀ - i = (i₀ - i) + (j₀ - i₀) by omega, hsum, hhf]
    have hd : ((j₀ : ℝ) - (i₀ : ℝ)) ≠ 0 := by
      have : (i₀ : ℝ) < (j₀ : ℝ) := by exact_mod_cast hlt
      linarith
    have hcast : ((j₀ - i₀ : ℕ) : ℝ) = (j₀ : ℝ) - (i₀ : ℝ) := by rw [Nat.cast_sub hlt.le]
    rw [hcast, nextVertex_slope_eq_sInf' v hstep, slopeReal]
    field_simp
    ring
  refine ⟨hvx1, hik.trans hlt.le, nextVertex_j₁_eq v hstep, hhf1, fun t ht => ?_⟩
  rcases lt_or_ge t (i₀ - i) with h' | h'
  · exact hlow t h'
  · rw [hseg t h' ht]; simp

/-- **The walk**: every step of the algorithm which has not terminated is the step out of a vertex
satisfying the invariant. -/
private lemma walk_step {i : ℕ} {c : Γ}
    (hstart : (NewtonPolygon₀.construction v).starting_point.1 = (i : ℤ))
    (hff : findFirstFinite v 0 = some (i, c))
    (hvi : v i = (c : WithTop Γ)) : ∀ n : ℕ, stream' v n ≠ none →
      ∃ (i₀ : ℕ) (i₁ : Γ), WalkInv v i n i₀ i₁ ∧ stream' v n = some (nextStep v i₀ i₁) := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨i, c, walkInv_zero v hff hvi, stream'_zero_eq v hff⟩
  | succ n ih =>
    intro hne
    obtain ⟨i₀, i₁, hInv, hnp⟩ := ih (stream'_ne_none_of_le v (Nat.le_succ n) hne)
    obtain ⟨p₀, p₁, l, m, hprev⟩ := stream'_nextVertex_of_succ_ne_none v hne
    have hstep : nextStep v i₀ i₁ = .nextVertex p₀ p₁ l m := Option.some.inj (hnp.symm.trans hprev)
    exact ⟨p₀, p₁, walkInv_succ v hstart hInv hprev hstep, stream'_succ_eq v hprev⟩

/-- The invariant at the vertex produced by a `nextVertex` step. -/
private lemma walkInv_out {n j₀ l : ℕ} {j₁ : Γ} {m : ℝ}
    (h : stream' v n = some (.nextVertex j₀ j₁ l m)) :
    ∃ i : ℕ, (NewtonPolygon₀.construction v).starting_point.1 = (i : ℤ) ∧
      WalkInv v i (n + 1) j₀ j₁ := by
  obtain ⟨p₀, p₁, hstep0⟩ := nextStep_nextVertex v h
  obtain ⟨i, c, hff, hstart, hvi, -⟩ := exists_anchor v ⟨j₀, nextVertex_j₀Finite v hstep0⟩
  obtain ⟨i₀, i₁, hInv, hnp⟩ :=
    walk_step v hstart hff hvi n (by rw [h]; exact Option.some_ne_none _)
  exact ⟨i, hstart, walkInv_succ v hstart hInv h (Option.some.inj (hnp.symm.trans h))⟩

/-- At a vertex of the walk the constructed polygon's height *is* the point's height. -/
private lemma height_eq_at_vertex {i n i₀ : ℕ} {i₁ : Γ}
    (hstart : (NewtonPolygon₀.construction v).starting_point.1 = (i : ℤ))
    (hInv : WalkInv v i n i₀ i₁) :
    (NewtonPolygon₀.construction v).height (i₀ : ℤ) = ((algebraMap Γ ℝ i₁ : ℝ) : WithBotTop ℝ) := by
  have hle := hInv.le
  rw [show ((i₀ : ℤ)) = (NewtonPolygon₀.construction v).starting_point.1 + ((i₀ - i : ℕ) : ℤ) by
      rw [hstart]; omega,
    height_eq_heightFun' _ hInv.unitSlope_ne_top, hInv.heightFun_eq]

/-- On the segment leaving the current vertex the constructed polygon *is* the line of the step's
slope through that vertex. -/
private lemma height_eq_segment {i n i₀ k : ℕ} {i₁ : Γ} {m : ℝ}
    (hstart : (NewtonPolygon₀.construction v).starting_point.1 = (i : ℤ))
    (hInv : WalkInv v i n i₀ i₁)
    (hslope : (NewtonPolygon₀.construction v).slopes n = ((m : ℝ) : WithBotTop ℝ))
    (hend : ∀ t < k - i,
      (((i : ℤ) + t : ℤ) : WithTop ℤ) < (NewtonPolygon₀.construction v).vertexX (n + 1))
    (hik : i₀ ≤ k) :
    (NewtonPolygon₀.construction v).height (k : ℤ) =
      ((algebraMap Γ ℝ i₁ + ((k : ℝ) - (i₀ : ℝ)) * m : ℝ) : WithBotTop ℝ) := by
  have hle := hInv.le
  have hseg : ∀ t, i₀ - i ≤ t → t < k - i →
      (NewtonPolygon₀.construction v).unitSlope t = ((m : ℝ) : WithBotTop ℝ) := fun t h1 h2 =>
    unitSlope_eq_of_mem_segment v hstart hInv.vertexX_eq hslope hInv.le h1 (hend t h2)
  have hne : ∀ t < k - i, (NewtonPolygon₀.construction v).unitSlope t ≠ ⊤ := fun t ht => by
    rcases lt_or_ge t (i₀ - i) with h' | h'
    · exact hInv.unitSlope_ne_top t h'
    · rw [hseg t h' ht]; simp
  rw [show (k : ℤ) = (NewtonPolygon₀.construction v).starting_point.1 + ((k - i : ℕ) : ℤ) by
      rw [hstart]; omega,
    height_eq_heightFun' _ hne, show k - i = (i₀ - i) + (k - i₀) by omega,
    heightFun_add_of_unitSlope_eq _ (k - i₀) fun t ht _ => hseg t ht (by omega),
    hInv.heightFun_eq, show ((k - i₀ : ℕ) : ℝ) = (k : ℝ) - (i₀ : ℝ) from by rw [Nat.cast_sub hik]]

/-- The `x`-coordinate of vertex `n + 1` of the constructed polygon is the output vertex `j₀` of
step `n` of the algorithm. -/
lemma vertexX_eq {n j₀ l : ℕ} {j₁ : Γ} {m : ℝ}
    (h : stream' v n = some (.nextVertex j₀ j₁ l m)) :
    (NewtonPolygon₀.construction v).vertexX (n + 1) = ((j₀ : ℤ) : WithTop ℤ) :=
  (walkInv_out v h).choose_spec.2.vertexX_eq

/-- **The constructed polygon touches the points at its vertices**: its height at an output
vertex of the algorithm is the height of that point. -/
lemma height_vertex {n j₀ l : ℕ} {j₁ : Γ} {m : ℝ}
    (h : stream' v n = some (.nextVertex j₀ j₁ l m)) :
    (NewtonPolygon₀.construction v).height (j₀ : ℤ) = ((algebraMap Γ ℝ j₁ : ℝ) : WithBotTop ℝ) :=
  let ⟨_, hstart, hInv⟩ := walkInv_out v h
  height_eq_at_vertex v hstart hInv

/-! ### Existence -/

/-- The rightmost point achieving a slope is a point of the sequence. -/
private lemma toFinset_max'_ne_top {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (hfin : (achievingSet v i₀ i₁ m).Finite) (hne : hfin.toFinset.Nonempty) :
    v (hfin.toFinset.max' hne) ≠ ⊤ :=
  (hfin.mem_toFinset.mp (Finset.max'_mem _ _)).2.1

/-- A `tail` step really means there are no points to the right of the current vertex: the only
other way the algorithm can return `tail` is a `⊤` value at the chosen vertex, which cannot
happen. -/
private lemma tail_no_finite_gt {i₀ : ℕ} {i₁ : Γ} (h : nextStep v i₀ i₁ = .tail) {k : ℕ}
    (hk : i₀ < k) {a : Γ} (ha : v k = (a : WithTop Γ)) : False := by
  have hmem := mem_slopeSet (i₁ := i₁) v hk ha
  simp_rw [nextStep] at h
  split_ifs at h with h1 h2 h3 h4
  · rw [h1] at hmem
    exact hmem
  · split at h
    · rename_i heq
      exact toFinset_max'_ne_top v _ _ heq
    · exact absurd h (by simp)

/-- At the current vertex the polygon touches the point, so the bound holds with equality. -/
private lemma height_le_at_vertex {i n i₀ : ℕ} {i₁ a : Γ}
    (hstart : (NewtonPolygon₀.construction v).starting_point.1 = (i : ℤ))
    (hInv : WalkInv v i n i₀ i₁)
    (hva : v i₀ = (a : WithTop Γ)) :
    (NewtonPolygon₀.construction v).height (i₀ : ℤ) ≤ ((algebraMap Γ ℝ a : ℝ) : WithBotTop ℝ) :=
  ((height_eq_at_vertex v hstart hInv).trans
    (by rw [WithTop.coe_injective (hInv.point.symm.trans hva)])).le

/-- On the segment leaving the current vertex the polygon is the line of the step's slope, so the
step's line bound is exactly the required height bound. -/
private lemma height_le_segment {i n i₀ k : ℕ} {i₁ a : Γ} {m : ℝ}
    (hstart : (NewtonPolygon₀.construction v).starting_point.1 = (i : ℤ))
    (hInv : WalkInv v i n i₀ i₁)
    (hslope : (NewtonPolygon₀.construction v).slopes n = ((m : ℝ) : WithBotTop ℝ))
    (hend : ∀ t < k - i,
      (((i : ℤ) + t : ℤ) : WithTop ℤ) < (NewtonPolygon₀.construction v).vertexX (n + 1))
    (hik : i₀ ≤ k) (hbound : m * ((k : ℝ) - i₀) ≤ algebraMap Γ ℝ a - algebraMap Γ ℝ i₁) :
    (NewtonPolygon₀.construction v).height (k : ℤ) ≤ ((algebraMap Γ ℝ a : ℝ) : WithBotTop ℝ) := by
  rw [height_eq_segment v hstart hInv hslope hend hik]
  refine WithBotTop.coe_le_coe.2 ?_
  rw [mul_comm]
  linarith

/-- **The line bound, walked along the algorithm.** Starting from a vertex on/left of `k`, the
polygon's height at `k` is bounded by the point `(k, a)`: either `k` is the vertex itself, or the
step out of it covers `k` (a segment or a final ray), or the walk moves on to the next vertex —
which is strictly to the right, so the recursion terminates. The `tail` and `unboundedBelow`
outputs are impossible: the former asserts that no point lies right of the vertex, the latter is
excluded by admissibility. -/
private lemma height_le_aux {i : ℕ}
    (hstart : (NewtonPolygon₀.construction v).starting_point.1 = (i : ℤ))
    (h2 : IsAdmissible v) {k : ℕ} {a : Γ} (hva : v k = (a : WithTop Γ)) :
    ∀ (d n i₀ : ℕ) (i₁ : Γ), k - i₀ ≤ d → WalkInv v i n i₀ i₁ →
      stream' v n = some (nextStep v i₀ i₁) → i₀ ≤ k →
      (NewtonPolygon₀.construction v).height (k : ℤ) ≤ ((algebraMap Γ ℝ a : ℝ) : WithBotTop ℝ) := by
  intro d
  induction d with
  | zero =>
    intro n i₀ i₁ hd hInv hnp hik
    obtain rfl : i₀ = k := by omega
    exact height_le_at_vertex v hstart hInv hva
  | succ d ih =>
    intro n i₀ i₁ hd hInv hnp hik
    rcases eq_or_lt_of_le hik with rfl | hlt
    · exact height_le_at_vertex v hstart hInv hva
    cases hs : nextStep v i₀ i₁ with
    | tail => exact (tail_no_finite_gt v hs hlt hva).elim
    | unboundedBelow => exact absurd (h2 i₀ i₁ hInv.point) (unboundedBelow v hs)
    | limitingRay mm =>
      have hnp' : stream' v n = some (Step.limitingRay mm) := by rw [hnp, hs]
      exact height_le_segment v hstart hInv (slopes_eq v hnp')
        (fun t _ => by rw [vertexX_succ_eq_top_of_ray v (.inl hnp')]; exact WithTop.coe_lt_top _)
        hik (limitingRay_slope_lt v hs hlt hva).le
    | infiniteRay mm =>
      have hnp' : stream' v n = some (Step.infiniteRay mm) := by rw [hnp, hs]
      exact height_le_segment v hstart hInv (slopes_eq v hnp')
        (fun t _ => by rw [vertexX_succ_eq_top_of_ray v (.inr hnp')]; exact WithTop.coe_lt_top _)
        hik (infiniteRay_slope_le v hs hlt hva)
    | nextVertex j₀ j₁ l mm =>
      have hnp' : stream' v n = some (Step.nextVertex j₀ j₁ l mm) := by rw [hnp, hs]
      have hInv1 := walkInv_succ v hstart hInv hnp' hs
      have hjlt : i₀ < j₀ := nextVertex_lt v hs
      have hle := hInv.le
      rcases le_or_gt k j₀ with hkj | hjk
      · refine height_le_segment v hstart hInv (slopes_eq v hnp') (fun t ht => ?_)
          hik (nextStep_slope_le v hs hlt hva)
        rw [hInv1.vertexX_eq]
        exact WithTop.coe_lt_coe.2 (by omega)
      · exact ih (n + 1) j₀ j₁ (by omega) hInv1 (stream'_succ_eq v hnp') (le_of_lt hjk)

/-- **The constructed polygon lies on/below the points.** -/
theorem height_le (h1 : ∃ i, v i ≠ ⊤) (h2 : IsAdmissible v) (k : ℕ) :
    (NewtonPolygon₀.construction v).height (k : ℤ) ≤ pointHeight v k := by
  obtain ⟨i, c, hff, hstart, hvi, hleft⟩ := exists_anchor v h1
  cases hvk : v k with
  | top =>
    rw [pointHeight_eq_top_iff.2 hvk]
    exact le_top
  | coe a =>
    rw [pointHeight_coe hvk]
    rcases lt_or_ge k i with hki | hik
    · exact absurd (hleft k hki) (by rw [hvk]; exact WithTop.coe_ne_top)
    · exact height_le_aux v hstart h2 hvk (k - i) 0 i c le_rfl (walkInv_zero v hff hvi)
        (stream'_zero_eq v hff) hik

/-! ### Maximality

A competitor lying on/below the points is compared to the constructed polygon segment by segment:
it is below its own chord (`NewtonPolygon₀.height_le_chord`), and the chord between two points of
the sequence which the constructed polygon passes through is the constructed segment itself. The
final rays carry no right-hand vertex, so there the chord runs to a point far to the right whose
slope approximates the ray's slope (exactly, for an `infiniteRay`; up to `ε`, for a
`limitingRay`). -/

/-- An `ε`-approximation criterion in `WithBotTop ℝ` (`le_of_forall_pos_le_add` exists only for
`ENNReal`, so the three cases are done by hand). -/
private lemma le_coe_of_forall_pos_add {u : WithBotTop ℝ} {t : ℝ}
    (h : ∀ ε > 0, u ≤ ((t + ε : ℝ) : WithBotTop ℝ)) : u ≤ ((t : ℝ) : WithBotTop ℝ) := by
  revert h
  induction u using WithBotTop.rec with
  | bot => exact fun _ => bot_le
  | top => exact fun h => absurd (top_le_iff.1 (h 1 one_pos)) (by simp)
  | coe q =>
    refine fun h => WithBotTop.coe_le_coe.2 (le_of_not_gt fun hq => ?_)
    have hε := WithBotTop.coe_le_coe.1 (h ((q - t) / 2) (by linarith))
    linarith

/-- A `tail` step terminates the algorithm, so the polygon has at most that many segments. -/
private lemma tail_support_le {n : ℕ} (hnp : stream' v n = some Step.tail) :
    (NewtonPolygon₀.construction v).support ≤ (n : WithTop ℕ) := by
  classical
  change stream'_numSegments v ≤ _
  unfold stream'_numSegments
  split_ifs with ht hn
  · exact_mod_cast Nat.find_le hnp
  · exact absurd ⟨n, hnp⟩ ht
  · exact absurd ⟨n, hnp⟩ ht

/-- Out of a vertex whose step is `tail` the polygon is junk: every later segment is empty, so the
unit slope leaving the vertex is the junk value `⊤`. -/
private lemma tail_unitSlope_eq_top {i n i₀ : ℕ} {i₁ : Γ}
    (hstart : (NewtonPolygon₀.construction v).starting_point.1 = (i : ℤ))
    (hInv : WalkInv v i n i₀ i₁)
    (hnp : stream' v n = some Step.tail) :
    (NewtonPolygon₀.construction v).unitSlope (i₀ - i) = ⊤ := by
  have hle := hInv.le
  have hsupp := tail_support_le v hnp
  have hzero : ∀ n' : ℕ, n ≤ n' → (NewtonPolygon₀.construction v).lengths n' = 0 := fun n' hn' =>
    (NewtonPolygon₀.construction v).lengths_junk n' (hsupp.trans (by exact_mod_cast hn'))
  have hvxeq : ∀ n' : ℕ, n ≤ n' →
      (NewtonPolygon₀.construction v).vertexX n' = ((i₀ : ℤ) : WithTop ℤ) := by
    intro n' hn'
    induction n', hn' using Nat.le_induction with
    | base => exact hInv.vertexX_eq
    | succ n'' hn'' ih =>
      rw [NewtonPolygon₀.vertexX_succ, ih, hzero n'' hn'',
        show WithTop.map (fun l : ℕ => (l : ℤ)) (0 : WithTop ℕ) = 0 from rfl, add_zero]
  rcases (NewtonPolygon₀.construction v).unitSlope_cases (i₀ - i) with ⟨n', hb1, hb2⟩ | htop
  · exfalso
    rw [show (NewtonPolygon₀.construction v).starting_point.1 + ((i₀ - i : ℕ) : ℤ) = (i₀ : ℤ) by
      rw [hstart]; omega] at hb1 hb2
    rcases le_or_gt n n' with h' | h'
    · rw [hvxeq (n' + 1) (by omega)] at hb2
      exact lt_irrefl _ hb2
    · have hmono := (NewtonPolygon₀.construction v).vertexX_mono (show n' + 1 ≤ n by omega)
      rw [hvxeq n le_rfl] at hmono
      exact lt_irrefl _ (hb2.trans_le hmono)
  · exact htop

/-- Right of a vertex whose step is `tail` the constructed polygon is `⊤`: it has ended. -/
private lemma height_eq_top_of_tail {i n i₀ k : ℕ} {i₁ : Γ}
    (hstart : (NewtonPolygon₀.construction v).starting_point.1 = (i : ℤ))
    (hInv : WalkInv v i n i₀ i₁)
    (hnp : stream' v n = some Step.tail) (hk : i₀ < k) :
    (NewtonPolygon₀.construction v).height (k : ℤ) = ⊤ := by
  have hle := hInv.le
  by_contra hcon
  rw [show ((k : ℤ)) = (NewtonPolygon₀.construction v).starting_point.1 + ((k - i : ℕ) : ℤ) by
    rw [hstart]; omega] at hcon
  exact (NewtonPolygon₀.construction v).unitSlope_ne_top_of_height_ne_top hcon
    (show i₀ - i < k - i by omega) (tail_unitSlope_eq_top v hstart hInv hnp)

/-- **The competitor is below the chord out of the current vertex**: a polygon lying on/below the
points is, at any `k` between the current vertex `i₀` and a later point `k'`, below the chord from
`(i₀, i₁)` to `(k', a)` — whose slope is `slopeReal i₀ k' i₁ a`. -/
private lemma competitor_chord {i n i₀ k k' : ℕ} {i₁ a : Γ} {Q : NewtonPolygon₀ (Γ := Γ)}
    (hQ : Q.starting_point.1 = (i : ℤ)) (hle : ∀ k : ℕ, Q.height (k : ℤ) ≤ pointHeight v k)
    (hInv : WalkInv v i n i₀ i₁) (hik : i₀ ≤ k) (hkk' : k ≤ k') (hva : v k' = (a : WithTop Γ)) :
    Q.height (k : ℤ) ≤ ((algebraMap Γ ℝ i₁ +
      slopeReal i₀ k' i₁ a * ((k : ℝ) - (i₀ : ℝ)) : ℝ) : WithBotTop ℝ) := by
  have hQv := (hle i₀).trans_eq (pointHeight_coe hInv.point)
  have hQv' := (hle k').trans_eq (pointHeight_coe hva)
  refine (Q.height_le_chord (x := (i₀ : ℤ)) (y := (k : ℤ)) (z := (k' : ℤ))
    (by rw [hQ]; exact_mod_cast hInv.le) (by exact_mod_cast hik) (by exact_mod_cast hkk')
    hQv hQv').trans_eq ?_
  congr 1

/-- **Maximality, walked along the algorithm.** At the current vertex the competitor is below the
point, which the constructed polygon touches; on the segment or ray leaving it the competitor is
below the chord to a point on/approximating that segment; and beyond the segment the walk moves on
to the next vertex, which is strictly to the right, so the recursion terminates. -/
private lemma isGreatest_aux {i : ℕ}
    (hstart : (NewtonPolygon₀.construction v).starting_point.1 = (i : ℤ))
    (h2 : IsAdmissible v) {Q : NewtonPolygon₀ (Γ := Γ)} (hQ : Q.starting_point.1 = (i : ℤ))
    (hle : ∀ k : ℕ, Q.height (k : ℤ) ≤ pointHeight v k) :
    ∀ (d n i₀ k : ℕ) (i₁ : Γ), k - i₀ ≤ d → WalkInv v i n i₀ i₁ →
      stream' v n = some (nextStep v i₀ i₁) → i₀ ≤ k →
      Q.height (k : ℤ) ≤ (NewtonPolygon₀.construction v).height (k : ℤ) := by
  intro d
  induction d with
  | zero =>
    intro n i₀ k i₁ hd hInv hnp hik
    obtain rfl : i₀ = k := by omega
    rw [height_eq_at_vertex v hstart hInv, ← pointHeight_coe hInv.point]
    exact hle i₀
  | succ d ih =>
    intro n i₀ k i₁ hd hInv hnp hik
    rcases eq_or_lt_of_le hik with rfl | hlt
    · rw [height_eq_at_vertex v hstart hInv, ← pointHeight_coe hInv.point]
      exact hle i₀
    have hD : (0 : ℝ) < (k : ℝ) - (i₀ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt)
    cases hs : nextStep v i₀ i₁ with
    | tail =>
      rw [height_eq_top_of_tail v hstart hInv (by rw [hnp, hs]) hlt]
      exact le_top
    | unboundedBelow => exact absurd (h2 i₀ i₁ hInv.point) (unboundedBelow v hs)
    | limitingRay mm =>
      have hnp' : stream' v n = some (Step.limitingRay mm) := by rw [hnp, hs]
      rw [height_eq_segment v hstart hInv (slopes_eq v hnp')
        (fun t _ => by rw [vertexX_succ_eq_top_of_ray v (.inl hnp')]; exact WithTop.coe_lt_top _)
        hik]
      -- the limiting slope is approached from above arbitrarily far to the right
      refine le_coe_of_forall_pos_add fun ε hε => ?_
      obtain ⟨k', hk'gt, a, hva, hslt⟩ :=
        limitingRay_exists_slope_lt v hs (show (0 : ℝ) < ε / ((k : ℝ) - i₀) from div_pos hε hD)
          (max i₀ k)
      have hkk' : k ≤ k' := le_of_lt (lt_of_le_of_lt (le_max_right i₀ k) hk'gt)
      refine (competitor_chord v hQ hle hInv hik hkk' hva).trans (WithBotTop.coe_le_coe.2 ?_)
      have hdiv : ε / ((k : ℝ) - (i₀ : ℝ)) * ((k : ℝ) - (i₀ : ℝ)) = ε :=
        div_mul_cancel₀ ε hD.ne'
      nlinarith [mul_lt_mul_of_pos_right hslt hD]
    | infiniteRay mm =>
      have hnp' : stream' v n = some (Step.infiniteRay mm) := by rw [hnp, hs]
      rw [height_eq_segment v hstart hInv (slopes_eq v hnp')
        (fun t _ => by rw [vertexX_succ_eq_top_of_ray v (.inr hnp')]; exact WithTop.coe_lt_top _)
        hik]
      -- the ray's slope is achieved arbitrarily far to the right, so a single chord suffices
      obtain ⟨k', hk'gt, -, -, a, hva, hmeq⟩ := infiniteRay_exists_achieving_gt v hs (max i₀ k)
      have hkk' : k ≤ k' := le_of_lt (lt_of_le_of_lt (le_max_right i₀ k) hk'gt)
      refine (competitor_chord v hQ hle hInv hik hkk' hva).trans_eq ?_
      rw [← hmeq]
      congr 1
      ring
    | nextVertex j₀ j₁ l mm =>
      have hnp' : stream' v n = some (Step.nextVertex j₀ j₁ l mm) := by rw [hnp, hs]
      have hInv1 := walkInv_succ v hstart hInv hnp' hs
      have hjlt : i₀ < j₀ := nextVertex_lt v hs
      have hle' := hInv.le
      rcases le_or_gt k j₀ with hkj | hjk
      · rw [height_eq_segment v hstart hInv (slopes_eq v hnp') (fun t ht => by
          rw [hInv1.vertexX_eq]; exact WithTop.coe_lt_coe.2 (by omega)) hik]
        refine (competitor_chord v hQ hle hInv hik hkj (nextVertex_j₁_eq v hs)).trans_eq ?_
        rw [← nextVertex_slope_eq_sInf' v hs]
        congr 1
        ring
      · exact ih (n + 1) j₀ k j₁ (by omega) hInv1 (stream'_succ_eq v hnp') (le_of_lt hjk)

/-- **The constructed polygon is the greatest polygon below the points**: any competitor with
the same starting `x`-coordinate lying on/below the points lies on/below it. -/
theorem isGreatest (h1 : ∃ i, v i ≠ ⊤) (h2 : IsAdmissible v)
    (Q : NewtonPolygon₀ (Γ := Γ))
    (hQ : Q.starting_point.1 = (NewtonPolygon₀.construction v).starting_point.1)
    (hle : ∀ k : ℕ, Q.height (k : ℤ) ≤ pointHeight v k) :
    Q.IsBelow (NewtonPolygon₀.construction v) := by
  obtain ⟨i, c, hff, hstart, hvi, -⟩ := exists_anchor v h1
  rw [hstart] at hQ
  rw [NewtonPolygon₀.isBelow_iff_height]
  intro x
  rcases lt_or_ge x (i : ℤ) with hx | hx
  -- strictly left of the common anchor the competitor is `⊥`
  · rw [(Q.height_eq_bot_iff x).2 (by omega)]
    exact bot_le
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, x = (k : ℤ) := ⟨x.toNat, by omega⟩
    exact isGreatest_aux v hstart h2 hQ hle (k - i) 0 i k c le_rfl (walkInv_zero v hff hvi)
      (stream'_zero_eq v hff) (by exact_mod_cast hx)

/-- **Existence: the algorithm constructs the lower convex hull.** For an admissible sequence
with at least one point, the polygon `NewtonPolygon₀.construction v` built by the step algorithm
is the Newton polygon of `v` in the sense of the geometric specification `IsNewtonPolygonOf`. -/
theorem isNewtonPolygonOf_construction (h1 : ∃ i, v i ≠ ⊤) (h2 : IsAdmissible v) :
    IsNewtonPolygonOf v (NewtonPolygon₀.construction v) :=
  ⟨start_le v h1, start_mem v h1,
    height_le v h1 h2, isGreatest v h1 h2⟩

/-- Existence, packaged for power series: the Newton polygon of `f` with respect to the
coefficient valuation `val` satisfies the geometric specification. -/
theorem isNewtonPolygonOf_ofPowerSeries {R : Type*} [Semiring R] (val : R → WithTop Γ)
    (f : PowerSeries R) (h1 : ∃ i, ofPowerSeries.coeffSeq val f i ≠ ⊤)
    (h2 : IsAdmissible (ofPowerSeries.coeffSeq val f)) :
    IsNewtonPolygonOf (ofPowerSeries.coeffSeq val f) (NewtonPolygon₀.ofPowerSeries val f) :=
  isNewtonPolygonOf_construction (ofPowerSeries.coeffSeq val f) h1 h2

/-- If the sequence has no points at all, nothing satisfies the specification. -/
lemma not_isNewtonPolygonOf_of_forall_eq_top (h : ∀ i, v i = ⊤) (P : NewtonPolygon₀ (Γ := Γ)) :
    ¬ IsNewtonPolygonOf v P := by
  intro hspec
  obtain ⟨k, -, hk⟩ := hspec.start_mem
  rw [h k] at hk
  exact WithTop.coe_ne_top hk.symm

end NewtonPolygon₀.construction
