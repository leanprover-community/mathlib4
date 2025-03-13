import Mathlib


section
variable {k E} [LinearOrderedField k] [OrderedAddCommGroup E]
variable [Module k E] [OrderedSMul k E]

variable {a b : E} {r r' : k}

open AffineMap

theorem lineMap_le_lineMap_iff_of_lt' (h : a < b) : lineMap a b r ≤ lineMap a b r' ↔ r ≤ r' := by
  simp only [lineMap_apply_module']
  rw [add_le_add_iff_right, smul_le_smul_iff_of_pos_right (sub_pos.mpr h)]

theorem left_le_lineMap_iff_le' (h : a < b) : a ≤ lineMap a b r ↔ 0 ≤ r :=
  Iff.trans (by rw [lineMap_apply_zero]) (lineMap_le_lineMap_iff_of_lt' h)

theorem lineMap_le_right_iff_le' (h : a < b) : lineMap a b r ≤ b ↔ r ≤ 1 :=
  Iff.trans (by rw [lineMap_apply_one]) (lineMap_le_lineMap_iff_of_lt' h)

end

open Finset


theorem exists_between_and_le_dist (S : Finset ℝ) (n : Nat) (a b : ℝ) (hab : a < b)
    (hS : #(S.filter (· ∈ Set.Ioo a b)) < n) :
    ∃ x : ℝ, a < x ∧ x < b ∧ ∀ y ∈ S, (b - a) / (2 * n) ≤ |x - y| := by
  have : n > 0 := by omega
  -- make `n` defEq to `_ + 1`
  cases' n with n; · contradiction
  set n := n+1
  -- separate the interval `(0,1)` into `n` equally spaced intervals
  let interval (i : Fin n) : Set ℝ :=
    Set.Ioo (AffineMap.lineMap a b ((i : ℝ) / n)) (AffineMap.lineMap a b (((i : ℝ) + 1) / n))

  let rel (y : ℝ) (i : Fin n) : Prop :=
    y ∈ interval i

  by_cases h : ∀ i ∈ Finset.univ, ∃ y ∈ S.filter (· ∈ Set.Ioo a b), rel y i
  · -- show that the intervals are disjoint
    have disjoint : Pairwise fun i j => Disjoint (interval i) (interval j) := by
      rw [pairwise_disjoint_on]
      intro i j hlt
      unfold interval
      rw [Set.Ioo_disjoint_Ioo]
      apply le_sup_of_le_right; apply inf_le_of_left_le
      replace hlt : (i : ℝ) + 1 ≤ j := by norm_cast
      rw [lineMap_le_lineMap_iff_of_lt' hab]
      gcongr
    -- use the pigeon hole principle on the disjoint intervals
    have := card_le_card_of_forall_subsingleton' rel h <| by
      intro y _
      unfold rel
      intro x ⟨_, hx⟩ y ⟨_, hy⟩
      by_contra h
      have : Disjoint (interval x) (interval y) := disjoint h
      rw [Set.disjoint_left] at this
      exact this hx hy
    rw [card_univ, Fintype.card_fin] at this
    omega

  push_neg at h
  -- the `i`th interval in disjoint with `S`
  rcases h with ⟨i, _, h⟩
  unfold rel at h
  -- use the midpoint of the `i`th interval
  use AffineMap.lineMap a b ((i : ℝ) / n + 1 / (2 * n))
  have ineq₁: (i : ℝ) / n ≤ 1 - 1 / n := by
    field_simp [n]; gcongr; exact Fin.is_le _
  have : b - a > 0 := by linarith
  -- check that the point is in between `0` and `1`
  constructor
  · simp [AffineMap.lineMap_apply_module']
    positivity
  constructor
  · simp [AffineMap.lineMap_apply_module']
    have ineq₂: (1 : ℝ) / (2 * n) < 1 / n := by
      gcongr; norm_cast; omega
    linear_combination (ineq₁ + ineq₂) * (b - a)
  intro y hy
  -- the `i`th interval is disjoint with `S`
  have : y ∉ interval i := by
    by_cases ha : a < y
    · by_cases hb : y < b
      · apply h
        simp [ha, hb, hy]
      · apply Set.not_mem_Ioo_of_ge
        push_neg at hb
        simp [AffineMap.lineMap_apply_module']
        linear_combination ineq₁ * (b - a) + hb
    · apply Set.not_mem_Ioo_of_le
      have ineq₃ : (0:ℝ) ≤ i / n := by positivity
      push_neg at ha
      simp [AffineMap.lineMap_apply_module']
      linear_combination ineq₃ * (b - a) + ha
  simp only [interval, Set.mem_Ioo, not_and_or, not_lt] at this
  -- `y ∈ S` is either above or below the interval, either way we get the bound
  rcases this with h | h
  · trans; swap; · apply le_abs_self
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le']
    trans; · exact h
    simp [AffineMap.lineMap_apply_module']
    ring_nf; rfl
  · rw [abs_sub_comm]
    trans; swap; · apply le_abs_self
    rw [le_sub_iff_add_le]
    trans; swap; · exact h
    simp [AffineMap.lineMap_apply_module']
    ring_nf; rfl



open Module
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] (k : Nat) [Fact (finrank ℝ V = k+1)]


noncomputable def project (a b p : P) : ℝ := innerSL ℝ (a -ᵥ b) (a -ᵥ p) / (‖a -ᵥ b‖ ^ 2)

@[simp] theorem project_self_left  (a b : P) : project a b a = 0 := by simp [project]
@[simp] theorem project_self_right (a b : P) (h : a ≠ b := by positivity) : project a b b = 1 := by
    simp [project]
    rw [real_inner_self_eq_norm_sq, div_self]
    apply pow_ne_zero 2; rwa [norm_ne_zero_iff, vsub_ne_zero]


open scoped Classical

theorem exists_affine_between_and_le_dist {S : Finset P} (n : Nat) (a b : P)
    (i j : ℝ) (hi : 0 ≤ i) (hij : i < j) (hj : j ≤ 1)
    (hS : #((S.filter (project a b · ∈ Set.Ioo i j))) < n)
    (hab : a ≠ b) :
    ∃ l : AffineSubspace ℝ P, finrank ℝ l.direction = k ∧ l.SOppSide a b ∧
    ∀ p ∈ S, (j - i) * dist a b / (2 * n) ≤ Metric.infDist p l := by

  replace hS : #(filter (· ∈ Set.Ioo i j) (image (project a b) S)) < n := by
    refine lt_of_le_of_lt ?_ hS
    rw [filter_image]
    exact card_image_le

  have ha' : project a b a = 0 := by simp [project]
  have hb' : project a b b = 1 := by
    simp [project]
    rw [real_inner_self_eq_norm_sq, div_self]
    apply pow_ne_zero 2; rwa [norm_ne_zero_iff, vsub_ne_zero]

  obtain ⟨x, lt_x, x_lt, hx⟩ := exists_between_and_le_dist (image (project a b) S) n i j hij hS

  use .mk' (AffineMap.lineMap a b x) (LinearMap.ker (innerₛₗ ℝ (a -ᵥ b)))

  have : Nonempty (AffineSubspace.mk'
      (AffineMap.lineMap a b x) (LinearMap.ker (innerₛₗ ℝ (a -ᵥ b)))) := by
    constructor
    use (AffineMap.lineMap a b x)
    apply AffineSubspace.self_mem_mk'

  constructor
  · -- The subspace has the required dimension
    have : LinearMap.ker ((innerₛₗ ℝ) (a -ᵥ b)) = (ℝ ∙ (a -ᵥ b))ᗮ := by
      ext x
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]; rfl
    rw [AffineSubspace.direction_mk', this]
    apply finrank_orthogonal_span_singleton (by rwa [vsub_ne_zero])
  have : 0 < ‖a -ᵥ b‖ := by
    rwa [norm_pos_iff, vsub_ne_zero]
  constructor
  · refine Sbtw.sOppSide_of_not_mem_of_mem ?_ ?_ (AffineSubspace.self_mem_mk' _ _)
    · simp [hab, lt_of_le_of_lt hi lt_x, lt_of_lt_of_le x_lt hj]
    · simp [hab, (lt_of_le_of_lt hi lt_x).ne.symm]

  intro p hp
  -- we show that the distance between `p` and the plane corresponds to
  -- the distance between `project p` and `x`.
  specialize hx (project a b p) (Finset.mem_image_of_mem (project a b) hp)
  rw [Metric.infDist_eq_iInf]
  apply le_ciInf
  intro ⟨y, hy⟩; simp only [dist_eq_norm_vsub]
  simp at hy
  have h : |inner (a -ᵥ b) (p -ᵥ (AffineMap.lineMap a b) x)| ≤ ‖a -ᵥ b‖ * ‖p -ᵥ y‖ := by
    convert abs_real_inner_le_norm (a -ᵥ b) (p -ᵥ y) using 2
    rw [← sub_eq_zero, ← inner_sub_right]; simpa
  rw [← mul_le_mul_left this]
  trans; swap; · exact h
  rw [project, sub_div' (by positivity), abs_div, le_div_iff₀ (by positivity),
    abs_eq_self.mpr (by positivity)] at hx
  ring_nf at hx ⊢
  trans; · exact hx
  apply le_of_eq
  rw [abs_eq_abs]; left
  simp
  rw [sub_eq_iff_eq_add, ← inner_add_right]
  rw [add_comm]; simp
  rw [inner_smul_right, real_inner_self_eq_norm_sq, mul_comm]



variable [Fact (Module.finrank ℝ V = 2)]

theorem result : ∃ c : ℝ, 0 < c ∧ ∀ {n : ℕ} (hn : 1 < n) {S : Finset P} (hSn : #S = n)
    (hSdist : (S : Set P).Pairwise fun x y ↦ 1 ≤ dist x y),
    ∃ l : AffineSubspace ℝ P, finrank ℝ l.direction = 1 ∧
      (∃ p₁ p₂, p₁ ∈ S ∧ p₂ ∈ S ∧ l.SOppSide p₁ p₂) ∧
      ∀ p ∈ S, c * (n : ℝ) ^ (-1 / 3 : ℝ) ≤ Metric.infDist p l := by
  let c : ℝ := 1/100
  use c, by norm_num
  intro n hn S hS one_le_dist
  -- There are two main cases: either there is or there isn't a large distance between two points.
  by_cases h : ∃ᵉ (a ∈ S) (b ∈ S), (n : ℝ) ^ (2 / 3 : ℝ) ≤ dist a b
  · -- If there are points with distance at least `n^(2/3)`, then we can solve the problem by
    -- choosing the best perpendicular line though this segment.
    -- sorry
    obtain ⟨a, ha, b, hb, hab⟩ := h
    have : 0 < dist a b := lt_of_lt_of_le (by positivity) hab
    rw [dist_pos] at this
    obtain ⟨l, rank, sOpp, h⟩ := exists_affine_between_and_le_dist 1 (n*2) a b 0 1
      le_rfl zero_lt_one le_rfl (lt_of_le_of_lt (card_filter_le S _) (by omega)) this
    simp at h
    use l, rank
    constructor; · use a, b, ha, hb
    intro p hp
    specialize h p hp
    trans; swap; · exact h
    rw [le_div_iff₀ (by positivity)]
    trans; swap; · exact hab
    rw [neg_div, Real.rpow_neg (by positivity)]
    field_simp; rw [div_le_iff₀ (by positivity), ← Real.rpow_add (by positivity)]
    rw [show (2/3+1/3 : ℝ) = 1 by norm_num, Real.rpow_one]
    field_simp [c, div_le_iff₀]; linarith only

  · push_neg at h
    -- If the points are closer than `n^(2/3)` together, then we can solve the problem by
    -- picking the furthest such points `a` and `b`, and choosing the best perpendiculer line
    -- through the segment of with `1/2` at the edge.
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ᵉ (a ∈ S) (b ∈ S), ∀ᵉ (x ∈ S) (y ∈ S), dist x y ≤ dist a b := by
      -- sorry
      have : Nonempty S := Nonempty.to_subtype (Finset.card_pos.mp (by omega))
      obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, _, hab⟩ := Set.Finite.exists_maximal_wrt (fun xy : S × S => dist xy.1.val xy.2.val)
          Set.univ Set.finite_univ Set.univ_nonempty
      use a, ha, b, hb
      intro x hx y hy
      specialize hab ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ (Set.mem_univ _)
      dsimp at hab
      contrapose! hab
      constructor <;> linarith only [hab]

    sorry

#check Submodule.mem_orthogonal_singleton_iff_inner_right
