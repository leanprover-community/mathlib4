import Mathlib


section lineMap

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

end lineMap

open Finset

theorem exists_between_and_separated {ι : Type*} (S : Finset ι) (f : ι → ℝ) (n : Nat)
    (a b : ℝ) (hab : a < b) (hS : #{p ∈ S | f p ∈ Set.Ioo a b} < n) :
    ∃ x ∈ Set.Ioo a b, ∀ p ∈ S, (b - a) / (2 * n) ≤ |x - f p| := by
  have : n > 0 := by omega
  -- make `n` defEq to `_ + 1`
  cases' n with n; · contradiction
  set n := n+1
  -- separate the interval `(0,1)` into `n` equally spaced intervals
  let interval (i : Fin n) : Set ℝ :=
    Set.Ioo (AffineMap.lineMap a b ((i : ℝ) / n)) (AffineMap.lineMap a b (((i : ℝ) + 1) / n))

  let rel (p : ι) (k : Fin n) : Prop :=
    f p ∈ interval k

  by_cases h : ∀ k ∈ Finset.univ, ∃ p ∈ ({p ∈ S | f p ∈ Set.Ioo a b} : Finset _), rel p k
  · -- show that the `n` intervals are disjoint
    have disjoint : Pairwise fun i j => Disjoint (interval i) (interval j) := by
      rw [pairwise_disjoint_on]
      intro i j hlt
      unfold interval
      rw [Set.Ioo_disjoint_Ioo]; apply le_sup_of_le_right; apply inf_le_of_left_le
      rw [lineMap_le_lineMap_iff_of_lt' hab]
      gcongr
      norm_cast
    -- use the pigeon hole principle on the disjoint intervals
    have := card_le_card_of_forall_subsingleton' rel h <| by
      simp only [mem_univ, true_and]
      intro p _
      unfold rel
      intro i hi j hj
      by_contra h
      have : Disjoint (interval i) (interval j) := disjoint h
      rw [Set.disjoint_left] at this
      exact this hi hj
    rw [card_univ, Fintype.card_fin] at this
    omega
  push_neg at h; simp at h
  -- the `i`th interval in disjoint with `S`
  obtain ⟨i, h⟩ := h; unfold rel at h
  -- use the midpoint of the `i`th interval
  use AffineMap.lineMap a b (i / n + 1 / (2 * n) : ℝ)
  have ineq₁: (i / n : ℝ) ≤ 1 - 1 / n := by field_simp [n]; gcongr; apply Fin.is_le
  have : b - a > 0 := sub_pos.mpr hab
  -- check that the point is in between `a` and `b`
  constructor; constructor
  · simp [AffineMap.lineMap_apply_ring']
    positivity
  · rw [AffineMap.lineMap_apply_ring']
    have ineq₂: (1 / (2 * n) : ℝ) < 1 / n := by
      gcongr; norm_cast; omega
    linear_combination (ineq₁ + ineq₂) * (b - a)
  intro p hp
  -- the `i`th interval is disjoint with `f '' S`
  have : f p ∉ interval i := by
    by_cases ha : a < f p; by_cases hb : f p < b
    · exact h p hp ha hb
    · apply Set.not_mem_Ioo_of_ge
      push_neg at hb
      rw [AffineMap.lineMap_apply_ring']
      linear_combination ineq₁ * (b - a) + hb
    · apply Set.not_mem_Ioo_of_le
      push_neg at ha
      rw [AffineMap.lineMap_apply_ring']
      have ineq₃ : (0:ℝ) ≤ i / n := by positivity
      linear_combination ineq₃ * (b - a) + ha
  simp only [interval, Set.mem_Ioo, not_and_or, not_lt] at this
  -- `y ∈ S` is either above or below the interval, either way we get the bound
  rcases this with h | h
  · trans; swap; · apply le_abs_self
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le']
    trans; · exact h
    rw [AffineMap.lineMap_apply_ring', AffineMap.lineMap_apply_ring']
    ring_nf; rfl
  · rw [abs_sub_comm]
    trans; swap; · apply le_abs_self
    rw [le_sub_iff_add_le]
    trans; swap; · exact h
    rw [AffineMap.lineMap_apply_ring', AffineMap.lineMap_apply_ring']
    ring_nf; rfl



open Module
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] (dim : Nat) [Fact (finrank ℝ V = dim+1)]


noncomputable def project (a b p : P) : ℝ := innerSL ℝ (a -ᵥ b) (a -ᵥ p) / (‖a -ᵥ b‖ ^ 2)

@[simp] theorem project_self_left  (a b : P) : project a b a = 0 := by simp [project]
@[simp] theorem project_self_right (a b : P) (h : a ≠ b := by positivity) : project a b b = 1 := by
    simp [project]
    rw [real_inner_self_eq_norm_sq, div_self]
    apply pow_ne_zero 2; rwa [norm_ne_zero_iff, vsub_ne_zero]


open scoped Classical

theorem exists_affine_between_and_separated {ι : Type*} (S : Finset ι) (f : ι → P) (n : Nat)
    (a b : P) (i j : ℝ) (hi : 0 ≤ i) (hij : i < j) (hj : j ≤ 1)
    (hS : #{p ∈ S | project a b (f p) ∈ Set.Ioo i j} < n)
    (hab : a ≠ b) :
    ∃ l : AffineSubspace ℝ P, finrank ℝ l.direction = dim ∧ l.SOppSide a b ∧
    ∀ p ∈ S, dist a b * ((j - i) / (2 * n)) ≤ Metric.infDist (f p) l := by

  obtain ⟨x, x_ioo, hx⟩ := exists_between_and_separated S (project a b <| f ·) n i j hij hS

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
    · simp [hab, lt_of_le_of_lt hi x_ioo.1, lt_of_lt_of_le x_ioo.2 hj]
    · simp [hab, (lt_of_le_of_lt hi x_ioo.1).ne.symm]

  intro p hp
  -- we show that the distance between `p` and the plane corresponds to
  -- the distance between `project p` and `x`.
  specialize hx p hp
  rw [project, sub_div' (by positivity), abs_div, le_div_iff₀' (by positivity),
    abs_of_pos (by positivity)] at hx
  rw [Metric.infDist_eq_iInf]
  apply le_ciInf
  simp [dist_eq_norm_vsub]
  intro y hy
  rw [← mul_le_mul_left this]
  calc
    _ = ‖a -ᵥ b‖ ^ 2 * ((j - i) / (2 * ↑n)) := by ring
    _ ≤ |x * ‖a -ᵥ b‖ ^ 2 - ⟪a -ᵥ b, a -ᵥ f p⟫| := hx
    _ = |⟪a -ᵥ b, f p -ᵥ (AffineMap.lineMap a b) x⟫| := by
      congr 1
      rw [sub_eq_iff_eq_add', ← inner_add_right]
      simp [inner_smul_right, real_inner_self_eq_norm_sq]
    _ = |⟪a -ᵥ b, f p -ᵥ y⟫| := by congr 1; rw [← sub_eq_zero, ← inner_sub_right]; simp; exact hy
    _ ≤ ‖a -ᵥ b‖ * ‖f p -ᵥ y‖ := abs_real_inner_le_norm _ _

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
    obtain ⟨l, rank, sOpp, h⟩ := exists_affine_between_and_separated 1 S (·) (n*2) a b 0 1
      le_rfl zero_lt_one le_rfl (lt_of_le_of_lt (card_filter_le S _) (by omega)) this
    norm_num at h
    use l, rank
    constructor; · use a, b, ha, hb
    intro p hp
    specialize h p hp
    trans; swap; · exact h
    rw [← mul_inv_le_iff₀ (by positivity)]
    trans; swap; · exact hab
    rw [neg_div, Real.rpow_neg (by positivity)]
    field_simp [div_le_iff₀]
    rw [← Real.rpow_add (by positivity)]
    norm_num; linarith only

  · push_neg at h
    -- If the points are closer than `n^(2/3)` together, then we can solve the problem by
    -- picking the furthest such points `a` and `b`, and choosing the best perpendiculer line
    -- through the segment of width `1/2` at the edge.
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ᵉ (a ∈ S) (b ∈ S), ∀ᵉ (x ∈ S) (y ∈ S), dist x y ≤ dist a b := by
      -- sorry
      have : Nonempty S := Nonempty.to_subtype (Finset.card_pos.mp (by omega))
      obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, _, hab⟩ :=
        Set.Finite.exists_maximal_wrt (fun xy : S × S => dist xy.1.val xy.2.val)
          Set.univ Set.finite_univ Set.univ_nonempty
      use a, ha, b, hb
      intro x hx y hy
      specialize hab ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ (Set.mem_univ _)
      dsimp at hab
      contrapose! hab
      constructor <;> linarith only [hab]

    sorry
