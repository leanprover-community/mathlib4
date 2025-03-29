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
      replace disjoint : Disjoint (interval i) (interval j) := disjoint h
      rw [Set.disjoint_left] at disjoint
      exact disjoint hi hj
    rw [card_univ, Fintype.card_fin] at this
    omega
  push_neg at h; simp at h
  -- the `i`th interval in disjoint with `(f '' S) ∩ (a, b)`
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

/-- Computes "how far along" the segment from `a` to `b` the point `p` lies. -/
noncomputable def project (a b p : P) : ℝ := innerSL ℝ (a -ᵥ b) (a -ᵥ p) / ‖a -ᵥ b‖

@[simp] theorem project_self_left  (a b : P) : project a b a = 0 := by simp [project]
@[simp] theorem project_self_right (a b : P) (h : a ≠ b := by positivity) :
    project a b b = ‖a -ᵥ b‖ := by
  simp [project]
  rw [real_inner_self_eq_norm_sq, div_eq_iff, pow_two]
  · rwa [norm_ne_zero_iff, vsub_ne_zero]


open scoped Classical

theorem exists_affine_between_and_separated {ι : Type*} (S : Finset ι) (f : ι → P) (n : ℝ)
    (a b : P) (i j : ℝ) (hi : 0 ≤ i) (hij : i < j) (hj : j ≤ dist a b)
    (hS : #{p ∈ S | project a b (f p) ∈ Set.Ioo i j} ≤ n - 1)
    (hab : a ≠ b) :
    ∃ l : AffineSubspace ℝ P, finrank ℝ l.direction = dim ∧ l.SOppSide a b ∧
    ∀ p ∈ S, (j - i) / (2 * n) ≤ Metric.infDist (f p) l := by

  obtain ⟨x, x_ioo, hx⟩ := exists_between_and_separated S (project a b <| f ·) (⌊n-1⌋₊+1) i j hij
    (by
    rw [← Nat.cast_lt (α := ℝ)]; push_cast
    exact lt_of_le_of_lt hS (Nat.lt_floor_add_one (n - 1)))

  use .mk' (AffineMap.lineMap a b (x / dist a b)) (LinearMap.ker (innerₛₗ ℝ (a -ᵥ b)))

  have : Nonempty (AffineSubspace.mk'
      (AffineMap.lineMap a b (x / dist a b)) (LinearMap.ker (innerₛₗ ℝ (a -ᵥ b)))) := by
    constructor
    use (AffineMap.lineMap a b (x / dist a b))
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
    · simp [hab, lt_of_le_of_lt hi x_ioo.1, lt_of_lt_of_le x_ioo.2 hj, div_lt_one]
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
    _ ≤ ‖a -ᵥ b‖ * ((j - i) / (2 * ↑(⌊n - 1⌋₊ + 1))) := by
      gcongr
      · linarith only [hij]
      · push_cast; rw [← le_sub_iff_add_le]
        refine Nat.floor_le (le_trans (by simp) hS)
    _ ≤ |x * ‖a -ᵥ b‖ - ⟪a -ᵥ b, a -ᵥ f p⟫| := hx
    _ = |⟪a -ᵥ b, f p -ᵥ (AffineMap.lineMap a b) (x / ‖a -ᵥ b‖)⟫| := by
      congr 1
      rw [sub_eq_iff_eq_add', ← inner_add_right]
      simp
      rw [inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp; ring
    _ = |⟪a -ᵥ b, f p -ᵥ y⟫| := by congr 1; rw [← sub_eq_zero, ← inner_sub_right]; simp; exact hy
    _ ≤ ‖a -ᵥ b‖ * ‖f p -ᵥ y‖ := abs_real_inner_le_norm ..


theorem card_le_of_separated {ι : Type*} (S : Finset ι) (f : ι → ℝ) {ε a b : ℝ} (hε : 0 < ε)
    (hab : a ≤ b) (h_sep : (S : Set ι).Pairwise fun x y => ε ≤ dist (f x) (f y))
    (hbound : ∀ x ∈ S, f x ∈ Set.Icc a b) : #S ≤ ⌊(b - a) / ε + 1⌋ := by
  suffices h : #S ≤ #(Icc 0 ⌊(b - a) / ε⌋) by
    have : 0 ≤ ⌊(b - a) / ε⌋ + 1 := by
      have := sub_nonneg_of_le hab
      positivity
    simpa [this] using h
  apply Finset.card_le_card_of_injOn fun x => ⌊(f x - a) / ε⌋
  · intro x hx
    rw [mem_Icc]; constructor
    · rw [Int.floor_nonneg]
      refine div_nonneg ?_ hε.le
      rw [sub_nonneg]
      exact (hbound x hx).1
    · apply Int.floor_le_floor
      rw [div_le_div_iff_of_pos_right hε, sub_le_sub_iff_right]
      exact (hbound x hx).2
  · intro x hx y hy h
    apply Int.abs_sub_lt_one_of_floor_eq_floor at h
    field_simp at h
    rw [abs_div, abs_eq_self.mpr hε.le, div_lt_one hε] at h
    contrapose! h
    exact h_sep hx hy h

/--
In a strip of width `1/2`, if the points have pairwise distance at least `1`,
then we can bound the number of points.
-/
theorem card_le_of_separated_in_strip (eqv : P ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2)) (S : Finset P)
    (h_sep : (S.filter (eqv · 0 ∈ Set.Ioo 0 (1/2)) : Set P).Pairwise fun x y => 1 ≤ dist x y)
    (N : ℝ) (hN : 1 ≤ N) (h_bound : ∀ x ∈ S.filter (eqv · 0 ∈ Set.Ioo 0 (1/2)), |eqv x 1| ≤ N) :
    #(S.filter (eqv · 0 ∈ Set.Ioo 0 (1/2))) ≤ N*6-1 := by
  suffices h : #(S.filter (eqv · 0 ∈ Set.Ioo 0 (1/2))) ≤ ⌊(N - (-N)) / (1/2) + 1⌋ by
    rw [Int.le_floor, Int.cast_natCast] at h
    linarith only [h, hN]
  refine card_le_of_separated (S.filter (eqv · 0 ∈ Set.Ioo 0 (1/2))) (eqv · 1)
    (by norm_num) (by linarith only [hN]) ?_
    (fun x hx => ⟨neg_le_of_abs_le (h_bound x hx), le_of_abs_le (h_bound x hx)⟩)
  intro x hx y hy h_ne
  specialize h_sep hx hy h_ne
  dsimp only
  have := EuclideanSpace.dist_eq (eqv x) (eqv y)
  simp at this
  rw [this] at h_sep
  rw [Real.one_le_sqrt] at h_sep
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  suffices (dist (eqv x 0) (eqv y 0))^2 ≤ (1/2)^2 by
    linarith only [this, h_sep]
  rw [sq_le_sq₀ (by positivity) (by positivity), Real.dist_eq, abs_le]
  rw [coe_filter] at hx hy
  rcases hx with ⟨_, xl, xr⟩
  rcases hy with ⟨_, yl, yr⟩
  constructor
  · linear_combination xl + yr
  · linear_combination xr + yl


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
  by_cases h_dist : ∃ᵉ (a ∈ S) (b ∈ S), (n : ℝ) ^ (2 / 3 : ℝ) ≤ dist a b
  · -- If there are points with distance at least `n^(2/3)`, then we can solve the problem by
    -- choosing the best perpendicular line though this segment.
    -- sorry
    obtain ⟨a, ha, b, hb, hab⟩ := h_dist
    have : 0 < dist a b := lt_of_lt_of_le (by positivity) hab
    rw [dist_pos] at this
    obtain ⟨l, rank, _sOpp, h⟩ := exists_affine_between_and_separated 1 S (·) (n*2) a b 0 (dist a b)
      le_rfl (dist_pos.mpr this) le_rfl (by
      rw [le_sub_iff_add_le]; norm_cast
      exact lt_of_le_of_lt (card_filter_le S _) (by omega)) this
    norm_num at h
    use l, rank
    constructor; · use a, b, ha, hb
    intro p hp
    specialize h p hp
    trans; swap; · exact h
    rw [le_div_iff₀ (by positivity)]
    trans; swap; · exact hab
    rw [neg_div, Real.rpow_neg (by positivity)]
    field_simp [div_le_iff₀]
    rw [← Real.rpow_add (by positivity)]
    norm_num; linarith only

  push_neg at h_dist
  -- If the points are closer than `n^(2/3)` together, then we can solve the problem by
  -- picking the furthest such points `a` and `b`, and choosing the best perpendiculer line
  -- through the segment of width `1/2` at the edge.
  obtain ⟨a, ha, b, hb, h_max⟩ : ∃ᵉ (a ∈ S) (b ∈ S), ∀ᵉ (x ∈ S) (y ∈ S), dist x y ≤ dist a b := by
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
  have h_ne : a ≠ b := by
    rintro rfl
    simp [← Finset.card_le_one] at h_max
    omega
  have : 0 < ‖b -ᵥ a‖ := by
    simp [h_ne.symm]

  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 1
  obtain ⟨basis, hbasis₀⟩ := by
    refine Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℝ) (ι := Fin 2) (by simp [‹Fact (finrank ℝ V = 2)›.1]) (v := fun _ => ‖b -ᵥ a‖⁻¹ • (b -ᵥ a)) (s := {i | i = 0}) ?_
    simp [Set.restrict_def]
    rw [orthonormal_iff_ite]
    simp
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_mul_norm]
    field_simp
  simp at hbasis₀
  let eqv := (AffineIsometryEquiv.vaddConst ℝ a).symm.trans basis.repr.toAffineIsometryEquiv
  have h_iso_b : eqv b = EuclideanSpace.single 0 (dist a b) := by
    simp [eqv]
    ext i
    rw [OrthonormalBasis.repr_apply_apply]
    match i with
    | 0 =>
      simp [hbasis₀]
      rw [dist_eq_norm_vsub', real_inner_smul_left, real_inner_self_eq_norm_mul_norm]
      field_simp
    | 1 =>
      rw [eq_inv_smul_iff₀ (by positivity)] at hbasis₀
      rw [← hbasis₀, real_inner_smul_right]
      simp
  have project_eq_eqv (p) : project a b p = eqv p 0 := by
    simp [project, eqv]
    rw [OrthonormalBasis.repr_apply_apply, hbasis₀, real_inner_smul_left]
    rw [← neg_vsub_eq_vsub_rev b, ← neg_vsub_eq_vsub_rev p, inner_neg_neg, norm_neg]
    ring
  -- Compute a bount for the points lying in a strip on the edge
  have strip_bound (x) (h : x ∈ S.filter (eqv · 0 ∈ Set.Ioo 0 (1/2))) : |eqv x 1| ≤ √(dist a b) := by
    apply Real.abs_le_sqrt
    rw [mem_filter] at h
    obtain ⟨hx, h₁, h₂⟩ := h
    specialize h_max x hx b hb
    have := EuclideanSpace.dist_eq (eqv x) (eqv b)
    simp at this; simp [h_iso_b] at this
    rw [this, Real.sqrt_le_left (by positivity), Real.dist_eq] at h_max
    have : 1 ≤ dist a b := one_le_dist ha hb h_ne
    rw [abs_eq_neg_self.mpr (by linarith only [this, h₂]), ← sub_nonneg] at h_max
    have : dist a b * eqv x 0 * 2 < dist a b := by
      rwa [mul_assoc, ← lt_div_iff₀' (by positivity), div_self (by positivity), ← lt_div_iff₀ (by norm_num)]
    linarith only [this, h_max, sq_nonneg (eqv x 0)]

  have bound := by
    refine card_le_of_separated_in_strip eqv S ?_ _ (Real.one_le_sqrt.mpr (one_le_dist ha hb h_ne)) strip_bound
    · intro x hx y hy; rw [coe_filter] at hx hy; exact one_le_dist hx.1 hy.1
  simp_rw [← project_eq_eqv] at bound
  obtain ⟨l, rank, _sOpp, h⟩ := exists_affine_between_and_separated 1 S (·) _ a b 0 (1/2) le_rfl
    (by norm_num) (by linarith only [one_le_dist ha hb h_ne]) bound h_ne
  use l, rank
  constructor; · use a, b, ha, hb
  intro p hp
  specialize h p hp
  trans; swap; · exact h
  field_simp [le_div_iff₀, show 0 < dist a b by simp [h_ne]]

  specialize h_dist a ha b hb
  replace h_dist := Real.sqrt_le_sqrt h_dist.le
  rw [← mul_le_mul_right (show (0:ℝ) < 6 by norm_num)] at h_dist
  rw [← mul_le_mul_left (show (0:ℝ) < 2 by norm_num)] at h_dist
  rw [← mul_le_mul_left (show (0:ℝ) < 2 by norm_num)] at h_dist
  rw [← le_div_iff₀' (by positivity)]
  trans; · exact h_dist
  rw [le_div_iff₀' (by positivity)]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  rw [show (-1/3:ℝ) = -(1/3) by norm_num, Real.rpow_neg (by positivity)]
  norm_num
  ring_nf
  field_simp
  norm_num
