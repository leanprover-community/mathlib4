import Mathlib

noncomputable section

section foo

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] --[ProperSpace E]
variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
variable {X : Type*} [NormedAddCommGroup X]

variable {L}

lemma IsZLattice.exists_forall_norm_lt_mul_imp_abs_repr_lt
    {ι : Type*} (b : Basis ι ℤ L) :
    ∃ (ε : ℝ), 0 < ε ∧ ∀ (x : L) (n : ℕ), ‖x‖ < n * ε → ∀ i, |b.repr x i| < n := by
  wlog H : IsZLattice ℝ L
  · have inst : Finite ι := Module.Finite.finite_basis b
    let E' := Submodule.span ℝ (L : Set E)
    let L' : Submodule ℤ E' := ZLattice.comap ℝ L E'.subtype
    have inst : DiscreteTopology L' :=
      ZLattice.comap_discreteTopology _ _ (by fun_prop) Subtype.val_injective
    let e : L' ≃ₗ[ℤ] L := Submodule.comapSubtypeEquivOfLe (p := L) (q := E'.restrictScalars ℤ)
      Submodule.subset_span
    have inst : IsZLattice ℝ L' := by
      refine ⟨Submodule.map_injective_of_injective (f := E'.subtype) Subtype.val_injective ?_⟩
      simp [Submodule.map_span, E', L', Set.image_preimage_eq_inter_range,
        Set.inter_eq_left.mpr Submodule.subset_span]
    obtain ⟨ε, hε, H⟩ := this (b.map e.symm) inst
    exact ⟨ε, hε, fun x n h i ↦ by simpa using H ⟨⟨x.1, Submodule.subset_span x.2⟩, x.2⟩ n h i⟩
  have : Finite ι := Module.Finite.finite_basis b
  let b' : Basis ι ℝ E := Basis.ofZLatticeBasis ℝ L b
  let e := ((b'.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _).toContinuousLinearEquiv (𝕜 := ℝ))
  have := e.continuous.1 (Set.univ.pi fun _ ↦ Set.Ioo (-1) 1)
    (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo)
  obtain ⟨ε, hε, hε'⟩ := Metric.isOpen_iff.mp this 0 (by simp)
  refine ⟨ε, hε, fun x n hxn i ↦ ?_⟩
  have hn : (n : ℝ) ≠ 0 := fun e ↦ hxn.not_ge (by simp [e])
  have : ‖(n : ℝ)⁻¹ • x.1‖ < ε := by
    rwa [norm_smul, norm_inv, inv_mul_lt_iff₀ (by positivity), Real.norm_natCast]
  have : (n : ℝ)⁻¹ * |(b.repr x i : ℝ)| < 1 := by
    have := hε' (by simpa using this) i trivial
    simpa [b', e, ← abs_lt, abs_mul, abs_inv] using this
  rw [inv_mul_lt_iff₀ (by positivity), mul_one] at this
  norm_cast at this

def IsZLattice.normBound {ι : Type*} (b : Basis ι ℤ L) : ℝ :=
  (exists_forall_norm_lt_mul_imp_abs_repr_lt b).choose

lemma IsZLattice.normBound_pos {ι : Type*} (b : Basis ι ℤ L) : 0 < normBound b :=
  (exists_forall_norm_lt_mul_imp_abs_repr_lt b).choose_spec.1

lemma IsZLattice.normBound_spec {ι : Type*} (b : Basis ι ℤ L) (x : L) (n : ℕ)
    (hxn : ‖x‖ < n * normBound b) (i : ι) : |b.repr x i| < n :=
  (exists_forall_norm_lt_mul_imp_abs_repr_lt b).choose_spec.2 x n hxn i

lemma IsZLattice.mul_normBound_le_norm {ι : Type*} (b : Basis ι ℤ L) (x : L) (n : ℕ) (i : ι)
    (hi : n ≤ |b.repr x i|) : n * normBound b ≤ ‖x‖ := by
  contrapose! hi
  exact normBound_spec b x n hi i

@[to_additive]
lemma Finset.prod_eq_prod_range_sdiff
    {α β : Type*} [DecidableEq α] [CommMonoid β] (s : ℕ → Finset α) (hf : Monotone s)
     (g : α → β) (n : ℕ) :
    ∏ i ∈ s n, g i = (∏ i ∈ s 0, g i) * ∏ i ∈ range n, ∏ j ∈ s (i + 1) \ s i, g j := by
  have : s n = s 0 ∪ (range n).biUnion fun i ↦ s (i + 1) \ s i := by
    induction n with
    | zero => simp
    | succ n IH =>
      rw [range_succ, biUnion_insert, ← union_assoc, union_right_comm, ← IH,
        union_sdiff_self_eq_union, eq_comm, union_eq_right]
      exact hf n.le_succ
  rw [this, prod_union, prod_biUnion]
  · rintro i - j - e
    simp only [Function.onFun, disjoint_iff_inter_eq_empty]
    wlog h : j < i generalizing i j
    · rw [← this e.symm (lt_of_le_of_ne (le_of_not_gt h) e), inter_comm]
    ext x
    simp only [mem_inter, mem_sdiff, notMem_empty, iff_false, not_and, Decidable.not_not, and_imp]
    exact fun _ h₁ h₂ ↦ (h₁ (hf h h₂)).elim
  · rw [disjoint_iff_inter_eq_empty]
    ext x
    have : x ∈ s 0 → ∀ n, x ∈ s n := fun H n ↦ hf (Nat.zero_le _) H
    simp +contextual [this]

open Finset in
lemma IsZLattice.sum_piFinset_Icc_rpow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ L) {d : ℕ} (hd : d = Fintype.card ι)
    (n : ℕ) (r : ℝ) (hr : r < -d) :
    ∑ p ∈ Fintype.piFinset fun _ : ι ↦ Icc (-n : ℤ) n, ‖∑ i, p i • b i‖ ^ r ≤
      2 * d * 3 ^ (d - 1) * normBound b ^ r * ∑' k : ℕ, (k : ℝ) ^ (d - 1 + r) := by
  let s (n : ℕ) := Fintype.piFinset fun i : ι ↦ Icc (-n : ℤ) n
  subst hd
  set d := Fintype.card ι
  have hr' : r < 0 := hr.trans_le (by linarith)
  by_cases hd : d = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hd
    simp [hd, hr'.ne]
  replace hd : 1 ≤ d := by rwa [Nat.one_le_iff_ne_zero]
  have hs0 : s 0 = {0} := by ext; simp [s, funext_iff]
  have hs {a b : ℕ} (ha : a ≤ b) : s a ⊆ s b := by
    intros x hx
    simp only [Fintype.mem_piFinset, s] at hx ⊢
    exact fun i ↦ Icc_subset_Icc (by simpa) (by simpa) (hx i)
  have (k : ℕ) : #(s (k + 1) \ s k) ≤ 2 * d * (2 * k + 3) ^ (d - 1) := by
    trans (2 * k + 3) ^ d - (2 * k + 1) ^ d
    · rw [card_sdiff]
      · simp only [Fintype.card_piFinset, Int.card_Icc, prod_const, card_univ, s, sub_neg_eq_add]
        gcongr <;> norm_cast <;> omega
      · exact hs (by simp)
    · have := abs_pow_sub_pow_le (α := ℤ) ↑(2 * k + 3) ↑(2 * k + 1) d
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        add_sub_add_left_eq_sub, Int.reduceSub, Nat.abs_ofNat, s] at this
      zify
      convert this using 3
      · rw [abs_eq_self.mpr, Nat.cast_sub]
        · simp
        · gcongr; omega
        · rw [sub_nonneg]
          gcongr; omega
      · rw [max_eq_left, abs_eq_self.mpr]
        · positivity
        gcongr; omega
  let ε := normBound b
  have hε : 0 < ε := normBound_pos b
  calc ∑ p ∈ s n, ‖∑ i, p i • b i‖ ^ r
      = ∑ k ∈ range n, ∑ p ∈ (s (k + 1) \ s k), ‖∑ i, p i • b i‖ ^ r := by
        rw [Finset.sum_eq_sum_range_sdiff _ @hs]
        simp [hs0, hr'.ne]
    _ ≤ ∑ k ∈ range n, ∑ p ∈ (s (k + 1) \ s k), ((k + 1) * ε) ^ r := by
        gcongr ∑ k ∈ Finset.range n, ∑ p ∈ (s (k + 1) \ s k), ?_ with k hk v hv
        rw [← Nat.cast_one, ← Nat.cast_add]
        refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hr'.le
        obtain ⟨j, hj⟩ : ∃ i, v i ∉ Icc (-k : ℤ) k := by simpa [s] using (mem_sdiff.mp hv).2
        refine IsZLattice.mul_normBound_le_norm b _ _ j ?_
        suffices ↑k + 1 ≤ |v j| by simpa [Finsupp.single_apply] using this
        by_contra! H
        rw [Int.lt_add_one_iff, abs_le, ← Finset.mem_Icc] at H
        exact hj H
    _ = ∑ k ∈ range n, #(s (k + 1) \ s k) * ((k + 1) * ε) ^ r := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ range n, ↑(2 * d * (2 * k + 3) ^ (d - 1)) * ((k + 1) * ε) ^ r := by
      gcongr with k hk
      · exact this _
    _ ≤ ∑ k ∈ range n, ↑(2 * d * (3 * (k + 1)) ^ (d - 1)) * ((k + 1) * ε) ^ r := by
      gcongr; omega
    _ = 2 * d * 3 ^ (d - 1) * ε ^ r * ∑ k ∈ range n, (k + 1) ^ (d - 1) * (k + 1 : ℝ) ^ r := by
      simp_rw [Finset.mul_sum]
      congr with k
      push_cast
      rw [Real.mul_rpow, mul_pow]
      · group
      · positivity
      · exact (IsZLattice.normBound_pos b).le
    _ = 2 * d * 3 ^ (d - 1) * ε ^ r * ∑ k ∈ range n, (↑(k + 1) : ℝ) ^ (d - 1 + r) := by
      congr with k
      rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity), Nat.cast_sub hd]
      norm_cast
    _ ≤ 2 * d * 3 ^ (d - 1) * ε ^ r * ∑ k ∈ range (n + 1), (k : ℝ) ^ (d - 1 + r) := by
      gcongr
      rw [Finset.sum_range_succ', le_add_iff_nonneg_right]
      positivity
    _ ≤ 2 * d * 3 ^ (d - 1) * ε ^ r * ∑' k : ℕ, (k : ℝ) ^ (d - 1 + r) := by
      gcongr
      refine Summable.sum_le_tsum _ (fun _ _ ↦ by positivity) ?_
      rw [Real.summable_nat_rpow]
      linarith

variable (L)

lemma IsZLattice.exists_finset_sum_norm_rpow_le_tsum :
    ∃ A > (0 : ℝ), ∀ r < (-(Module.finrank ℤ L) : ℝ), ∀ s : Finset L,
      ∑ z ∈ s, ‖z‖ ^ r ≤ A ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r) := by
  cases subsingleton_or_nontrivial L
  · refine ⟨1, zero_lt_one, fun r hr s ↦ ?_⟩
    have hr : r ≠ 0 := by linarith
    simpa [Subsingleton.elim _ (0 : L), Real.zero_rpow hr] using tsum_nonneg fun _ ↦ by positivity
  classical
  let I : Type _ := Module.Free.ChooseBasisIndex ℤ L
  have : Fintype I := inferInstance
  let b : Basis I ℤ L := Module.Free.chooseBasis ℤ L
  simp_rw [Module.finrank_eq_card_basis b]
  set d := Fintype.card I
  have hd : d ≠ 0 := by simp [d]
  let ε := IsZLattice.normBound b
  obtain ⟨A, hA, B, hB, H⟩ : ∃ A > (0 : ℝ), ∃ B > (0 : ℝ), ∀ r < (-d : ℝ), ∀ s : Finset L,
      ∑ z ∈ s, ‖z‖ ^ r ≤ A * B ^ r * ∑' k : ℕ, (k : ℝ) ^ (d - 1 + r) := by
    refine ⟨2 * d * 3 ^ (d - 1), by positivity, ε, normBound_pos b, fun r hr u ↦ ?_⟩
    let e : (I → ℤ) ≃ₗ[ℤ] L := (b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _).symm
    obtain ⟨u, rfl⟩ : ∃ u' : Finset _, u = u'.image e.toEmbedding :=
      ⟨u.image e.symm.toEmbedding, Finset.coe_injective
        (by simpa using (e.image_symm_image _).symm)⟩
    dsimp
    simp only [EmbeddingLike.apply_eq_iff_eq, implies_true, Set.injOn_of_eq_iff_eq,
      Finset.sum_image, ge_iff_le]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, u ⊆ Fintype.piFinset fun _ : I ↦ Finset.Icc (-n : ℤ) n := by
      obtain ⟨r, hr, hr'⟩ := u.finite_toSet.isCompact.isBounded.subset_closedBall_lt 0 0
      refine ⟨⌊r⌋.toNat, fun x hx ↦ ?_⟩
      have hr'' : ⌊r⌋ ⊔ 0 = ⌊r⌋ := by simp; positivity
      have := hr' hx
      simp only [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr.le,
        Int.norm_eq_abs, ← Int.cast_abs, ← Int.le_floor] at this
      simpa only [Int.ofNat_toNat, Fintype.mem_piFinset, Finset.mem_Icc, ← abs_le, hr'']
    refine (Finset.sum_le_sum_of_subset_of_nonneg hn (by intros; positivity)).trans ?_
    dsimp
    simp only [Submodule.norm_coe]
    convert IsZLattice.sum_piFinset_Icc_rpow_le b rfl n r hr with x
    simp [e, Finsupp.linearCombination]
    rfl
  have (r : ℝ) : 0 ≤ ∑' k : ℕ, (k : ℝ) ^ (d - 1 + r) := tsum_nonneg fun _ ↦ by positivity
  by_cases hA' : A ≤ 1
  · refine ⟨B, hB, fun r hr s ↦ (H r hr s).trans ?_⟩
    rw [mul_assoc]
    exact mul_le_of_le_one_left (mul_nonneg (by positivity) (this r)) hA'
  · refine ⟨A⁻¹ * B, mul_pos (inv_pos.mpr hA) hB, fun r hr s ↦ (H r hr s).trans ?_⟩
    rw [Real.mul_rpow (inv_pos.mpr hA).le hB.le, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by positivity) (this r))
    rw [← Real.rpow_neg_one, ← Real.rpow_mul hA.le]
    refine Real.self_le_rpow_of_one_le (not_le.mp hA').le ?_
    simp only [neg_mul, one_mul, le_neg (b := r)]
    refine hr.le.trans ?_
    norm_num
    exact Nat.one_le_iff_ne_zero.mpr hd

def IsZLattice.tsumNormRPowBound : ℝ :=
  (IsZLattice.exists_finset_sum_norm_rpow_le_tsum L).choose

lemma IsZLattice.tsumNormRPowBound_pos : 0 < tsumNormRPowBound L :=
  (IsZLattice.exists_finset_sum_norm_rpow_le_tsum L).choose_spec.1

lemma IsZLattice.tsumNormRPowBound_spec (r : ℝ) (h : r < -(Module.finrank ℤ L)) (s : Finset L) :
    ∑ z ∈ s, ‖z‖ ^ r ≤
      (tsumNormRPowBound L) ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r) :=
  (IsZLattice.exists_finset_sum_norm_rpow_le_tsum L).choose_spec.2 r h s

/-- If `L` is a `ℤ`-lattice with rank `d` in `E`, then `∑ z ∈ L, ‖z‖ʳ` converges when `r < -d`. -/
lemma IsZLattice.summable_norm_rpow (r : ℝ) (hr : r < -(Module.finrank ℤ L)) :
    Summable fun z : L ↦ ‖z‖ ^ r :=
  summable_of_sum_le (fun _ ↦ by positivity) (tsumNormRPowBound_spec L r hr)

lemma IsZLattice.tsum_norm_rpow_le (r : ℝ) (hr : r < -(Module.finrank ℤ L)) :
    ∑' z : L, ‖z‖ ^ r ≤
      (tsumNormRPowBound L) ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r) :=
  Summable.tsum_le_of_sum_le (summable_norm_rpow L r hr) (tsumNormRPowBound_spec L r hr)

lemma IsZLattice.summable_norm_sub_rpow (r : ℝ) (hr : r < -(Module.finrank ℤ L)) (x : E) :
    Summable fun z : L ↦ ‖z - x‖ ^ r := by
  cases subsingleton_or_nontrivial L
  · exact .of_finite
  refine Summable.of_norm_bounded_eventually
    (.mul_left ((1 / 2) ^ r) (IsZLattice.summable_norm_rpow L r hr)) ?_
  have H : IsClosed (X := E) L := @AddSubgroup.isClosed_of_discrete _ _ _ _ _
    L.toAddSubgroup (inferInstanceAs (DiscreteTopology L))
  have := ProperSpace.of_isClosed H
  refine ((Metric.isCompact_of_isClosed_isBounded Metric.isClosed_closedBall
    ((Metric.isBounded_closedBall (x := (0 : L)) (r := 2 * ‖x‖)))).finite inferInstance).subset ?_
  intro t ht
  by_cases ht₁ : ‖t‖ = 0
  · simp [show t = 0 by simpa using ht₁]
  by_cases ht₂ : ‖t - x‖ = 0
  · simp [show t = x by simpa [sub_eq_zero] using ht₂, two_mul]
  have : 0 < Module.finrank ℤ L := Module.finrank_pos
  have : ‖t - x‖ < 2⁻¹ * ‖t‖ := by
    rw [← Real.rpow_lt_rpow_iff_of_neg (z := r)
      (by positivity) (by positivity) (hr.trans (by simpa))]
    simpa [Real.mul_rpow, abs_eq_self.mpr (show 0 ≤ ‖t - x‖ ^ r by positivity)] using ht
  have := (norm_sub_norm_le _ _).trans_lt this
  rw [sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', AddSubgroupClass.coe_norm] at this
  simp only [Metric.mem_closedBall, dist_zero_right, AddSubgroupClass.coe_norm, ge_iff_le]
  linarith

lemma IsZLattice.summable_norm_sub_zpow (r : ℤ) (hr : r < -(Module.finrank ℤ L)) (x : E) :
    Summable fun z : L ↦ ‖z - x‖ ^ r := by
  exact_mod_cast summable_norm_sub_rpow L r (by exact_mod_cast hr) x

lemma deriv_one_div_sub_pow (r : ℕ) (z w : ℂ) :
    deriv (fun z : ℂ ↦ 1 / (z - w) ^ r) z = - (r / (z - w) ^ (r + 1)) := by
  rw [deriv_comp_sub_const (f := fun z ↦ 1 / z ^ r) (a := w)]
  simp only [one_div, ← zpow_natCast, ← zpow_neg, deriv_zpow]
  rw [sub_eq_add_neg (-r : ℤ), ← neg_add, zpow_neg]
  norm_cast
  field_simp

lemma iteratedDeriv_one_div_sub_pow (i : ℕ) (r : ℕ) (z w : ℂ) :
    iteratedDeriv i (fun z : ℂ ↦ 1 / (z - w) ^ r) z =
      (-1) ^ i * r.ascFactorial i * (1 / (z - w) ^ (r + i)) := by
  revert z
  apply funext_iff.mp
  induction i with
  | zero => simp
  | succ n IH =>
    rw [iteratedDeriv_succ, IH]
    simp only [deriv_const_mul_field', deriv_one_div_sub_pow, Nat.ascFactorial_succ]
    ext
    simp
    ring

lemma deriv_one_div_sub_pow' (r : ℕ) (z w : ℂ) :
    deriv (fun z : ℂ ↦ 1 / (w - z) ^ r) z = r / (w - z) ^ (r + 1) := by
  rw [deriv_comp_const_sub (f := fun z ↦ 1 / z ^ r) (a := w)]
  simp only [one_div, ← zpow_natCast, ← zpow_neg, deriv_zpow]
  rw [sub_eq_add_neg (-r : ℤ), ← neg_add, zpow_neg]
  norm_cast
  field_simp

lemma iteratedDeriv_one_div_sub_pow' (i : ℕ) (r : ℕ) (z w : ℂ) :
    iteratedDeriv i (fun z : ℂ ↦ 1 / (w - z) ^ r) z =
      r.ascFactorial i * (1 / (w - z) ^ (r + i)) := by
  revert z
  apply funext_iff.mp
  induction i with
  | zero => simp
  | succ n IH =>
    rw [iteratedDeriv_succ, IH]
    simp only [deriv_const_mul_field', deriv_one_div_sub_pow', Nat.ascFactorial_succ]
    ext
    simp
    ring

lemma Nat.two_ascFactorial (i) : Nat.ascFactorial 2 i = i.factorial * (i + 1) := by
  rw [← Nat.one_ascFactorial, mul_comm, add_comm, ← Nat.succ_ascFactorial, one_mul]

lemma Complex.tsum_eq_one_div_sub_sq (w z : ℂ) (hz : ‖z‖ < ‖w‖) :
    ∑' i : ℕ, (i + 1) * w ^ (- ↑(i + 2) : ℤ) * z ^ i = 1 / (z - w) ^ 2 := by
  convert Complex.taylorSeries_eq_on_ball' (f := fun z ↦ 1 / (z - w) ^ 2)
    (show z ∈ Metric.ball 0 ‖w‖ by simpa using hz) _ using 4 with i
  · rw [iteratedDeriv_one_div_sub_pow, eq_inv_mul_iff_mul_eq₀ (by norm_cast; positivity),
      ← mul_assoc, mul_comm ((-1) ^ _), mul_assoc _ ((-1) ^ _), Nat.two_ascFactorial]
    congr 1
    · norm_cast
    rw [zpow_neg, zpow_natCast, zero_sub, ← neg_one_mul w, mul_pow]
    ring_nf
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ (by simp)]
    norm_num
  · simp
  · exact .div (by fun_prop) (by fun_prop) (by simp [sub_eq_zero, imp_not_comm])

lemma Complex.tsum_add_const_mul_pow (z a : ℂ) (hz : ‖z‖ < 1) :
    ∑' i : ℕ, (i + a) * z ^ i = (a - 1) * 1 / (1 - z) + 1 / (1 - z) ^ 2 := by
  convert Complex.taylorSeries_eq_on_ball'
    (f := (fun z ↦ (a - 1) * (1 / (1 - z) ^ 1)) + (fun z ↦ 1 / (1 - z) ^ 2))
    (show z ∈ Metric.ball 0 1 by simpa using hz) _ using 1
  · rw [sub_zero]
    congr! 3 with i
    rw [iteratedDeriv_add, iteratedDeriv_const_mul, iteratedDeriv_one_div_sub_pow',
      iteratedDeriv_one_div_sub_pow', Nat.two_ascFactorial, Nat.one_ascFactorial]
    · simp only [sub_zero, one_pow, ne_eq, one_ne_zero, not_false_eq_true, div_self, mul_one,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [mul_comm (a - 1), ← mul_add, sub_add_add_cancel, add_comm, inv_mul_cancel_left₀]
      norm_num
      positivity
    · exact .div contDiffAt_const (.pow (by fun_prop) _) (by simp)
    · exact .mul (by fun_prop) (.div (by fun_prop) (.pow (by fun_prop) _) (by simp))
    · exact .div (by fun_prop) (.pow (by fun_prop) _) (by simp)
  · simp [div_eq_mul_inv]
  · refine .add (.mul ?_ (.div ?_ ?_ (by simp [sub_eq_zero, imp_not_comm])))
      (.div ?_ ?_ (by simp [sub_eq_zero, imp_not_comm])) <;> fun_prop

lemma Real.tsum_eq_one_div_sub_sq (w z : ℝ) (hz : |z| < |w|) :
    ∑' i : ℕ, (i + 1) * w ^ (- ↑(i + 2) : ℤ) * z ^ i = 1 / (z - w) ^ 2 := by
  exact_mod_cast Complex.tsum_eq_one_div_sub_sq w z (by simpa)

lemma Real.tsum_add_const_mul_pow (a z : ℝ) (hz : |z| < 1) :
    ∑' i : ℕ, (i + a) * z ^ i = (a - 1) * 1 / (1 - z) + 1 / (1 - z) ^ 2 := by
  exact_mod_cast Complex.tsum_add_const_mul_pow z a (by simpa)

lemma tsum_eq_one_div_sub_sq_sub_one_div_sq (w z x : ℂ) (hz : ‖z - x‖ < ‖w - x‖) :
    1 / (z - w) ^ 2 - 1 / w ^ 2 = ∑' i : ℕ,
      ((i + 1) * (w - x) ^ (- ↑(i + 2) : ℤ) - i.casesOn (w ^ (-2 : ℤ)) 0) * (z - x) ^ i := by
  have := Complex.tsum_eq_one_div_sub_sq (w - x) (z - x) hz
  rw [sub_sub_sub_cancel_right] at this
  rw [← this, ← tsum_ite_eq 0 (1 / w ^ 2), ← Summable.tsum_sub]
  · simp_rw [sub_mul]
    congr! 3 with i
    cases i <;> simp [zpow_ofNat]
  · by_contra H
    obtain rfl : z = w := by
      simpa [sub_eq_zero] using this.symm.trans (tsum_eq_zero_of_not_summable H)
    simp at hz
  · exact summable_of_finite_support ((Set.finite_singleton 0).subset (by simp_all))

def optionProdEquiv {α β : Type*} : Option α × β ≃ β ⊕ α × β where
  toFun x := x.1.casesOn (.inl x.2) (fun a ↦ .inr (a, x.2))
  invFun x := x.casesOn (Prod.mk none) (Prod.map some id)
  left_inv
  | (none, _) => rfl
  | (some _, _) => rfl
  right_inv
  | .inl _ => rfl
  | .inr (_, _) => rfl

lemma not_continuousAt_inv_sq_sub (x : ℂ) : ¬ ContinuousAt (fun z ↦ ((z - x) ^ 2)⁻¹) x := by
  intro H
  have := H (U := Metric.ball 0 1) (Metric.isOpen_ball.mem_nhds (by simp))
  have : {x} ∈ nhds x := by
    convert (nhds x).inter_mem this (Metric.isOpen_ball (x := x) (ε := 1).mem_nhds (by simp))
    ext a
    by_cases hx : a = x
    · simp [hx]
    · simp +contextual [hx, inv_lt_one_iff₀, Complex.dist_eq, sq_nonpos_iff, le_of_lt, sub_eq_zero]
  have := isOpen_singleton_of_finite_mem_nhds _ this (Set.finite_singleton x)
  exact not_isOpen_singleton _ this

@[simp]
lemma Nat.rec_succ {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) (n : ℕ) :
    Nat.rec (motive := C) h0 h ofNat(n + 1) = h n (Nat.rec h0 h n) := rfl

lemma Int.le_floor_add_one {α : Type*}
    [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α] (a : α) :
    a ≤ ↑⌊a⌋ + 1 :=
  (Int.le_ceil a).trans (by norm_cast; exact Int.ceil_le_floor_add_one a)

lemma IsZLattice.isCompact_range_of_periodic
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (f : E → F)
    [TopologicalSpace F] (hf : Continuous f)
    (hf' : ∀ z w, w ∈ L → f (z + w) = f z) : IsCompact (Set.range f) := by
  have := ZLattice.module_free ℝ L
  let b := Module.Free.chooseBasis ℤ L
  convert (b.ofZLatticeBasis ℝ).parallelepiped.isCompact.image hf
  refine le_antisymm ?_ (Set.image_subset_range _ _)
  rintro _ ⟨x, rfl⟩
  let x' : L := b.repr.symm (Finsupp.equivFunOnFinite.symm
    fun i ↦ ⌊(b.ofZLatticeBasis ℝ).repr x i⌋)
  refine ⟨x + (- x'), ?_, hf' _ _ (- x').2⟩
  simp [parallelepiped_basis_eq, x', Int.floor_le, Int.le_floor_add_one, add_comm (1 : ℝ)]

end foo


structure PeriodPairs : Type where
  ω₁ : ℂ
  ω₂ : ℂ
  indep : LinearIndependent ℝ ![ω₁, ω₂]

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (L : PeriodPairs)

def PeriodPairs.basis : Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank L.indep (by simp)

@[simp] lemma PeriodPairs.basis_zero : L.basis 0 = L.ω₁ := by simp [basis]
@[simp] lemma PeriodPairs.basis_one : L.basis 1 = L.ω₂ := by simp [basis]

def PeriodPairs.lattice : Submodule ℤ ℂ := Submodule.span ℤ {L.ω₁, L.ω₂}

lemma PeriodPairs.mem_lattice {L : PeriodPairs} {x : ℂ} :
    x ∈ L.lattice ↔ ∃ m n : ℤ, m * L.ω₁ + n * L.ω₂ = x := by
  simp only [lattice, Submodule.mem_span_pair, zsmul_eq_mul]

lemma PeriodPairs.ω₁_div_two_not_mem_lattice : L.ω₁ / 2 ∉ L.lattice := by
  intro h
  obtain ⟨m, n, e⟩ := mem_lattice.mp h
  rw [← sub_eq_zero] at e
  have := (LinearIndependent.pair_iff.mp L.indep (m - 1/2) n (by convert e using 1; simp; ring)).1
  rw [sub_eq_zero, eq_div_iff (by norm_num)] at this
  norm_cast at this
  exact Int.two_dvd_ne_zero (n := 1).mpr rfl ⟨m, by linarith⟩

lemma PeriodPairs.ω₂_div_two_not_mem_lattice : L.ω₂ / 2 ∉ L.lattice := by
  intro h
  obtain ⟨m, n, e⟩ := mem_lattice.mp h
  rw [← sub_eq_zero] at e
  have := (LinearIndependent.pair_iff.mp L.indep m (n - 1/2) (by convert e using 1; simp; ring)).2
  rw [sub_eq_zero, eq_div_iff (by norm_num)] at this
  norm_cast at this
  exact Int.two_dvd_ne_zero (n := 1).mpr rfl ⟨n, by linarith⟩

-- helper lemma to connect to the ZLattice API
lemma PeriodPairs.lattice_eq_span_range_basis :
    L.lattice = Submodule.span ℤ (Set.range ⇑L.basis) := by
  have : Finset.univ (α := Fin 2) = {0, 1} := rfl
  rw [PeriodPairs.lattice, ← Set.image_univ, ← Finset.coe_univ, this]
  simp [Set.image_insert_eq]

instance : DiscreteTopology L.lattice := by
  rw [L.lattice_eq_span_range_basis]
  infer_instance

instance : IsZLattice ℝ L.lattice := by
  simp_rw [L.lattice_eq_span_range_basis]
  infer_instance

lemma PeriodPairs.isClosed_lattice : IsClosed (X := ℂ) L.lattice :=
  @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.lattice.toAddSubgroup
    (inferInstanceAs (DiscreteTopology L.lattice))

lemma PeriodPairs.isClosed_lattice_sdiff (s : Set ℂ) : IsClosed (L.lattice \ s) := by
  convert L.isClosed_lattice.isClosedMap_subtype_val _ (isClosed_discrete ((↑) ⁻¹' sᶜ))
  · convert Set.image_preimage_eq_inter_range.symm using 1; simp [Set.diff_eq_compl_inter]
  · exact inferInstanceAs (DiscreteTopology L.lattice)

instance PeriodPairs.properSpace_lattice : ProperSpace L.lattice :=
  .of_isClosed L.isClosed_lattice

lemma PeriodPairs.ω₁_mem_lattice : L.ω₁ ∈ L.lattice := Submodule.subset_span (by simp)

lemma PeriodPairs.ω₂_mem_lattice : L.ω₂ ∈ L.lattice := Submodule.subset_span (by simp)

def PeriodPairs.latticeBasis : Basis (Fin 2) ℤ L.lattice :=
  (Basis.span (v := ![L.ω₁, L.ω₂]) (L.indep.restrict_scalars' _)).map
    (.ofEq _ _ (by simp [lattice, Set.pair_comm L.ω₂ L.ω₁]))

@[simp]
lemma PeriodPairs.latticeBasis_zero : L.latticeBasis 0 = L.ω₁ := by
  simp [latticeBasis, Basis.span_apply]

@[simp]
lemma PeriodPairs.latticeBasis_one : L.latticeBasis 1 = L.ω₂ := by
  simp [latticeBasis, Basis.span_apply]

@[simp]
lemma PeriodPairs.finrank_lattice : Module.finrank ℤ L.lattice = 2 :=
    Module.finrank_eq_card_basis L.latticeBasis

def PeriodPairs.latticeEquivProd : L.lattice ≃ₗ[ℤ] ℤ × ℤ :=
  L.latticeBasis.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _ ≪≫ₗ .finTwoArrow ℤ ℤ

lemma PeriodPairs.latticeEquiv_symm_apply (x : ℤ × ℤ) :
    (L.latticeEquivProd.symm x).1 = x.1 * L.ω₁ + x.2 * L.ω₂ := by
  simp [latticeEquivProd, Finsupp.linearCombination]
  rfl

open Topology Filter in
lemma PeriodPairs.tendstoLocallyUniformly_aux (f : L.lattice → ℂ → ℂ)
    (u : ℝ → L.lattice → ℝ) (hu : ∀ r > 0, Summable (u r))
    (hf : ∀ r > 0, ∀ᶠ (R : ℝ) in atTop, ∀ x, ‖x‖ < r →
      ∀ l : L.lattice, ‖l.1‖ = R → ‖f l x‖ ≤ u r l) :
    TendstoLocallyUniformly (∑ i ∈ ·, f i ·) (∑' j, f j ·) Filter.atTop := by
  rw [tendstoLocallyUniformly_iff_filter]
  intro x
  obtain ⟨r, hr, hr'⟩ : ∃ r, 0 < r ∧ 𝓝 x ≤ 𝓟 (Metric.ball 0 r) :=
    ⟨‖x‖ + 1, by positivity, Filter.le_principal_iff.mpr (Metric.isOpen_ball.mem_nhds (by simp))⟩
  refine .mono_right ?_ hr'
  rw [← tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]
  refine tendstoUniformlyOn_tsum_of_cofinite_eventually (hu r hr) ?_
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hf r hr)
  refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : L.lattice) R)).subset ?_
  intros l hl
  simp only [Metric.mem_ball, dist_zero_right, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall,
    not_le, Metric.mem_closedBall, AddSubgroupClass.coe_norm] at hl ⊢
  obtain ⟨s, hs, hs'⟩ := hl
  contrapose! hs'
  exact hR _ hs'.le _ hs _ rfl

lemma PeriodPairs.℘_bound (r : ℝ) (hr : r > 0) (s : ℂ) (hs : ‖s‖ < r)
    (l : ℂ) (h : 2 * r ≤ ‖l‖) :
    ‖1 / (s - l) ^ 2 - 1 / l ^ 2‖ ≤ 10 * r * ‖l‖ ^ (-3 : ℝ) := by
  have : s ≠ ↑l := by rintro rfl; exfalso; linarith
  have : 0 < ‖l‖ := by
    suffices l ≠ 0 by simpa
    rintro rfl
    simp only [norm_zero] at h
    linarith
  calc
    _ = ‖(↑l ^ 2 - (s - ↑l) ^ 2) / ((s - ↑l) ^ 2 * ↑l ^ 2)‖ := by
      rw [div_sub_div, one_mul, mul_one]
      · simpa [sub_eq_zero]
      · simpa
    _ = ‖l ^ 2 - (s - l) ^ 2‖ / (‖s - l‖ ^ 2 * ‖l‖ ^ 2) := by simp
    _ ≤ ‖l ^ 2 - (s - l) ^ 2‖ / ((‖l‖ / 2) ^ 2 * ‖l‖ ^ 2) := by
      gcongr
      rw [norm_sub_rev]
      exact .trans (by linarith) (norm_sub_norm_le l s)
    _ = ‖s * (2 * l - s)‖ / (‖l‖ ^ 4 / 4) := by
      congr 1
      · rw [sq_sub_sq]; simp [← sub_add, two_mul, sub_add_eq_add_sub]
      · ring
    _ = (‖s‖ * ‖2 * l - s‖) / (‖l‖ ^ 4 / 4) := by simp
    _ = (4 * ‖s‖ * ‖2 * l - s‖) / ‖l‖ ^ 4 := by field_simp; ring
    _ ≤ (4 * r * (2.5 * ‖l‖)) / ‖l‖ ^ 4 := by
      gcongr (4 * ?_ * ?_) / ‖l‖ ^ 4
      refine (norm_sub_le _ _).trans ?_
      simp only [Complex.norm_mul, Complex.norm_ofNat]
      linarith
    _ = 10 * r / ‖l‖ ^ 3 := by field_simp; ring
    _ = _ := by norm_cast

section ℘Except

def PeriodPairs.℘Except (l₀ : ℂ) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l.1 = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2)

lemma PeriodPairs.tendstoLocallyUniformly_℘Except (l₀ : ℂ) :
    TendstoLocallyUniformly
      (fun (s : Finset L.lattice) (z : ℂ) ↦
        ∑ l ∈ s, if l.1 = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2))
      (L.℘Except l₀) Filter.atTop := by
  refine L.tendstoLocallyUniformly_aux (u := (10 * · * ‖·‖ ^ (-3 : ℝ))) _
    (fun _ _ ↦ (IsZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · simp; positivity
  · exact PeriodPairs.℘_bound r hr s hs l h

lemma PeriodPairs.hasSum_℘Except (l₀ : ℂ) (z : ℂ) :
    HasSum (fun l : L.lattice ↦ if l.1 = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2))
      (L.℘Except l₀ z) :=
  (L.tendstoLocallyUniformly_℘Except l₀).tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ z)

lemma PeriodPairs.differentiableOn_℘Except (l₀ : ℂ) :
    DifferentiableOn ℂ (L.℘Except l₀) (L.lattice \ {l₀})ᶜ := by
  refine (L.tendstoLocallyUniformly_℘Except l₀).tendstoLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ .sum fun i hi ↦ ?_) (L.isClosed_lattice_sdiff _).isOpen_compl
  split_ifs
  · simp
  refine .sub (.div (by fun_prop) (by fun_prop) fun x hx ↦ ?_) (by fun_prop)
  have : x ≠ i := by rintro rfl; simp_all
  simpa [sub_eq_zero]

lemma PeriodPairs.℘Except_neg (l₀ : ℂ) (z : ℂ) : L.℘Except l₀ (-z) = L.℘Except (-l₀) z := by
  simp only [℘Except]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  congr! 3 with l
  · simp [neg_eq_iff_eq_neg]
  simp
  ring

end ℘Except

section ℘

def PeriodPairs.℘ (z : ℂ) : ℂ := ∑' l : L.lattice, (1 / (z - l) ^ 2 - 1 / l ^ 2)

lemma PeriodPairs.℘Except_add (l₀ : L.lattice) (z : ℂ) :
    L.℘Except l₀ z + (1 / (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) = L.℘ z := by
  trans L.℘Except l₀ z +
    ∑' i : L.lattice, if i.1 = l₀.1 then (1 / (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) else 0
  · simp
  rw [℘Except, ← Summable.tsum_add]
  · congr with w; split_ifs <;> simp only [zero_add, add_zero, *]
  · exact ⟨_, L.hasSum_℘Except _ _⟩
  · exact summable_of_finite_support ((Set.finite_singleton l₀).subset (by simp_all))

lemma PeriodPairs.℘Except_def (l₀ : L.lattice) (z : ℂ) :
    L.℘Except l₀ z = L.℘ z + (1 / l₀.1 ^ 2 - 1 / (z - l₀.1) ^ 2) := by
  rw [← L.℘Except_add l₀]
  abel

lemma PeriodPairs.℘Except_of_not_mem (l₀ : ℂ) (hl : l₀ ∉ L.lattice) :
    L.℘Except l₀ = L.℘ := by
  delta ℘Except ℘
  congr! 3 with z l
  have : l.1 ≠ l₀ := by rintro rfl; simp at hl
  simp [this]

lemma PeriodPairs.tendstoLocallyUniformly_℘ :
    TendstoLocallyUniformly
      (fun (s : Finset L.lattice) (z : ℂ) ↦ ∑ l ∈ s, (1 / (z - l) ^ 2 - 1 / l ^ 2))
      L.℘ Filter.atTop := by
  convert L.tendstoLocallyUniformly_℘Except (L.ω₁ / 2) using 4 with s z l hl
  · rw [if_neg]; exact fun e ↦ L.ω₁_div_two_not_mem_lattice (e ▸ l.2)
  · rw [L.℘Except_of_not_mem _ L.ω₁_div_two_not_mem_lattice]

lemma PeriodPairs.hasSum_℘ (z : ℂ) :
    HasSum (fun l : L.lattice ↦ (1 / (z - l) ^ 2 - 1 / l ^ 2)) (L.℘ z) :=
  L.tendstoLocallyUniformly_℘.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ z)

lemma PeriodPairs.differentiableOn_℘ :
    DifferentiableOn ℂ L.℘ L.latticeᶜ := by
  rw [← L.℘Except_of_not_mem _ L.ω₁_div_two_not_mem_lattice]
  convert L.differentiableOn_℘Except _
  simp [Set.ext_iff, imp_not_comm, L.ω₁_div_two_not_mem_lattice]

@[simp]
lemma PeriodPairs.℘_neg (z : ℂ) : L.℘ (-z) = L.℘ z := by
  simp only [℘]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  congr with l
  simp
  ring

end ℘

section ℘'Except

def PeriodPairs.℘'Except (l₀ : ℂ) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l.1 = l₀ then 0 else -2 / (z - l) ^ 3

lemma PeriodPairs.tendstoLocallyUniformly_℘'Except (l₀ : ℂ) :
    TendstoLocallyUniformly
      (fun (s : Finset L.lattice) (z : ℂ) ↦ ∑ l ∈ s, if l.1 = l₀ then 0 else -2 / (z - l) ^ 3)
      (L.℘'Except l₀) Filter.atTop := by
  refine L.tendstoLocallyUniformly_aux (u := fun _ ↦ (16 * ‖·‖ ^ (-3 : ℝ))) _
    (fun _ _ ↦ (IsZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · simp; positivity
  have : s ≠ ↑l := by rintro rfl; exfalso; linarith
  have : l ≠ 0 := by rintro rfl; simp_all; linarith
  simp only [Complex.norm_div, norm_neg, Complex.norm_ofNat, norm_pow, AddSubgroupClass.coe_norm]
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, div_le_div_iff₀, norm_sub_rev]
  · refine LE.le.trans_eq (b := 2 * (2 * ‖l - s‖) ^ 3) ?_ (by ring)
    norm_cast
    gcongr
    refine le_trans ?_ (mul_le_mul le_rfl (norm_sub_norm_le _ _) (by linarith) (by linarith))
    norm_cast at *
    linarith
  · exact pow_pos (by simpa [sub_eq_zero]) _
  · exact Real.rpow_pos_of_pos (by simpa) _

lemma PeriodPairs.hasSum_℘'Except (l₀ : ℂ) (z : ℂ) :
    HasSum (fun l : L.lattice ↦ if l.1 = l₀ then 0 else -2 / (z - l) ^ 3)
      (L.℘'Except l₀ z) :=
  (L.tendstoLocallyUniformly_℘'Except l₀).tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ z)

lemma PeriodPairs.differentiableOn_℘'Except (l₀ : ℂ) :
    DifferentiableOn ℂ (L.℘'Except l₀) (L.lattice \ {l₀})ᶜ := by
  refine (L.tendstoLocallyUniformly_℘'Except l₀).tendstoLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ .sum fun i hi ↦ ?_) (L.isClosed_lattice_sdiff _).isOpen_compl
  split_ifs
  · simp
  refine .div (by fun_prop) (by fun_prop) fun x hx ↦ ?_
  have : x ≠ i := by rintro rfl; simp_all
  simpa [sub_eq_zero]

lemma PeriodPairs.eqOn_deriv_℘Except_℘'Except (l₀ : ℂ) :
    Set.EqOn (deriv (L.℘Except l₀)) (L.℘'Except l₀) (L.lattice \ {l₀})ᶜ := by
  refine ((L.tendstoLocallyUniformly_℘Except l₀).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun s ↦ ?_) (L.isClosed_lattice_sdiff _).isOpen_compl).unique ?_
  · refine .sum fun i hi ↦ ?_
    split_ifs
    · simp
    refine .sub (.div (by fun_prop) (by fun_prop) fun x hx ↦ ?_) (by fun_prop)
    have : x ≠ i := by rintro rfl; simp_all
    simpa [sub_eq_zero]
  · refine (L.tendstoLocallyUniformly_℘'Except l₀).tendstoLocallyUniformlyOn.congr ?_
    intro s l hl
    simp only [Function.comp_apply]
    rw [deriv_sum]
    · congr with x
      split_ifs with hl₁
      · simp
      have hl₁ : l - x ≠ 0 := fun e ↦ hl₁ (by
        obtain rfl := sub_eq_zero.mp e
        simpa using hl)
      rw [deriv_sub (.div (by fun_prop) (by fun_prop) (by simpa)) (by fun_prop), deriv_const]
      simp_rw [← zpow_natCast, one_div, ← zpow_neg, Nat.cast_ofNat]
      rw [deriv_comp_sub_const (f := (· ^ (-2 : ℤ))), deriv_zpow]
      simp
      field_simp
    · intros x hxs
      split_ifs with hl₁
      · simp
      have hl₁ : l - x ≠ 0 := fun e ↦ hl₁ (by
        obtain rfl := sub_eq_zero.mp e
        simpa using hl)
      exact .sub (.div (by fun_prop) (by fun_prop) (by simpa)) (by fun_prop)

lemma PeriodPairs.℘'Except_neg (l₀ : ℂ) (z : ℂ) : L.℘'Except l₀ (-z) = - L.℘'Except (-l₀) z := by
  simp only [℘'Except]
  rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, sub_neg_eq_add, neg_add_eq_sub, neg_neg,
    ← div_neg, ← tsum_neg, apply_ite, neg_zero]
  congr! 3 with l
  · simp [neg_eq_iff_eq_neg]
  ring

end ℘'Except

section Periodicity

lemma PeriodPairs.℘'Except_add_coe (l₀ : ℂ) (z : ℂ) (l : L.lattice) :
    L.℘'Except l₀ (z + l) = L.℘'Except (l₀ - l) z := by
  simp only [℘'Except]
  rw [← (Equiv.addRight l).tsum_eq]
  simp only [← tsum_neg, ← div_neg, Equiv.coe_addRight,
    Submodule.coe_add, add_sub_add_right_eq_sub, eq_sub_iff_add_eq]

-- Subsumed by `PeriodPairs.℘_add_coe`
private lemma PeriodPairs.℘Except_add_coe_aux
    (l₀ : ℂ) (hl₀ : l₀ ∈ L.lattice) (l : L.lattice) (hl : l.1 / 2 ∉ L.lattice) :
    Set.EqOn (L.℘Except l₀ <| · + l) (L.℘Except (l₀ - l) · + (1 / l₀ ^ 2 - 1 / (l₀ - ↑l) ^ 2))
      (L.lattice \ {l₀ - l})ᶜ := by
  apply IsOpen.eqOn_of_deriv_eq (𝕜 := ℂ) (L.isClosed_lattice_sdiff _).isOpen_compl
    ?_ ?_ ?_ ?_ (x := - (l / 2)) ?_ ?_
  · refine (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) ?_).2
    exact .mono sdiff_le (countable_of_Lindelof_of_discrete (X := L.lattice))
  · refine (L.differentiableOn_℘Except l₀).comp (f := (· + l.1)) (by fun_prop) ?_
    rintro x h₁ ⟨h₂ : x + l ∈ _, h₃ : x + l ≠ l₀⟩
    exact h₁ ⟨by simpa using sub_mem h₂ l.2, by rintro rfl; simp at h₃⟩
  · refine .add (L.differentiableOn_℘Except _) (by simp)
  · intro x hx
    simp only [deriv_add_const', deriv_comp_add_const]
    rw [L.eqOn_deriv_℘Except_℘'Except, L.eqOn_deriv_℘Except_℘'Except, L.℘'Except_add_coe]
    · simpa using hx
    · simp only [Set.mem_compl_iff, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff, not_and,
        Decidable.not_not, eq_sub_iff_add_eq] at hx ⊢
      exact fun H ↦ hx (by simpa using sub_mem H l.2)
  · simp [hl]
  · rw [L.℘Except_neg, L.℘Except_def ⟨l₀, hl₀⟩, L.℘Except_def ⟨_, neg_mem (sub_mem hl₀ l.2)⟩,
      add_assoc]
    congr 2 <;> ring

-- Subsumed by `PeriodPairs.℘_add_coe`
private lemma PeriodPairs.℘_add_coe_aux (z : ℂ) (l : L.lattice) (hl : l.1 / 2 ∉ L.lattice) :
    L.℘ (z + l) = L.℘ z := by
  have hl0 : l ≠ 0 := by rintro rfl; simp at hl
  by_cases hz : z ∈ L.lattice
  · have := L.℘Except_add_coe_aux (z + l) (add_mem hz l.2) l hl
      (x := z) (by simp [eq_sub_iff_add_eq, hl0])
    dsimp at this
    rw [← L.℘Except_add ⟨z + l, add_mem hz l.2⟩, this, ← L.℘Except_add ⟨z, hz⟩]
    simp
    ring
  · have := L.℘Except_add_coe_aux 0 (zero_mem _) l hl (x := z) (by simp [hz])
    simp only [zero_sub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
      even_two, Even.neg_pow, one_div] at this
    rw [← L.℘Except_add 0, Submodule.coe_zero, this, ← L.℘Except_add (-l)]
    simp
    ring

@[simp]
lemma PeriodPairs.℘_add_coe (z : ℂ) (l : L.lattice) : L.℘ (z + l) = L.℘ z := by
  let G : AddSubgroup ℂ :=
  { carrier := { z | (L.℘ <| · + z) = L.℘ }
    add_mem' := by simp_all [funext_iff, ← add_assoc]
    zero_mem' := by simp
    neg_mem' {z} hz := funext fun i ↦ by conv_lhs => rw [← hz]; simp }
  have : L.lattice ≤ G.toIntSubmodule := by
    rw [lattice, Submodule.span_le]
    rintro _ (rfl|rfl)
    · ext i
      exact L.℘_add_coe_aux _ ⟨_, L.ω₁_mem_lattice⟩ L.ω₁_div_two_not_mem_lattice
    · ext i
      exact L.℘_add_coe_aux _ ⟨_, L.ω₂_mem_lattice⟩ L.ω₂_div_two_not_mem_lattice
  exact congr_fun (this l.2) _

@[simp]
lemma PeriodPairs.℘_zero : L.℘ 0 = 0 := by simp [℘]

@[simp]
lemma PeriodPairs.℘_coe (l : L.lattice) : L.℘ l = 0 := by
  rw [← zero_add l.1, L.℘_add_coe, L.℘_zero]

@[simp]
lemma PeriodPairs.℘_sub_coe (z : ℂ) (l : L.lattice) : L.℘ (z - l) = L.℘ z := by
  rw [← L.℘_add_coe _ l, sub_add_cancel]

end Periodicity

section ℘'

def PeriodPairs.℘' (z : ℂ) : ℂ := - ∑' l : L.lattice, 2 / (z - l) ^ 3

lemma PeriodPairs.℘'Except_sub (l₀ : L.lattice) (z : ℂ) :
    L.℘'Except l₀ z - 2 / (z - l₀) ^ 3 = L.℘' z := by
  trans L.℘'Except l₀ z + ∑' i : L.lattice, if i.1 = l₀.1 then (- 2 / (z - l₀) ^ 3) else 0
  · simp [sub_eq_add_neg, neg_div]
  rw [℘', ℘'Except, ← Summable.tsum_add, ← tsum_neg]
  · congr with w; split_ifs <;> simp only [zero_add, add_zero, *, neg_div]
  · exact ⟨_, L.hasSum_℘'Except _ _⟩
  · exact summable_of_finite_support ((Set.finite_singleton l₀).subset (by simp_all))

lemma PeriodPairs.℘'Except_def (l₀ : L.lattice) (z : ℂ) :
    L.℘'Except l₀ z = L.℘' z + 2 / (z - l₀) ^ 3 := by
  rw [← L.℘'Except_sub l₀, sub_add_cancel]

lemma PeriodPairs.℘'Except_of_not_mem (l₀ : ℂ) (hl : l₀ ∉ L.lattice) :
    L.℘'Except l₀ = L.℘' := by
  delta ℘'Except ℘'
  simp_rw [← tsum_neg]
  congr! 3 with z l
  have : l.1 ≠ l₀ := by rintro rfl; simp at hl
  simp [this, neg_div]

lemma PeriodPairs.tendstoLocallyUniformly_℘' :
    TendstoLocallyUniformly (fun (s : Finset L.lattice) (z : ℂ) ↦ - ∑ l ∈ s, 2 / (z - l) ^ 3)
      L.℘' Filter.atTop := by
  simp_rw [← Finset.sum_neg_distrib]
  convert L.tendstoLocallyUniformly_℘'Except (L.ω₁ / 2) using 4 with s z l hl
  · rw [if_neg, neg_div]; exact fun e ↦ L.ω₁_div_two_not_mem_lattice (e ▸ l.2)
  · rw [L.℘'Except_of_not_mem _ L.ω₁_div_two_not_mem_lattice]

lemma PeriodPairs.hasSum_℘' (z : ℂ) :
    HasSum (fun l : L.lattice ↦ (1 / (z - l) ^ 2 - 1 / l ^ 2)) (L.℘ z) :=
  L.tendstoLocallyUniformly_℘.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ z)

lemma PeriodPairs.differentiableOn_℘' :
    DifferentiableOn ℂ L.℘' L.latticeᶜ := by
  rw [← L.℘'Except_of_not_mem _ L.ω₁_div_two_not_mem_lattice]
  convert L.differentiableOn_℘'Except _
  simp [Set.ext_iff, imp_not_comm, L.ω₁_div_two_not_mem_lattice]

@[simp]
lemma PeriodPairs.℘'_neg (z : ℂ) : L.℘' (-z) = - L.℘' z := by
  simp only [℘']
  rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, sub_neg_eq_add, neg_add_eq_sub, neg_neg,
    ← div_neg, ← tsum_neg]
  congr! with l
  ring

@[simp]
lemma PeriodPairs.℘'_add_coe (z : ℂ) (l : L.lattice) : L.℘' (z + l) = L.℘' z := by
  simp only [℘']
  rw [← (Equiv.addRight l).tsum_eq]
  simp only [← tsum_neg, ← div_neg, Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub]

@[simp]
lemma PeriodPairs.℘'_zero : L.℘' 0 = 0 := by
  rw [← CharZero.eq_neg_self_iff, ← L.℘'_neg, neg_zero]

@[simp]
lemma PeriodPairs.℘'_coe (l : L.lattice) : L.℘' l = 0 := by
  rw [← zero_add l.1, L.℘'_add_coe, L.℘'_zero]

@[simp]
lemma PeriodPairs.℘'_sub_coe (z : ℂ) (l : L.lattice) : L.℘' (z - l) = L.℘' z := by
  rw [← L.℘'_add_coe _ l, sub_add_cancel]

lemma PeriodPairs.not_continuousAt_℘ (x : ℂ) (hx : x ∈ L.lattice) : ¬ ContinuousAt L.℘ x := by
  eta_expand
  simp_rw [← L.℘Except_add ⟨x, hx⟩]
  intro H
  have := (H.sub ((L.differentiableOn_℘Except x).differentiableAt (x := x) ?_).continuousAt).add
    (continuous_const (y := 1 / x ^ 2)).continuousAt
  · exact not_continuousAt_inv_sq_sub x (by simpa using this)
  · exact (L.isClosed_lattice_sdiff _).isOpen_compl.mem_nhds (by simp)

@[simp]
lemma PeriodPairs.deriv_℘ : deriv L.℘ = L.℘' := by
  ext x
  by_cases hx : x ∈ L.lattice
  · rw [deriv_zero_of_not_differentiableAt, L.℘'_coe ⟨x, hx⟩]
    exact fun H ↦ L.not_continuousAt_℘ x hx H.continuousAt
  · rw [← L.℘Except_of_not_mem _ L.ω₁_div_two_not_mem_lattice,
      ← L.℘'Except_of_not_mem _ L.ω₁_div_two_not_mem_lattice,
      L.eqOn_deriv_℘Except_℘'Except (L.ω₁/2) (x := x) (by simp [hx])]

end ℘'

section Analytic℘Except

def PeriodPairs.sumInvPow (x : ℂ) (r : ℕ) : ℂ := ∑' l : L.lattice, ((l - x) ^ r)⁻¹

def PeriodPairs.℘ExceptSeriesSummand (l₀ x : ℂ) (i : ℕ) (l : L.lattice) : ℂ :=
  if l.1 = l₀ then 0 else ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : ℤ) - i.casesOn (l.1 ^ (-2 : ℤ)) 0)

def PeriodPairs.℘ExceptSeries (l₀ x : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  letI := Classical.propDecidable
  .ofScalars _ fun i ↦ i.casesOn (L.℘Except l₀ x) fun i ↦ (i + 2) *
    (L.sumInvPow x (i + 3) - if l₀ ∈ L.lattice then ((l₀ - x) ^ (i + 3))⁻¹ else 0)

lemma PeriodPairs.coeff_℘ExceptSeries (l₀ x : ℂ) (i : ℕ) :
    (L.℘ExceptSeries l₀ x).coeff i = ∑' l : L.lattice, L.℘ExceptSeriesSummand l₀ x i l := by
  delta ℘ExceptSeriesSummand
  rw [℘ExceptSeries, FormalMultilinearSeries.coeff_ofScalars]
  cases i with
  | zero => simp [℘Except, sub_sq_comm x, zpow_ofNat]
  | succ i =>
    dsimp
    split_ifs with hl₀
    · trans (i + 2) * (L.sumInvPow x (i + 3) -
        ∑' l : L.lattice, if l = ⟨l₀, hl₀⟩ then (l₀ - x) ^ (-↑(i + 3) : ℤ) else 0)
      · congr 2
        rw [tsum_ite_eq, zpow_neg, zpow_natCast]
      · rw [sumInvPow, ← Summable.tsum_sub]
        · rw [← tsum_mul_left]
          simp_rw [Subtype.ext_iff, zpow_neg]
          congr with l
          split_ifs with e
          · simp only [e, zpow_neg, zpow_natCast, sub_self, mul_zero]
          · norm_cast; ring
        · refine Summable.of_norm_bounded
            (IsZLattice.summable_norm_sub_zpow L.lattice (-↑(i + 3)) ?_ x) fun l ↦ ?_
          · simp; linarith
          · rw [← zpow_natCast, ← zpow_neg, ← norm_zpow]
        · exact summable_of_finite_support ((Set.finite_singleton ⟨l₀, hl₀⟩).subset (by simp_all))
    · have (l : L.lattice) : l.1 ≠ l₀ := fun e ↦ hl₀ (e ▸ l.2)
      simp only [this, if_false, sub_zero, tsum_mul_left, sumInvPow]
      congr 1
      simp [add_assoc, one_add_one_eq_two]

lemma PeriodPairs.summable_℘ExceptSeriesSummand (l₀ z x : ℂ)
    (hx : ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ < ‖l - x‖) :
    Summable (Function.uncurry fun b c ↦ L.℘ExceptSeriesSummand l₀ x b c * (z - x) ^ b) := by
  obtain ⟨ε, hε, hε'⟩ : ∃ ε : ℝ, 1 < ε ∧
      ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ * ε < ‖l - x‖ := by
    obtain ⟨δ, hδ, h⟩ := Disjoint.exists_cthickenings (by
      simp only [Set.disjoint_iff_inter_eq_empty, Set.mem_diff, Set.mem_inter_iff, not_lt, not_and,
        Metric.mem_closedBall, Complex.dist_eq, Set.ext_iff, SetLike.mem_coe, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, Decidable.not_not, not_imp_comm (a := _ = _)] at hx ⊢
      exact fun x h₁ h₂ ↦ hx ⟨x, h₂⟩ h₁)
        (isCompact_closedBall x ‖z - x‖) (L.isClosed_lattice_sdiff {l₀})
    by_cases hz : z = x
    · refine ⟨2, one_lt_two, fun l hl ↦ by simpa [hz] using hx l hl⟩
    have : 0 < ‖z - x‖ := by simp [sub_eq_zero, hz]
    refine ⟨δ / ‖z - x‖ + 1, by simp; positivity, fun l hl ↦ ?_⟩
    rw [mul_add, mul_one, mul_div, mul_div_cancel_left₀ _ this.ne']
    rw [cthickening_closedBall hδ.le (by positivity)] at h
    have := Set.subset_compl_iff_disjoint_left.mpr h (Metric.self_subset_cthickening _ ⟨l.2, hl⟩)
    simpa [Complex.dist_eq] using this
  let e : ℕ × L.lattice ≃ L.lattice ⊕ (ℕ × L.lattice) :=
    (Equiv.prodCongrLeft fun a ↦ (Denumerable.eqv (Option ℕ)).symm).trans (by exact? )
  have he₁ : e.symm ∘ Sum.inl = Prod.mk 0 := rfl
  have he₂ : e.symm ∘ Sum.inr = Prod.map Nat.succ id := rfl
  rw [← e.symm.summable_iff]
  apply Summable.sum
  · simp only [Function.comp_assoc, he₁, ℘ExceptSeriesSummand]
    simpa [Function.comp_def, sub_sq_comm x] using (L.hasSum_℘Except l₀ x).summable
  · simp only [Function.comp_assoc, he₂]
    simp only [Nat.cast_add, Nat.cast_ofNat, neg_add_rev, Int.reduceNeg, zpow_neg, Pi.zero_apply,
      Function.comp_def, Function.uncurry, Prod.map_snd, id_eq, Prod.map_fst, Nat.succ_eq_add_one,
      Nat.cast_one, sub_zero]
    refine Summable.of_norm_bounded (g := fun p : ℕ × L.lattice ↦
        ((p.1 + 2) * ε ^ (- p.1 : ℤ)) * (‖p.2 - x‖ ^ (-3 : ℤ) * ‖z - x‖)) ?_ ?_
    · refine Summable.mul_of_nonneg (f := fun p : ℕ ↦ ((p + 2) * ε ^ (- p : ℤ)))
        (g := fun p : L.lattice ↦ ‖p - x‖ ^ (-3 : ℤ) * ‖z - x‖) ?_ ?_ ?_ ?_
      · simp_rw [zpow_neg, zpow_natCast, ← inv_pow]
        by_contra H
        have : 1 - ε⁻¹ > 0 := by simp [inv_lt_one_iff₀, hε]
        have : |ε⁻¹| < 1 := by
          rw [abs_inv, abs_eq_self.mpr (by positivity), inv_lt_one_iff₀]; exact .inr hε
        have := (tsum_eq_zero_of_not_summable H).symm.trans
          (Real.tsum_add_const_mul_pow 2 ε⁻¹ this)
        norm_num at this
        exact not_ne_iff.mpr this (by positivity)
      · apply Summable.mul_right
        apply IsZLattice.summable_norm_sub_zpow
        simp
      · intro; positivity
      · intro; positivity
    · intro p
      simp only [℘ExceptSeriesSummand]
      split_ifs with hp
      · simp; positivity
      simp only [zpow_neg, zpow_natCast, add_assoc]
      norm_num
      simp only [mul_assoc, add_assoc, one_add_one_eq_two]
      rw [pow_succ (n := p.1)]
      refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · norm_cast
      · simp only [← mul_assoc]
        refine mul_le_mul ?_ le_rfl (by positivity) (by positivity)
        rw [pow_add, mul_inv_rev, mul_assoc, mul_comm ((ε ^ p.1)⁻¹)]
        refine mul_le_mul le_rfl ?_ (by positivity) (by positivity)
        rw [← inv_pow, ← inv_pow, ← mul_pow]
        gcongr
        have : ‖z - x‖ * ε < ‖p.2 - x‖ := hε' p.2 hp
        have h : 0 < ‖p.2 - x‖ := (show 0 ≤ ‖z - x‖ * ε by positivity).trans_lt this
        rw [inv_mul_le_iff₀ h, le_mul_inv_iff₀ (by positivity)]
        exact this.le

lemma PeriodPairs.℘Except_eq_tsum (l₀ z x : ℂ)
    (hx : ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ < ‖l - x‖) :
    L.℘Except l₀ z = ∑' i : ℕ, (L.℘ExceptSeries l₀ x).coeff i * (z - x) ^ i := by
  trans ∑' (l : L.lattice) (i : ℕ), if l.1 = l₀ then 0 else
      ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : ℤ) - i.casesOn (l.1 ^ (-2 : ℤ)) 0) * (z - x) ^ i
  · delta ℘Except
    congr 1 with l
    split_ifs with h
    · simp
    rw [tsum_eq_one_div_sub_sq_sub_one_div_sq l z x (hx l h)]
  trans ∑' (l : ↥L.lattice) (i : ℕ), L.℘ExceptSeriesSummand l₀ x i l * (z - x) ^ i
  · simp only [℘ExceptSeriesSummand, ← tsum_mul_right, ite_mul, zero_mul]
  · simp_rw [coeff_℘ExceptSeries, ← tsum_mul_right]
    apply Summable.tsum_comm
    exact L.summable_℘ExceptSeriesSummand l₀ z x hx

lemma PeriodPairs.℘ExceptSeries_hasSum (l₀ z x : ℂ)
    (hx : ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ < ‖l - x‖) :
    HasSum (fun i ↦ (L.℘ExceptSeries l₀ x).coeff i * (z - x) ^ i) (L.℘Except l₀ z) := by
  refine (Summable.hasSum_iff ?_).mpr (L.℘Except_eq_tsum l₀ z x hx).symm
  simp_rw [coeff_℘ExceptSeries, ← tsum_mul_right]
  exact (L.summable_℘ExceptSeriesSummand l₀ z x hx).prod

lemma PeriodPairs.hasFPowerSeriesOnBall_℘Except (l₀ x : ℂ) (r : NNReal) (hr0 : 0 < r)
    (hr : Metric.closedBall x r ⊆ (L.lattice \ {l₀})ᶜ) :
    HasFPowerSeriesOnBall (L.℘Except l₀) (L.℘ExceptSeries l₀ x) x r := by
  constructor
  · apply FormalMultilinearSeries.le_radius_of_tendsto (l := 0)
    convert tendsto_norm.comp (L.℘ExceptSeries_hasSum l₀ (x + r) x
      ?_).summable.tendsto_atTop_zero using 2 with i
    · simp
    · simp
    · intro l hl
      simpa using Set.subset_compl_comm.mp hr ⟨l.2, hl⟩
  · exact ENNReal.coe_pos.mpr hr0
  · intro z hz
    replace hz : ‖z‖ < r := by simpa using hz
    have := L.℘ExceptSeries_hasSum l₀ (x + z) x
    simp only [add_sub_cancel_left] at this
    convert this (fun l hl ↦ hz.trans (by simpa using Set.subset_compl_comm.mp hr ⟨l.2, hl⟩)) with i
    rw [℘ExceptSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      FormalMultilinearSeries.coeff_ofScalars]
    rfl

lemma PeriodPairs.analyticOnNhd_℘Except (l₀ : ℂ) :
    AnalyticOnNhd ℂ (L.℘Except l₀) (L.lattice \ {l₀})ᶜ := by
  intro x hx
  obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.mp (L.isClosed_lattice_sdiff {l₀}).isOpen_compl x hx
  lift ε to NNReal using hε.le
  exact ⟨L.℘ExceptSeries l₀ x, _, L.hasFPowerSeriesOnBall_℘Except l₀ x (ε / 2)
    (div_pos hε (by simp)) ((Metric.closedBall_subset_ball (by norm_num; exact hε)).trans h)⟩

end Analytic℘Except

section Analytic℘'Except

def PeriodPairs.℘'ExceptSeries (l₀ x : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  letI := Classical.propDecidable
  .ofScalars _ fun i ↦ (i + 1) * (i + 2) *
    (L.sumInvPow x (i + 3) - if l₀ ∈ L.lattice then ((l₀ - x) ^ (i + 3))⁻¹ else 0)

lemma PeriodPairs.hasFPowerSeriesOnBall_℘'Except (l₀ x : ℂ) (r : NNReal) (hr0 : 0 < r)
    (hr : Metric.closedBall x r ⊆ (L.lattice \ {l₀})ᶜ) :
    HasFPowerSeriesOnBall (L.℘'Except l₀) (L.℘'ExceptSeries l₀ x) x r := by
  refine .congr ?_ ((L.eqOn_deriv_℘Except_℘'Except l₀).mono (subset_trans ?_ hr))
  · have := (L.hasFPowerSeriesOnBall_℘Except l₀ x r hr0 hr).fderiv
    convert (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall this
    ext n
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, smul_eq_mul,
      ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, map_smul,
      ContinuousLinearMap.apply_apply, FormalMultilinearSeries.derivSeries_coeff_one, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, mul_eq_mul_left_iff]
    left
    simp [℘ExceptSeries, ℘'ExceptSeries, mul_assoc]
  · simpa using Metric.ball_subset_closedBall

lemma PeriodPairs.analyticOnNhd_℘'Except (l₀ : ℂ) :
    AnalyticOnNhd ℂ (L.℘'Except l₀) (L.lattice \ {l₀})ᶜ := by
  intro x hx
  obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.mp (L.isClosed_lattice_sdiff {l₀}).isOpen_compl x hx
  lift ε to NNReal using hε.le
  exact ⟨L.℘'ExceptSeries l₀ x, _, L.hasFPowerSeriesOnBall_℘'Except l₀ x (ε / 2)
    (div_pos hε (by simp)) ((Metric.closedBall_subset_ball (by norm_num; exact hε)).trans h)⟩

end Analytic℘'Except

section Analytic

def PeriodPairs.℘SeriesSummand (x : ℂ) (i : ℕ) (l : L.lattice) : ℂ :=
  ((i + 1) * (l.1 - x) ^ (- ↑(i + 2) : ℤ) - i.casesOn (l.1 ^ (-2 : ℤ)) 0)

def PeriodPairs.℘Series (x : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  letI := Classical.propDecidable
  .ofScalars _ fun i ↦ i.casesOn (L.℘ x) fun i ↦ (i + 2) * L.sumInvPow x (i + 3)

lemma PeriodPairs.℘ExceptSeries_of_not_mem (l₀ : ℂ) (hl₀ : l₀ ∉ L.lattice) :
    L.℘ExceptSeries l₀ = L.℘Series := by
  delta ℘Series ℘ExceptSeries
  congr! with z i f
  · rw [L.℘Except_of_not_mem _ hl₀]
  · simp [hl₀]

lemma PeriodPairs.℘ExceptSeriesSummand_of_not_mem (l₀ : ℂ) (hl₀ : l₀ ∉ L.lattice) :
    L.℘ExceptSeriesSummand l₀ = L.℘SeriesSummand := by
  delta ℘SeriesSummand ℘ExceptSeriesSummand
  ext l z l'
  have : l'.1 ≠ l₀ := fun e ↦ hl₀ (e ▸ l'.2)
  simp [this]

lemma PeriodPairs.coeff_℘Series (x : ℂ) (i : ℕ) :
    (L.℘Series x).coeff i = ∑' l : L.lattice, L.℘SeriesSummand x i l := by
  simp_rw [← L.℘ExceptSeries_of_not_mem _ L.ω₁_div_two_not_mem_lattice, L.coeff_℘ExceptSeries,
    ← L.℘ExceptSeriesSummand_of_not_mem _ L.ω₁_div_two_not_mem_lattice]

lemma PeriodPairs.summable_℘SeriesSummand (z x : ℂ)
    (hx : ∀ l : L.lattice, ‖z - x‖ < ‖l - x‖) :
    Summable (Function.uncurry fun b c ↦ L.℘SeriesSummand x b c * (z - x) ^ b) := by
  simp_rw [← L.℘ExceptSeriesSummand_of_not_mem _ L.ω₁_div_two_not_mem_lattice]
  refine L.summable_℘ExceptSeriesSummand _ z x fun l hl ↦ hx l

lemma PeriodPairs.℘Series_hasSum (z x : ℂ) (hx : ∀ l : L.lattice, ‖z - x‖ < ‖l - x‖) :
    HasSum (fun i ↦ (L.℘Series x).coeff i * (z - x) ^ i) (L.℘ z) := by
  simp_rw [← L.℘ExceptSeries_of_not_mem _ L.ω₁_div_two_not_mem_lattice,
    ← L.℘Except_of_not_mem _ L.ω₁_div_two_not_mem_lattice]
  exact L.℘ExceptSeries_hasSum _ z x fun l hl ↦ hx l

lemma PeriodPairs.hasFPowerSeriesOnBall_℘ (x : ℂ) (r : NNReal) (hr0 : 0 < r)
    (hr : Metric.closedBall x r ⊆ L.latticeᶜ) :
    HasFPowerSeriesOnBall L.℘ (L.℘Series x) x r := by
  simp_rw [← L.℘ExceptSeries_of_not_mem _ L.ω₁_div_two_not_mem_lattice,
    ← L.℘Except_of_not_mem _ L.ω₁_div_two_not_mem_lattice]
  exact L.hasFPowerSeriesOnBall_℘Except _ x r hr0
    (hr.trans (Set.compl_subset_compl.mpr Set.diff_subset))

lemma PeriodPairs.analyticOnNhd_℘ : AnalyticOnNhd ℂ L.℘ L.latticeᶜ := by
  simp_rw [← L.℘Except_of_not_mem _ L.ω₁_div_two_not_mem_lattice]
  refine (L.analyticOnNhd_℘Except _).mono (Set.compl_subset_compl.mpr Set.diff_subset)

lemma PeriodPairs.ite_eq_one_sub_sq_mul_℘ (l₀ : ℂ) (hl₀ : l₀ ∈ L.lattice) (z : ℂ) :
   (if z = l₀ then 1 else (z - l₀) ^ 2 * L.℘ z) =
    (z - l₀) ^ 2 * L.℘Except l₀ z + 1 - (z - l₀) ^ 2 / l₀ ^ 2 := by
  split_ifs with h
  · subst h
    simp
  rw [← L.℘Except_add ⟨_, hl₀⟩, mul_add, mul_sub, add_sub_assoc,
    ← mul_div_assoc, mul_one, ← mul_div_assoc, mul_one, div_self]
  simpa [sub_eq_zero] using h

lemma PeriodPairs.meromorphicAt_℘ (x : ℂ) : MeromorphicAt L.℘ x := by
  by_cases hx : x ∈ L.lattice
  · use 3
    simp_rw [← L.℘Except_add ⟨x, hx⟩, smul_eq_mul, mul_add, mul_sub]
    refine .add (.mul (by fun_prop) (L.analyticOnNhd_℘Except x x (fun e ↦ e.2 rfl)))
      (.sub ?_ (by fun_prop))
    convert_to AnalyticAt ℂ (fun z ↦ z - x) x
    · ext z
      by_cases h : z - x = 0
      · simp [h]
      · rw [pow_succ', one_div, mul_inv_cancel_right₀]
        simpa
    · fun_prop
  · exact (L.analyticOnNhd_℘ x hx).meromorphicAt

lemma PeriodPairs.order_℘ (l₀ : ℂ) (h : l₀ ∈ L.lattice) :
    meromorphicOrderAt L.℘ l₀ = -2 := by
  trans ↑(-2 : ℤ)
  · rw [meromorphicOrderAt_eq_int_iff (L.meromorphicAt_℘ l₀)]
    refine ⟨fun z ↦ (z - l₀) ^ 2 * L.℘Except l₀ z + 1 - (z - l₀) ^ 2 / l₀ ^ 2, ?_, ?_, ?_⟩
    · refine .sub (.add (.mul (by fun_prop) ?_) (by fun_prop)) ?_
      · exact L.analyticOnNhd_℘Except l₀ l₀ (by simp)
      · by_cases hl₀ : l₀ = 0
        · simpa [hl₀] using analyticAt_const
        · exact .div (by fun_prop) (by fun_prop) (by simpa)
    · simp
    · refine Filter.eventually_of_mem self_mem_nhdsWithin ?_
      rintro z (hz : _ ≠ _)
      have : (z - l₀) ^ 2 ≠ 0 := by simpa [sub_eq_zero]
      simp [← L.ite_eq_one_sub_sq_mul_℘ l₀ h, if_neg hz, inv_mul_cancel_left₀ this, zpow_ofNat]

  · norm_num

end Analytic

open Metric NNReal Finset in
lemma HasFPowerSeriesOnBall.exists_eq_add_mul_sub (f : ℂ → ℂ) (a : ℕ → ℂ) {x} {r : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f (.ofScalars ℂ a) x r) :
    ∃ g : ℂ → ℂ, HasFPowerSeriesOnBall g (.ofScalars ℂ (a <| · + 1)) x r ∧ g x = a 1 ∧
      f = (fun z ↦ a 0 + g z * (z - x)) := by
  have H : f x = a 0 := by symm; simpa using hf.coeff_zero
  refine ⟨fun z ↦ if z = x then a 1 else (f z - a 0) / (z - x), ?_, (by simp), ?_⟩
  · constructor
    · refine hf.1.trans ?_
      unfold FormalMultilinearSeries.radius
      simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef,
        FormalMultilinearSeries.coeff_ofScalars, iSup_le_iff]
      intro r' b hrb
      by_cases hr' : r' = 0
      · simp [hr']
      refine le_iSup_of_le r' (le_iSup_of_le ((↑r')⁻¹ * b) (le_iSup_of_le (fun n ↦ ?_) le_rfl))
      rw [le_inv_mul_iff₀ (by positivity), mul_comm, mul_assoc, ← pow_succ]
      exact hrb _
    · exact hf.2
    · rintro y hy
      have := (hasSum_nat_add_iff' 1).mpr (hf.3 hy)
      simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, prod_const, card_univ,
        Fintype.card_fin, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, add_eq_left,
        add_sub_cancel_left, range_one, sum_singleton, pow_zero, one_mul] at this ⊢
      split_ifs with hy'
      · simp only [hy', zero_pow_eq, ite_mul, one_mul, zero_mul]
        convert hasSum_ite_eq 0 _
        simp_all
      · convert this.div_const y using 2 with n
        rw [mul_comm (y ^ (n + 1)), pow_succ, ← mul_div, mul_div_cancel_right₀ _ hy', mul_comm]
  · ext z
    by_cases hz : x = z
    · simp only [hz, sub_self, zero_pow_eq, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_range]
      · simp [← hz, H]
    · have : z - x ≠ 0 := by simp [sub_eq_zero, Ne.symm hz]
      simp [this, Ne.symm hz]

open Metric NNReal Finset in
lemma HasFPowerSeriesOnBall.exists_eq_add_mul_sub_pow (f : ℂ → ℂ) (a : ℕ → ℂ) {x} {r : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f (.ofScalars ℂ a) x r) (k : ℕ) :
    ∃ g : ℂ → ℂ, HasFPowerSeriesOnBall g (.ofScalars ℂ (a <| · + k)) x r ∧ g x = a k ∧
      f = (fun z ↦ ∑ i ∈ range k, a i * (z - x) ^ i + g z * (z - x) ^ k) := by
  induction k with
  | zero => refine ⟨f, (by simpa using hf), by symm; simpa using hf.coeff_zero, by simp⟩
  | succ k IH =>
    obtain ⟨g, hg, h, rfl⟩ := IH
    obtain ⟨g', hg', h', rfl⟩ := hg.exists_eq_add_mul_sub
    simp_rw [add_assoc, add_comm 1] at hg'
    refine ⟨g', hg', add_comm 1 k ▸ h', ?_⟩
    ext z
    simp [add_mul, pow_succ', mul_assoc, Finset.sum_range_succ, add_assoc]

section Relation

def PeriodPairs.G (n : ℕ) : ℂ := ∑' l : L.lattice, (l ^ n)⁻¹

@[simp]
lemma PeriodPairs.sumInvPow_zero : L.sumInvPow 0 = L.G := by
  ext; simp [sumInvPow, G]

lemma PeriodPairs.G_eq_zero_of_odd (n : ℕ) (hn : Odd n) : L.G n = 0 := by
  rw [← CharZero.eq_neg_self_iff, G, ← tsum_neg, ← (Equiv.neg _).tsum_eq]
  congr with l
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, neg_inv, hn.neg_pow]

def PeriodPairs.g₂ : ℂ := 60 * L.G 4

def PeriodPairs.g₃ : ℂ := 140 * L.G 6

@[simp]
lemma PeriodPairs.℘Except_zero (x) : L.℘Except x 0 = 0 := by simp [℘Except]

@[simp]
lemma PeriodPairs.℘'Except_zero : L.℘'Except 0 0 = 0 := by
  rw [L.℘'Except_def ⟨0, zero_mem _⟩]
  simp

-- `℘(z) = z⁻² + 3G₄z² + 5G₆z⁴ + O(z⁶)`
lemma PeriodPairs.exists_℘_expansion (k : ℕ) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      g 0 = ↑(2 * k + 3) * L.G (2 * k + 4) ∧ ∀ z, L.℘ z = 1 / z ^ 2 + (∑ i ∈ Finset.range k,
        ↑(2 * i + 3) * L.G (2 * i + 4) * z ^ (2 * i + 2)) + g z * z ^ (2 * k + 2) := by
  obtain ⟨r, h₁, h₂⟩ := Metric.isOpen_iff.mp (L.isClosed_lattice_sdiff {0}).isOpen_compl 0 (by simp)
  lift r to NNReal using h₁.le
  have := L.hasFPowerSeriesOnBall_℘Except 0 0 (r / 2)
    (div_pos h₁ (by simp)) ((Metric.closedBall_subset_ball (by norm_num; exact h₁)).trans h₂)
  obtain ⟨g, hg, h, e⟩ := this.exists_eq_add_mul_sub_pow _ _ (2 * k + 2)
  refine ⟨g, hg.analyticAt, ?_, fun z ↦ ?_⟩
  · have : g 0 = (2 * ↑k + 1 + 2) * L.G (2 * k + 1 + 3) := by simpa using h
    exact_mod_cast this
  rw [← L.℘Except_add 0, Submodule.coe_zero, e]
  simp only [℘Except_zero, sumInvPow_zero, Submodule.zero_mem, ↓reduceIte, sub_self, ne_eq,
    AddLeftCancelMonoid.add_eq_zero, OfNat.ofNat_ne_zero, and_false, not_false_eq_true, zero_pow,
    inv_zero, sub_zero, div_zero]
  rw [add_comm, add_assoc]
  congr 2
  clear h e hg
  induction k with
  | zero => simp [Finset.sum_range_succ, L.G_eq_zero_of_odd 3 (by decide)]
  | succ n IH =>
    rw [show 2 * n + 2 = 2 * (n + 1) by omega] at IH
    simp only [Finset.sum_range_succ, IH, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
      add_assoc, add_right_inj]
    simp [mul_add, L.G_eq_zero_of_odd (2 * n + 2 + 3) ⟨n + 2, by omega⟩, add_assoc,
      show (1 : ℂ) + 2 = 3 by norm_num]

-- `℘(z) = -2z⁻³ + 6G₄z + 20G₆z³ + O(z⁵)`
lemma PeriodPairs.exists_℘'_expansion (k : ℕ) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
    g 0 = ↑((2 * k + 2) * (2 * k + 3)) * L.G (2 * k + 4) ∧
      ∀ z, L.℘' z = - 2 / z ^ 3 + (∑ i ∈ Finset.range k, ↑((2 * i + 2) * (2 * i + 3)) *
        L.G (2 * i + 4) * z ^ (2 * i + 1)) + g z * z ^ (2 * k + 1) := by
  obtain ⟨r, h₁, h₂⟩ := Metric.isOpen_iff.mp (L.isClosed_lattice_sdiff {0}).isOpen_compl 0 (by simp)
  lift r to NNReal using h₁.le
  have := L.hasFPowerSeriesOnBall_℘'Except 0 0 (r / 2)
    (div_pos h₁ (by simp)) ((Metric.closedBall_subset_ball (by norm_num; exact h₁)).trans h₂)
  obtain ⟨g, hg, h, e⟩ := this.exists_eq_add_mul_sub_pow _ _ (2 * k + 1)
  refine ⟨g, hg.analyticAt, ?_, fun z ↦ ?_⟩
  · have : g 0 = (2 * ↑k + 1 + 1) * (2 * ↑k + 1 + 2) * L.G (2 * k + 4) := by simpa using h
    exact_mod_cast this
  rw [← L.℘'Except_sub 0, Submodule.coe_zero, e]
  simp only [℘'Except_zero, Submodule.zero_mem, ↓reduceIte, sub_self, ne_eq,
    AddLeftCancelMonoid.add_eq_zero, OfNat.ofNat_ne_zero, and_false, not_false_eq_true, zero_pow,
    inv_zero, sub_zero, div_zero]
  rw [sub_eq_add_neg, add_comm, neg_div, add_assoc]
  congr 2
  clear h e hg
  induction k with
  | zero => simp [Finset.sum_range_succ, L.G_eq_zero_of_odd 3 (by decide)]
  | succ n IH =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, Finset.sum_range_succ, IH]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, add_assoc, add_right_inj]
    simp only [show (1 : ℂ) + 2 = 3 by norm_num, mul_add, Nat.reduceAdd, sumInvPow_zero, mul_one,
      L.G_eq_zero_of_odd (2 * n + 2 + 3) ⟨n + 2, by omega⟩, mul_zero, zero_mul, add_zero,
      mul_eq_mul_right_iff, ne_eq, AddLeftCancelMonoid.add_eq_zero, mul_eq_zero,
      OfNat.ofNat_ne_zero, false_or, one_ne_zero, and_false, not_false_eq_true, pow_eq_zero_iff]
    left
    left
    ring

def PeriodPairs.relation (z : ℂ) : ℂ :=
  letI := Classical.propDecidable
  if z ∈ L.lattice then 0 else L.℘' z ^ 2 - 4 * L.℘ z ^ 3 + L.g₂ * L.℘ z + L.g₃

lemma PeriodPairs.analyticAt_relation_zero : AnalyticAt ℂ L.relation 0 := by
  obtain ⟨g₁, hg₁, h₀₁, e₁⟩ : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = - 80 * L.G 6 ∧
      ∀ z ≠ 0, (L.℘' z) ^ 2 = 4 / z ^ 6 - 24 * L.G 4 / z ^ 2 + g z := by
    obtain ⟨g, h₁, h₂, e⟩ := L.exists_℘'_expansion 1
    refine ⟨fun z ↦ - 4 * g z + 12 * L.G 4 * z * g z * z ^ 3 + (6 * L.G 4 * z) ^ 2 +
      (g z * z ^ 3) ^ 2, by fun_prop, by simp [h₂, ← mul_assoc]; norm_num, fun z hz ↦ ?_⟩
    simp only [e]
    field_simp
    ring
  obtain ⟨g₂, hg₂, h₀₂, e₂⟩ : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 5 * L.G 6 ∧
      ∀ z, L.℘ z = 1 / z ^ 2 + 3 * L.G 4 * z ^ 2 + g z * z ^ 4 := by
    obtain ⟨g, h₁, h₂, e⟩ := L.exists_℘_expansion 1
    refine ⟨g, h₁, by simp [h₂, ← mul_assoc], by simpa [-one_div] using e⟩
  obtain ⟨g₃, hg₃, h₀₃, e₃⟩ : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 15 * L.G 6 ∧
      ∀ z ≠ 0, (L.℘ z) ^ 3 = 1 / z ^ 6 + 9 * L.G 4 / z ^ 2 + g z := by
    refine ⟨fun z ↦ (3 * L.G 4 * z ^ 2 + g₂ z * z ^ 4) ^ 3 +
      3 * (3 * L.G 4 * z ^ 2 + g₂ z * z ^ 4) * (3 * L.G 4 + g₂ z * z ^ 2) + 3 * g₂ z, by fun_prop,
      by simp [h₀₂, ← mul_assoc]; norm_num, fun z hz ↦ ?_⟩
    simp only [e₂]
    field_simp
    ring
  let F (z) := z ^ 2 * L.G 4 ^ 2 * 180 + z ^ 4 * L.G 4 * g₂ z * 60 + g₁ z - g₃ z * 4 + L.G 6 * 140
  refine (show AnalyticAt ℂ F 0 by fun_prop).congr ?_
  refine Filter.eventuallyEq_of_mem
    ((L.isClosed_lattice_sdiff {0}).isOpen_compl.mem_nhds (by simp)) ?_
  intro z hz
  by_cases hz' : z ∈ L.lattice
  · obtain rfl : z = 0 := not_not.mp fun e ↦ hz ⟨hz', e⟩
    simp [*, relation, F]
    ring
  have : z ≠ 0 := by rintro rfl; simp at hz'
  simp only [relation, hz', ↓reduceIte]
  simp_rw [e₁ z this, e₃ z this, e₂ z, PeriodPairs.g₂, PeriodPairs.g₃]
  ring

lemma PeriodPairs.analyticOnNhd_℘' : AnalyticOnNhd ℂ L.℘' L.latticeᶜ := by
  rw [← L.℘'Except_of_not_mem _ L.ω₁_div_two_not_mem_lattice]
  exact (L.analyticOnNhd_℘'Except _).mono (Set.compl_subset_compl.mpr Set.diff_subset)

@[simp]
lemma PeriodPairs.relation_add_coe (x : ℂ) (l : L.lattice) :
    L.relation (x + l) = L.relation x := by
  simp only [relation, Function.comp_apply, ℘'_add_coe, ℘_add_coe]
  congr 1
  simpa using (L.lattice.toAddSubgroup.add_mem_cancel_right (y := x) l.2)

@[simp]
lemma PeriodPairs.relation_sub_coe (x : ℂ) (l : L.lattice) :
    L.relation (x - l) = L.relation x := by
  rw [← L.relation_add_coe _ l, sub_add_cancel]

lemma PeriodPairs.analyticAt_relation (x : ℂ) : AnalyticAt ℂ L.relation x := by
  by_cases hx : x ∈ L.lattice
  · lift x to L.lattice using hx
    have := L.analyticAt_relation_zero
    rw [← sub_self x.1] at this
    convert this.comp (f := (· - x.1)) (by fun_prop)
    ext a
    simp
  · have : AnalyticAt ℂ (fun z ↦ L.℘' z ^ 2 - 4 * L.℘ z ^ 3 + L.g₂ * L.℘ z + L.g₃) x := by
      refine .add (.add (.sub (.pow ?_ _) (.mul (by fun_prop) (.pow ?_ _)))
        (.mul (by fun_prop) ?_)) (by fun_prop)
      · exact L.analyticOnNhd_℘' _ (by simpa)
      · exact L.analyticOnNhd_℘ _ (by simpa)
      · exact L.analyticOnNhd_℘ _ (by simpa)
    refine this.congr (Filter.eventuallyEq_of_mem
      (L.isClosed_lattice.isOpen_compl.mem_nhds (by simpa)) ?_)
    intro x hx
    simp_all [relation]

lemma PeriodPairs.relation_eq_zero : L.relation = 0 := by
  have : Differentiable ℂ L.relation := fun x ↦ (L.analyticAt_relation x).differentiableAt
  have := this.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice _ this.continuous ?_).isBounded
  · ext x
    rw [this x 0, relation]
    simp
  · intro z w hw
    lift w to L.lattice using hw
    simp

lemma PeriodPairs.℘'_sq (z : ℂ) (hz : z ∉ L.lattice) :
    L.℘' z ^ 2 = 4 * L.℘ z ^ 3 - L.g₂ * L.℘ z - L.g₃ := by
  rw [← sub_eq_zero]
  convert congr_fun L.relation_eq_zero z using 1
  simp [relation, hz, sub_sub, sub_add]

end Relation

set_option linter.style.longFile 0
