/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Disjoint
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.PSeries

/-!
# Convergence of `p`-series on lattices

Let `E` be a finite dimensional normed `ℝ`-space, and `L` a discrete subgroup of `E` of rank `d`.
We show that `∑ z ∈ L, ‖z - x‖ʳ` is convergent for `r < -d`.

## Main results
- `ZLattice.summable_norm_rpow`: `∑ z ∈ L, ‖z‖ʳ` converges when `r < -d`.
- `ZLattice.summable_norm_sub_rpow`: `∑ z ∈ L, ‖z - x‖ʳ` converges when `r < -d`.
- `ZLattice.tsum_norm_rpow_le`:
  `∑ z ∈ L, ‖z‖ʳ ≤ Aʳ * ∑ k : ℕ, kᵈ⁺ʳ⁻¹` for some `A > 0` depending only on `L`.

-/

noncomputable section

open Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]
variable {ι : Type*} (b : Basis ι ℤ L)

lemma ZLattice.exists_forall_abs_repr_le_norm :
    ∃ (ε : ℝ), 0 < ε ∧ ∀ (x : L), ∀ i, ε * |b.repr x i| ≤ ‖x‖ := by
  wlog H : IsZLattice ℝ L
  · let E' := Submodule.span ℝ (L : Set E)
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
    exact ⟨ε, hε, fun x i ↦ by simpa using H ⟨⟨x.1, Submodule.subset_span x.2⟩, x.2⟩ i⟩
  have : Finite ι := Module.Finite.finite_basis b
  let b' : Basis ι ℝ E := Basis.ofZLatticeBasis ℝ L b
  let e := ((b'.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _).toContinuousLinearEquiv (𝕜 := ℝ))
  have := e.continuous.1 (Set.univ.pi fun _ ↦ Set.Ioo (-1) 1)
    (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo)
  obtain ⟨ε, hε, hε'⟩ := Metric.isOpen_iff.mp this 0 (by simp)
  refine ⟨ε / 2, by positivity, fun x i ↦ ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hx : ‖x.1‖ ≠ 0 := by simpa
  have : |ε / 2 * (‖↑x‖⁻¹ * (b.repr x) i)| < 1 := by
    simpa [e, b', ← abs_lt] using @hε' ((ε / 2) • ‖x‖⁻¹ • x)
      (by simpa [norm_smul, inv_mul_cancel₀ hx, abs_eq_self.mpr hε.le]) i trivial
  rw [abs_mul, abs_mul, abs_inv, mul_left_comm, abs_norm, inv_mul_lt_iff₀ (by positivity),
    mul_one, abs_eq_self.mpr (by positivity), ← Int.cast_abs] at this
  exact this.le

/--
Given a basis of a (possibly not full rank) `ℤ`-lattice, there exists a `ε > 0` such that
`|b.repr x i| < n` for all `‖x‖ < n * ε` (i.e. `b.repr x i = O(x)` depending only on `b`).
This is an arbitrary choice of such an `ε`.
-/
def ZLattice.normBound {ι : Type*} (b : Basis ι ℤ L) : ℝ :=
  (exists_forall_abs_repr_le_norm b).choose

lemma ZLattice.normBound_pos {ι : Type*} (b : Basis ι ℤ L) : 0 < normBound b :=
  (exists_forall_abs_repr_le_norm b).choose_spec.1

lemma ZLattice.normBound_spec {ι : Type*} (b : Basis ι ℤ L) (x : L) (i : ι) :
    normBound b * |b.repr x i| ≤ ‖x‖ :=
  (exists_forall_abs_repr_le_norm b).choose_spec.2 x i

lemma ZLattice.abs_repr_le {ι : Type*} (b : Basis ι ℤ L) (x : L) (i : ι) :
    |b.repr x i| ≤ (normBound b)⁻¹ * ‖x‖ := by
  rw [le_inv_mul_iff₀ (normBound_pos b)]
  exact normBound_spec b x i

lemma ZLattice.abs_repr_lt_of_norm_lt {ι : Type*} (b : Basis ι ℤ L) (x : L) (n : ℕ)
    (hxn : ‖x‖ < normBound b * n) (i : ι) : |b.repr x i| < n := by
  refine Int.cast_lt.mp ((abs_repr_le b x i).trans_lt ?_)
  rwa [inv_mul_lt_iff₀ (normBound_pos b)]

lemma ZLattice.le_norm_of_le_abs_repr {ι : Type*} (b : Basis ι ℤ L) (x : L) (n : ℕ) (i : ι)
    (hi : n ≤ |b.repr x i|) : normBound b * n ≤ ‖x‖ := by
  contrapose! hi
  exact abs_repr_lt_of_norm_lt b x n hi i

open Finset in
lemma ZLattice.sum_piFinset_Icc_rpow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
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
    · simp only [le_add_iff_nonneg_right, zero_le, hs, card_sdiff_of_subset, s]
      simp only [Fintype.card_piFinset, Int.card_Icc, sub_neg_eq_add, prod_const, card_univ, s]
      gcongr <;> norm_cast <;> omega
    · have := abs_pow_sub_pow_le (α := ℤ) ↑(2 * k + 3) ↑(2 * k + 1) d
      norm_num at this
      zify
      convert this using 3
      · rw [abs_eq_self.mpr (sub_nonneg.mpr (by gcongr; omega)), Nat.cast_sub (by gcongr; omega)]
        simp
      · rw [max_eq_left (by gcongr; omega), abs_eq_self.mpr (by positivity)]
  let ε := normBound b
  have hε : 0 < ε := normBound_pos b
  calc ∑ p ∈ s n, ‖∑ i, p i • b i‖ ^ r
      = ∑ k ∈ range n, ∑ p ∈ (s (k + 1) \ s k), ‖∑ i, p i • b i‖ ^ r := by
        simp [Finset.sum_eq_sum_range_sdiff _ @hs, hs0, hr'.ne]
    _ ≤ ∑ k ∈ range n, ∑ p ∈ (s (k + 1) \ s k), ((k + 1) * ε) ^ r := by
        gcongr ∑ k ∈ Finset.range n, ∑ p ∈ (s (k + 1) \ s k), ?_ with k hk v hv
        rw [← Nat.cast_one, ← Nat.cast_add]
        refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hr'.le
        obtain ⟨j, hj⟩ : ∃ i, v i ∉ Icc (-k : ℤ) k := by simpa [s] using (mem_sdiff.mp hv).2
        refine mul_comm _ ε ▸ ZLattice.le_norm_of_le_abs_repr b _ _ j ?_
        suffices ↑k + 1 ≤ |v j| by simpa [Finsupp.single_apply] using this
        by_contra! H
        rw [Int.lt_add_one_iff, abs_le, ← Finset.mem_Icc] at H
        exact hj H
    _ ≤ ∑ k ∈ range n, ↑(2 * d * (3 * (k + 1)) ^ (d - 1)) * ((k + 1) * ε) ^ r := by
        simp only [sum_const, nsmul_eq_mul]
        gcongr with k hk
        refine (this _).trans ?_
        gcongr
        omega
    _ = 2 * d * 3 ^ (d - 1) * ε ^ r * ∑ k ∈ range n, (k + 1) ^ (d - 1) * (k + 1 : ℝ) ^ r := by
        simp_rw [Finset.mul_sum]
        congr with k
        push_cast
        rw [Real.mul_rpow (by positivity) (by positivity), mul_pow]
        group
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
        refine Summable.sum_le_tsum _ (fun _ _ ↦ by positivity) (Real.summable_nat_rpow.mpr ?_)
        linarith

variable (L)

lemma ZLattice.exists_finset_sum_norm_rpow_le_tsum :
    ∃ A > (0 : ℝ), ∀ r < (-Module.finrank ℤ L : ℝ), ∀ s : Finset L,
      ∑ z ∈ s, ‖z‖ ^ r ≤ A ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r) := by
  classical
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
  let ε := normBound b
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
    convert ZLattice.sum_piFinset_Icc_rpow_le b rfl n r hr with x
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

/--
Let `L` be a lattice with (possibly non-full) rank `d`, and `r : ℝ` such that `d < r`.
Then `∑ z ∈ L, ‖z‖⁻ʳ ≤ A⁻ʳ * ∑ k : ℕ, kᵈ⁻ʳ⁻¹` for some `A > 0` depending only on `L`.
This is an arbitrary choice of `A`. See `ZLattice.tsum_norm_rpow_le`.
-/
def ZLattice.tsumNormRPowBound : ℝ :=
  (exists_finset_sum_norm_rpow_le_tsum L).choose

lemma ZLattice.tsumNormRPowBound_pos : 0 < tsumNormRPowBound L :=
  (exists_finset_sum_norm_rpow_le_tsum L).choose_spec.1

lemma ZLattice.tsumNormRPowBound_spec (r : ℝ) (h : r < -Module.finrank ℤ L) (s : Finset L) :
    ∑ z ∈ s, ‖z‖ ^ r ≤
      tsumNormRPowBound L ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r) :=
  (ZLattice.exists_finset_sum_norm_rpow_le_tsum L).choose_spec.2 r h s

/-- If `L` is a `ℤ`-lattice with rank `d` in `E`, then `∑ z ∈ L, ‖z‖ʳ` converges when `r < -d`. -/
lemma ZLattice.summable_norm_rpow (r : ℝ) (hr : r < -Module.finrank ℤ L) :
    Summable fun z : L ↦ ‖z‖ ^ r :=
  summable_of_sum_le (fun _ ↦ by positivity) (tsumNormRPowBound_spec L r hr)

/-- `∑ z ∈ L, ‖z‖⁻ʳ ≤ A⁻ʳ * ∑ k : ℕ, kᵈ⁻ʳ⁻¹` for some `A > 0` depending only on `L`. -/
lemma ZLattice.tsum_norm_rpow_le (r : ℝ) (hr : r < -Module.finrank ℤ L) :
    ∑' z : L, ‖z‖ ^ r ≤
      tsumNormRPowBound L ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r) :=
  Summable.tsum_le_of_sum_le (summable_norm_rpow L r hr) (tsumNormRPowBound_spec L r hr)

lemma ZLattice.summable_norm_sub_rpow (r : ℝ) (hr : r < -Module.finrank ℤ L) (x : E) :
    Summable fun z : L ↦ ‖z - x‖ ^ r := by
  cases subsingleton_or_nontrivial L
  · exact .of_finite
  refine Summable.of_norm_bounded_eventually
    (.mul_left ((1 / 2) ^ r) (summable_norm_rpow L r hr)) ?_
  have H : IsClosed (X := E) L := @AddSubgroup.isClosed_of_discrete _ _ _ _ _
    L.toAddSubgroup (inferInstanceAs (DiscreteTopology L))
  refine ((Metric.finite_isBounded_inter_isClosed
    (Metric.isBounded_closedBall (x := (0 : E)) (r := 2 * ‖x‖)) H).preimage_embedding
    (.subtype _)).subset ?_
  intro t ht
  by_cases ht₁ : ‖t‖ = 0
  · simp [show t = 0 by simpa using ht₁]
  by_cases ht₂ : ‖t - x‖ = 0
  · simpa [show t = x by simpa [sub_eq_zero] using ht₂, two_mul] using t.2
  have : 0 < Module.finrank ℤ L := Module.finrank_pos
  have : ‖t - x‖ < 2⁻¹ * ‖t‖ := by
    rw [← Real.rpow_lt_rpow_iff_of_neg (by positivity) (by positivity) (hr.trans (by simpa))]
    simpa [Real.mul_rpow, abs_eq_self.mpr (show 0 ≤ ‖t - x‖ ^ r by positivity)] using ht
  have := (norm_sub_norm_le _ _).trans_lt this
  rw [sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', AddSubgroupClass.coe_norm] at this
  simpa using show ‖t.1‖ ≤ 2 * ‖x‖ by linarith

lemma ZLattice.summable_norm_sub_zpow (n : ℤ) (hn : n < -Module.finrank ℤ L) (x : E) :
    Summable fun z : L ↦ ‖z - x‖ ^ n := by
  exact_mod_cast summable_norm_sub_rpow L n (by exact_mod_cast hn) x

lemma ZLattice.summable_norm_zpow (n : ℤ) (hn : n < -Module.finrank ℤ L) :
    Summable fun z : L ↦ ‖z‖ ^ n := by
  simpa using summable_norm_sub_zpow L n hn 0

lemma ZLattice.summable_norm_sub_inv_pow (n : ℕ) (hn : Module.finrank ℤ L < n) (x : E) :
    Summable fun z : L ↦ ‖z - x‖⁻¹ ^ n := by
  simpa using summable_norm_sub_zpow L (-n) (by gcongr) x

lemma ZLattice.summable_norm_pow_inv (n : ℕ) (hn : Module.finrank ℤ L < n) :
    Summable fun z : L ↦ ‖z‖⁻¹ ^ n := by
  simpa using summable_norm_sub_inv_pow L n hn 0
