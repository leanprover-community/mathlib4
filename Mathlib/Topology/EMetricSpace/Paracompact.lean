/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.SetTheory.Cardinal.Order

/-!
# (Extended) metric spaces are paracompact

In this file we provide two instances:

* `EMetric.instParacompactSpace`: a `PseudoEMetricSpace` is paracompact; formalization is based
  on [MR0236876];
* `EMetric.instNormalSpace`: an `EMetricSpace` is a normal topological space.

## TODO

Generalize to `PseudoMetrizableSpace`s.

## Tags

metric space, paracompact space, normal space
-/

variable {α : Type*}

open ENNReal Topology Set

namespace EMetric

-- See note [lower instance priority]
/-- A `PseudoEMetricSpace` is always a paracompact space.
Formalization is based on [MR0236876]. -/
instance (priority := 100) instParacompactSpace [PseudoEMetricSpace α] : ParacompactSpace α := by
  /- We start with trivial observations about `1 / 2 ^ k`. Here and below we use `1 / 2 ^ k` in
    the comments and `2⁻¹ ^ k` in the code. -/
  have pow_pos : ∀ k : ℕ, (0 : ℝ≥0∞) < 2⁻¹ ^ k := fun k =>
    ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _
  have hpow_le : ∀ {m n : ℕ}, m ≤ n → (2⁻¹ : ℝ≥0∞) ^ n ≤ 2⁻¹ ^ m := @fun m n h =>
    pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.2 ENNReal.one_lt_two.le) h
  have h2pow : ∀ n : ℕ, 2 * (2⁻¹ : ℝ≥0∞) ^ (n + 1) = 2⁻¹ ^ n := fun n => by
    simp [pow_succ', ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ofNat_ne_top]
  -- Consider an open covering `S : Set (Set α)`
  refine ⟨fun ι s ho hcov => ?_⟩
  simp only [iUnion_eq_univ_iff] at hcov
  -- choose a well-founded order on `S`
  obtain ⟨_, wf⟩ := exists_wellOrder ι
  -- Let `ind x` be the minimal index `s : S` such that `x ∈ s`.
  let ind (x : α) : ι := wellFounded_lt.min { i : ι | x ∈ s i } (hcov x)
  have mem_ind (x) : x ∈ s (ind x) := wellFounded_lt.min_mem _ (hcov x)
  have notMem_of_lt_ind {x i} (hlt : i < ind x) (hxi : x ∈ s i) : False :=
    wellFounded_lt.not_lt_min _ (hcov x) hxi hlt
  /- The refinement `D : ℕ → ι → Set α` is defined recursively. For each `n` and `i`, `D n i`
    is the union of balls `ball x (1 / 2 ^ n)` over all points `x` such that

    * `ind x = i`;
    * `x` does not belong to any `D m j`, `m < n`;
    * `ball x (3 / 2 ^ n) ⊆ s i`;

    We define this sequence using `Nat.strongRecOn'`, then restate it as `Dn` and `memD`.
  -/
  set D : ℕ → ι → Set α := fun n =>
    Nat.strongRecOn' n fun n D' i =>
      ⋃ (x : α) (hxs : ind x = i) (hb : ball x (3 * 2⁻¹ ^ n) ⊆ s i) (hlt :
        ∀ (m : ℕ) (H : m < n), ∀ (j : ι), x ∉ D' m H j), ball x (2⁻¹ ^ n) with hD
  have Dn (n i) : D n i = ⋃ (x : α) (hxs : ind x = i) (hb : ball x (3 * 2⁻¹ ^ n) ⊆ s i)
      (hlt : ∀ m < n, ∀ (j : ι), x ∉ D m j), ball x (2⁻¹ ^ n) := by
    simp only [hD]
    rw [Nat.strongRecOn'_beta]
  have memD {n i y} :
      y ∈ D n i ↔ ∃ x : α, ind x = i ∧ ball x (3 * 2⁻¹ ^ n) ⊆ s i ∧
        (∀ m < n, ∀ (j : ι), x ∉ D m j) ∧ edist y x < 2⁻¹ ^ n := by
    rw [Dn n i]
    simp only [mem_iUnion, mem_ball, exists_prop]
  -- The sets `D n i` cover the whole space. Indeed, for each `x` we can choose `n` such that
  -- `ball x (3 / 2 ^ n) ⊆ s (ind x)`, then either `x ∈ D n i`, or `x ∈ D m i` for some `m < n`.
  have Dcov (x) : ∃ n i, x ∈ D n i := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ball x (3 * 2⁻¹ ^ n) ⊆ s (ind x) := by
      -- This proof takes 5 lines because we can't import `specific_limits` here
      rcases isOpen_iff.1 (ho <| ind x) x (mem_ind x) with ⟨ε, ε0, hε⟩
      have : 0 < ε / 3 := ENNReal.div_pos_iff.2 ⟨ε0.lt.ne', ENNReal.coe_ne_top⟩
      rcases ENNReal.exists_inv_two_pow_lt this.ne' with ⟨n, hn⟩
      refine ⟨n, Subset.trans (ball_subset_ball ?_) hε⟩
      simpa only [div_eq_mul_inv, mul_comm] using (ENNReal.mul_lt_of_lt_div hn).le
    by_contra! h
    apply h n (ind x)
    exact memD.2 ⟨x, rfl, hn, fun _ _ _ => h _ _, mem_ball_self (pow_pos _)⟩
  -- Each `D n i` is a union of open balls, hence it is an open set
  have Dopen (n i) : IsOpen (D n i) := by
    rw [Dn]
    iterate 4 refine isOpen_iUnion fun _ => ?_
    exact isOpen_ball
  -- the covering `D n i` is a refinement of the original covering: `D n i ⊆ s i`
  have HDS (n i) : D n i ⊆ s i := fun x => by
    rw [memD]
    rintro ⟨y, rfl, hsub, -, hyx⟩
    refine hsub (hyx.trans_le <| le_mul_of_one_le_left' ?_)
    norm_num1
  -- Let us show the rest of the properties. Since the definition expects a family indexed
  -- by a single parameter, we use `ℕ × ι` as the domain.
  refine ⟨ℕ × ι, fun ni => D ni.1 ni.2, fun _ => Dopen _ _, ?_, ?_, fun ni => ⟨ni.2, HDS _ _⟩⟩
  -- The sets `D n i` cover the whole space as we proved earlier
  · refine iUnion_eq_univ_iff.2 fun x ↦ ?_
    rcases Dcov x with ⟨n, i, h⟩
    exact ⟨⟨n, i⟩, h⟩
  /- Let us prove that the covering `D n i` is locally finite. Take a point `x` and choose
    `n`, `i` so that `x ∈ D n i`. Since `D n i` is an open set, we can choose `k` so that
    `B = ball x (1 / 2 ^ (n + k + 1)) ⊆ D n i`. -/
  · intro x
    rcases Dcov x with ⟨n, i, hn⟩
    have : D n i ∈ 𝓝 x := IsOpen.mem_nhds (Dopen _ _) hn
    rcases (nhds_basis_uniformity uniformity_basis_edist_inv_two_pow).mem_iff.1 this with
      ⟨k, -, hsub : ball x (2⁻¹ ^ k) ⊆ D n i⟩
    set B := ball x (2⁻¹ ^ (n + k + 1))
    refine ⟨B, ball_mem_nhds _ (pow_pos _), ?_⟩
    -- The sets `D m i`, `m > n + k`, are disjoint with `B`
    have Hgt (m) (hm : n + k + 1 ≤ m) (i : ι) : Disjoint (D m i) B := by
      rw [disjoint_iff_inf_le]
      rintro y ⟨hym, hyx⟩
      rcases memD.1 hym with ⟨z, rfl, _hzi, H, hz⟩
      have : z ∉ ball x (2⁻¹ ^ k) := fun hz' => H n (by omega) i (hsub hz')
      apply this
      calc
        edist z x ≤ edist y z + edist y x := edist_triangle_left _ _ _
        _ < 2⁻¹ ^ m + 2⁻¹ ^ (n + k + 1) := ENNReal.add_lt_add hz hyx
        _ ≤ 2⁻¹ ^ (k + 1) + 2⁻¹ ^ (k + 1) :=
          (add_le_add (hpow_le <| by omega) (hpow_le <| by omega))
        _ = 2⁻¹ ^ k := by rw [← two_mul, h2pow]
    -- For each `m ≤ n + k` there is at most one `j` such that `D m j ∩ B` is nonempty.
    have Hle (m) (hm : m ≤ n + k) : Set.Subsingleton { j | (D m j ∩ B).Nonempty } := by
      rintro j₁ ⟨y, hyD, hyB⟩ j₂ ⟨z, hzD, hzB⟩
      by_contra! h' : j₁ ≠ j₂
      wlog h : j₁ < j₂ generalizing j₁ j₂ y z
      · exact this z hzD hzB y hyD hyB h'.symm (h'.lt_or_gt.resolve_left h)
      rcases memD.1 hyD with ⟨y', rfl, hsuby, -, hdisty⟩
      rcases memD.1 hzD with ⟨z', rfl, -, -, hdistz⟩
      suffices edist z' y' < 3 * 2⁻¹ ^ m from notMem_of_lt_ind h (hsuby this)
      calc
        edist z' y' ≤ edist z' x + edist x y' := edist_triangle _ _ _
        _ ≤ edist z z' + edist z x + (edist y x + edist y y') :=
          (add_le_add (edist_triangle_left _ _ _) (edist_triangle_left _ _ _))
        _ < 2⁻¹ ^ m + 2⁻¹ ^ (n + k + 1) + (2⁻¹ ^ (n + k + 1) + 2⁻¹ ^ m) := by
          apply_rules [ENNReal.add_lt_add]
        _ = 2 * (2⁻¹ ^ m + 2⁻¹ ^ (n + k + 1)) := by simp only [two_mul, add_comm]
        _ ≤ 2 * (2⁻¹ ^ m + 2⁻¹ ^ (m + 1)) := by
          gcongr 2 * (_ + ?_); exact hpow_le (add_le_add hm le_rfl)
        _ = 3 * 2⁻¹ ^ m := by
          rw [mul_add, h2pow, ← two_add_one_eq_three, add_mul, one_mul]
    -- Finally, we glue `Hgt` and `Hle`
    have : (⋃ (m ≤ n + k) (i ∈ { i : ι | (D m i ∩ B).Nonempty }), {(m, i)}).Finite :=
      (finite_le_nat _).biUnion' fun i hi =>
        (Hle i hi).finite.biUnion' fun _ _ => finite_singleton _
    refine this.subset fun I hI => ?_
    simp only [mem_iUnion]
    refine ⟨I.1, ?_, I.2, hI, rfl⟩
    exact not_lt.1 fun hlt => (Hgt I.1 hlt I.2).le_bot hI.choose_spec

theorem t4Space [EMetricSpace α] : T4Space α := inferInstance

end EMetric
