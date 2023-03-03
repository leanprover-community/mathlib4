/-
Copyright (c) 202 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module topology.metric_space.emetric_paracompact
! leanprover-community/mathlib commit 57ac39bd365c2f80589a700f9fbb664d3a1a30c2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.SetTheory.Ordinal.Basic
import Mathbin.Topology.MetricSpace.EmetricSpace
import Mathbin.Topology.Paracompact

/-!
# (Extended) metric spaces are paracompact

In this file we provide two instances:

* `emetric.paracompact_space`: a `pseudo_emetric_space` is paracompact; formalization is based
  on [MR0236876];
* `emetric.normal_of_metric`: an `emetric_space` is a normal topological space.

## Tags

metric space, paracompact space, normal space
-/


variable {α : Type _}

open ENNReal Topology

open Set

namespace Emetric

-- See note [lower instance priority]
/-- A `pseudo_emetric_space` is always a paracompact space. Formalization is based
on [MR0236876]. -/
instance (priority := 100) [PseudoEMetricSpace α] : ParacompactSpace α := by
  classical
    /- We start with trivial observations about `1 / 2 ^ k`. Here and below we use `1 / 2 ^ k` in
      the comments and `2⁻¹ ^ k` in the code. -/
    have pow_pos : ∀ k : ℕ, (0 : ℝ≥0∞) < 2⁻¹ ^ k := fun k =>
      ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.two_ne_top) _
    have hpow_le : ∀ {m n : ℕ}, m ≤ n → (2⁻¹ : ℝ≥0∞) ^ n ≤ 2⁻¹ ^ m := fun m n h =>
      pow_le_pow_of_le_one' (ENNReal.inv_le_one.2 ennreal.one_lt_two.le) h
    have h2pow : ∀ n : ℕ, 2 * (2⁻¹ : ℝ≥0∞) ^ (n + 1) = 2⁻¹ ^ n :=
      by
      intro n
      simp [pow_succ, ← mul_assoc, ENNReal.mul_inv_cancel]
    -- Consider an open covering `S : set (set α)`
    refine' ⟨fun ι s ho hcov => _⟩
    simp only [Union_eq_univ_iff] at hcov
    -- choose a well founded order on `S`
    letI : LinearOrder ι := linearOrderOfSTO WellOrderingRel
    have wf : WellFounded ((· < ·) : ι → ι → Prop) := @IsWellFounded.wf ι WellOrderingRel _
    -- Let `ind x` be the minimal index `s : S` such that `x ∈ s`.
    set ind : α → ι := fun x => wf.min { i : ι | x ∈ s i } (hcov x)
    have mem_ind : ∀ x, x ∈ s (ind x) := fun x => wf.min_mem _ (hcov x)
    have nmem_of_lt_ind : ∀ {x i}, i < ind x → x ∉ s i := fun x i hlt hxi =>
      wf.not_lt_min _ (hcov x) hxi hlt
    /- The refinement `D : ℕ → ι → set α` is defined recursively. For each `n` and `i`, `D n i`
      is the union of balls `ball x (1 / 2 ^ n)` over all points `x` such that
    
      * `ind x = i`;
      * `x` does not belong to any `D m j`, `m < n`;
      * `ball x (3 / 2 ^ n) ⊆ s i`;
    
      We define this sequence using `nat.strong_rec_on'`, then restate it as `Dn` and `memD`.
      -/
    set D : ℕ → ι → Set α := fun n =>
      Nat.strongRecOn' n fun n D' i =>
        ⋃ (x : α) (hxs : ind x = i) (hb : ball x (3 * 2⁻¹ ^ n) ⊆ s i) (hlt :
          ∀ m < n, ∀ (j : ι), x ∉ D' m ‹_› j), ball x (2⁻¹ ^ n)
    have Dn :
      ∀ n i,
        D n i =
          ⋃ (x : α) (hxs : ind x = i) (hb : ball x (3 * 2⁻¹ ^ n) ⊆ s i) (hlt :
            ∀ m < n, ∀ (j : ι), x ∉ D m j), ball x (2⁻¹ ^ n) :=
      fun n s => by
      simp only [D]
      rw [Nat.strongRecOn'_beta]
    have memD :
      ∀ {n i y},
        y ∈ D n i ↔
          ∃ (x : _)(hi : ind x = i)(hb : ball x (3 * 2⁻¹ ^ n) ⊆ s i)(hlt :
            ∀ m < n, ∀ (j : ι), x ∉ D m j), edist y x < 2⁻¹ ^ n :=
      by
      intro n i y
      rw [Dn n i]
      simp only [mem_Union, mem_ball]
    -- The sets `D n i` cover the whole space. Indeed, for each `x` we can choose `n` such that
    -- `ball x (3 / 2 ^ n) ⊆ s (ind x)`, then either `x ∈ D n i`, or `x ∈ D m i` for some `m < n`.
    have Dcov : ∀ x, ∃ n i, x ∈ D n i := by
      intro x
      obtain ⟨n, hn⟩ : ∃ n : ℕ, ball x (3 * 2⁻¹ ^ n) ⊆ s (ind x) :=
        by
        -- This proof takes 5 lines because we can't import `specific_limits` here
        rcases is_open_iff.1 (ho <| ind x) x (mem_ind x) with ⟨ε, ε0, hε⟩
        have : 0 < ε / 3 := ENNReal.div_pos_iff.2 ⟨ε0.lt.ne', ENNReal.coe_ne_top⟩
        rcases ENNReal.exists_inv_two_pow_lt this.ne' with ⟨n, hn⟩
        refine' ⟨n, subset.trans (ball_subset_ball _) hε⟩
        simpa only [div_eq_mul_inv, mul_comm] using (ENNReal.mul_lt_of_lt_div hn).le
      by_contra' h
      apply h n (ind x)
      exact memD.2 ⟨x, rfl, hn, fun _ _ _ => h _ _, mem_ball_self (pow_pos _)⟩
    -- Each `D n i` is a union of open balls, hence it is an open set
    have Dopen : ∀ n i, IsOpen (D n i) := by
      intro n i
      rw [Dn]
      iterate 4 refine' isOpen_unionᵢ fun _ => _
      exact is_open_ball
    -- the covering `D n i` is a refinement of the original covering: `D n i ⊆ s i`
    have HDS : ∀ n i, D n i ⊆ s i := by
      intro n s x
      rw [memD]
      rintro ⟨y, rfl, hsub, -, hyx⟩
      refine' hsub (lt_of_lt_of_le hyx _)
      calc
        2⁻¹ ^ n = 1 * 2⁻¹ ^ n := (one_mul _).symm
        _ ≤ 3 * 2⁻¹ ^ n := mul_le_mul_right' _ _
        
      -- TODO: use `norm_num`
      have : ((1 : ℕ) : ℝ≥0∞) ≤ (3 : ℕ) := Nat.cast_le.2 (by norm_num1)
      exact_mod_cast this
    -- Let us show the rest of the properties. Since the definition expects a family indexed
    -- by a single parameter, we use `ℕ × ι` as the domain.
    refine' ⟨ℕ × ι, fun ni => D ni.1 ni.2, fun _ => Dopen _ _, _, _, fun ni => ⟨ni.2, HDS _ _⟩⟩
    -- The sets `D n i` cover the whole space as we proved earlier
    · refine' Union_eq_univ_iff.2 fun x => _
      rcases Dcov x with ⟨n, i, h⟩
      exact ⟨⟨n, i⟩, h⟩
    · /- Let us prove that the covering `D n i` is locally finite. Take a point `x` and choose
          `n`, `i` so that `x ∈ D n i`. Since `D n i` is an open set, we can choose `k` so that
          `B = ball x (1 / 2 ^ (n + k + 1)) ⊆ D n i`. -/
      intro x
      rcases Dcov x with ⟨n, i, hn⟩
      have : D n i ∈ 𝓝 x := IsOpen.mem_nhds (Dopen _ _) hn
      rcases(nhds_basis_uniformity uniformity_basis_edist_inv_two_pow).mem_iff.1 this with
        ⟨k, -, hsub : ball x (2⁻¹ ^ k) ⊆ D n i⟩
      set B := ball x (2⁻¹ ^ (n + k + 1))
      refine' ⟨B, ball_mem_nhds _ (pow_pos _), _⟩
      -- The sets `D m i`, `m > n + k`, are disjoint with `B`
      have Hgt : ∀ m ≥ n + k + 1, ∀ (i : ι), Disjoint (D m i) B :=
        by
        rintro m hm i
        rw [disjoint_iff_inf_le]
        rintro y ⟨hym, hyx⟩
        rcases memD.1 hym with ⟨z, rfl, hzi, H, hz⟩
        have : z ∉ ball x (2⁻¹ ^ k) := fun hz => H n (by linarith) i (hsub hz)
        apply this
        calc
          edist z x ≤ edist y z + edist y x := edist_triangle_left _ _ _
          _ < 2⁻¹ ^ m + 2⁻¹ ^ (n + k + 1) := (ENNReal.add_lt_add hz hyx)
          _ ≤ 2⁻¹ ^ (k + 1) + 2⁻¹ ^ (k + 1) :=
            (add_le_add (hpow_le <| by linarith) (hpow_le <| by linarith))
          _ = 2⁻¹ ^ k := by rw [← two_mul, h2pow]
          
      -- For each `m ≤ n + k` there is at most one `j` such that `D m j ∩ B` is nonempty.
      have Hle : ∀ m ≤ n + k, Set.Subsingleton { j | (D m j ∩ B).Nonempty } :=
        by
        rintro m hm j₁ ⟨y, hyD, hyB⟩ j₂ ⟨z, hzD, hzB⟩
        by_contra' h' : j₁ ≠ j₂
        wlog h : j₁ < j₂ generalizing j₁ j₂ y z
        · exact this z hzD hzB y hyD hyB h'.symm (h'.lt_or_lt.resolve_left h)
        rcases memD.1 hyD with ⟨y', rfl, hsuby, -, hdisty⟩
        rcases memD.1 hzD with ⟨z', rfl, -, -, hdistz⟩
        suffices : edist z' y' < 3 * 2⁻¹ ^ m
        exact nmem_of_lt_ind h (hsuby this)
        calc
          edist z' y' ≤ edist z' x + edist x y' := edist_triangle _ _ _
          _ ≤ edist z z' + edist z x + (edist y x + edist y y') :=
            (add_le_add (edist_triangle_left _ _ _) (edist_triangle_left _ _ _))
          _ < 2⁻¹ ^ m + 2⁻¹ ^ (n + k + 1) + (2⁻¹ ^ (n + k + 1) + 2⁻¹ ^ m) := by
            apply_rules [ENNReal.add_lt_add]
          _ = 2 * (2⁻¹ ^ m + 2⁻¹ ^ (n + k + 1)) := by simp only [two_mul, add_comm]
          _ ≤ 2 * (2⁻¹ ^ m + 2⁻¹ ^ (m + 1)) :=
            (mul_le_mul' le_rfl <| add_le_add le_rfl <| hpow_le (add_le_add hm le_rfl))
          _ = 3 * 2⁻¹ ^ m := by rw [mul_add, h2pow, bit1, add_mul, one_mul]
          
      -- Finally, we glue `Hgt` and `Hle`
      have : (⋃ (m ≤ n + k) (i ∈ { i : ι | (D m i ∩ B).Nonempty }), {(m, i)}).Finite :=
        (finite_le_nat _).bunionᵢ' fun i hi =>
          (Hle i hi).Finite.bunionᵢ' fun _ _ => finite_singleton _
      refine' this.subset fun I hI => _
      simp only [mem_Union]
      refine' ⟨I.1, _, I.2, hI, prod.mk.eta.symm⟩
      exact not_lt.1 fun hlt => (Hgt I.1 hlt I.2).le_bot hI.some_spec

-- see Note [lower instance priority]
instance (priority := 100) normal_of_emetric [EMetricSpace α] : NormalSpace α :=
  normal_of_paracompact_t2
#align emetric.normal_of_emetric Emetric.normal_of_emetric

end Emetric

