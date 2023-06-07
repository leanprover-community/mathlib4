/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.bounded_variation
! leanprover-community/mathlib commit 3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Fderiv.Equiv
import Mathlib.Analysis.Calculus.Fderiv.Prod
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Data.Set.Function
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Wlog

/-!
# Functions of bounded variation

We study functions of bounded variation. In particular, we show that a bounded variation function
is a difference of monotone functions, and differentiable almost everywhere. This implies that
Lipschitz functions from the real line into finite-dimensional vector space are also differentiable
almost everywhere.

## Main definitions and results

* `evariation_on f s` is the total variation of the function `f` on the set `s`, in `ℝ≥0∞`.
* `has_bounded_variation_on f s` registers that the variation of `f` on `s` is finite.
* `has_locally_bounded_variation f s` registers that `f` has finite variation on any compact
  subinterval of `s`.
* `variation_on_from_to f s a b` is the signed variation of `f` on `s ∩ Icc a b`, converted to `ℝ`.

* `evariation_on.Icc_add_Icc` states that the variation of `f` on `[a, c]` is the sum of its
  variations on `[a, b]` and `[b, c]`.
* `has_locally_bounded_variation_on.exists_monotone_on_sub_monotone_on` proves that a function
  with locally bounded variation is the difference of two monotone functions.
* `lipschitz_with.has_locally_bounded_variation_on` shows that a Lipschitz function has locally
  bounded variation.
* `has_locally_bounded_variation_on.ae_differentiable_within_at` shows that a bounded variation
  function into a finite dimensional real vector space is differentiable almost everywhere.
* `lipschitz_on_with.ae_differentiable_within_at` is the same result for Lipschitz functions.

We also give several variations around these results.

## Implementation

We define the variation as an extended nonnegative real, to allow for infinite variation. This makes
it possible to use the complete linear order structure of `ℝ≥0∞`. The proofs would be much
more tedious with an `ℝ`-valued or `ℝ≥0`-valued variation, since one would always need to check
that the sets one uses are nonempty and bounded above as these are only conditionally complete.
-/


open scoped BigOperators NNReal ENNReal Topology UniformConvergence

open Set MeasureTheory Filter

variable {α β : Type _} [LinearOrder α] [LinearOrder β] {E F : Type _} [PseudoEMetricSpace E]
  [PseudoEMetricSpace F] {V : Type _} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The (extended real valued) variation of a function `f` on a set `s` inside a linear order is
the supremum of the sum of `edist (f (u (i+1))) (f (u i))` over all finite increasing
sequences `u` in `s`. -/
noncomputable def evariationOn (f : α → E) (s : Set α) : ℝ≥0∞ :=
  ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    ∑ i in Finset.range p.1, edist (f ((p.2 : ℕ → α) (i + 1))) (f ((p.2 : ℕ → α) i))
#align evariation_on evariationOn

/-- A function has bounded variation on a set `s` if its total variation there is finite. -/
def HasBoundedVariationOn (f : α → E) (s : Set α) :=
  evariationOn f s ≠ ∞
#align has_bounded_variation_on HasBoundedVariationOn

/-- A function has locally bounded variation on a set `s` if, given any interval `[a, b]` with
endpoints in `s`, then the function has finite variation on `s ∩ [a, b]`. -/
def HasLocallyBoundedVariationOn (f : α → E) (s : Set α) :=
  ∀ a b, a ∈ s → b ∈ s → HasBoundedVariationOn f (s ∩ Icc a b)
#align has_locally_bounded_variation_on HasLocallyBoundedVariationOn

/-! ## Basic computations of variation -/


namespace evariationOn

theorem nonempty_monotone_mem {s : Set α} (hs : s.Nonempty) :
    Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ s } := by
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨fun i => x, fun i j hij => le_rfl, fun i => hx⟩⟩
#align evariation_on.nonempty_monotone_mem evariationOn.nonempty_monotone_mem

theorem eq_of_edist_zero_on {f f' : α → E} {s : Set α} (h : ∀ ⦃x⦄, x ∈ s → edist (f x) (f' x) = 0) :
    evariationOn f s = evariationOn f' s := by
  dsimp only [evariationOn]
  congr 1 with p : 1
  congr 1 with i : 1
  rw [edist_congr_right (h <| p.snd.prop.2 (i + 1)), edist_congr_left (h <| p.snd.prop.2 i)]
#align evariation_on.eq_of_edist_zero_on evariationOn.eq_of_edist_zero_on

theorem eq_of_eqOn {f f' : α → E} {s : Set α} (h : EqOn f f' s) :
    evariationOn f s = evariationOn f' s :=
  eq_of_edist_zero_on fun x xs => by rw [h xs, edist_self]
#align evariation_on.eq_of_eq_on evariationOn.eq_of_eqOn

theorem sum_le (f : α → E) {s : Set α} (n : ℕ) {u : ℕ → α} (hu : Monotone u) (us : ∀ i, u i ∈ s) :
    (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤ evariationOn f s :=
  le_iSup_of_le ⟨n, u, hu, us⟩ le_rfl
#align evariation_on.sum_le evariationOn.sum_le

theorem sum_le_of_monotoneOn_Iic (f : α → E) {s : Set α} {n : ℕ} {u : ℕ → α}
    (hu : MonotoneOn u (Iic n)) (us : ∀ i ≤ n, u i ∈ s) :
    (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤ evariationOn f s := by
  let v i := if i ≤ n then u i else u n
  have vs : ∀ i, v i ∈ s := by
    intro i
    simp only [v]
    split_ifs
    · exact us i h
    · exact us n le_rfl
  have hv : Monotone v := by
    apply monotone_nat_of_le_succ fun i => _
    simp only [v]
    rcases lt_trichotomy i n with (hi | rfl | hi)
    · have : i + 1 ≤ n := by linarith
      simp only [hi.le, this, if_true]
      exact hu hi.le this (Nat.le_succ i)
    · simp only [le_refl, if_true, add_le_iff_nonpos_right, le_zero_iff, Nat.one_ne_zero, if_false]
    · have A : ¬i ≤ n := by linarith
      have B : ¬i + 1 ≤ n := by linarith
      simp [A, B]
  convert sum_le f n hv vs using 1
  apply Finset.sum_congr rfl fun i hi => _
  simp only [Finset.mem_range] at hi 
  have : i + 1 ≤ n := by linarith
  simp only [v]
  simp [this, hi.le]
#align evariation_on.sum_le_of_monotone_on_Iic evariationOn.sum_le_of_monotoneOn_Iic

theorem sum_le_of_monotoneOn_Icc (f : α → E) {s : Set α} {m n : ℕ} {u : ℕ → α}
    (hu : MonotoneOn u (Icc m n)) (us : ∀ i ∈ Icc m n, u i ∈ s) :
    (∑ i in Finset.Ico m n, edist (f (u (i + 1))) (f (u i))) ≤ evariationOn f s := by
  rcases le_or_lt n m with (hnm | hmn)
  · simp only [Finset.Ico_eq_empty_of_le hnm, Finset.sum_empty, zero_le']
  let v i := u (m + i)
  have hv : MonotoneOn v (Iic (n - m)) := by
    intro a ha b hb hab
    simp only [le_tsub_iff_left hmn.le, mem_Iic] at ha hb 
    exact hu ⟨le_add_right le_rfl, ha⟩ ⟨le_add_right le_rfl, hb⟩ (add_le_add le_rfl hab)
  have vs : ∀ i ∈ Iic (n - m), v i ∈ s := by
    intro i hi
    simp only [le_tsub_iff_left hmn.le, mem_Iic] at hi 
    exact us _ ⟨le_add_right le_rfl, hi⟩
  calc
    (∑ i in Finset.Ico m n, edist (f (u (i + 1))) (f (u i))) =
        ∑ i in Finset.range (n - m), edist (f (u (m + i + 1))) (f (u (m + i))) := by
      rw [Finset.range_eq_Ico]
      convert (Finset.sum_Ico_add (fun i => edist (f (u (i + 1))) (f (u i))) 0 (n - m) m).symm
      · rw [zero_add]
      · rw [tsub_add_cancel_of_le hmn.le]
    _ = ∑ i in Finset.range (n - m), edist (f (v (i + 1))) (f (v i)) := by
      apply Finset.sum_congr rfl fun i hi => _
      simp only [v, add_assoc]
    _ ≤ evariationOn f s := sum_le_of_monotone_on_Iic f hv vs
    
#align evariation_on.sum_le_of_monotone_on_Icc evariationOn.sum_le_of_monotoneOn_Icc

theorem mono (f : α → E) {s t : Set α} (hst : t ⊆ s) : evariationOn f t ≤ evariationOn f s := by
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, ut⟩⟩
  exact sum_le f n hu fun i => hst (ut i)
#align evariation_on.mono evariationOn.mono

theorem HasBoundedVariationOn.mono {f : α → E} {s : Set α} (h : HasBoundedVariationOn f s)
    {t : Set α} (ht : t ⊆ s) : HasBoundedVariationOn f t :=
  (lt_of_le_of_lt (evariationOn.mono f ht) (lt_top_iff_ne_top.2 h)).Ne
#align has_bounded_variation_on.mono HasBoundedVariationOn.mono

theorem HasBoundedVariationOn.hasLocallyBoundedVariationOn {f : α → E} {s : Set α}
    (h : HasBoundedVariationOn f s) : HasLocallyBoundedVariationOn f s := fun x y hx hy =>
  h.mono (inter_subset_left _ _)
#align has_bounded_variation_on.has_locally_bounded_variation_on HasBoundedVariationOn.hasLocallyBoundedVariationOn

theorem edist_le (f : α → E) {s : Set α} {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    edist (f x) (f y) ≤ evariationOn f s := by
  wlog hxy : x ≤ y
  · rw [edist_comm]
    exact this f hy hx (le_of_not_le hxy)
  let u : ℕ → α := fun n => if n = 0 then x else y
  have hu : Monotone u := by
    intro m n hmn
    dsimp only [u]
    split_ifs
    exacts [le_rfl, hxy, by linarith [pos_iff_ne_zero.2 h], le_rfl]
  have us : ∀ i, u i ∈ s := by
    intro i
    dsimp only [u]
    split_ifs
    exacts [hx, hy]
  convert sum_le f 1 hu us
  simp [u, edist_comm]
#align evariation_on.edist_le evariationOn.edist_le

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem eq_zero_iff (f : α → E) {s : Set α} :
    evariationOn f s = 0 ↔ ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), edist (f x) (f y) = 0 := by
  constructor
  · rintro h x xs y ys
    rw [← le_zero_iff, ← h]
    exact edist_le f xs ys
  · rintro h
    dsimp only [evariationOn]
    rw [ENNReal.iSup_eq_zero]
    rintro ⟨n, u, um, us⟩
    exact Finset.sum_eq_zero fun i hi => h _ (us i.succ) _ (us i)
#align evariation_on.eq_zero_iff evariationOn.eq_zero_iff

theorem constant_on {f : α → E} {s : Set α} (hf : (f '' s).Subsingleton) : evariationOn f s = 0 :=
  by
  rw [eq_zero_iff]
  rintro x xs y ys
  rw [hf ⟨x, xs, rfl⟩ ⟨y, ys, rfl⟩, edist_self]
#align evariation_on.constant_on evariationOn.constant_on

@[simp]
protected theorem subsingleton (f : α → E) {s : Set α} (hs : s.Subsingleton) :
    evariationOn f s = 0 :=
  constant_on (hs.image f)
#align evariation_on.subsingleton evariationOn.subsingleton

theorem lower_continuous_aux {ι : Type _} {F : ι → α → E} {p : Filter ι} {f : α → E} {s : Set α}
    (Ffs : ∀ x ∈ s, Tendsto (fun i => F i x) p (𝓝 (f x))) {v : ℝ≥0∞} (hv : v < evariationOn f s) :
    ∀ᶠ n : ι in p, v < evariationOn (F n) s := by
  obtain ⟨⟨n, ⟨u, um, us⟩⟩, hlt⟩ :
    ∃ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
      v < ∑ i in Finset.range p.1, edist (f ((p.2 : ℕ → α) (i + 1))) (f ((p.2 : ℕ → α) i)) :=
    lt_supr_iff.mp hv
  have :
    tendsto (fun j => ∑ i : ℕ in Finset.range n, edist (F j (u (i + 1))) (F j (u i))) p
      (𝓝 (∑ i : ℕ in Finset.range n, edist (f (u (i + 1))) (f (u i)))) := by
    apply tendsto_finset_sum
    exact fun i hi => tendsto.edist (Ffs (u i.succ) (us i.succ)) (Ffs (u i) (us i))
  exact
    (eventually_gt_of_tendsto_gt hlt this).mono fun i h => lt_of_lt_of_le h (sum_le (F i) n um us)
#align evariation_on.lower_continuous_aux evariationOn.lower_continuous_aux

/-- The map `λ f, evariation_on f s` is lower semicontinuous for pointwise convergence *on `s`*.
Pointwise convergence on `s` is encoded here as uniform convergence on the family consisting of the
singletons of elements of `s`.
-/
@[protected]
theorem lowerSemicontinuous (s : Set α) :
    LowerSemicontinuous fun f : α →ᵤ[s.image singleton] E => evariationOn f s := by
  intro f
  apply @lower_continuous_aux _ _ _ _ (UniformOnFun α E (s.image singleton)) id (𝓝 f) f s _
  simpa only [UniformOnFun.tendsto_iff_tendstoUniformlyOn, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, tendstoUniformlyOn_singleton_iff_tendsto] using @tendsto_id _ (𝓝 f)
#align evariation_on.lower_semicontinuous evariationOn.lowerSemicontinuous

/-- The map `λ f, evariation_on f s` is lower semicontinuous for uniform convergence on `s`.
-/
theorem lowerSemicontinuous_uniform_on (s : Set α) :
    LowerSemicontinuous fun f : α →ᵤ[{s}] E => evariationOn f s := by
  intro f
  apply @lower_continuous_aux _ _ _ _ (UniformOnFun α E {s}) id (𝓝 f) f s _
  have := @tendsto_id _ (𝓝 f)
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at this 
  simp_rw [← tendstoUniformlyOn_singleton_iff_tendsto]
  exact fun x xs => (this s rfl).mono (singleton_subset_iff.mpr xs)
#align evariation_on.lower_semicontinuous_uniform_on evariationOn.lowerSemicontinuous_uniform_on

theorem HasBoundedVariationOn.dist_le {E : Type _} [PseudoMetricSpace E] {f : α → E} {s : Set α}
    (h : HasBoundedVariationOn f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    dist (f x) (f y) ≤ (evariationOn f s).toReal := by
  rw [← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, ENNReal.ofReal_toReal h, ← edist_dist]
  exact edist_le f hx hy
#align has_bounded_variation_on.dist_le HasBoundedVariationOn.dist_le

theorem HasBoundedVariationOn.sub_le {f : α → ℝ} {s : Set α} (h : HasBoundedVariationOn f s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : f x - f y ≤ (evariationOn f s).toReal := by
  apply (le_abs_self _).trans
  rw [← Real.dist_eq]
  exact h.dist_le hx hy
#align has_bounded_variation_on.sub_le HasBoundedVariationOn.sub_le

/-- Consider a monotone function `u` parameterizing some points of a set `s`. Given `x ∈ s`, then
one can find another monotone function `v` parameterizing the same points as `u`, with `x` added.
In particular, the variation of a function along `u` is bounded by its variation along `v`. -/
theorem add_point (f : α → E) {s : Set α} {x : α} (hx : x ∈ s) (u : ℕ → α) (hu : Monotone u)
    (us : ∀ i, u i ∈ s) (n : ℕ) :
    ∃ (v : ℕ → α) (m : ℕ),
      Monotone v ∧
        (∀ i, v i ∈ s) ∧
          x ∈ v '' Iio m ∧
            (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤
              ∑ j in Finset.range m, edist (f (v (j + 1))) (f (v j)) := by
  rcases le_or_lt (u n) x with (h | h)
  · let v i := if i ≤ n then u i else x
    have vs : ∀ i, v i ∈ s := by
      intro i
      simp only [v]
      split_ifs
      · exact us i
      · exact hx
    have hv : Monotone v := by
      apply monotone_nat_of_le_succ fun i => _
      simp only [v]
      rcases lt_trichotomy i n with (hi | rfl | hi)
      · have : i + 1 ≤ n := Nat.succ_le_of_lt hi
        simp only [hi.le, this, if_true]
        exact hu (Nat.le_succ i)
      ·
        simp only [le_refl, if_true, add_le_iff_nonpos_right, le_zero_iff, Nat.one_ne_zero,
          if_false, h]
      · have A : ¬i ≤ n := hi.not_le
        have B : ¬i + 1 ≤ n := fun h => A (i.le_succ.trans h)
        simp only [A, B, if_false]
    refine' ⟨v, n + 2, hv, vs, (mem_image _ _ _).2 ⟨n + 1, _, _⟩, _⟩
    · rw [mem_Iio]; exact Nat.lt_succ_self (n + 1)
    · have : ¬n + 1 ≤ n := Nat.not_succ_le_self n
      simp only [this, ite_eq_right_iff, IsEmpty.forall_iff]
    ·
      calc
        (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) =
            ∑ i in Finset.range n, edist (f (v (i + 1))) (f (v i)) := by
          apply Finset.sum_congr rfl fun i hi => _
          simp only [Finset.mem_range] at hi 
          have : i + 1 ≤ n := Nat.succ_le_of_lt hi
          dsimp only [v]
          simp only [hi.le, this, if_true]
        _ ≤ ∑ j in Finset.range (n + 2), edist (f (v (j + 1))) (f (v j)) :=
          Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_add_right n 2))
        
  have exists_N : ∃ N, N ≤ n ∧ x < u N := ⟨n, le_rfl, h⟩
  let N := Nat.find exists_N
  have hN : N ≤ n ∧ x < u N := Nat.find_spec exists_N
  let w : ℕ → α := fun i => if i < N then u i else if i = N then x else u (i - 1)
  have ws : ∀ i, w i ∈ s := by
    dsimp only [w]
    intro i
    split_ifs
    exacts [us _, hx, us _]
  have hw : Monotone w := by
    apply monotone_nat_of_le_succ fun i => _
    dsimp only [w]
    rcases lt_trichotomy (i + 1) N with (hi | hi | hi)
    · have : i < N := Nat.lt_of_le_of_lt (Nat.le_succ i) hi
      simp only [hi, this, if_true]
      exact hu (Nat.le_succ _)
    · have A : i < N := hi ▸ i.lt_succ_self
      have B : ¬i + 1 < N := by rw [← hi]; exact fun h => h.Ne rfl
      rw [if_pos A, if_neg B, if_pos hi]
      have T := Nat.find_min exists_N A
      push_neg at T 
      exact T (A.le.trans hN.1)
    · have A : ¬i < N := (nat.lt_succ_iff.mp hi).not_lt
      have B : ¬i + 1 < N := hi.not_lt
      have C : ¬i + 1 = N := hi.ne.symm
      have D : i + 1 - 1 = i := Nat.pred_succ i
      rw [if_neg A, if_neg B, if_neg C, D]
      split_ifs
      · exact hN.2.le.trans (hu (le_of_not_lt A))
      · exact hu (Nat.pred_le _)
  refine' ⟨w, n + 1, hw, ws, (mem_image _ _ _).2 ⟨N, hN.1.trans_lt (Nat.lt_succ_self n), _⟩, _⟩
  · dsimp only [w]; rw [if_neg (lt_irrefl N), if_pos rfl]
  rcases eq_or_lt_of_le (zero_le N) with (Npos | Npos)
  ·
    calc
      (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ∑ i in Finset.range n, edist (f (w (1 + i + 1))) (f (w (1 + i))) := by
        apply Finset.sum_congr rfl fun i hi => _
        dsimp only [w]
        simp only [← Npos, Nat.not_lt_zero, Nat.add_succ_sub_one, add_zero, if_false,
          add_eq_zero_iff, Nat.one_ne_zero, false_and_iff, Nat.succ_add_sub_one, zero_add]
        rw [add_comm 1 i]
      _ = ∑ i in Finset.Ico 1 (n + 1), edist (f (w (i + 1))) (f (w i)) := by
        rw [Finset.range_eq_Ico]
        exact Finset.sum_Ico_add (fun i => edist (f (w (i + 1))) (f (w i))) 0 n 1
      _ ≤ ∑ j in Finset.range (n + 1), edist (f (w (j + 1))) (f (w j)) := by
        apply Finset.sum_le_sum_of_subset _
        rw [Finset.range_eq_Ico]
        exact Finset.Ico_subset_Ico zero_le_one le_rfl
      
  ·
    calc
      (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ((∑ i in Finset.Ico 0 (N - 1), edist (f (u (i + 1))) (f (u i))) +
              ∑ i in Finset.Ico (N - 1) N, edist (f (u (i + 1))) (f (u i))) +
            ∑ i in Finset.Ico N n, edist (f (u (i + 1))) (f (u i)) := by
        rw [Finset.sum_Ico_consecutive, Finset.sum_Ico_consecutive, Finset.range_eq_Ico]
        · exact zero_le _
        · exact hN.1
        · exact zero_le _
        · exact Nat.pred_le _
      _ =
          (∑ i in Finset.Ico 0 (N - 1), edist (f (w (i + 1))) (f (w i))) +
              edist (f (u N)) (f (u (N - 1))) +
            ∑ i in Finset.Ico N n, edist (f (w (1 + i + 1))) (f (w (1 + i))) := by
        congr 1; congr 1
        · apply Finset.sum_congr rfl fun i hi => _
          simp only [Finset.mem_Ico, zero_le', true_and_iff] at hi 
          dsimp only [w]
          have A : i + 1 < N := Nat.lt_pred_iff.1 hi
          have B : i < N := Nat.lt_of_succ_lt A
          rw [if_pos A, if_pos B]
        · have A : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos Npos
          have : Finset.Ico (N - 1) N = {N - 1} := by rw [← Nat.Ico_succ_singleton, A]
          simp only [this, A, Finset.sum_singleton]
        · apply Finset.sum_congr rfl fun i hi => _
          simp only [Finset.mem_Ico] at hi 
          dsimp only [w]
          have A : ¬1 + i + 1 < N := fun h => by
            rw [add_assoc, add_comm] at h 
            exact hi.left.not_lt (i.lt_succ_self.trans (i.succ.lt_succ_self.trans h))
          have B : ¬1 + i + 1 = N := fun h => by
            rw [← h, add_assoc, add_comm] at hi 
            exact Nat.not_succ_le_self i (i.succ.le_succ.trans hi.left)
          have C : ¬1 + i < N := fun h => by rw [add_comm] at h ;
            exact hi.left.not_lt (i.lt_succ_self.trans h)
          have D : ¬1 + i = N := fun h => by rw [← h, add_comm, Nat.succ_le_iff] at hi ;
            exact hi.left.ne rfl
          rw [if_neg A, if_neg B, if_neg C, if_neg D]
          congr 3 <;> · rw [add_comm, Nat.sub_one]; apply Nat.pred_succ
      _ =
          (∑ i in Finset.Ico 0 (N - 1), edist (f (w (i + 1))) (f (w i))) +
              edist (f (w (N + 1))) (f (w (N - 1))) +
            ∑ i in Finset.Ico (N + 1) (n + 1), edist (f (w (i + 1))) (f (w i)) := by
        congr 1; congr 1
        · dsimp only [w]
          have A : ¬N + 1 < N := Nat.not_succ_lt_self
          have B : N - 1 < N := Nat.pred_lt Npos.ne'
          simp only [A, not_and, not_lt, Nat.succ_ne_self, Nat.add_succ_sub_one, add_zero, if_false,
            B, if_true]
        · exact Finset.sum_Ico_add (fun i => edist (f (w (i + 1))) (f (w i))) N n 1
      _ ≤
          ((∑ i in Finset.Ico 0 (N - 1), edist (f (w (i + 1))) (f (w i))) +
              ∑ i in Finset.Ico (N - 1) (N + 1), edist (f (w (i + 1))) (f (w i))) +
            ∑ i in Finset.Ico (N + 1) (n + 1), edist (f (w (i + 1))) (f (w i)) := by
        refine' add_le_add (add_le_add le_rfl _) le_rfl
        have A : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos Npos
        have B : N - 1 + 1 < N + 1 := A.symm ▸ N.lt_succ_self
        have C : N - 1 < N + 1 := lt_of_le_of_lt N.pred_le N.lt_succ_self
        rw [Finset.sum_eq_sum_Ico_succ_bot C, Finset.sum_eq_sum_Ico_succ_bot B, A, Finset.Ico_self,
          Finset.sum_empty, add_zero, add_comm (edist _ _)]
        exact edist_triangle _ _ _
      _ = ∑ j in Finset.range (n + 1), edist (f (w (j + 1))) (f (w j)) := by
        rw [Finset.sum_Ico_consecutive, Finset.sum_Ico_consecutive, Finset.range_eq_Ico]
        · exact zero_le _
        · exact Nat.succ_le_succ hN.left
        · exact zero_le _
        · exact N.pred_le.trans N.le_succ
      
#align evariation_on.add_point evariationOn.add_point

/-- The variation of a function on the union of two sets `s` and `t`, with `s` to the left of `t`,
bounds the sum of the variations along `s` and `t`. -/
theorem add_le_union (f : α → E) {s t : Set α} (h : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
    evariationOn f s + evariationOn f t ≤ evariationOn f (s ∪ t) := by
  by_cases hs : s = ∅
  · simp [hs]
  have : Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ s } :=
    nonempty_monotone_mem (nonempty_iff_ne_empty.2 hs)
  by_cases ht : t = ∅
  · simp [ht]
  have : Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ t } :=
    nonempty_monotone_mem (nonempty_iff_ne_empty.2 ht)
  refine' ENNReal.iSup_add_iSup_le _
  /- We start from two sequences `u` and `v` along `s` and `t` respectively, and we build a new
    sequence `w` along `s ∪ t` by juxtaposing them. Its variation is larger than the sum of the
    variations. -/
  rintro ⟨n, ⟨u, hu, us⟩⟩ ⟨m, ⟨v, hv, vt⟩⟩
  let w i := if i ≤ n then u i else v (i - (n + 1))
  have wst : ∀ i, w i ∈ s ∪ t := by
    intro i
    by_cases hi : i ≤ n
    · simp [w, hi, us]
    · simp [w, hi, vt]
  have hw : Monotone w := by
    intro i j hij
    dsimp only [w]
    split_ifs
    · exact hu hij
    · apply h _ (us _) _ (vt _)
    · exfalso; exact h_1 (hij.trans h_2)
    · apply hv (tsub_le_tsub hij le_rfl)
  calc
    ((∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) +
          ∑ i : ℕ in Finset.range m, edist (f (v (i + 1))) (f (v i))) =
        (∑ i in Finset.range n, edist (f (w (i + 1))) (f (w i))) +
          ∑ i : ℕ in Finset.range m, edist (f (w (n + 1 + i + 1))) (f (w (n + 1 + i))) := by
      dsimp only [w]
      congr 1
      · apply Finset.sum_congr rfl fun i hi => _
        simp only [Finset.mem_range] at hi 
        have : i + 1 ≤ n := Nat.succ_le_of_lt hi
        simp [hi.le, this]
      · apply Finset.sum_congr rfl fun i hi => _
        simp only [Finset.mem_range] at hi 
        have B : ¬n + 1 + i ≤ n := by linarith
        have A : ¬n + 1 + i + 1 ≤ n := fun h => B ((n + 1 + i).le_succ.trans h)
        have C : n + 1 + i - n = i + 1 := by
          rw [tsub_eq_iff_eq_add_of_le]
          · abel
          · exact n.le_succ.trans (n.succ.le_add_right i)
        simp only [A, B, C, Nat.succ_sub_succ_eq_sub, if_false, add_tsub_cancel_left]
    _ =
        (∑ i in Finset.range n, edist (f (w (i + 1))) (f (w i))) +
          ∑ i : ℕ in Finset.Ico (n + 1) (n + 1 + m), edist (f (w (i + 1))) (f (w i)) := by
      congr 1
      rw [Finset.range_eq_Ico]
      convert Finset.sum_Ico_add (fun i : ℕ => edist (f (w (i + 1))) (f (w i))) 0 m (n + 1) using
          3 <;>
        abel
    _ ≤ ∑ i in Finset.range (n + 1 + m), edist (f (w (i + 1))) (f (w i)) := by
      rw [← Finset.sum_union]
      · apply Finset.sum_le_sum_of_subset _
        rintro i hi
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico] at hi ⊢
        cases hi
        · exact lt_of_lt_of_le hi (n.le_succ.trans (n.succ.le_add_right m))
        · exact hi.2
      · apply Finset.disjoint_left.2 fun i hi h'i => _
        simp only [Finset.mem_Ico, Finset.mem_range] at hi h'i 
        exact hi.not_lt (Nat.lt_of_succ_le h'i.left)
    _ ≤ evariationOn f (s ∪ t) := sum_le f _ hw wst
    
#align evariation_on.add_le_union evariationOn.add_le_union

/-- If a set `s` is to the left of a set `t`, and both contain the boundary point `x`, then
the variation of `f` along `s ∪ t` is the sum of the variations. -/
theorem union (f : α → E) {s t : Set α} {x : α} (hs : IsGreatest s x) (ht : IsLeast t x) :
    evariationOn f (s ∪ t) = evariationOn f s + evariationOn f t := by
  classical
  apply le_antisymm _ (evariationOn.add_le_union f fun a ha b hb => le_trans (hs.2 ha) (ht.2 hb))
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, ust⟩⟩
  obtain ⟨v, m, hv, vst, xv, huv⟩ :
    ∃ (v : ℕ → α) (m : ℕ),
      Monotone v ∧
        (∀ i, v i ∈ s ∪ t) ∧
          x ∈ v '' Iio m ∧
            (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤
              ∑ j in Finset.range m, edist (f (v (j + 1))) (f (v j))
  exact evariationOn.add_point f (mem_union_left t hs.1) u hu ust n
  obtain ⟨N, hN, Nx⟩ : ∃ N, N < m ∧ v N = x
  exact xv
  calc
    (∑ j in Finset.range n, edist (f (u (j + 1))) (f (u j))) ≤
        ∑ j in Finset.range m, edist (f (v (j + 1))) (f (v j)) :=
      huv
    _ =
        (∑ j in Finset.Ico 0 N, edist (f (v (j + 1))) (f (v j))) +
          ∑ j in Finset.Ico N m, edist (f (v (j + 1))) (f (v j)) :=
      by rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (zero_le _) hN.le]
    _ ≤ evariationOn f s + evariationOn f t := by
      refine' add_le_add _ _
      · apply sum_le_of_monotone_on_Icc _ (hv.monotone_on _) fun i hi => _
        rcases vst i with (h | h); · exact h
        have : v i = x := by
          apply le_antisymm
          · rw [← Nx]; exact hv hi.2
          · exact ht.2 h
        rw [this]
        exact hs.1
      · apply sum_le_of_monotone_on_Icc _ (hv.monotone_on _) fun i hi => _
        rcases vst i with (h | h); swap; · exact h
        have : v i = x := by
          apply le_antisymm
          · exact hs.2 h
          · rw [← Nx]; exact hv hi.1
        rw [this]
        exact ht.1
    
#align evariation_on.union evariationOn.union

theorem Icc_add_Icc (f : α → E) {s : Set α} {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) (hb : b ∈ s) :
    evariationOn f (s ∩ Icc a b) + evariationOn f (s ∩ Icc b c) = evariationOn f (s ∩ Icc a c) := by
  have A : IsGreatest (s ∩ Icc a b) b :=
    ⟨⟨hb, hab, le_rfl⟩, (inter_subset_right _ _).trans Icc_subset_Iic_self⟩
  have B : IsLeast (s ∩ Icc b c) b :=
    ⟨⟨hb, le_rfl, hbc⟩, (inter_subset_right _ _).trans Icc_subset_Ici_self⟩
  rw [← evariationOn.union f A B, ← inter_union_distrib_left, Icc_union_Icc_eq_Icc hab hbc]
#align evariation_on.Icc_add_Icc evariationOn.Icc_add_Icc

theorem comp_le_of_monotoneOn (f : α → E) {s : Set α} {t : Set β} (φ : β → α) (hφ : MonotoneOn φ t)
    (φst : MapsTo φ t s) : evariationOn (f ∘ φ) t ≤ evariationOn f s :=
  iSup_le fun ⟨n, u, hu, ut⟩ =>
    le_iSup_of_le ⟨n, φ ∘ u, fun x y xy => hφ (ut x) (ut y) (hu xy), fun i => φst (ut i)⟩ le_rfl
#align evariation_on.comp_le_of_monotone_on evariationOn.comp_le_of_monotoneOn

theorem comp_le_of_antitoneOn (f : α → E) {s : Set α} {t : Set β} (φ : β → α) (hφ : AntitoneOn φ t)
    (φst : MapsTo φ t s) : evariationOn (f ∘ φ) t ≤ evariationOn f s := by
  refine' iSup_le _
  rintro ⟨n, u, hu, ut⟩
  rw [← Finset.sum_range_reflect]
  refine'
    (Finset.sum_congr rfl fun x hx => _).trans_le
      (le_iSup_of_le
        ⟨n, fun i => φ (u <| n - i), fun x y xy => hφ (ut _) (ut _) (hu <| n.sub_le_sub_left xy),
          fun i => φst (ut _)⟩
        le_rfl)
  dsimp only [Subtype.coe_mk]
  rw [edist_comm, Nat.sub_sub, add_comm, Nat.sub_succ, Nat.add_one, Nat.succ_pred_eq_of_pos]
  simpa only [tsub_pos_iff_lt, Finset.mem_range] using hx
#align evariation_on.comp_le_of_antitone_on evariationOn.comp_le_of_antitoneOn

theorem comp_eq_of_monotoneOn (f : α → E) {t : Set β} (φ : β → α) (hφ : MonotoneOn φ t) :
    evariationOn (f ∘ φ) t = evariationOn f (φ '' t) := by
  apply le_antisymm (comp_le_of_monotone_on f φ hφ (maps_to_image φ t))
  cases isEmpty_or_nonempty β
  · convert zero_le _
    exact
      evariationOn.subsingleton f ((subsingleton_of_subsingleton.image _).anti (surj_on_image φ t))
  let ψ := φ.inv_fun_on t
  have ψφs : eq_on (φ ∘ ψ) id (φ '' t) := (surj_on_image φ t).rightInvOn_invFunOn
  have ψts : maps_to ψ (φ '' t) t := (surj_on_image φ t).mapsTo_invFunOn
  have hψ : MonotoneOn ψ (φ '' t) := Function.monotoneOn_of_rightInvOn_of_mapsTo hφ ψφs ψts
  change evariationOn (f ∘ id) (φ '' t) ≤ evariationOn (f ∘ φ) t
  rw [← eq_of_eq_on (ψφs.comp_left : eq_on (f ∘ φ ∘ ψ) (f ∘ id) (φ '' t))]
  exact comp_le_of_monotone_on _ ψ hψ ψts
#align evariation_on.comp_eq_of_monotone_on evariationOn.comp_eq_of_monotoneOn

-- porting note: move to file `data.set.intervals.basic` once the port is over,
-- and use it in theorem `polynomial_functions_closure_eq_top`
-- in the file `topology/continuous_function/weierstrass.lean`
theorem Set.subsingleton_Icc_of_ge {α : Type _} [PartialOrder α] {a b : α} (h : b ≤ a) :
    Set.Subsingleton (Icc a b) := by
  rintro c ⟨ac, cb⟩ d ⟨ad, db⟩
  cases le_antisymm (cb.trans h) ac
  cases le_antisymm (db.trans h) ad
  rfl
#align set.subsingleton_Icc_of_ge Set.subsingleton_Icc_of_ge

theorem comp_inter_Icc_eq_of_monotoneOn (f : α → E) {t : Set β} (φ : β → α) (hφ : MonotoneOn φ t)
    {x y : β} (hx : x ∈ t) (hy : y ∈ t) :
    evariationOn (f ∘ φ) (t ∩ Icc x y) = evariationOn f (φ '' t ∩ Icc (φ x) (φ y)) := by
  rcases le_total x y with (h | h)
  · convert comp_eq_of_monotone_on f φ (hφ.mono (Set.inter_subset_left t (Icc x y)))
    apply le_antisymm
    · rintro _ ⟨⟨u, us, rfl⟩, vφx, vφy⟩
      rcases le_total x u with (xu | ux)
      · rcases le_total u y with (uy | yu)
        · exact ⟨u, ⟨us, ⟨xu, uy⟩⟩, rfl⟩
        · rw [le_antisymm vφy (hφ hy us yu)]
          exact ⟨y, ⟨hy, ⟨h, le_rfl⟩⟩, rfl⟩
      · rw [← le_antisymm vφx (hφ us hx ux)]
        exact ⟨x, ⟨hx, ⟨le_rfl, h⟩⟩, rfl⟩
    · rintro _ ⟨u, ⟨⟨hu, xu, uy⟩, rfl⟩⟩
      refine' ⟨⟨u, hu, rfl⟩, ⟨hφ hx hu xu, hφ hu hy uy⟩⟩
  · rw [evariationOn.subsingleton, evariationOn.subsingleton]
    exacts [(Set.subsingleton_Icc_of_ge (hφ hy hx h)).anti (Set.inter_subset_right _ _),
      (Set.subsingleton_Icc_of_ge h).anti (Set.inter_subset_right _ _)]
#align evariation_on.comp_inter_Icc_eq_of_monotone_on evariationOn.comp_inter_Icc_eq_of_monotoneOn

theorem comp_eq_of_antitoneOn (f : α → E) {t : Set β} (φ : β → α) (hφ : AntitoneOn φ t) :
    evariationOn (f ∘ φ) t = evariationOn f (φ '' t) := by
  apply le_antisymm (comp_le_of_antitone_on f φ hφ (maps_to_image φ t))
  cases isEmpty_or_nonempty β
  · convert zero_le _
    exact
      evariationOn.subsingleton f ((subsingleton_of_subsingleton.image _).anti (surj_on_image φ t))
  let ψ := φ.inv_fun_on t
  have ψφs : eq_on (φ ∘ ψ) id (φ '' t) := (surj_on_image φ t).rightInvOn_invFunOn
  have ψts := (surj_on_image φ t).mapsTo_invFunOn
  have hψ : AntitoneOn ψ (φ '' t) := Function.antitoneOn_of_rightInvOn_of_mapsTo hφ ψφs ψts
  change evariationOn (f ∘ id) (φ '' t) ≤ evariationOn (f ∘ φ) t
  rw [← eq_of_eq_on (ψφs.comp_left : eq_on (f ∘ φ ∘ ψ) (f ∘ id) (φ '' t))]
  exact comp_le_of_antitone_on _ ψ hψ ψts
#align evariation_on.comp_eq_of_antitone_on evariationOn.comp_eq_of_antitoneOn

open OrderDual

theorem comp_ofDual (f : α → E) (s : Set α) :
    evariationOn (f ∘ ofDual) (ofDual ⁻¹' s) = evariationOn f s := by
  convert comp_eq_of_antitone_on f of_dual fun _ _ _ _ => id
  simp only [Equiv.image_preimage]
#align evariation_on.comp_of_dual evariationOn.comp_ofDual

end evariationOn

/-! ## Monotone functions and bounded variation -/


theorem MonotoneOn.evariationOn_le {f : α → ℝ} {s : Set α} (hf : MonotoneOn f s) {a b : α}
    (as : a ∈ s) (bs : b ∈ s) : evariationOn f (s ∩ Icc a b) ≤ ENNReal.ofReal (f b - f a) := by
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) =
        ∑ i in Finset.range n, ENNReal.ofReal (f (u (i + 1)) - f (u i)) := by
      apply Finset.sum_congr rfl fun i hi => _
      simp only [Finset.mem_range] at hi 
      rw [edist_dist, Real.dist_eq, abs_of_nonneg]
      exact sub_nonneg_of_le (hf (us i).1 (us (i + 1)).1 (hu (Nat.le_succ _)))
    _ = ENNReal.ofReal (∑ i in Finset.range n, f (u (i + 1)) - f (u i)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i hi
      exact sub_nonneg_of_le (hf (us i).1 (us (i + 1)).1 (hu (Nat.le_succ _)))
    _ = ENNReal.ofReal (f (u n) - f (u 0)) := by rw [Finset.sum_range_sub fun i => f (u i)]
    _ ≤ ENNReal.ofReal (f b - f a) := by
      apply ENNReal.ofReal_le_ofReal
      exact sub_le_sub (hf (us n).1 bs (us n).2.2) (hf as (us 0).1 (us 0).2.1)
    
#align monotone_on.evariation_on_le MonotoneOn.evariationOn_le

theorem MonotoneOn.hasLocallyBoundedVariationOn {f : α → ℝ} {s : Set α} (hf : MonotoneOn f s) :
    HasLocallyBoundedVariationOn f s := fun a b as bs =>
  ((hf.evariationOn_le as bs).trans_lt ENNReal.ofReal_lt_top).Ne
#align monotone_on.has_locally_bounded_variation_on MonotoneOn.hasLocallyBoundedVariationOn

/-- The **signed** variation of `f` on the interval `Icc a b` intersected with the set `s`,
squashed to a real (therefore only really meaningful if the variation is finite)
-/
noncomputable def variationOnFromTo (f : α → E) (s : Set α) (a b : α) : ℝ :=
  if a ≤ b then (evariationOn f (s ∩ Icc a b)).toReal else -(evariationOn f (s ∩ Icc b a)).toReal
#align variation_on_from_to variationOnFromTo

namespace variationOnFromTo

variable (f : α → E) (s : Set α)

@[protected]
theorem self (a : α) : variationOnFromTo f s a a = 0 := by
  dsimp only [variationOnFromTo]
  rw [if_pos le_rfl, Icc_self, evariationOn.subsingleton, ENNReal.zero_toReal]
  exact fun x hx y hy => hx.2.trans hy.2.symm
#align variation_on_from_to.self variationOnFromTo.self

@[protected]
theorem nonneg_of_le {a b : α} (h : a ≤ b) : 0 ≤ variationOnFromTo f s a b := by
  simp only [variationOnFromTo, if_pos h, ENNReal.toReal_nonneg]
#align variation_on_from_to.nonneg_of_le variationOnFromTo.nonneg_of_le

@[protected]
theorem eq_neg_swap (a b : α) : variationOnFromTo f s a b = -variationOnFromTo f s b a := by
  rcases lt_trichotomy a b with (ab | rfl | ba)
  · simp only [variationOnFromTo, if_pos ab.le, if_neg ab.not_le, neg_neg]
  · simp only [self, neg_zero]
  · simp only [variationOnFromTo, if_pos ba.le, if_neg ba.not_le, neg_neg]
#align variation_on_from_to.eq_neg_swap variationOnFromTo.eq_neg_swap

@[protected]
theorem nonpos_of_ge {a b : α} (h : b ≤ a) : variationOnFromTo f s a b ≤ 0 := by
  rw [eq_neg_swap]
  exact neg_nonpos_of_nonneg (nonneg_of_le f s h)
#align variation_on_from_to.nonpos_of_ge variationOnFromTo.nonpos_of_ge

@[protected]
theorem eq_of_le {a b : α} (h : a ≤ b) :
    variationOnFromTo f s a b = (evariationOn f (s ∩ Icc a b)).toReal :=
  if_pos h
#align variation_on_from_to.eq_of_le variationOnFromTo.eq_of_le

@[protected]
theorem eq_of_ge {a b : α} (h : b ≤ a) :
    variationOnFromTo f s a b = -(evariationOn f (s ∩ Icc b a)).toReal := by
  rw [eq_neg_swap, neg_inj, eq_of_le f s h]
#align variation_on_from_to.eq_of_ge variationOnFromTo.eq_of_ge

@[protected]
theorem add {f : α → E} {s : Set α} (hf : HasLocallyBoundedVariationOn f s) {a b c : α} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) :
    variationOnFromTo f s a b + variationOnFromTo f s b c = variationOnFromTo f s a c := by
  symm
  refine' additive_of_isTotal (· ≤ ·) (variationOnFromTo f s) (· ∈ s) _ _ ha hb hc
  · rintro x y xs ys
    simp only [eq_neg_swap f s y x, Subtype.coe_mk, add_right_neg, forall_true_left]
  · rintro x y z xy yz xs ys zs
    rw [eq_of_le f s xy, eq_of_le f s yz, eq_of_le f s (xy.trans yz), ←
      ENNReal.toReal_add (hf x y xs ys) (hf y z ys zs), evariationOn.Icc_add_Icc f xy yz ys]
#align variation_on_from_to.add variationOnFromTo.add

@[protected]
theorem edist_zero_of_eq_zero {f : α → E} {s : Set α} (hf : HasLocallyBoundedVariationOn f s)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : variationOnFromTo f s a b = 0) :
    edist (f a) (f b) = 0 := by
  wlog h' : a ≤ b
  · rw [edist_comm]
    apply this hf hb ha _ (le_of_not_le h')
    rw [eq_neg_swap, h, neg_zero]
  · apply le_antisymm _ (zero_le _)
    rw [← ENNReal.ofReal_zero, ← h, eq_of_le f s h', ENNReal.ofReal_toReal (hf a b ha hb)]
    apply evariationOn.edist_le
    exacts [⟨ha, ⟨le_rfl, h'⟩⟩, ⟨hb, ⟨h', le_rfl⟩⟩]
#align variation_on_from_to.edist_zero_of_eq_zero variationOnFromTo.edist_zero_of_eq_zero

@[protected]
theorem eq_left_iff {f : α → E} {s : Set α} (hf : HasLocallyBoundedVariationOn f s) {a b c : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    variationOnFromTo f s a b = variationOnFromTo f s a c ↔ variationOnFromTo f s b c = 0 := by
  simp only [← add hf ha hb hc, self_eq_add_right]
#align variation_on_from_to.eq_left_iff variationOnFromTo.eq_left_iff

@[protected]
theorem eq_zero_iff_of_le {f : α → E} {s : Set α} (hf : HasLocallyBoundedVariationOn f s) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (ab : a ≤ b) :
    variationOnFromTo f s a b = 0 ↔
      ∀ ⦃x⦄ (hx : x ∈ s ∩ Icc a b) ⦃y⦄ (hy : y ∈ s ∩ Icc a b), edist (f x) (f y) = 0 := by
  rw [eq_of_le _ _ ab, ENNReal.toReal_eq_zero_iff, or_iff_left (hf a b ha hb),
    evariationOn.eq_zero_iff]
#align variation_on_from_to.eq_zero_iff_of_le variationOnFromTo.eq_zero_iff_of_le

@[protected]
theorem eq_zero_iff_of_ge {f : α → E} {s : Set α} (hf : HasLocallyBoundedVariationOn f s) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (ba : b ≤ a) :
    variationOnFromTo f s a b = 0 ↔
      ∀ ⦃x⦄ (hx : x ∈ s ∩ Icc b a) ⦃y⦄ (hy : y ∈ s ∩ Icc b a), edist (f x) (f y) = 0 := by
  rw [eq_of_ge _ _ ba, neg_eq_zero, ENNReal.toReal_eq_zero_iff, or_iff_left (hf b a hb ha),
    evariationOn.eq_zero_iff]
#align variation_on_from_to.eq_zero_iff_of_ge variationOnFromTo.eq_zero_iff_of_ge

@[protected]
theorem eq_zero_iff {f : α → E} {s : Set α} (hf : HasLocallyBoundedVariationOn f s) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) :
    variationOnFromTo f s a b = 0 ↔
      ∀ ⦃x⦄ (hx : x ∈ s ∩ uIcc a b) ⦃y⦄ (hy : y ∈ s ∩ uIcc a b), edist (f x) (f y) = 0 := by
  rcases le_total a b with (ab | ba)
  · rw [uIcc_of_le ab]
    exact eq_zero_iff_of_le hf ha hb ab
  · rw [uIcc_of_ge ba]
    exact eq_zero_iff_of_ge hf ha hb ba
#align variation_on_from_to.eq_zero_iff variationOnFromTo.eq_zero_iff

variable {f} {s}

@[protected]
theorem monotoneOn (hf : HasLocallyBoundedVariationOn f s) {a : α} (as : a ∈ s) :
    MonotoneOn (variationOnFromTo f s a) s := by
  rintro b bs c cs bc
  rw [← add hf as bs cs]
  exact le_add_of_nonneg_right (nonneg_of_le f s bc)
#align variation_on_from_to.monotone_on variationOnFromTo.monotoneOn

@[protected]
theorem antitoneOn (hf : HasLocallyBoundedVariationOn f s) {b : α} (bs : b ∈ s) :
    AntitoneOn (fun a => variationOnFromTo f s a b) s := by
  rintro a as c cs ac
  dsimp only
  rw [← add hf as cs bs]
  exact le_add_of_nonneg_left (nonneg_of_le f s ac)
#align variation_on_from_to.antitone_on variationOnFromTo.antitoneOn

@[protected]
theorem sub_self_monotoneOn {f : α → ℝ} {s : Set α} (hf : HasLocallyBoundedVariationOn f s) {a : α}
    (as : a ∈ s) : MonotoneOn (variationOnFromTo f s a - f) s := by
  rintro b bs c cs bc
  rw [Pi.sub_apply, Pi.sub_apply, le_sub_iff_add_le, add_comm_sub, ← le_sub_iff_add_le']
  calc
    f c - f b ≤ |f c - f b| := le_abs_self _
    _ = dist (f b) (f c) := by rw [dist_comm, Real.dist_eq]
    _ ≤ variationOnFromTo f s b c := by
      rw [eq_of_le f s bc, dist_edist]
      apply ENNReal.toReal_mono (hf b c bs cs)
      apply evariationOn.edist_le f
      exacts [⟨bs, le_rfl, bc⟩, ⟨cs, bc, le_rfl⟩]
    _ = variationOnFromTo f s a c - variationOnFromTo f s a b := by
      rw [← add hf as bs cs, add_sub_cancel']
    
#align variation_on_from_to.sub_self_monotone_on variationOnFromTo.sub_self_monotoneOn

@[protected]
theorem comp_eq_of_monotoneOn (f : α → E) {t : Set β} (φ : β → α) (hφ : MonotoneOn φ t) {x y : β}
    (hx : x ∈ t) (hy : y ∈ t) :
    variationOnFromTo (f ∘ φ) t x y = variationOnFromTo f (φ '' t) (φ x) (φ y) := by
  rcases le_total x y with (h | h)
  ·
    rw [eq_of_le _ _ h, eq_of_le _ _ (hφ hx hy h),
      evariationOn.comp_inter_Icc_eq_of_monotoneOn f φ hφ hx hy]
  ·
    rw [eq_of_ge _ _ h, eq_of_ge _ _ (hφ hy hx h),
      evariationOn.comp_inter_Icc_eq_of_monotoneOn f φ hφ hy hx]
#align variation_on_from_to.comp_eq_of_monotone_on variationOnFromTo.comp_eq_of_monotoneOn

end variationOnFromTo

/-- If a real valued function has bounded variation on a set, then it is a difference of monotone
functions there. -/
theorem HasLocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn {f : α → ℝ} {s : Set α}
    (h : HasLocallyBoundedVariationOn f s) :
    ∃ p q : α → ℝ, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨c, cs⟩)
  ·
    exact
      ⟨f, 0, subsingleton_empty.monotone_on _, subsingleton_empty.monotone_on _, (sub_zero f).symm⟩
  ·
    exact
      ⟨_, _, variationOnFromTo.monotoneOn h cs, variationOnFromTo.sub_self_monotoneOn h cs,
        (sub_sub_cancel _ _).symm⟩
#align has_locally_bounded_variation_on.exists_monotone_on_sub_monotone_on HasLocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn

/-! ## Lipschitz functions and bounded variation -/


theorem LipschitzOnWith.comp_evariationOn_le {f : E → F} {C : ℝ≥0} {t : Set E}
    (h : LipschitzOnWith C f t) {g : α → E} {s : Set α} (hg : MapsTo g s t) :
    evariationOn (f ∘ g) s ≤ C * evariationOn g s := by
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    (∑ i in Finset.range n, edist (f (g (u (i + 1)))) (f (g (u i)))) ≤
        ∑ i in Finset.range n, C * edist (g (u (i + 1))) (g (u i)) :=
      Finset.sum_le_sum fun i hi => h (hg (us _)) (hg (us _))
    _ = C * ∑ i in Finset.range n, edist (g (u (i + 1))) (g (u i)) := by rw [Finset.mul_sum]
    _ ≤ C * evariationOn g s := mul_le_mul_left' (evariationOn.sum_le _ _ hu us) _
    
#align lipschitz_on_with.comp_evariation_on_le LipschitzOnWith.comp_evariationOn_le

theorem LipschitzOnWith.comp_hasBoundedVariationOn {f : E → F} {C : ℝ≥0} {t : Set E}
    (hf : LipschitzOnWith C f t) {g : α → E} {s : Set α} (hg : MapsTo g s t)
    (h : HasBoundedVariationOn g s) : HasBoundedVariationOn (f ∘ g) s :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top h) (hf.comp_evariationOn_le hg)
#align lipschitz_on_with.comp_has_bounded_variation_on LipschitzOnWith.comp_hasBoundedVariationOn

theorem LipschitzOnWith.comp_hasLocallyBoundedVariationOn {f : E → F} {C : ℝ≥0} {t : Set E}
    (hf : LipschitzOnWith C f t) {g : α → E} {s : Set α} (hg : MapsTo g s t)
    (h : HasLocallyBoundedVariationOn g s) : HasLocallyBoundedVariationOn (f ∘ g) s :=
  fun x y xs ys =>
  hf.comp_hasBoundedVariationOn (hg.mono_left (inter_subset_left _ _)) (h x y xs ys)
#align lipschitz_on_with.comp_has_locally_bounded_variation_on LipschitzOnWith.comp_hasLocallyBoundedVariationOn

theorem LipschitzWith.comp_hasBoundedVariationOn {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f)
    {g : α → E} {s : Set α} (h : HasBoundedVariationOn g s) : HasBoundedVariationOn (f ∘ g) s :=
  (hf.LipschitzOnWith univ).comp_hasBoundedVariationOn (mapsTo_univ _ _) h
#align lipschitz_with.comp_has_bounded_variation_on LipschitzWith.comp_hasBoundedVariationOn

theorem LipschitzWith.comp_hasLocallyBoundedVariationOn {f : E → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) {g : α → E} {s : Set α} (h : HasLocallyBoundedVariationOn g s) :
    HasLocallyBoundedVariationOn (f ∘ g) s :=
  (hf.LipschitzOnWith univ).comp_hasLocallyBoundedVariationOn (mapsTo_univ _ _) h
#align lipschitz_with.comp_has_locally_bounded_variation_on LipschitzWith.comp_hasLocallyBoundedVariationOn

theorem LipschitzOnWith.hasLocallyBoundedVariationOn {f : ℝ → E} {C : ℝ≥0} {s : Set ℝ}
    (hf : LipschitzOnWith C f s) : HasLocallyBoundedVariationOn f s :=
  hf.comp_hasLocallyBoundedVariationOn (mapsTo_id _)
    (@monotoneOn_id ℝ _ s).HasLocallyBoundedVariationOn
#align lipschitz_on_with.has_locally_bounded_variation_on LipschitzOnWith.hasLocallyBoundedVariationOn

theorem LipschitzWith.hasLocallyBoundedVariationOn {f : ℝ → E} {C : ℝ≥0} (hf : LipschitzWith C f)
    (s : Set ℝ) : HasLocallyBoundedVariationOn f s :=
  (hf.LipschitzOnWith s).HasLocallyBoundedVariationOn
#align lipschitz_with.has_locally_bounded_variation_on LipschitzWith.hasLocallyBoundedVariationOn

/-! ## Almost everywhere differentiability of functions with locally bounded variation -/


namespace HasLocallyBoundedVariationOn

/-- A bounded variation function into `ℝ` is differentiable almost everywhere. Superseded by
`ae_differentiable_within_at_of_mem`. -/
theorem ae_differentiableWithinAt_of_mem_real {f : ℝ → ℝ} {s : Set ℝ}
    (h : HasLocallyBoundedVariationOn f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  obtain ⟨p, q, hp, hq, fpq⟩ : ∃ p q, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q
  exact h.exists_monotone_on_sub_monotone_on
  filter_upwards [hp.ae_differentiable_within_at_of_mem, hq.ae_differentiable_within_at_of_mem] with
    x hxp hxq xs
  have fpq : ∀ x, f x = p x - q x := by simp [fpq]
  refine' ((hxp xs).sub (hxq xs)).congr (fun y hy => fpq y) (fpq x)
#align has_locally_bounded_variation_on.ae_differentiable_within_at_of_mem_real HasLocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem_real

/-- A bounded variation function into a finite dimensional product vector space is differentiable
almost everywhere. Superseded by `ae_differentiable_within_at_of_mem`. -/
theorem ae_differentiableWithinAt_of_mem_pi {ι : Type _} [Fintype ι] {f : ℝ → ι → ℝ} {s : Set ℝ}
    (h : HasLocallyBoundedVariationOn f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  have A : ∀ i : ι, LipschitzWith 1 fun x : ι → ℝ => x i := fun i => LipschitzWith.eval i
  have : ∀ i : ι, ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ (fun x : ℝ => f x i) s x := by
    intro i
    apply ae_differentiable_within_at_of_mem_real
    exact LipschitzWith.comp_hasLocallyBoundedVariationOn (A i) h
  filter_upwards [ae_all_iff.2 this] with x hx xs
  exact differentiableWithinAt_pi.2 fun i => hx i xs
#align has_locally_bounded_variation_on.ae_differentiable_within_at_of_mem_pi HasLocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem_pi

/-- A real function into a finite dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
theorem ae_differentiableWithinAt_of_mem {f : ℝ → V} {s : Set ℝ}
    (h : HasLocallyBoundedVariationOn f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  let A := (Basis.ofVectorSpace ℝ V).equivFun.toContinuousLinearEquiv
  suffices H : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ (A ∘ f) s x
  · filter_upwards [H] with x hx xs
    have : f = (A.symm ∘ A) ∘ f := by
      simp only [ContinuousLinearEquiv.symm_comp_self, Function.comp.left_id]
    rw [this]
    exact A.symm.differentiable_at.comp_differentiable_within_at x (hx xs)
  apply ae_differentiable_within_at_of_mem_pi
  exact A.lipschitz.comp_has_locally_bounded_variation_on h
#align has_locally_bounded_variation_on.ae_differentiable_within_at_of_mem HasLocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem

/-- A real function into a finite dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
theorem ae_differentiableWithinAt {f : ℝ → V} {s : Set ℝ} (h : HasLocallyBoundedVariationOn f s)
    (hs : MeasurableSet s) : ∀ᵐ x ∂volume.restrict s, DifferentiableWithinAt ℝ f s x := by
  rw [ae_restrict_iff' hs]
  exact h.ae_differentiable_within_at_of_mem
#align has_locally_bounded_variation_on.ae_differentiable_within_at HasLocallyBoundedVariationOn.ae_differentiableWithinAt

/-- A real function into a finite dimensional real vector space with bounded variation
is differentiable almost everywhere. -/
theorem ae_differentiableAt {f : ℝ → V} (h : HasLocallyBoundedVariationOn f univ) :
    ∀ᵐ x, DifferentiableAt ℝ f x := by
  filter_upwards [h.ae_differentiable_within_at_of_mem] with x hx
  rw [differentiableWithinAt_univ] at hx 
  exact hx (mem_univ _)
#align has_locally_bounded_variation_on.ae_differentiable_at HasLocallyBoundedVariationOn.ae_differentiableAt

end HasLocallyBoundedVariationOn

/-- A real function into a finite dimensional real vector space which is Lipschitz on a set
is differentiable almost everywhere in this set . -/
theorem LipschitzOnWith.ae_differentiableWithinAt_of_mem {C : ℝ≥0} {f : ℝ → V} {s : Set ℝ}
    (h : LipschitzOnWith C f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x :=
  h.HasLocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem
#align lipschitz_on_with.ae_differentiable_within_at_of_mem LipschitzOnWith.ae_differentiableWithinAt_of_mem

/-- A real function into a finite dimensional real vector space which is Lipschitz on a set
is differentiable almost everywhere in this set. -/
theorem LipschitzOnWith.ae_differentiableWithinAt {C : ℝ≥0} {f : ℝ → V} {s : Set ℝ}
    (h : LipschitzOnWith C f s) (hs : MeasurableSet s) :
    ∀ᵐ x ∂volume.restrict s, DifferentiableWithinAt ℝ f s x :=
  h.HasLocallyBoundedVariationOn.ae_differentiableWithinAt hs
#align lipschitz_on_with.ae_differentiable_within_at LipschitzOnWith.ae_differentiableWithinAt

/-- A real Lipschitz function into a finite dimensional real vector space is differentiable
almost everywhere. -/
theorem LipschitzWith.ae_differentiableAt {C : ℝ≥0} {f : ℝ → V} (h : LipschitzWith C f) :
    ∀ᵐ x, DifferentiableAt ℝ f x :=
  (h.HasLocallyBoundedVariationOn univ).ae_differentiableAt
#align lipschitz_with.ae_differentiable_at LipschitzWith.ae_differentiableAt

