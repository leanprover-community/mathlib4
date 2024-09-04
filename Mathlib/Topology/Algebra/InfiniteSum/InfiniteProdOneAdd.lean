
/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence

open Filter Function Complex

open scoped Interval Topology BigOperators Nat Classical UpperHalfPlane Complex


variable {α  ι: Type*}

lemma tendstouniformlyOn_le (f : ι → α → ℝ) {p : Filter ι} (g : α → ℝ) (K : Set α) (T : ℝ)
    (hf : TendstoUniformlyOn f g p K) (hg : ∀ x : α, x ∈ K → (g x) ≤ T) :
      ∃ B, ∀ᶠ (n : ι) in p, ∀ x, x ∈ K → f n x ≤ B := by
  rw [Metric.tendstoUniformlyOn_iff] at hf
  have hf2 := hf 1 (Real.zero_lt_one)
  use T + 1
  simp_rw [Filter.eventually_iff_exists_mem, dist_comm ] at *
  obtain ⟨N, hN, hN2⟩ := hf2
  refine ⟨N, hN, fun n hn x hx => ?_⟩
  apply le_trans (tsub_le_iff_right.mp (le_trans (Real.le_norm_self _) (hN2 n hn x hx).le))
  linarith [hg x hx]

lemma tendstouniformlyOn_iff_restrict {α β ι: Type*} [PseudoMetricSpace β]
    [Preorder ι] (f : ι → α → β) (g : α → β) (K : Set α) : TendstoUniformlyOn f g atTop K ↔
      TendstoUniformly (fun n : ι => K.restrict (f n)) (K.restrict g) atTop := by
  simp only [Metric.tendstoUniformlyOn_iff, gt_iff_lt, eventually_atTop, ge_iff_le, ←
    tendstoUniformlyOn_univ, Set.mem_univ, Set.restrict_apply, true_implies, Subtype.forall] at *

lemma tendstouniformlyOn_iff_shift {α β : Type*} [PseudoMetricSpace β]
    (f : ℕ → α → β) (g : α → β) (K : Set α) (d : ℕ) :
      TendstoUniformlyOn f g atTop K ↔ TendstoUniformlyOn
        (fun n => fun x => f (n + d) x) g atTop K := by
  simp_rw [Metric.tendstoUniformlyOn_iff, gt_iff_lt, eventually_atTop, ge_iff_le] at *
  apply forall₂_congr
  intro ε _
  constructor
  · exact fun h ↦
    Exists.casesOn h fun N hN ↦
      Exists.intro (N - d) fun n hn x hx ↦
        hN (n + d) (Eq.mp (congrArg (fun _a ↦ _a) (propext tsub_le_iff_right)) hn) x hx
  · intro h
    obtain ⟨N, hN⟩ := h
    refine ⟨N + d, fun n hn x hx => ?_⟩
    have : ∃ b' : ℕ, n = b' + d ∧ N ≤ b' := by
      rw [@le_iff_exists_add] at hn
      obtain ⟨c, hc⟩ := hn
      use N + c
      omega
    obtain ⟨b', hb', hb''⟩ := this
    rw [hb']
    apply hN b' hb'' x hx

lemma tendstoUniformlyOn_comp_exp {α : Type*} {f : ℕ → α → ℂ} {g : α → ℂ}
    (K : Set α) (hf : TendstoUniformlyOn f g atTop K) (hg : ∃ T : ℝ, ∀ x : α, x ∈ K → (g x).re ≤ T):
        TendstoUniformlyOn (fun n => fun x => cexp (f n x)) (cexp ∘ g) atTop K := by
  obtain ⟨T, hT⟩ := hg
  have h2 :=  tendstouniformlyOn_le (fun n x => (f n x).re) (fun x => (g x).re) K T
    hf.re hT
  simp only [eventually_atTop, ge_iff_le] at h2
  obtain ⟨B, δ, hδ⟩ := h2
  have w2 := tendstoUniformlyOn_univ.mpr <| UniformContinuousOn.comp_tendstoUniformly
    {x : ℂ | x.re ≤ max B T} (fun a => K.restrict (f (a + δ))) (fun b => g b) ?_ ?_
      (UniformlyContinuousOn.cexp (max B T)) (p := atTop) ?_
  rw [tendstouniformlyOn_iff_restrict, ← tendstoUniformlyOn_univ, tendstouniformlyOn_iff_shift]
  exact w2
  · intro n k
    simp only [le_add_iff_nonneg_left, zero_le, true_implies, le_max_iff, Set.mem_setOf_eq]
    left
    apply (hδ (n + δ) (Nat.le_add_left δ n) k k.2)
  · intro x
    simp only [le_max_iff, Set.mem_setOf_eq]
    right
    apply le_trans (hT x x.2) (by rfl)
  · simp only [Metric.tendstoUniformlyOn_iff, gt_iff_lt, eventually_atTop, ge_iff_le, Set.coe_setOf,
        Set.mem_setOf_eq, Metric.tendstoUniformly_iff, Subtype.forall] at *
    intro ε hε
    obtain ⟨N2, hN2⟩ := hf ε hε
    refine ⟨(max N2 δ) - δ, fun n hn x hx => ?_ ⟩
    rw [@Nat.sub_le_iff_le_add] at hn
    apply hN2 (n + δ) (le_trans (Nat.le_max_left N2 δ) hn) x hx

lemma prod_tendstoUniformlyOn_tprod {α : Type*} {f : ℕ → α → ℂ} (K : Set α)
    (h : ∀ x : K, Summable fun n => log (f n x))
    (hf : TendstoUniformlyOn (fun n : ℕ => fun a : α => ∑ i in Finset.range n, log (f i a))
      (fun a : α => ∑' n : ℕ, log (f n a)) atTop K)
    (hfn : ∀ x : K, ∀ n : ℕ, f n x ≠ 0)
    (hg : ∃ T : ℝ, ∀ x : α, x ∈ K → (∑' n : ℕ, log (f n x)).re ≤ T) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i in Finset.range n, (f i a))
      (fun a => ∏' i, (f i a)) atTop K := by
  have := TendstoUniformlyOn.congr (tendstoUniformlyOn_comp_exp K hf hg)
    (F':= (fun n : ℕ => fun a : α => ∏ i in Finset.range n, (f i a)))
  have HU : TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i in Finset.range n, (f i a))
       (cexp ∘ fun a ↦ ∑' (n : ℕ), log (f n a)) atTop K := by
      apply this
      simp only [eventually_atTop, ge_iff_le]
      refine ⟨0, fun b _ x hx => ?_⟩
      simp only [exp_sum]
      congr
      ext y
      apply Complex.exp_log (hfn ⟨x, hx⟩ y)
  apply TendstoUniformlyOn.congr_right HU
  intro x hx
  exact congrFun (Complex.cexp_tsum_eq_tprod (fun n => fun x : K => f n x) hfn h) ⟨x, hx⟩

open Real

lemma Complex.log_of_summable {f : ℕ → ℂ} (hf : Summable f) :
    Summable (fun n : ℕ => Complex.log (1 + f n)) := by
  have hff := Summable.const_smul ((3 : ℝ) / 2) (summable_norm_iff.mpr hf)
  have := Metric.tendsto_atTop.mp (Summable.tendsto_atTop_zero ((summable_norm_iff.mpr hf)))
  apply Summable.of_norm_bounded_eventually_nat (fun n => (3/2) * Complex.abs (f n)) hff
  simp only [smul_eq_mul, gt_iff_lt, ge_iff_le, dist_zero_right, Real.norm_eq_abs, Complex.abs_abs,
    Complex.norm_eq_abs, eventually_atTop] at *
  obtain ⟨n, hn⟩ := this (1/2) (one_half_pos)
  exact Exists.intro n fun m hm ↦ norm_log_one_add_half_le_self (LT.lt.le (hn m hm))

lemma Real.log_of_summable {f : ℕ → ℝ} (hf : Summable f) :
    Summable (fun n : ℕ => Real.log (1 + |f n|)) := by
  apply Summable.of_norm_bounded_eventually_nat (fun n => |(f n)|)
    (by apply summable_norm_iff.mpr hf)
  simp only [gt_iff_lt, ge_iff_le, norm_eq_abs, dist_zero_right, _root_.abs_abs,
    eventually_atTop]
  obtain ⟨n, _⟩ := Metric.tendsto_atTop.mp
    (Summable.tendsto_atTop_zero ((summable_norm_iff.mpr hf))) (1/2) (one_half_pos)
  use n
  intro m _
  have ht : 0  < 1 + |f m| := by
    rw [add_comm]
    apply add_pos_of_nonneg_of_pos (abs_nonneg _)  Real.zero_lt_one
  have := Real.log_le_sub_one_of_pos ht
  simp only [add_sub_cancel_left] at this
  apply le_trans _ this
  have habs : |Real.log (1 + |f m|)| = Real.log (1 + |f m|) := by
    rw [abs_eq_self]
    apply Real.log_nonneg
    simp only [le_add_iff_nonneg_right, abs_nonneg]
  rw [habs]

lemma Complex.summable_multipliable_one_add (f : ℕ → ℂ) (hf : Summable f)
    (hff : ∀ n : ℕ, 1 + f n  ≠ 0) : Multipliable (fun n : ℕ => (1 + f n)) := by
  have := log_of_summable hf
  rw [Summable] at this
  simp_rw [HasSum] at this
  obtain ⟨a, ha⟩ := this
  have := Filter.Tendsto.cexp ha
  have h1 : (fun n : Finset ℕ ↦ cexp (∑ x ∈ n, Complex.log (1 + f x))) =
     (fun n : Finset ℕ ↦ (∏ x ∈ n,  (1 + f x))) := by
    ext y
    rw [Complex.exp_sum]
    congr
    ext r
    rw [Complex.exp_log]
    apply hff r
  rw [h1] at this
  refine ⟨exp a, this⟩

lemma Real.summable_multipliable_one_add (f : ℕ → ℝ) (hf : Summable f) :
    Multipliable (fun n : ℕ => (1 + |f n|)) := by
  have := log_of_summable hf
  rw [Summable] at this
  simp_rw [HasSum] at this
  obtain ⟨a, ha⟩ := this
  have := Filter.Tendsto.rexp ha
  have h1 : (fun n : Finset ℕ ↦ rexp (∑ x ∈ n, Real.log (1 + |f x|))) =
     (fun n : Finset ℕ ↦ (∏ x ∈ n, (1 + |f x|))) := by
    ext y
    rw [Real.exp_sum]
    congr
    ext r
    rw [Real.exp_log]
    apply add_pos_of_pos_of_nonneg
    exact Real.zero_lt_one
    apply abs_nonneg
  rw [h1] at this
  refine ⟨exp a, this⟩


theorem Complex.closedEmbedding_coe_complex : ClosedEmbedding ((↑) : ℤ → ℂ) := by
  apply Metric.closedEmbedding_of_pairwise_le_dist zero_lt_one
  convert Int.pairwise_one_le_dist
  simp_rw [dist_eq_norm]
  norm_cast
  rw [Int.norm_eq_abs]
  exact norm_int

lemma int_img_closed : IsClosed (((↑) : ℤ → ℂ)'' ⊤) := by
  simp only [Set.top_eq_univ, Set.image_univ]
  exact Complex.closedEmbedding_coe_complex.isClosed_range

lemma ints_comp_IsOpen : IsOpen {z : ℂ | ¬ ∃ (n : ℤ), z = ↑n} := by
  refine IsClosed.not ?_
  convert int_img_closed
  ext y
  aesop

local notation "ℂ_ℤ" =>  {z : ℂ // ¬ ∃ (n : ℤ), z = n}

noncomputable instance : UniformSpace ℂ_ℤ := by infer_instance

instance : LocallyCompactSpace ℂ_ℤ := IsOpen.locallyCompactSpace ints_comp_IsOpen

lemma upper_half_plane_ne_int (z : ℍ) : ∀ n : ℤ, z.1 ≠ n := by
  intro n
  have h1 := z.2
  aesop

lemma upper_half_plane_ne_int_pow_two (z : ℍ) (n : ℤ) : (z : ℂ) ^ 2 - n ^ 2 ≠ 0 := by
  intro h
  rw [sq_sub_sq, mul_eq_zero] at h
  cases h with
  | inr h =>
    have := upper_half_plane_ne_int z n
    rw [sub_eq_zero] at h
    apply absurd h this
  | inl h =>
    have := upper_half_plane_ne_int z (-n)
    rw [add_eq_zero_iff_eq_neg] at h
    simp only [ Int.cast_neg, ne_eq] at *
    apply absurd h this

instance : Coe ℍ ℂ_ℤ := ⟨fun x => ⟨x, by simpa using upper_half_plane_ne_int x⟩⟩

lemma int_comp_add_ne_zero (x : ℂ_ℤ) (a : ℤ) : x.1 + a ≠ 0 := by
  intro h
  rw [add_eq_zero_iff_eq_neg] at h
  have := not_exists.mp x.2 (-a)
  aesop

lemma int_comp_not_zero (x : ℂ_ℤ) : x.1 ≠ 0 := by
  simpa using int_comp_add_ne_zero x 0

lemma int_comp_not_zero2 (x : ℂ_ℤ) (n : ℕ) : 1 + -x.1 ^ 2 / (n + 1) ^ 2 ≠ 0 := by
  intro h
  rw [add_eq_zero_iff_eq_neg, neg_div', eq_div_iff] at h
  simp only [one_mul, neg_neg, sq_eq_sq_iff_eq_or_eq_neg] at h
  rcases h with h1| h2
  · have := not_exists.mp x.2 (n+1)
    simp  [Int.cast_add, Int.cast_natCast, Int.cast_one, not_true_eq_false] at this
    exact this (id (Eq.symm h1))
  · have := not_exists.mp x.2 (-(n+1))
    rw [← neg_eq_iff_eq_neg ] at h2
    rw [← h2] at this
    simp only [neg_add_rev, Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one,
      Int.cast_natCast, not_true_eq_false] at *
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    exact Nat.cast_add_one_ne_zero n

theorem summable_pow_shift {α : Type*} (x : α) [RCLike α] (p q k : ℕ) (hq : 1 < q) :
    Summable fun n : ℕ => ‖(x ^ p / (↑n + k) ^ q)‖ := by
  simp_rw [div_eq_mul_inv, norm_mul]
  apply Summable.mul_left
  simp_rw [inv_eq_one_div]
  have := summable_nat_add_iff (f := fun x => ‖1/ (x^q : α)‖) k
  simp only [hq, Nat.cast_add, one_div, norm_inv, norm_pow, Complex.norm_eq_abs,
    RCLike.norm_natCast, summable_nat_pow_inv, iff_true] at *
  apply this


theorem tendsto_euler_sin_prod' (x : ℂ) (h0 : x ≠ 0) :
    Tendsto (fun n : ℕ => ∏ i : ℕ in Finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2)) atTop
      (𝓝 ((fun t : ℂ => sin (↑π * t) / (↑π * t)) x)) := by
  rw [show ((fun t : ℂ => sin (↑π * t) / (↑π * t)) x) = sin (↑π * x) * (1 / (↑π * x)) by ring]
  apply (Filter.Tendsto.mul_const (b := 1/(π * x)) (tendsto_euler_sin_prod x)).congr
  intro n
  have : (1 / (↑π * x)) * (↑π * x) = 1 := by
    apply div_mul_cancel₀
    have := Real.pi_ne_zero
    aesop
  rw [mul_comm, ← mul_assoc, this, one_mul]
  congr
  ext y
  ring

lemma euler_sin_tprod (x : ℂ_ℤ) :
    ∏' i : ℕ, (1 + -x.1 ^ 2 / (i + 1) ^ 2) = Complex.sin (π * x) / (π * x) := by
  rw [← Multipliable.hasProd_iff, Multipliable.hasProd_iff_tendsto_nat]
  apply tendsto_euler_sin_prod' x (int_comp_not_zero x)
  repeat {
  apply Complex.summable_multipliable_one_add
  · rw [← summable_norm_iff]
    simpa using summable_pow_shift x.1 2 2 1
  · apply int_comp_not_zero2 x}


variable {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : ℕ → ℝ}
open Metric

theorem tendstoUniformlyOn_tsum_eventually {f : ℕ → β → F} (hu : Summable u) {s : Set β}
    (hfu : ∃ a, ∀ (b : Finset ℕ), a ⊆ b → ∀ x, x ∈ s → ∀ n, n ∉ b → ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun t : Finset ℕ => fun x => ∑ n ∈ t, f n x)
      (fun x => ∑' n, f n x) atTop s := by
  refine tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  have := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero u)).2 _ εpos
  simp at *
  obtain ⟨t, ht⟩ := this
  obtain ⟨N, hN⟩ := hfu
  use N ∪ t
  intro n hn x hx
  have A : Summable fun n => ‖f n x‖ := by ---Summable.of_norm_bounded_eventually
    apply Summable.add_compl (s := N)
    exact Summable.of_finite
    apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ (hu.subtype _)
    simp
    apply hN N (by simp) x hx
  rw [dist_eq_norm, ← sum_add_tsum_subtype_compl A.of_norm (n), add_sub_cancel_left]
  have hN2 := hN (n) (by exact Finset.union_subset_left hn) x hx
  have ht2 := ht (n) (by exact Finset.union_subset_right hn)
  apply lt_of_le_of_lt _ ht2
  apply (norm_tsum_le_tsum_norm ?_).trans
  · apply tsum_le_tsum
    · intro i
      apply hN2
      apply i.2
    · apply (A.subtype _)
    · apply (hu.subtype _)
  · apply (A.subtype _)


/- theorem tendstoUniformlyOn_tsum_nat2 {f : ℕ → ℂ → ℂ} {u : ℕ → ℝ} (hu : Summable u) {s : Set ℂ}
    (hfu : ∃ N : ℕ,  ∀ n : ℕ, N ≤ n → ∀ x, x ∈ s → ‖f n x‖ ≤ u n) :
   TendstoUniformlyOn (fun N => fun x => ∑ n ∈ Finset.range N, f n x) (fun x => ∑' n, f n x) atTop
      s:= by
      intro v hv
      apply tendsto_finset_range.eventually (tendstoUniformlyOn_tsum_eventually hu ?_ v hv)
      obtain ⟨N, hN⟩ := hfu
      use Finset.range N
      intro b hb x hx n hn
      apply hN n _ x hx
      by_contra h
      simp only [not_le] at h
      rw [← @Finset.mem_range] at h
      exact hn (hb h ) -/

theorem tendstoUniformlyOn_tsum_nat2alph {α : Type*} {f : ℕ → α → ℂ} {u : ℕ → ℝ}
    (hu : Summable u) {s : Set α} (hfu : ∃ N : ℕ,  ∀ n : ℕ, N ≤ n → ∀ x, x ∈ s → ‖f n x‖ ≤ u n) :
      TendstoUniformlyOn (fun N => fun x => ∑ n ∈ Finset.range N, f n x)
        (fun x => ∑' n, f n x) atTop s:= by
  intro v hv
  apply tendsto_finset_range.eventually (tendstoUniformlyOn_tsum_eventually hu ?_ v hv)
  obtain ⟨N, hN⟩ := hfu
  use Finset.range N
  intro b hb x hx n hn
  apply hN n _ x hx
  by_contra h
  simp only [not_le] at h
  rw [← @Finset.mem_range] at h
  exact hn (hb h )

theorem tendstoUniformlyOn_tsum_nat2alph_real {α : Type*} {f : ℕ → α → ℝ} {u : ℕ → ℝ}
    (hu : Summable u) {s : Set α} (hfu : ∃ N : ℕ,  ∀ n : ℕ, N ≤ n → ∀ x, x ∈ s → ‖f n x‖ ≤ u n) :
      TendstoUniformlyOn (fun N => fun x => ∑ n ∈ Finset.range N, f n x)
          (fun x ↦ ∑' n, f n x) atTop s:= by
  intro v hv
  apply tendsto_finset_range.eventually (tendstoUniformlyOn_tsum_eventually hu ?_ v hv)
  obtain ⟨N, hN⟩ := hfu
  use Finset.range N
  intro b hb x hx n hn
  apply hN n _ x hx
  by_contra h
  simp only [not_le] at h
  rw [← @Finset.mem_range] at h
  exact hn (hb h )


lemma tendstoUniformlyOn_tsum_log_one_add {α : Type*} (f : ℕ → α → ℂ) (K : Set α) (u : ℕ → ℝ)
    (hu : Summable u) (h : ∀ n x, x ∈ K → (‖(f n x)‖) ≤ u n) :
      TendstoUniformlyOn (fun n : ℕ => fun a : α => ∑ i in Finset.range n,
        (Complex.log (1 + f i a))) (fun a => ∑' i : ℕ, Complex.log (1 + f i a)) atTop K := by
  --apply tendstoUniformlyOn_tsum_nat (u := u) hu
  apply tendstoUniformlyOn_tsum_nat2alph (hu.mul_left (3/2))
  have := Summable.tendsto_atTop_zero hu
  rw [Metric.tendsto_atTop] at this
  obtain ⟨N, hN⟩ := this (1/2) (one_half_pos)
  use N
  intro n hn x hx
  simp
  have := (Complex.norm_log_one_add_half_le_self  (z :=(f n x)) ?_)
  apply le_trans this
  simp
  apply h
  apply hx
  apply le_trans _ (hN n hn).le
  simp at h
  apply le_trans (h n x hx)
  simp only [dist_zero_right, Real.norm_eq_abs]
  exact le_norm_self (u n)


lemma tendstoUniformlyOn_tsum_log_one_add_re {α : Type*} (f : ℕ → α → ℂ) (K : Set α) (u : ℕ → ℝ)
    (hu : Summable u) (h : ∀ n x, x ∈ K → (‖(f n x)‖) ≤ u n) :
   TendstoUniformlyOn (fun n : ℕ => fun a : α =>
  ∑ i in Finset.range n, Real.log (Complex.abs (1 + f i a)))
    (fun a => ∑' i : ℕ, Real.log (Complex.abs (1 + f i a))) atTop K := by
  apply tendstoUniformlyOn_tsum_nat2alph_real (hu.mul_left (3/2))
  have := Summable.tendsto_atTop_zero hu
  rw [Metric.tendsto_atTop] at this
  obtain ⟨N, hN⟩ := this (1/2) (one_half_pos)
  use N
  intro n hn x hx
  simp
  have := (Complex.norm_log_one_add_half_le_self (z := (f n x)) ?_)
  rw [← log_re]
  simp
  apply le_trans (abs_re_le_abs _)
  apply le_trans this
  simp
  apply h
  apply hx
  apply le_trans _ (hN n hn).le
  simp at h
  apply le_trans (h n x hx)
  simp
  exact le_norm_self (u n)


lemma unif_lem (Z : Set ℂ_ℤ) (hZ : IsCompact Z) :
    TendstoUniformlyOn (fun (n : ℕ) (a : ℂ_ℤ) ↦
      ∑ i ∈ Finset.range n, Complex.log (1 + -a.1 ^ 2 / (↑i + 1) ^ 2))
        (fun a ↦ ∑' (n : ℕ), Complex.log (1 + -↑a ^ 2 / (↑n + 1) ^ 2)) atTop Z := by
  have hf : ContinuousOn (fun x : ℂ_ℤ => ( Complex.abs (-x.1 ^ 2)) ) Z := by
    apply ContinuousOn.comp
    let g := fun x : ℂ_ℤ =>-x.1 ^ 2
    apply Continuous.continuousOn Complex.continuous_abs  (s := ((g '' Z)))
    apply (ContinuousOn.neg (ContinuousOn.pow (Continuous.continuousOn continuous_subtype_val) 2))
    exact Set.mapsTo_image (fun x ↦ -x.1 ^ 2) Z
  have := IsCompact.bddAbove_image  hZ hf
  rw [@bddAbove_def] at this
  simp at *
  obtain ⟨s, hs⟩ := this
  apply tendstoUniformlyOn_tsum_log_one_add (u := (fun n : ℕ => Complex.abs (s / (n + 1) ^ 2)))
  have := summable_pow_shift (s : ℂ) 1 2 1 (by omega)
  simp at *
  exact this
  intro n x hx
  simp
  gcongr
  apply le_trans _ (le_abs_self s)
  apply hs
  apply hx
  rfl
  aesop


 lemma unif_lem_re (Z : Set ℂ_ℤ) (hZ : IsCompact Z) :
   TendstoUniformlyOn (fun (n : ℕ) (a : ℂ_ℤ) ↦
    (∑ i ∈ Finset.range n, Real.log (Complex.abs (1 + -a.1 ^ 2 / (i + 1) ^ 2))))
      (fun a ↦ (∑' (n : ℕ), Real.log  (Complex.abs (1 + -a ^ 2 / (n + 1) ^ 2)))) atTop Z:= by
  have hf : ContinuousOn (fun x : ℂ_ℤ => ( Complex.abs (-x.1 ^ 2)) ) Z := by
    apply ContinuousOn.comp
    let g := fun x : ℂ_ℤ => -x.1 ^ 2
    apply Continuous.continuousOn Complex.continuous_abs  (s := ((g '' Z)))
    apply (ContinuousOn.neg (ContinuousOn.pow (Continuous.continuousOn continuous_subtype_val) 2))
    exact Set.mapsTo_image (fun x ↦ -x.1 ^ 2) Z
  have := IsCompact.bddAbove_image  hZ hf
  rw [@bddAbove_def] at this
  simp at *
  obtain ⟨s, hs⟩ := this
  apply tendstoUniformlyOn_tsum_log_one_add_re (u := (fun n : ℕ => Complex.abs (s / (n + 1) ^ 2)))
  have := summable_pow_shift (s : ℂ) 1 2 1 (by omega)
  simp at *
  exact this
  intro n x hx
  simp
  gcongr
  apply le_trans _ (le_abs_self s)
  apply hs
  apply hx
  rfl
  aesop


theorem tendstoUniformlyOn_compact_euler_sin_prod (Z : Set ℂ_ℤ) (hZ : IsCompact Z) :
    TendstoUniformlyOn
      (fun n : ℕ => fun z : ℂ_ℤ => ∏ j in Finset.range n, (1 + -z.1 ^ 2 / (j + 1) ^ 2))
        (fun x => (Complex.sin (↑π * x) / (↑π * x))) atTop Z := by
  conv =>
    enter [2]
    ext x
    rw [← euler_sin_tprod ]
  apply prod_tendstoUniformlyOn_tprod
  intro x
  apply Complex.log_of_summable
  rw [← summable_norm_iff]
  simpa using summable_pow_shift x.1.1 2 2 1
  apply unif_lem Z hZ
  intro x n
  apply int_comp_not_zero2 x
  have hf : ContinuousOn (fun x : ℂ_ℤ =>
      (∑' n : ℕ, Complex.log (1 + -x ^ 2 / (n + 1) ^ 2)).re ) Z := by
    have hcon :=  (unif_lem_re Z hZ).continuousOn
    have : (fun x : ℂ_ℤ => (∑' n : ℕ, Complex.log (1+-x ^ 2 / (n + 1) ^ 2)).re ) =
      (fun x : ℂ_ℤ => (∑' n : ℕ, (Complex.log (1+-x ^ 2 / (n + 1) ^ 2)).re)) := by
        ext x
        rw [Complex.re_tsum ]
        apply Complex.log_of_summable
        rw [← summable_norm_iff]
        simpa using summable_pow_shift x.1 2 2 1
    rw [this]
    conv =>
      enter [1]
      ext y
      conv =>
        enter [1]
        ext n
        rw [log_re]
    apply hcon
    simp
    use 1
    intro b _
    apply continuousOn_finset_sum
    intro c _
    apply ContinuousOn.log
    apply ContinuousOn.comp
    let g := fun x : ℂ_ℤ => 1+-x.1 ^ 2 / (c + 1) ^ 2
    apply Continuous.continuousOn Complex.continuous_abs  (s := ((g '' Z)))
    apply (ContinuousOn.add continuousOn_const
    (ContinuousOn.mul
      (ContinuousOn.neg (ContinuousOn.pow (Continuous.continuousOn continuous_subtype_val) 2))
      continuousOn_const))
    exact Set.mapsTo_image (fun x ↦ 1 + -x.1 ^ 2 / ((c : ℂ) + 1) ^ 2) Z
    intro z _
    simp only [ne_eq, map_eq_zero]
    apply int_comp_not_zero2 z
  have := IsCompact.bddAbove_image  hZ hf
  rw [@bddAbove_def] at this
  simp at *
  obtain ⟨T, hT⟩ := this
  use T
  intro x hx hxint
  apply hT
  apply hxint
  rfl
  aesop


open Finset


theorem sin_pi_z_ne_zero (z : ℂ_ℤ) : Complex.sin (π * z) ≠ 0 :=
  by
  apply Complex.sin_ne_zero_iff.2
  intro k
  rw [mul_comm]
  by_contra h
  simp at h
  cases' h with h h
  aesop
  have := Real.pi_ne_zero
  exact this h

theorem prod_diff_on' (n : ℕ) :
    DifferentiableOn ℂ (fun z : ℂ => ∏ j in Finset.range n, (1 + -z ^ 2 / (j + 1) ^ 2))
      {z : ℂ | ¬ ∃ (n : ℤ), z = n} :=
  by
  apply DifferentiableOn.finset_prod
  intro i _
  exact
    DifferentiableOn.add (differentiableOn_const 1)
      (DifferentiableOn.div_const
        (DifferentiableOn.neg
          (DifferentiableOn.pow (Differentiable.differentiableOn differentiable_id) 2))
        (((i : ℂ) + 1) ^ 2))



theorem tendsto_euler_log_derv_sin_prodde (x : ℂ_ℤ) :
    Tendsto
      (fun n : ℕ =>
        logDeriv (fun z =>  ∏ j in Finset.range n, (1 + -(z : ℂ) ^ 2 / (j + 1) ^ 2)) x)
      atTop (𝓝 <| logDeriv (fun t => (Complex.sin (π * t)/ (π * t))) x) := by
  have :=
    logDeriv_tendsto
      (fun n : ℕ => fun z => ∏ j in Finset.range n, (1 + -z ^ 2 / (j + 1) ^ 2))
      ((Complex.sin ∘ fun t => π * t)/(fun (t : ℂ) => π * t)) ints_comp_IsOpen x (p := atTop)
  apply this
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact]
  intro K hK hK2
  let Z : Set ℂ_ℤ :=  (Set.inclusion hK)'' ⊤
  have hZ : IsCompact Z := by
    apply IsCompact.image
    exact isCompact_iff_isCompact_univ.mp hK2
    exact continuous_inclusion hK
  have := tendstoUniformlyOn_compact_euler_sin_prod Z hZ
  simp_rw [Z] at this
  rw [Metric.tendstoUniformlyOn_iff] at *
  simp only [not_exists, eventually_atTop, ge_iff_le, Set.mem_setOf_eq, comp_apply, ne_eq,
    forall_exists_index, Set.coe_setOf, gt_iff_lt, Set.top_eq_univ, Set.image_univ,
    Set.range_inclusion, Subtype.forall] at *
  intro ε hε
  obtain ⟨N, hN⟩ := this ε hε
  refine ⟨N, ?_⟩
  intro n hn y hy
  simp
  have := hN n hn y ?_ hy
  exact this
  have := (hK hy)
  simpa using this
  exact ints_comp_IsOpen
  simp
  use 1
  intro b _
  have := prod_diff_on' b
  simpa using this
  simp
  refine ⟨sin_pi_z_ne_zero x , Real.pi_ne_zero ,int_comp_not_zero x⟩

theorem logDeriv_sin_div (z : ℂ_ℤ) :
    logDeriv (fun t => (Complex.sin (π * t) / (π * t))) z =  π * cot (π * z) - 1/z := by
  have : (fun t => (Complex.sin (π * t)/ (π * t))) = fun z =>
    (Complex.sin ∘ fun t => π * t) z / (π * z) := by
    ext1
    simp only [Pi.div_apply, comp_apply]
  rw [this, logDeriv_div _ (by apply sin_pi_z_ne_zero) ?_
    (DifferentiableAt.comp _ (Complex.differentiableAt_sin) (by fun_prop)) (by fun_prop),
    logDeriv_comp (Complex.differentiableAt_sin) (by fun_prop), Complex.logDeriv_sin,
    deriv_const_mul _ (by fun_prop), deriv_id'', logDeriv_const_mul, logDeriv_id']
  field_simp [mul_comm]
  · simpa only [ne_eq, ofReal_eq_zero] using Real.pi_ne_zero
  · simp only [Set.mem_setOf_eq, ne_eq, mul_eq_zero, ofReal_eq_zero, not_or]
    refine ⟨Real.pi_ne_zero, int_comp_not_zero _⟩


lemma logDeriv_of_prod (x : ℂ_ℤ) (n : ℕ) :
    logDeriv (fun (z : ℂ) =>  ∏ j in Finset.range n, (1 + -z ^ 2 / (j + 1) ^ 2)) x =
     ∑ j in Finset.range n, (1 / ((x : ℂ) - (j + 1)) + 1 / (x + (j + 1))) := by
    rw [logDeriv_prod]
    congr
    ext1 i
    simp only [Set.mem_setOf_eq, logDeriv_apply, differentiableAt_const, deriv_const_add',
      deriv_div_const, deriv.neg', differentiableAt_id', deriv_pow'', Nat.cast_ofNat,
      Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, one_div]
    simp_rw [div_eq_mul_inv]
    set i1 := ((x : ℂ) + (i+1))⁻¹
    set i2 := ((x : ℂ) - (i+1))⁻¹
    set i3 := ((i+1 : ℂ)^2)⁻¹
    set i4 := (1+ -x^2*i3)⁻¹
    have h1  : ((x : ℂ) + (i+1))* i1 = 1 := by
      refine Complex.mul_inv_cancel ?h
      simpa using int_comp_add_ne_zero x (i+1)
    have h2 : ((x : ℂ) - (i+1)) * i2 = 1 := by
      apply Complex.mul_inv_cancel
      rw [sub_eq_add_neg]
      simpa using int_comp_add_ne_zero x (-(i+1))
    have h3 : ((i+1 : ℂ)^2) * i3 = 1 := by
      apply Complex.mul_inv_cancel
      norm_cast
      exact Nat.add_one_ne_zero ((((i + 1).pow 1).mul i).add (((i + 1).pow 0).mul i))
    have h4 : (1+ -x^2 * i3) * i4 = 1 := by
      apply Complex.mul_inv_cancel (int_comp_not_zero2 x i)
    clear_value i1 i2 i3 i4
    linear_combination
      (2 * i4 * i2 * i1 * ↑i + 2 * i4 * i2 * i1 + 2 * i4 * i1) * h3 +
            (2 * i2 * i1 * ↑i + 2 * i2 * i1 + 2 * i1) * h4 +
          (2 * i3 * i4 * ↑i + 2 * i3 * i4 - 1 * i1) * h2 +
        (2 * ↑x * i3 * i4 * i2 * ↑i - 2 * i3 * i4 * i2 * ↑i ^ 2 + 2 * ↑x * i3 * i4 * i2 -
                      4 * i3 * i4 * i2 * ↑i +
                    2 * ↑x * i3 * i4 -
                  2 * i3 * i4 * i2 -
                2 * i3 * i4 * ↑i -
              2 * i3 * i4 +
            i2) *
          h1
    · exact fun i _ ↦ int_comp_not_zero2 x i
    · intro i _
      simp only [Set.mem_setOf_eq, differentiableAt_const, differentiableAt_const_add_iff,
        differentiableAt_neg_iff, differentiableAt_id', DifferentiableAt.pow,
        DifferentiableAt.div_const]


theorem tendsto_euler_log_derv_sin_prodd' (x : ℂ_ℤ) :
    Tendsto
      (fun n : ℕ =>  ∑ j in Finset.range n, (1 / ((x : ℂ) - (j + 1)) + 1 / (x + (j + 1))))
      atTop (𝓝 <| π * cot (π * x)- 1 / x) :=
  by
  have := tendsto_euler_log_derv_sin_prodde x
  have h1 := logDeriv_of_prod x
  have h2 := logDeriv_sin_div x
  rw [← h2]
  simp_rw [← h1]
  simp at *
  exact this

lemma nat_inv_sub_squares (z : ℂ_ℤ) :
  (fun n : ℕ => 1 / ((z : ℂ) - (n+1)) + 1 / (z + (n+1))) =
    fun n : ℕ => 2 * z.1 * (1 / (z ^ 2 - (n + 1) ^ 2)):= by
  funext n
  field_simp
  rw [one_div_add_one_div]
  ring
  rw [sub_eq_add_neg]
  simpa using int_comp_add_ne_zero z (-(n + 1) : ℤ)
  have := int_comp_add_ne_zero z ((n : ℤ)+1)
  simpa using this

lemma tendsto_const_div_pow (r : ℝ) (k : ℕ) (hk : k ≠ 0) :
    Tendsto (fun n : ℕ => r / n^k) atTop (𝓝 0) := by
  have h := Filter.Tendsto.const_mul r (l := atTop) (f := fun (n : ℕ ) => 1 / n^k) (c := 0) ?_
  simp only [one_div, mul_zero] at *
  apply h.congr
  intro y
  ring
  simp only [one_div]
  apply tendsto_inv_atTop_zero.comp
  have ha := Filter.tendsto_pow_atTop hk (α := ℕ)
  have hb := tendsto_natCast_atTop_atTop (R := ℝ)
  apply (hb.comp ha).congr
  simp only [Nat.reduceAdd, comp_apply, Nat.cast_pow, implies_true]


lemma half_le (a : ℝ) (ha : a < 1/2) : 1 / 2 ≤  |a - 1| := by
  rw [← neg_lt_neg_iff] at ha
  have hb := (Real.add_lt_add_iff_left 1).mpr ha
  rw [abs_sub_comm]
  have : (1 : ℝ) + -(1/2) = 1/2 := by
    ring
  rw [this, Mathlib.Tactic.RingNF.add_neg] at hb
  have : |1 -a| = 1 - a := by
    rw [abs_eq_self]
    linarith
  rw [this]
  apply hb.le


theorem lhs_summable_re (z : ℂ_ℤ) (hz : z.1.im = 0) : Summable fun n : ℕ => 1 / ((z : ℂ) - (n+1)) +
    1 / (z + (n+1)) := by
  have h1 := nat_inv_sub_squares z
  rw [h1]
  apply Summable.mul_left
  apply summable_norm_iff.1
  simp
  have : z.1 = (z.1.re : ℂ) := by
    rw [@Complex.ext_iff]
    simp [hz]
  rw [this]
  have : (fun x : ℕ ↦ (Complex.abs (↑(z.1).re ^ 2 - (↑x + 1) ^ 2))⁻¹) =
    (fun x : ℕ => |z.1.re ^ 2 - (x + 1) ^ 2|⁻¹) := by
    ext y
    congr
    norm_cast
  rw [this]
  set Z := z.1.re
  have := Filter.Tendsto.sub_const (tendsto_const_div_pow (Z^2) 2 (by omega)) 1
  simp at this
  rw [Metric.tendsto_atTop] at this
  simp at this
  obtain ⟨B, hB⟩ := this (1/2) (one_half_pos)
  have hB2 : ∀ (n : ℕ), B ≤ n → 1/2 ≤ |Z^2/ n^2 -1| := by
    intro n hn
    have hB3 := hB n hn
    apply half_le
    exact hB3
  apply Summable.comp_nat_add (k := B)
  have hs : Summable fun n : ℕ => (1/(2 : ℝ) * (n+B+1) ^ 2)⁻¹ := by
    simp
    apply Summable.mul_right
    field_simp
    norm_cast
    simp_rw [add_assoc]
    have := (summable_nat_add_iff  (f := fun x => 1/ ((x^2) : ℝ)) (B+1))
    simp at *
    apply this
  apply Summable.of_nonneg_of_le _ _ hs
  · intro b
    rw [inv_nonneg]
    apply abs_nonneg
  · intro b
    have : Z^2 - (((b+B) : ℕ)+1)^2 = ((Z/((b+B)+1))^2 - 1)* ((b+B)+1)^2 := by
        field_simp
    rw [this]
    rw [abs_mul]
    simp
    refine mul_le_mul_of_nonneg ?h₁ ?h₂ ?a0 ?d0
    · rfl
    · have := hB2 (b + B + 1) (by omega)
      norm_cast at *
      rw [inv_eq_one_div ]
      rw [one_div_le (b := 2)]
      exact this
      refine abs_sub_pos.mpr ?ha.a
      apply ne_of_lt
      have hBB := hB (b + B + 1) (by omega)
      apply lt_trans hBB
      linarith
      · norm_num
    · rw [inv_nonneg]
      exact sq_nonneg ((b : ℝ) + ↑B + 1)
    · norm_num


theorem upbnd (z : ℍ) (d : ℤ) :
    (d ^ 2 : ℝ) * EisensteinSeries.r z ^ 2 ≤ Complex.abs (z ^ 2 - d ^ 2) := by
  by_cases hd : d ≠ 0
  have h1 : (z ^ 2 : ℂ) - d ^ 2 = d ^ 2 * (1 / d ^ 2 * z ^ 2 - 1) := by ring_nf; simp [hd]
  rw [h1, map_mul]
  have ha  := EisensteinSeries.auxbound2 z (c:= 1/d) (d:= -1)
  have hb := EisensteinSeries.auxbound2 z (c:= 1/d) (d:= 1)
  simp only [ne_eq, one_div, even_two, Even.neg_pow, one_pow, le_refl, ofReal_inv, ofReal_intCast,
    ofReal_neg, ofReal_one, true_implies, map_pow, abs_intCast, _root_.sq_abs, ge_iff_le] at *
  have h4 := mul_le_mul ha hb (EisensteinSeries.r_pos z).le (Complex.abs.nonneg _)
  rw [← AbsoluteValue.map_mul, ← pow_two] at h4
  gcongr
  apply le_trans h4
  apply le_of_eq
  congr
  ring
  simp only [ne_eq, Decidable.not_not] at hd
  rw [hd]
  simp

theorem lhs_summable_up (z : ℍ) :
    Summable fun n : ℕ => 1 / ((z : ℂ) - (n+1)) + 1 / (z + (n+1)) := by
  rw [nat_inv_sub_squares z]
  apply Summable.mul_left
  apply summable_norm_iff.1
  simp
  have hs : Summable fun n : ℕ => (EisensteinSeries.r z ^ 2 * (n +1) ^ 2)⁻¹ := by
    simp_rw [mul_inv]
    apply Summable.mul_left
    have := summable_nat_add_iff (f := fun x => 1/ (x^2 : ℝ)) 1
    simpa using this
  apply Summable.of_nonneg_of_le _ _ hs
  · intro b
    rw [inv_nonneg]
    apply Complex.abs.nonneg
  intro b
  rw [inv_le_inv]
  · have := upbnd z (b+1)
    rw [mul_comm]
    norm_cast at *
  · simp at *
    simpa using  (upper_half_plane_ne_int_pow_two z (b+1))
  apply mul_pos
  · norm_cast
    apply pow_pos
    apply EisensteinSeries.r_pos
  norm_cast
  aesop


theorem lhs_summable2 (z : ℂ_ℤ) :
    Summable fun n : ℕ => 1 / ((z : ℂ) - (n+1)) + 1 / (z + (n+1)) := by
   by_cases hz : z.1.im = 0
   apply lhs_summable_re z hz
   by_cases hz2 : z.1.im > 0
   apply lhs_summable_up ⟨z, hz2⟩
   simp at *
   have hz3 : (-z.1).im > 0 := by
    simp at *
    exact lt_of_le_of_ne hz2 hz
   have := lhs_summable_up ⟨-z, hz3⟩
   simp at this
   rw [← summable_norm_iff ] at *
   apply Summable.of_nonneg_of_le _ _ this
   apply fun b : ℕ ↦ norm_nonneg (((z: ℂ) - ((b : ℂ) + 1))⁻¹ + ((z : ℂ) + (↑b + 1))⁻¹)
   intro b
   simp
   apply le_of_eq
   rw [← AbsoluteValue.map_neg Complex.abs]
   congr
   field_simp
   congr 1
   rw [← neg_div_neg_eq]
   simp
   abel_nf
   simp
   rfl
   rw [← neg_div_neg_eq]
   simp
   abel_nf
   simp
   rfl

theorem nat_pos_tsum2' [TopologicalSpace α] [AddCommMonoid α]  (f : ℕ → α) :
    (Summable fun x : ℕ+ => f x) ↔ Summable fun x : ℕ => f (x + 1) :=
  by
  rw [← Equiv.summable_iff _root_.Equiv.pnatEquivNat]
  constructor
  intro hf
  apply Summable.congr hf
  intro b
  simp
  intro hf
  apply Summable.congr hf
  intro b
  simp

theorem lhs_summable (z : ℂ_ℤ) : Summable fun n : ℕ+ => 1 / ((z : ℂ) - n) + 1 / (z + n) := by
  rw [nat_pos_tsum2' fun n => 1 / ((z : ℂ) - n) + 1 / (z + n)]
  have := lhs_summable2 z
  simp at *
  apply this

theorem cot_series_rep' (z : ℂ_ℤ) : ↑π * Complex.cot (↑π * z) - 1 / z =
    ∑' n : ℕ, (1 / ((z : ℂ) - (n + 1)) + 1 / (z + (n + 1))) := by
  rw [HasSum.tsum_eq _]
  rw [Summable.hasSum_iff_tendsto_nat]
  have h := tendsto_euler_log_derv_sin_prodd' z
  apply h
  have H := lhs_summable z
  have HH := nat_pos_tsum2' fun n => 1 / ((z : ℂ) - n) + 1 / (z + n)
  simp at *
  rw [← HH]
  exact H

/- theorem cot_series_rep (z : ℍ) :
    ↑π * Complex.cot (↑π * z) - 1 / z = ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) :=
  by
  have := tsum_pnat' fun n => 1 / ((z: ℂ) - n) + 1 / (z + n)
  have h1 := cot_series_rep' z
  simp [one_div, Nat.cast_add, algebraMap.coe_one] at *
  rw [this]
  apply h1 -/
