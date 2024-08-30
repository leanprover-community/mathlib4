
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter


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

lemma tendstouniformlyOn_iff_restrict {α β ι: Type*} [UniformSpace α] [PseudoMetricSpace β]
    [Preorder ι] (f : ι → α → β) (g : α → β) (K : Set α) : TendstoUniformlyOn f g atTop K ↔
      TendstoUniformly (fun n : ι => K.restrict (f n)) (K.restrict g) atTop := by
  simp only [Metric.tendstoUniformlyOn_iff, gt_iff_lt, eventually_atTop, ge_iff_le, ←
    tendstoUniformlyOn_univ, Set.mem_univ, Set.restrict_apply, true_implies, Subtype.forall] at *

lemma tendstouniformlyOn_iff_shift {α β : Type*} [UniformSpace α] [PseudoMetricSpace β]
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

lemma tendstoUniformlyOn_comp_exp {α : Type*} [UniformSpace α] {f : ℕ → α → ℂ} {g : α → ℂ}
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


lemma prod_tendstoUniformlyOn_tprod {α : Type*} [UniformSpace α] {f : ℕ → α → ℂ} (K : Set α)
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

theorem euler_sin_prod' (x : ℂ) (h0 : x ≠ 0) :
    Tendsto (fun n : ℕ => ∏ i : ℕ in Finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2)) atTop
      (𝓝 ((fun t : ℂ => sin (↑π * t) / (↑π * t)) x)) := by
  have := tendsto_euler_sin_prod x
  rw [Metric.tendsto_atTop] at *
  intro ε hε
  have hh : ↑π * x ≠ 0 := by apply mul_ne_zero; norm_cast; apply Real.pi_ne_zero; apply h0
  have hex : 0 < ε * Complex.abs (π * x) := by
    apply mul_pos; apply hε; apply Complex.abs.pos;
    apply hh
  have h1 := this (ε * Complex.abs (π * x)) hex
  obtain ⟨N, hN⟩ := h1
  refine ⟨N, ?_⟩
  intro n hn
  have h2 := hN n hn
  simp
  rw [dist_eq_norm] at *
  have :
    ∏ i : ℕ in Finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2) - sin (↑π * x) / (↑π * x) =
      (↑π * x * ∏ i : ℕ in Finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2) - sin (↑π * x)) / (↑π * x) :=
    by
    have tt :=
      sub_div' (sin (↑π * x)) (∏ i : ℕ in Finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2)) (↑π * x) hh
    simp at *
    rw [tt]
    ring
  norm_cast at *
  rw [this]
  field_simp
  rw [div_lt_iff]
  simp at *
  norm_cast at *
  have hr : Complex.abs ((↑π * x * ∏ x_1 in Finset.range n, (1 + -x ^ 2 / (((x_1 + 1) : ℕ) ^ 2)))
    - sin (↑π * x)) =
    Complex.abs ((↑π * x * ∏ x_1 in Finset.range n, (1 -x ^ 2 / ((x_1 + 1) ^ 2)) - sin (↑π * x)) ):=
    by
      congr
      ext1
      norm_cast
      ring
  norm_cast at *
  simp at *
  rw [hr]
  convert h2
  apply mul_pos
  simpa using Real.pi_ne_zero
  apply Complex.abs.pos
  exact h0

lemma log_of_summable {f : ℕ → ℂ} (hf : Summable f) :
    Summable (fun n : ℕ => Complex.log (1 + f n)) := by
  have hfc : Summable (fun n => Complex.abs (f n)) := by
    rw [← summable_norm_iff] at hf
    apply hf
  have hff : Summable (fun n => (3/2) * Complex.abs (f n)) := by
    apply Summable.const_smul ((3 : ℝ)/2) hfc
  have := Summable.tendsto_atTop_zero hfc
  rw [Metric.tendsto_atTop] at this
  simp at this
  apply Summable.of_norm_bounded_eventually_nat (fun n => (3/2) * Complex.abs (f n)) hff
  simp
  obtain ⟨n, hn⟩ := this (1/2) (one_half_pos)
  use n
  intro m hm
  apply Complex.norm_log_one_add_half_le_self
  exact (hn m hm).le

lemma log_of_summable_real {f : ℕ → ℝ} (hf : Summable f) :
    Summable (fun n : ℕ => Real.log (1 + |f n|)) := by
  have hfc : Summable (fun n => |(f n)|) := by
    rw [← summable_norm_iff] at hf
    apply hf
  have := Summable.tendsto_atTop_zero hfc
  rw [Metric.tendsto_atTop] at this
  simp at this
  apply Summable.of_norm_bounded_eventually_nat (fun n => |(f n)|) hfc
  simp only [log_abs, Real.norm_eq_abs, eventually_atTop, ge_iff_le]
  obtain ⟨n, _⟩ := this (1/2) (one_half_pos)
  use n
  intro m _
  have ht : 0  < 1 + |f m| := by
    rw [add_comm]
    apply add_pos_of_nonneg_of_pos
    apply abs_nonneg
    exact Real.zero_lt_one
  have := Real.log_le_sub_one_of_pos ht
  simp at this
  apply le_trans _ this
  have habs : |Real.log (1 + |f m|)| = Real.log (1 + |f m|) := by
    rw [@abs_eq_self]
    apply Real.log_nonneg
    simp
  rw [habs]


lemma summable_multipliable (f : ℕ → ℂ) (hf : Summable f) (hff : ∀ n : ℕ, 1 + f n  ≠ 0) :
    Multipliable (fun n : ℕ => (1 + f n)) := by
  have := log_of_summable  hf
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
  rw [Multipliable]
  simp_rw [HasProd]
  use exp a

theorem Complex.closedEmbedding_coe_complex : ClosedEmbedding ((↑) : ℤ → ℂ) := by
  apply Metric.closedEmbedding_of_pairwise_le_dist zero_lt_one
  convert Int.pairwise_one_le_dist
  simp_rw [dist_eq_norm]
  norm_cast
  rw [Int.norm_eq_abs]
  exact norm_int

lemma int_img_closed : IsClosed (((↑) : ℤ → ℂ)'' ⊤) := by
  simp
  have := Complex.closedEmbedding_coe_complex
  exact this.isClosed_range

lemma ints_comp_IsOpen : IsOpen {z : ℂ | ¬ ∃ (n : ℤ), z = ↑n} := by
  refine IsClosed.not ?_
  have := int_img_closed
  convert this
  ext y
  aesop

set_option quotPrecheck false
local notation "ℤᶜ" =>  {z : ℂ | ¬ ∃ (n : ℤ), z = n}

noncomputable instance : UniformSpace ℤᶜ := by infer_instance

instance : LocallyCompactSpace ℤᶜ := IsOpen.locallyCompactSpace ints_comp_IsOpen

lemma int_comp_not_zero (x : ℂ) (hx : x ∈ {z : ℂ | ¬ ∃ (n : ℤ), z = ↑n}) : x ≠ 0 := by
  intro h
  rw [h] at hx
  simp at hx
  have := hx 0
  simp only [Int.cast_zero, not_true_eq_false] at this

lemma int_comp_not_zero2 (x : ℂ) (hx : x ∈ {z : ℂ | ¬ ∃ (n : ℤ), z = ↑n}) (n : ℕ) :
  1 + -x ^ 2 / (n + 1) ^ 2 ≠ 0 := by
  intro h
  rw [@add_eq_zero_iff_eq_neg] at h
  rw [@neg_div'] at h
  simp at h
  rw [eq_div_iff] at h
  simp at h
  rw [@sq_eq_sq_iff_eq_or_eq_neg] at h
  rcases h with h1| h2
  simp at hx
  have := hx (n+1)
  simp  [Int.cast_add, Int.cast_natCast, Int.cast_one, not_true_eq_false] at this
  exact this (id (Eq.symm h1))
  simp at hx
  have := hx (-(n+1))
  simp at *
  rw [← neg_eq_iff_eq_neg ] at h2
  rw [← h2] at this
  simp at this
  simp
  exact Nat.cast_add_one_ne_zero n

lemma int_comp_add_ne_zero (x : ℂ) (hx : x ∈ {z : ℂ | ¬ ∃ (n : ℤ), z = ↑n}) (a : ℤ) :
    x + a ≠ 0 := by
  intro h
  rw [@add_eq_zero_iff_eq_neg] at h
  rw [h] at hx
  simp at hx
  have := hx (-a)
  simp only [Int.cast_neg, Int.cast_add, Int.cast_zero, not_true_eq_false] at this



theorem summable_rie_twist (x : ℂ) : Summable fun n : ℕ => Complex.abs (x ^ 2 / (↑n + 1) ^ 2) :=
  by
  simp
  simp_rw [div_eq_mul_inv]
  apply Summable.mul_left
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 2)⁻¹ :=
    by
    norm_cast
    simp
    have hkk : 1 < (2 : ℝ):= by linarith
    have H := Real.summable_nat_rpow_inv.2 hkk
    rw [← summable_nat_add_iff 1] at H
    norm_cast at H
    simpa using H
  apply Summable.congr hs
  intro b
  simp
  rw [← Complex.abs_pow]
  simp at *
  norm_cast at *
  rw [Complex.abs_natCast]
  simp


theorem summable_rie_twisters (x : ℂ) : Summable fun n : ℕ => Complex.abs (x  / (↑n + 1) ^ 2) :=
  by
  simp
  simp_rw [div_eq_mul_inv]
  apply Summable.mul_left
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 2)⁻¹ :=
    by
    norm_cast
    simp
    have hkk : 1 < (2 : ℝ):= by linarith
    have H := Real.summable_nat_rpow_inv.2 hkk
    rw [← summable_nat_add_iff 1] at H
    norm_cast at H
    simpa using H
  apply Summable.congr hs
  intro b
  simp
  rw [← Complex.abs_pow]
  simp at *
  norm_cast at *
  rw [Complex.abs_natCast]
  simp

-- wtf multipliable_iff_cauchySeq_finset
lemma prodd (x : ℂ) (h0 : x  ∈ {z : ℂ | ¬ ∃ (n : ℤ), z = n}) :
  (∏' i : ℕ, (1 + -x ^ 2 / (↑i + 1) ^ 2)) = (((fun t : ℂ => sin (↑π * t) / (↑π * t)) x)) := by
  have H := int_comp_not_zero2 x h0
  rw [← Multipliable.hasProd_iff]
  rw [Multipliable.hasProd_iff_tendsto_nat]
  have := euler_sin_prod' x (int_comp_not_zero x h0)
  simp at this
  apply this
  repeat {
  apply summable_multipliable
  · rw [← summable_norm_iff]
    simpa using summable_rie_twist x
  · apply H}

lemma prodd2 (x : ℂ) (h0 : x  ∈ {z : ℂ | ¬ ∃ (n : ℤ), z = n}) :
  ((↑π * x) * ∏' i : ℕ, (1 + -x ^ 2 / (↑i + 1) ^ 2)) = (((fun t : ℂ => sin (↑π * t)) x)) := by
  have H := prodd x h0
  simp_rw [H]
  refine mul_div_cancel_of_imp' ?h
  intro h
  rw [h]
  simp


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
  apply tsum_le_tsum
  intro i
  apply hN2
  apply i.2
  apply (A.subtype _)
  apply (hu.subtype _)
  apply (A.subtype _)


theorem tendstoUniformlyOn_tsum_nat2 {f : ℕ → ℂ → ℂ} {u : ℕ → ℝ} (hu : Summable u) {s : Set ℂ}
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
      exact hn (hb h )

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


lemma unif_lem (Z : Set ℤᶜ) (hZ : IsCompact Z) :
    TendstoUniformlyOn (fun (n : ℕ) (a : ℤᶜ) ↦
      ∑ i ∈ Finset.range n, Complex.log (1 + -a.1 ^ 2 / (↑i + 1) ^ 2))
        (fun a ↦ ∑' (n : ℕ), Complex.log (1 + -↑a ^ 2 / (↑n + 1) ^ 2)) atTop Z:= by
  have hf : ContinuousOn (fun x : ℤᶜ => ( Complex.abs (-x.1 ^ 2)) ) Z := by
    apply ContinuousOn.comp
    let g := fun x : ℤᶜ =>-x.1 ^ 2
    apply Continuous.continuousOn Complex.continuous_abs  (s := ((g '' Z)))
    apply (ContinuousOn.neg (ContinuousOn.pow (Continuous.continuousOn continuous_subtype_val) 2))
    exact Set.mapsTo_image (fun x ↦ -x.1 ^ 2) Z
  have := IsCompact.bddAbove_image  hZ hf
  rw [@bddAbove_def] at this
  simp at *
  obtain ⟨s, hs⟩ := this
  apply tendstoUniformlyOn_tsum_log_one_add (u := (fun n : ℕ => Complex.abs (s / (n + 1) ^ 2)))
  apply summable_rie_twisters s
  intro n x hx
  simp
  gcongr
  apply le_trans _ (le_abs_self s)
  apply hs
  apply hx
  rfl
  aesop


 lemma unif_lem_re (Z : Set ℤᶜ) (hZ : IsCompact Z) :
   TendstoUniformlyOn (fun (n : ℕ) (a : ℤᶜ) ↦
    (∑ i ∈ Finset.range n, Real.log (Complex.abs (1 + -a.1 ^ 2 / (i + 1) ^ 2))))
      (fun a ↦ (∑' (n : ℕ), Real.log  (Complex.abs (1 + -a ^ 2 / (n + 1) ^ 2)))) atTop Z:= by
  have hf : ContinuousOn (fun x : ℤᶜ => ( Complex.abs (-x.1 ^ 2)) ) Z := by
    apply ContinuousOn.comp
    let g := fun x : ℤᶜ => -x.1 ^ 2
    apply Continuous.continuousOn Complex.continuous_abs  (s := ((g '' Z)))
    apply (ContinuousOn.neg (ContinuousOn.pow (Continuous.continuousOn continuous_subtype_val) 2))
    exact Set.mapsTo_image (fun x ↦ -x.1 ^ 2) Z
  have := IsCompact.bddAbove_image  hZ hf
  rw [@bddAbove_def] at this
  simp at *
  obtain ⟨s, hs⟩ := this
  apply tendstoUniformlyOn_tsum_log_one_add_re (u := (fun n : ℕ => Complex.abs (s / (n + 1) ^ 2)))
  apply summable_rie_twisters s
  intro n x hx
  simp
  gcongr
  apply le_trans _ (le_abs_self s)
  apply hs
  apply hx
  rfl
  aesop


theorem tendsto_locally_uniformly_euler_sin_prod_comp (Z : Set ℤᶜ) (hZ : IsCompact Z) :
    TendstoUniformlyOn (fun n : ℕ => fun z : ℤᶜ => ∏ j in Finset.range n,
      (1 + -z.1 ^ 2 / (j + 1) ^ 2))
        (fun x => ( ∏' i : ℕ, (1 + -x.1 ^ 2 / (↑i + 1) ^ 2))) atTop Z := by
  apply prod_tendstoUniformlyOn_tprod
  intro x
  apply log_of_summable
  rw [← summable_norm_iff]
  simpa using  summable_rie_twist x
  apply unif_lem Z hZ
  intro x n
  apply int_comp_not_zero2 x.1 (Subtype.coe_prop x.1)
  have hf : ContinuousOn (fun x : ℤᶜ =>
      (∑' n : ℕ, Complex.log (1+-x ^ 2 / (n + 1) ^ 2)).re ) Z := by
    have hcon :=  (unif_lem_re Z hZ).continuousOn
    have : (fun x : ℤᶜ => (∑' n : ℕ, Complex.log (1+-x ^ 2 / (n + 1) ^ 2)).re ) =
      (fun x : ℤᶜ => (∑' n : ℕ, (Complex.log (1+-x ^ 2 / (n + 1) ^ 2)).re)) := by
        ext x
        simp
        rw [Complex.re_tsum ]
        apply log_of_summable
        rw [← summable_norm_iff]
        simpa using  summable_rie_twist x
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
    let g := fun x : ℤᶜ => 1+-x.1 ^ 2 / (c + 1) ^ 2
    apply Continuous.continuousOn Complex.continuous_abs  (s := ((g '' Z)))
    apply (ContinuousOn.add continuousOn_const
    (ContinuousOn.mul
      (ContinuousOn.neg (ContinuousOn.pow (Continuous.continuousOn continuous_subtype_val) 2))
      continuousOn_const))
    exact Set.mapsTo_image (fun x ↦ 1 + -x.1 ^ 2 / ((c : ℂ) + 1) ^ 2) Z
    intro z _
    simp only [ne_eq, map_eq_zero]
    apply int_comp_not_zero2 z.1 z.2
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
theorem tendsto_locally_uniformly_euler_sin_prod'' (Z : Set ℤᶜ) (hZ : IsCompact Z) :
    TendstoUniformlyOn (fun n : ℕ => fun z : ℤᶜ => ∏ j in range n, (1 + -z.1 ^ 2 / (j + 1) ^ 2))
      (fun x => ((fun t : ℂ => sin (↑π * t) / (↑π * t)) x)) atTop Z := by
  have := tendsto_locally_uniformly_euler_sin_prod_comp Z hZ
  apply TendstoUniformlyOn.congr_right this
  intro x _
  simp
  rw [prodd x]
  apply x.2



theorem sin_pi_z_ne_zero (z : ℤᶜ) : Complex.sin (π * z) ≠ 0 :=
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
    DifferentiableOn ℂ (fun z : ℂ => ∏ j in Finset.range n, (1 + -z ^ 2 / (j + 1) ^ 2)) ℤᶜ :=
  by
  apply DifferentiableOn.finset_prod
  intro i _
  apply DifferentiableOn.add
  apply differentiableOn_const
  apply DifferentiableOn.div_const
  apply DifferentiableOn.neg
  apply DifferentiableOn.pow
  apply differentiable_id.differentiableOn



theorem tendsto_euler_log_derv_sin_prodde (x : ℤᶜ) :
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
  let Z : Set ℤᶜ :=  (Set.inclusion hK)'' ⊤
  have hZ : IsCompact Z := by
    apply IsCompact.image
    exact isCompact_iff_isCompact_univ.mp hK2
    exact continuous_inclusion hK
  have := tendsto_locally_uniformly_euler_sin_prod'' Z hZ
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
  refine ⟨?_,?_,?_⟩
  have := sin_pi_z_ne_zero
  apply sin_pi_z_ne_zero
  apply Real.pi_ne_zero
  intro h
  have := x.2
  rw [h] at this
  simp at this
  have := this 0
  simp at this


theorem logDeriv_sin_div (z : ℤᶜ) :
    logDeriv (fun t => (Complex.sin (π * t) / (π * t))) z =
      π * cot (π * z) - 1/z := by
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
    refine ⟨Real.pi_ne_zero, int_comp_not_zero _ z.2⟩


lemma logDeriv_of_prod (x : ℤᶜ) (n : ℕ) :
    logDeriv (fun (z : ℂ) =>  ∏ j in Finset.range n, (1 + -z ^ 2 / (j + 1) ^ 2)) x =
     ∑ j in Finset.range n, (1 / ((x : ℂ) - (j + 1)) + 1 / (x + (j + 1))) := by
    rw [logDeriv_prod]
    congr
    ext1 i
    rw [logDeriv_apply]
    simp
    simp_rw [div_eq_mul_inv]
    set i1 := ((x : ℂ) + (i+1))⁻¹
    set i2 := ((x : ℂ) - (i+1))⁻¹
    set i3 := ((i+1 : ℂ)^2)⁻¹
    set i4 := (1+ -x^2*i3)⁻¹
    have h1  : ((x : ℂ) + (i+1))* i1 = 1 := by
      refine Complex.mul_inv_cancel ?h
      simpa using int_comp_add_ne_zero x x.2 (i+1)
    have h2 : ((x : ℂ) - (i+1)) * i2 = 1 := by
      apply Complex.mul_inv_cancel
      rw [sub_eq_add_neg]
      simpa using int_comp_add_ne_zero x x.2 (-(i+1))
    have h3 : ((i+1 : ℂ)^2) * i3 = 1 := by sorry
    have h4 : (1+ -x^2*i3)*i4 = 1 := by sorry
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
    sorry



    sorry

theorem tendsto_euler_log_derv_sin_prodd' (x : ℤᶜ) :
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

theorem lhs_summable (z : ℤᶜ) : Summable fun n : ℕ+ => 1 / ((z : ℂ) - n) + 1 / (z + n) := by sorry


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

theorem cot_series_rep' (z : ℤᶜ) : ↑π * Complex.cot (↑π * z) - 1 / z =
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
