
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

open Filter Function Complex

open scoped Interval Topology BigOperators Nat Classical UpperHalfPlane


variable {α  ι: Type*}

lemma norm_log_one_add_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 + z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := by
  rw [Eq.symm (sub_add_cancel (log (1 + z)) z)]
  apply le_trans (norm_add_le _ _)
  exact add_le_add_right (Complex.norm_log_one_add_sub_self_le hz) ‖z‖

/--For `‖z‖ ≤ 1/2`, the complex logarithm is bounded by `(3/2) * ‖z‖`. -/
lemma norm_log_one_add_half_le_self {z : ℂ} (hz : ‖z‖ ≤ 1/2) : ‖(log (1 + z))‖ ≤ (3/2) * ‖z‖ := by
  apply le_trans (norm_log_one_add_le (lt_of_le_of_lt hz one_half_lt_one))
  have hz3 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff]
    · linarith
    · linarith
  have hz4 : ‖z‖^2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖/2 * 2 / 2 := by
    gcongr
    · rw [inv_nonneg]
      linarith
    · rw [sq, div_eq_mul_one_div]
      apply mul_le_mul (by simp only [norm_eq_abs, mul_one, le_refl])
        (by simpa only [norm_eq_abs, one_div] using hz) (norm_nonneg z) (by simp only [norm_eq_abs,
          mul_one, apply_nonneg])
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel] at hz4
  linarith


/--The exponential of a infinite sum  of logs (which converges absolutely) is an infinite product.-/
lemma cexp_tsum_eq_tprod  (f : ι → α → ℂ) (hfn : ∀ x n, f n x ≠ 0)
  (hf : ∀ x : α,  Summable fun n => log ((f n x))) :
    (cexp ∘ (fun a : α => (∑' n : ι, log ((f n a))))) =
      (fun a : α => ∏' n : ι, ((f n a))) := by
  ext a
  apply (HasProd.tprod_eq ?_).symm
  apply ((hf a).hasSum.cexp).congr
  intro _
  congr
  exact funext fun x ↦ exp_log (hfn a x)

lemma UniformlyContinuosOn_cexp (a : ℝ) : UniformContinuousOn cexp {x : ℂ | x.re ≤ a} := by
  have : Continuous (cexp - 1) := Continuous.sub (Continuous.cexp continuous_id') continuous_one
  rw [Metric.uniformContinuousOn_iff, Metric.continuous_iff'] at *
  intro ε hε
  simp only [gt_iff_lt, Pi.sub_apply, Pi.one_apply, dist_sub_eq_dist_add_right,
    sub_add_cancel] at this
  have ha : 0 < ε / (2 * Real.exp a) := by positivity
  have H := this 0 (ε / (2 * Real.exp a)) ha
  rw [Metric.eventually_nhds_iff] at H
  obtain ⟨δ, hδ⟩ := H
  refine ⟨δ, hδ.1, ?_⟩
  intros x _ y hy hxy
  have h3 := hδ.2 (y := x - y) (by simpa only [dist_zero_right, norm_eq_abs] using hxy)
  rw [dist_eq_norm, exp_zero] at *
  have : cexp x - cexp y = cexp y * (cexp (x - y) - 1) := by
      rw [@mul_sub_one, ← exp_add]
      ring_nf
  rw [this, mul_comm]
  have hya : ‖cexp y‖ ≤ Real.exp a := by
    simp only [norm_eq_abs, abs_exp, Real.exp_le_exp]
    exact hy
  simp only [gt_iff_lt, dist_zero_right, norm_eq_abs, Set.mem_setOf_eq, norm_mul,
    Complex.abs_exp] at *
  apply lt_of_le_of_lt (mul_le_mul h3.le hya (Real.exp_nonneg y.re) (le_of_lt ha))
  have hrr : ε / (2 * a.exp) * a.exp = ε / 2 := by
    nth_rw 2 [mul_comm]
    field_simp [mul_assoc]
  rw [hrr]
  exact div_two_lt_of_pos hε



theorem UniformContinuousOn.comp_tendstoUniformly  {β γ ι: Type*}
    [UniformSpace β] {p : Filter ι} (s : Set β) (F : ι → γ → s) (f : γ → s) {g : β → β}
    (hg : UniformContinuousOn g s) (h : TendstoUniformly F f p) :
    TendstoUniformly (fun i => fun x =>  g  (F i x)) (fun x => g (f x)) p := by
  rw [uniformContinuousOn_iff_restrict] at hg
  apply (UniformContinuous.comp_tendstoUniformly hg h)

/- theorem UniformContinuousOn.comp_tendstoUniformlyOn (s : Set ℂ) (F : ℕ → ℂ → s)
    (f : ℂ → s) {g : ℂ → ℂ} (hg : UniformContinuousOn g s) (h : TendstoUniformlyOn F f atTop s) :
    TendstoUniformlyOn (fun i => fun x =>  g  (F i x)) (fun x => g (f x)) atTop s := by
  rw [uniformContinuousOn_iff_restrict] at hg
  apply (UniformContinuous.comp_tendstoUniformlyOn hg h)
 -/

lemma UniformlyContinous_re : UniformContinuous (fun x : ℂ => x.re) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  refine ⟨ε, hε, fun hxy =>  ?_⟩
  apply lt_of_le_of_lt (Complex.abs_re_le_abs _) hxy

lemma UniformlyContinous_im : UniformContinuous (fun x : ℂ => x.im) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  refine ⟨ε, hε, fun hxy =>  ?_⟩
  apply lt_of_le_of_lt (Complex.abs_im_le_abs _) hxy

lemma TendstoUniformly_re_part (f : ι → α → ℂ) {p : Filter ι} (g : α → ℂ) (K : Set α)
    (hf : TendstoUniformlyOn f g p K) : TendstoUniformlyOn (fun n x => (f n x).re)
      (fun y => (g y).re) p K := by
  apply UniformContinuous.comp_tendstoUniformlyOn UniformlyContinous_re hf

lemma TendstoUniformly_im_part (f : ι → α → ℂ) {p : Filter ι} (g : α → ℂ) (K : Set α)
    (hf : TendstoUniformlyOn f g p K) : TendstoUniformlyOn (fun n x => (f n x).im)
      (fun y => (g y).im) p K := by
  apply UniformContinuous.comp_tendstoUniformlyOn UniformlyContinous_im hf

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

lemma tendstouniformlyOn_iff_restrict {α : Type*} [UniformSpace α] (f : ℕ → α → ℂ) (g : α → ℂ)
    (K : Set α) : TendstoUniformlyOn f g atTop K ↔
      TendstoUniformly (fun n : ℕ => K.restrict (f n)) (K.restrict g) atTop := by
  simp only [Metric.tendstoUniformlyOn_iff, gt_iff_lt, eventually_atTop, ge_iff_le, ←
    tendstoUniformlyOn_univ, Set.mem_univ, Set.restrict_apply, true_implies, Subtype.forall] at *

lemma tendstouniformlyOn_iff_restrict2 {α ι: Type*} [UniformSpace α] {p : Filter ι}
    (f : ι → α → ℂ) (g : α → ℂ) (K : Set α) : TendstoUniformlyOn f g p K ↔
      TendstoUniformly (fun n : ι => K.restrict (f n)) (K.restrict g) p := by
  simp only [Metric.tendstoUniformlyOn_iff, gt_iff_lt, ← tendstoUniformlyOn_univ, Set.mem_univ,
    Set.restrict_apply, true_implies, Subtype.forall] at *

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

lemma tendstoUniformlyOn_comp_exp {α : Type*} [UniformSpace α] (f : ℕ → α → ℂ) (g : α → ℂ)
    (K : Set α) (hf : TendstoUniformlyOn f g atTop K) (hg : ∃ T : ℝ, ∀ x : α, x ∈ K → (g x).re ≤ T):
        TendstoUniformlyOn (fun n => fun x => cexp (f n x)) (cexp ∘ g) atTop K := by
  obtain ⟨T, hT⟩ := hg
  have h2 := tendstouniformlyOn_le (fun n x => (f n x).re) (fun x => (g x).re) K T
    (TendstoUniformly_re_part f g K hf) hT
  simp only [eventually_atTop, ge_iff_le] at h2
  obtain ⟨B, δ, hδ⟩ := h2
  let F : ℕ → K → {x : ℂ | x.re ≤ max B T} := fun n => fun x => ⟨f (n + δ) x, by
    have := hδ (n + δ)
    simp only [le_add_iff_nonneg_left, zero_le, true_implies, le_max_iff, Set.mem_setOf_eq] at *
    left
    apply (this x x.2)⟩
  let G : K → {x : ℂ | x.re ≤ max B T} := fun x => ⟨g x, by
    simp only [le_max_iff, Set.mem_setOf_eq]
    right
    apply le_trans (hT x x.2) (by rfl)⟩
  have wish : TendstoUniformly F G atTop := by
    simp only [Metric.tendstoUniformlyOn_iff, gt_iff_lt, eventually_atTop, ge_iff_le, Set.coe_setOf,
      Set.mem_setOf_eq, Metric.tendstoUniformly_iff, Subtype.forall, F, G] at *
    intro ε hε
    obtain ⟨N2, hN2⟩ := hf ε hε
    refine ⟨(max N2 δ) - δ, fun n hn x hx => ?_ ⟩
    rw [@Nat.sub_le_iff_le_add] at hn
    apply hN2 (n + δ) (le_trans (Nat.le_max_left N2 δ) hn) x hx
  have w2 := UniformContinuousOn.comp_tendstoUniformly {x : ℂ | x.re ≤ max B T} F G
    (UniformlyContinuosOn_cexp (max B T)) wish
  rw [← tendstoUniformlyOn_univ] at w2
  rw [tendstouniformlyOn_iff_restrict, ← tendstoUniformlyOn_univ,
    tendstouniformlyOn_iff_shift (d := δ)]
  apply w2

lemma tendstoUniformlyOn_comp_exp2 {α ι: Type*} [UniformSpace α] {p : Filter ι} (f : ι → α → ℂ) (g : α → ℂ)
    (K : Set α) (hf : TendstoUniformlyOn f g p K) (hg : ∃ T : ℝ, ∀ x : α, x ∈ K → (g x).re ≤ T):
        TendstoUniformlyOn (fun n => fun x => cexp (f n x)) (cexp ∘ g) p K := by
  obtain ⟨T, hT⟩ := hg
  have h2 := tendstouniformlyOn_le (fun n x => (f n x).re) (fun x => (g x).re) K T
    (TendstoUniformly_re_part f g K hf) hT
  simp_rw [eventually_iff_exists_mem] at h2
  obtain ⟨B, δ, h1, h2⟩ := h2
  let F : δ → K → {x : ℂ | x.re ≤ max B T} := fun n => fun x => ⟨f n x, by
    simp only [le_max_iff, Set.mem_setOf_eq]
    left
    apply (h2 n n.2 x x.2)⟩
  let G : K → {x : ℂ | x.re ≤ max B T} := fun x => ⟨g x, by
    simp only [le_max_iff, Set.mem_setOf_eq]
    right
    apply le_trans (hT x x.2) (by rfl)⟩
  have wish : TendstoUniformly F G (p.comap ((↑): δ → ι)) := by
    simp [Metric.tendstoUniformlyOn_iff, gt_iff_lt, eventually_atTop, ge_iff_le, Set.coe_setOf,
      Set.mem_setOf_eq, Metric.tendstoUniformly_iff, Subtype.forall, F, G] at *
    intro ε hε
    simp_rw [@eventually_iff_exists_mem] at *
    have hff := hf ε hε
    obtain ⟨N, hN⟩ := hff
    use N
    refine ⟨hN.1, ?_⟩
    intro y hy a ha hay x hx
    have :=  hN.2 y hy x hx
    rw [← hay] at this
    apply this
  have w2 := UniformContinuousOn.comp_tendstoUniformly {x : ℂ | x.re ≤ max B T} F G
    (UniformlyContinuosOn_cexp (max B T)) wish
  rw [← tendstoUniformlyOn_univ] at w2
  rw [tendstouniformlyOn_iff_restrict2, ← tendstoUniformlyOn_univ]

  apply w2


lemma prod_tendstoUniformlyOn_tprod {α : Type*} [UniformSpace α] (f : ℕ → α → ℂ) (K : Set α)
    (h : ∀ x : K, Summable fun n => log (1 + (f n x)))
    (hf : TendstoUniformlyOn (fun n : ℕ => fun a : α => ∑ i in Finset.range n, log (1 + (f i a)))
      (fun a : α => ∑' n : ℕ, log (1 + (f n a))) atTop K)
    (hfn : ∀ x : K, ∀ n : ℕ, 1 + f n x ≠ 0)
    (hg : ∃ T : ℝ, ∀ x : α, x ∈ K → (∑' n : ℕ, log (1 + (f n x))).re ≤ T) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i in Finset.range n, (1 + f i a))
      (fun a => ∏' i, (1 + f i a)) atTop K := by
  have := tendstoUniformlyOn_comp_exp (fun n : ℕ => fun a : α => ∑ i in Finset.range n,
    (Complex.log (1 + (f i a)))) (fun a : α =>(∑' n : ℕ, Complex.log (1 + (f n a)))) K hf hg
  have := TendstoUniformlyOn.congr this
    (F' := (fun n : ℕ => fun a : α => ∏ i in Finset.range n, (1 + (f i a))))
  have HU : TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i in Finset.range n, (1 + f i a))
       (cexp ∘ fun a ↦ ∑' (n : ℕ), log (1 + f n a)) atTop K := by
      apply this
      simp only [eventually_atTop, ge_iff_le]
      refine ⟨0, fun b _ x hx => ?_⟩
      simp only [exp_sum]
      congr
      ext y
      apply Complex.exp_log (hfn ⟨x, hx⟩ y)
  apply TendstoUniformlyOn.congr_right HU
  intro x hx
  exact congrFun (cexp_tsum_eq_tprod (fun n => fun x : K => 1 + f n x) hfn h) ⟨x, hx⟩


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
  apply norm_log_one_add_half_le_self
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
  have := (norm_log_one_add_half_le_self  (z :=(f n x)) ?_)
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
  have := (norm_log_one_add_half_le_self (z := (f n x)) ?_)
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
