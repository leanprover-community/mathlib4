
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit

open Filter Function Complex

open scoped Interval Topology BigOperators Nat Classical


variable {α ι: Type*}

theorem prod_be_exp  (f : ι → ℂ) (s : Finset ι) :
    ∏ i in s, (1 + Complex.abs (f i)) ≤ Real.exp (∑ i in s, Complex.abs (f i)) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  intro i _
  apply add_nonneg
  linarith
  apply Complex.abs.nonneg
  intro i _
  rw [add_comm]
  apply Real.add_one_le_exp


theorem unif_prod_bound (F : ι → α → ℂ)
    (hb : ∃ T : ℝ, ∀ x : α ,  ∑' n : ι, Complex.abs (F n x) ≤ T)
    (hs : ∀ x : α, Summable fun n : ι => Complex.abs (F n x)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ι) (x : α), ∏ i in s, (1 + Complex.abs (F i x)) ≤ C :=
  by
  obtain ⟨T, ht⟩ := hb
  have HB :
    ∀ (s : Finset ι) (a : α), ∑ i in s, Complex.abs (F i a) ≤ ∑' n : ι, Complex.abs (F n a) :=
    by
    intro n a
    apply sum_le_tsum
    intro b _
    apply Complex.abs.nonneg
    apply hs a
  have hexp : 0 < Real.exp T := by have := Real.exp_pos T; apply this
  refine' ⟨Real.exp T, _⟩
  simp [hexp]
  intro n x
  apply le_trans (prod_be_exp _ _)
  simp
  apply le_trans (HB n x)
  exact ht x

theorem unif_prod_bound2 (F : ι → α → ℂ)
    (hs : ∀ x : α, Summable fun n : ι => Complex.abs (F n x)) (s : Finset ι) (x : α):
        ∏ i in s, (1 + Complex.abs (F i x)) ≤ Real.exp (∑' n : ι, Complex.abs (F n x)) := by
  have HB :
    ∀ (s : Finset ι) (a : α), ∑ i in s, Complex.abs (F i a) ≤ ∑' n : ι, Complex.abs (F n a) :=
    by
    intro n a
    apply sum_le_tsum
    intro b _
    apply Complex.abs.nonneg
    apply hs a
  apply le_trans (prod_be_exp _ _)
  simp
  apply le_trans (HB s x)
  rfl

theorem sum_prod_unif_conv2 (F : ℕ → α → ℂ) (g : α → ℂ) (K : Set α)
    (hf :
      TendstoUniformlyOn (fun n : ℕ => fun a : α => ∑ i in Finset.range n, Complex.abs (F i a))
        (fun a : α => ∑' n : ℕ, Complex.abs (F n a)) Filter.atTop K)
    (hb : ∃ T : ℝ, ∀ x : α, x ∈ K → ∑' n : ℕ, Complex.abs (F n x) ≤ T)
    (hs : ∀ x : α, Summable fun n : ℕ => Complex.abs (F n x))
    (hp :
      ∀ x : α , x ∈ K → Tendsto (fun n : ℕ => ∏ i in Finset.range n, (1 + F i x)) atTop (𝓝 (g x))) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i in Finset.range n, (1 + F i a)) g Filter.atTop
      K := by
  apply UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto _ hp
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  sorry

lemma tenstoUniformlyOn_const_self {α: Type*} (ι) [Preorder ι] [UniformSpace α] (a : α → α)
    (K : Set α) : TendstoUniformlyOn (fun _: ι => a) a atTop K:= by
    refine TendstoUniformlyOnFilter.tendstoUniformlyOn ?_
    rw [tendstoUniformlyOnFilter_iff_tendsto]
    exact tendsto_diag_uniformity (fun x ↦ a x.2) (_ ×ˢ 𝓟 K)

theorem tsum_unif2 (F : ℕ → ℂ → ℂ) (K : Set ℂ)
    (hf : TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∑ i in Finset.range n,  (F i a))
        (fun a : ℂ => ∑' n : ℕ, (F n a)) Filter.atTop K)
    (hs : ∀ x : ℂ, x ∈ K →  Summable fun n : ℕ => (F n x)) :
    TendstoUniformlyOn (fun k : ℕ => fun a : ℂ => ∑' n : ℕ, (F (n + k) a)) 0 Filter.atTop K := by
  have := (tenstoUniformlyOn_const_self ℕ (fun a : ℂ => ∑' n : ℕ, (F n a)) K).sub hf
  simp only [sub_self] at this
  apply this.congr
  simp only [Pi.sub_apply, eventually_atTop, ge_iff_le]
  use 1
  intro b _
  intro x hx
  simp only [Pi.sub_apply]
  rw [← sum_add_tsum_nat_add b]
  ring
  exact hs x hx


theorem tsum_unif (F : ℕ → ℂ → ℂ) (K : Set ℂ)
    (hf :
      TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∑ i in Finset.range n, Complex.abs (F i a))
        (fun a : ℂ => ∑' n : ℕ, Complex.abs (F n a)) Filter.atTop K)
    (hs : ∀ x : ℂ, Summable fun n : ℕ => Complex.abs (F n x)) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ N : ℕ,
          ∀ (n : ℕ) (x : ℂ),
            x ∈ K → N ≤ n → Complex.abs (∑' i : ℕ, Complex.abs (F (i + N) x)) < ε :=
  by
  rw [Metric.tendstoUniformlyOn_iff] at hf
  simp at hf
  intro ε hε
  have HF := hf ε hε
  obtain ⟨N, hN⟩ := HF
  refine' ⟨N, _⟩
  intro n x hx _
  have hnn : N ≤ N := by rfl
  have HN2 := hN N hnn x hx
  simp_rw [dist_eq_norm] at *
  convert HN2
  rw [tsum_coe]
  rw [← norm_eq_abs]
  rw [Complex.norm_real]
  congr
  have hy := sum_add_tsum_nat_add N (hs x)
  simp at hy
  rw [← hy]
  ring

theorem tsum_unifo (F : ℕ → ℂ → ℂ) (K : Set ℂ)
    (hf :
      TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∑ i in Finset.range n, Complex.abs (F i a))
        (fun a : ℂ => ∑' n : ℕ, Complex.abs (F n a)) Filter.atTop K)
    (hs : ∀ x : ℂ, Summable fun n : ℕ => Complex.abs (F n x)) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ N : ℕ,
          ∀ (n m : ℕ) (x : ℂ),
            x ∈ K →
              N ≤ n ∧ N ≤ m ∧ m ≤ n → ∏ i in Finset.Ico m n, (1 + Complex.abs (F i x)) - 1 ≤ ε :=
  by
  intro ε hε
  have hl : 0 < Real.log (1 + ε) := by apply Real.log_pos; linarith
  have H2 := tsum_unif F K hf hs (Real.log (1 + ε)) hl
  obtain ⟨N, hN⟩ := H2
  use N
  intro n m x hK h
  have HN2 := hN n x hK h.1
  apply le_trans (sub_le_sub_right (prod_be_exp _ _) 1)
  rw [← Real.exp_lt_exp] at HN2
  have hll : 0 < 1 + ε := by linarith
  rw [Real.exp_log hll] at HN2
  rw [tsub_le_iff_left]
  apply le_trans _ HN2.le
  simp
  have hss : Summable fun n : ℕ => Complex.abs (F (n + N) x) :=
    by
    have := hs x
    rw [← summable_nat_add_iff N] at this
    apply this
  have := abs_tsum _ hss
  rw [abs_tsum_of_pos F x N]
  have := sum_add_tsum_nat_add N (hs x)
  apply sum_subtype_le_tsum
  constructor
  apply h.2.2
  apply h.2.1
  intro b
  apply Complex.abs.nonneg
  exact hs x

theorem sum_prod_unif_conv (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (K : Set ℂ)
    (hf :
      TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∑ i in Finset.range n, Complex.abs (F i a))
        (fun a : ℂ => ∑' n : ℕ, Complex.abs (F n a)) Filter.atTop K)
    (hb : ∃ T : ℝ, ∀ x : ℂ, x ∈ K → ∑' n : ℕ, Complex.abs (F n x) ≤ T)
    (hs : ∀ x : ℂ, Summable fun n : ℕ => Complex.abs (F n x))
    (hp :
      ∀ x : ℂ, x ∈ K → Tendsto (fun n : ℕ => ∏ i in Finset.range n, (1 + F i x)) atTop (𝓝 (g x))) :
    TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∏ i in Finset.range n, (1 + F i a)) g Filter.atTop
      K :=
  by
  apply UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have H := tsum_unifo F K hf hs
  have H2 := unif_prod_bound F K hb hs
  obtain ⟨C, hCp, hC⟩ := H2
  have hdelta := exists_pos_mul_lt hε C
  obtain ⟨δ, hδ⟩ := hdelta
  have HH := H δ hδ.1
  obtain ⟨N, HN⟩ := HH
  refine' ⟨N, _⟩
  intro n hn m hm x hx
  have hCm := hC (Finset.range m) x
  have hCn := hC (Finset.range n) x
  rw [dist_eq_norm]
  simp only [norm_eq_abs]
  by_cases hmn : m ≤ n
  rw [← Finset.prod_range_mul_prod_Ico _ hmn]
  rw [← mul_sub_one]
  simp only [AbsoluteValue.map_mul, abs_prod]
  have A : ∏ i : ℕ in Finset.range m, Complex.abs (1 + F i x) ≤ C :=
    by
    apply le_trans _ (hCm hx)
    apply Finset.prod_le_prod
    intro i _
    apply Complex.abs.nonneg
    intro i _
    apply le_trans (Complex.abs.add_le _ _)
    simp
  have B : Complex.abs (∏ i : ℕ in Finset.Ico m n, (1 + F i x) - 1) ≤ δ :=
    by
    have HI := HN n m x hx
    simp only [and_imp] at HI
    have HI2 := HI hn hm hmn
    have := prod_le_prod_abs_Ico_ond_add (fun i : ℕ => F i x) n m
    simp at this
    apply le_trans this
    exact HI2
  have AB := mul_le_mul A B ?_ hCp.le
  apply lt_of_le_of_lt AB
  apply hδ.2
  apply Complex.abs.nonneg
  simp at hmn
  rw [← Finset.prod_range_mul_prod_Ico _ hmn.le]
  rw [← mul_one_sub]
  simp
  have A : ∏ i : ℕ in Finset.range n, Complex.abs (1 + F i x) ≤ C :=
    by
    apply le_trans _ (hCn hx)
    apply Finset.prod_le_prod
    intro i _
    apply Complex.abs.nonneg
    intro i _
    apply le_trans (Complex.abs.add_le _ _)
    simp
  have B : Complex.abs (∏ i : ℕ in Finset.Ico n m, (1 + F i x) - 1) ≤ δ :=
    by
    have HI := HN m n x hx
    simp only [and_imp] at HI
    have HI2 := HI hm hn hmn.le
    have := prod_le_prod_abs_Ico_ond_add (fun i : ℕ => F i x) m n
    simp at this
    apply le_trans this
    exact HI2
  have AB := mul_le_mul A B ?_ hCp.le
  rw [auxreal _]
  apply lt_of_le_of_lt AB
  apply hδ.2
  apply Complex.abs.nonneg
  exact hp
