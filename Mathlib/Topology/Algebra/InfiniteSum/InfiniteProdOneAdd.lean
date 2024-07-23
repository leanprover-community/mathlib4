
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

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


theorem unif_prod_bound3 (F : ι → α → ℂ)
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
  refine ⟨Real.exp T, ?_⟩
  simp [hexp]
  intro n x
  apply le_trans (prod_be_exp _ _)
  simp
  apply le_trans (HB n x)
  exact ht x

theorem unif_prod_bound (F : ℕ → ℂ → ℂ) (K : Set ℂ)
    (hb : ∃ T : ℝ, ∀ x : ℂ, x ∈ K → ∑' n : ℕ, Complex.abs (F n x) ≤ T)
    (hs : ∀ x : ℂ, Summable fun n : ℕ => Complex.abs (F n x)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℕ) (x : ℂ), x ∈ K → ∏ i in s, (1 + Complex.abs (F i x)) ≤ C :=
  by
  obtain ⟨T, ht⟩ := hb
  have HB :
    ∀ (s : Finset ℕ) (a : ℂ), ∑ i in s, Complex.abs (F i a) ≤ ∑' n : ℕ, Complex.abs (F n a) :=
    by
    intro n a
    apply sum_le_tsum
    intro b _
    apply Complex.abs.nonneg
    apply hs a
  have hexp : 0 < Real.exp T := by have := Real.exp_pos T; apply this
  refine ⟨Real.exp T, ?_⟩
  simp [hexp]
  intro n x hx
  apply le_trans (prod_be_exp _ _)
  simp
  apply le_trans (HB n x)
  exact ht x hx


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






lemma tenstoUniformlyOn_const_self {α β : Type*} (ι) [Preorder ι] [UniformSpace α] [UniformSpace β]
    (a : α → β) (K : Set α) : TendstoUniformlyOn (fun _: ι => a) a atTop K:= by
    refine TendstoUniformlyOnFilter.tendstoUniformlyOn ?_
    rw [tendstoUniformlyOnFilter_iff_tendsto]
    exact tendsto_diag_uniformity (fun x ↦ a x.2) (_ ×ˢ 𝓟 K)

theorem tsum_unif23 {α ι: Type*} [Preorder ι] [UniformSpace α] [AddCommMonoid α] [ AddGroup α]
    [UniformAddGroup α] (F : ι → α → ℂ) (K : Set α)
    (hf : TendstoUniformlyOn (fun n : Finset ι => fun a : α => ∑ i in n, (F i a))
        (fun a : α => ∑' n : ι, (F n a)) Filter.atTop K)
    (hs : ∀ x : α, x ∈ K →  Summable fun n : ι => (F n x)) :
    TendstoUniformlyOn (fun k : Finset ι => fun a : α => ∑' n : {x // x ∉ k}, (F (n) a)) 0 Filter.atTop K := by
  have := (tenstoUniformlyOn_const_self (Finset ι) (fun a : α => ∑' n : ι, (F n a)) K).sub hf
  simp only [sub_self] at this
  apply this.congr
  simp only [Pi.sub_apply, eventually_atTop, ge_iff_le]
  use ⊥
  intro b _
  intro x hx
  simp only [Pi.sub_apply]
  rw [← sum_add_tsum_compl (s :=b)]
  ring_nf
  congr
  exact hs x hx


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

/-
theorem sum_prod_unif_conv23 (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (K : Set  ℂ)
    (hf :
      TendstoUniformlyOn (fun n : Finset ℕ => fun a : ℂ => ∑ i in n, (F i a))
        (fun a : ℂ  => ∑' n : ℕ, (F n a)) Filter.atTop K)
    (hb : ∃ T : ℝ, ∀ x :  ℂ, x ∈ K → ∑' n : ℕ, Complex.abs (F n x) ≤ T)
    (hs : ∀ x :  K, Summable fun n : ℕ => (F n x))
    (hpp :  Multipliable fun n a => 1 + F n a):
    TendstoUniformlyOn (fun N : Finset ℕ => fun a :  ℂ => ∏ b in N, (1 + F b a))
      (fun x => ∏' n,  (fun a => 1 + F n a) x ) Filter.atTop
      K := by

  apply UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto _
  have := hpp.hasProd
  rw [HasProd] at this
  have ht := this.apply_nhds
  intro x hx

  convert ht x
  exact Eq.symm (Finset.prod_apply x _ fun c a ↦ 1 + F c a)
  exact Eq.symm (tprod_apply hpp)
  simp at hs
  have tt := (tsum_unif23  F K hf hs)
  have tt2 := tt.uniformCauchySeqOn
  have ft2 := hf.uniformCauchySeqOn
  rw [Metric.uniformCauchySeqOn_iff] at *
  intro ε hε

  obtain ⟨T, hT⟩ := hb
  have hdelta := exists_pos_mul_lt hε (Real.exp T)
  have tt3:= tt2 (Real.exp T) (by exact Real.exp_pos T)
  obtain ⟨δ, hδ⟩ := hdelta
  obtain ⟨ N1, hN1⟩ := tt3
  obtain ⟨ N2, hN2⟩ := ft2 δ hδ.1
  use N1 ⊔ N2
  intro n hn m hm x hx
  have hN1 := hN1 n ?_ m ?_ x hx
  have hN2 := hN2 n ?_ m ?_ x hx
  have AB := mul_le_mul hN1.le hN2.le (by exact dist_nonneg) (by exact Real.exp_nonneg T)
  rw [dist_eq_norm] at *




  --apply lt_of_le_of_lt AB



  sorry
  simp
-/



/-
theorem sum_prod_unif_conv2 (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (K : Set  ℂ)
    (hf :
      TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∑ i in Finset.range n, (F i a))
        (fun a : ℂ  => ∑' n : ℕ, (F n a)) Filter.atTop K)
    (hb : ∃ T : ℝ, ∀ x :  ℂ, x ∈ K → ∑' n : ℕ, Complex.abs (F n x) ≤ T)
    (hs : ∀ x :  K, Summable fun n : ℕ => (F n x))
    (hpp :  Multipliable fun n a => 1 + F n a):
    TendstoUniformlyOn (fun N :  ℕ => fun a :  ℂ => ∏ b in Finset.range N, (1 + F b a))
      (fun x => ∏' n,  (fun a => 1 + F n a) x ) Filter.atTop
      K := by

  apply UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto _
  have := hpp.hasProd
  rw [HasProd] at this
  have ht := this.apply_nhds
  intro x hx

  convert ht x
  exact Eq.symm (Finset.prod_apply x _ fun c a ↦ 1 + F c a)
  exact Eq.symm (tprod_apply hpp)
  simp at hs
  have tt := (tsum_unif2  F K hf hs)
  have tt2 := tt.uniformCauchySeqOn
  have ft2 := hf.uniformCauchySeqOn
  rw [Metric.uniformCauchySeqOn_iff] at *
  intro ε hε
  have tt3:= tt2 ε hε
  simp at *
  --have hdelta := exists_pos_mul_lt hε (Real.exp (∑' n : ℕ, Complex.abs (F n x)))



  sorry
-/

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
  refine ⟨N, ?_⟩
  intro n x hx _
  have hnn : N ≤ N := by rfl
  have HN2 := hN N hnn x hx
  simp_rw [dist_eq_norm] at *
  convert HN2
  norm_cast
  simp
  congr
  have hy := sum_add_tsum_nat_add N (hs x)
  simp at hy
  rw [← hy]
  ring

theorem abs_tsum (f : ℕ → ℂ) (h : Summable fun i : ℕ => Complex.abs (f i)) :
    Complex.abs (∑' i : ℕ, f i) ≤ ∑' i : ℕ, Complex.abs (f i) :=
  by
  rw [← Complex.norm_eq_abs]
  simp_rw [← Complex.norm_eq_abs]
  apply norm_tsum_le_tsum_norm
  exact h

theorem abs_tsum_of_poss (F : ℕ → ℂ → ℝ) (h : ∀ (n : ℕ) (c : ℂ), 0 ≤ F n c) :
    ∀ x : ℂ, |∑' i : ℕ, F i x| = ∑' i : ℕ, F i x :=
  by
  intro x
  simp only [abs_eq_self]
  apply tsum_nonneg
  intro b
  apply h b x

theorem abs_tsum_of_pos (F : ℕ → ℂ → ℂ) :
    ∀ (x : ℂ) (N : ℕ),
      Complex.abs (∑' i : ℕ, Complex.abs (F (i + N) x) : ℂ) = ∑' i : ℕ, Complex.abs (F (i + N) x) :=
  by
  intro x N
  have := abs_tsum_of_poss (fun n : ℕ => fun x : ℂ => Complex.abs (F (n + N) x)) ?_ x
  rw [← this]
  rw [←Complex.abs_ofReal _]
  congr
  norm_cast
  intro n c
  apply Complex.abs.nonneg


theorem add_eq_sub_add (a b c d : ℝ) : b = c - a + d ↔ a + b = c + d :=
  by
  constructor
  repeat'
    intro h
    linarith [h]

  theorem sum_subtype_le_tsum (f : ℕ → ℝ) (m n N : ℕ) (hmn : m ≤ n ∧ N ≤ m) (hg : ∀ b, 0 ≤ f b)
    (hf : Summable f) : ∑ i : ℕ in Finset.Ico m n, f i ≤ ∑' i : ℕ, f (i + N) :=
  by
  have h1 : ∑ i : ℕ in Finset.Ico m n, f i ≤ ∑ i : ℕ in Finset.Ico N n, f i :=
    by
    have := Finset.Ico_union_Ico_eq_Ico hmn.2 hmn.1
    rw [← this]
    rw [Finset.sum_union]
    simp
    apply Finset.sum_nonneg
    intro i _
    apply hg i
    exact Finset.Ico_disjoint_Ico_consecutive N m n
  apply le_trans h1
  have h2 : ∑' i : ℕ, f (i + N) = ∑ i : ℕ in Finset.Ico N n, f i + ∑' i : ℕ, f (i + n) :=
    by
    have hh1 := sum_add_tsum_nat_add N hf
    have hh2 := sum_add_tsum_nat_add n hf
    rw [← hh2] at hh1
    rw [← add_eq_sub_add] at hh1
    rw [hh1]
    simp
    have hNn : N ≤ n := le_trans hmn.2 hmn.1
    have := Finset.sum_range_add_sum_Ico f hNn
    rw [← this]
    simp
  rw [h2]
  simp
  apply tsum_nonneg
  intro b
  apply hg (b + n)

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

theorem prod_le_prod_abs (f : ℕ → ℂ) (n : ℕ) :
    Complex.abs (∏ i in Finset.range n, (f i + 1) - 1) ≤
      ∏ i in Finset.range n, (Complex.abs (f i) + 1) - 1 :=
  by
  induction' n with h n_ih
  simp  [Finset.range_zero, Finset.prod_empty, sub_self, AbsoluteValue.map_zero]
  have HH :
    ∏ i in Finset.range (h + 1 ), (f i + 1) - 1 =
      (∏ i in Finset.range h, (f i + 1) - 1) * (f h + 1) + f h :=
    by
    simp_rw [Finset.prod_range_succ]
    ring
  rw [HH]
  have H3 :
    Complex.abs ((∏ i in Finset.range h, (f i + 1) - 1) * (f h + 1) + f h) ≤
      Complex.abs ((∏ i in Finset.range h, (f i + 1) - 1) * (f h + 1)) + Complex.abs (f h) :=
    by
    apply le_trans (Complex.abs.add_le _ _)
    simp
  apply le_trans H3
  have H4 :
    Complex.abs ((∏ i in Finset.range h, (f i + 1) - 1) * (f h + 1)) + Complex.abs (f h) ≤
      (∏ i in Finset.range h, (Complex.abs (f i) + 1) - 1) * (Complex.abs (f h) + 1) +
        Complex.abs (f h) :=
    by
    simp only [AbsoluteValue.map_mul, add_le_add_iff_right]
    have h1 :
      Complex.abs (∏ i in Finset.range h, (f i + 1) - 1) ≤
        ∏ i in Finset.range h, (Complex.abs (f i) + 1) - 1 :=
      by apply n_ih
    have h2 : Complex.abs (f h + 1) ≤ Complex.abs (f h) + 1 :=
      by
      apply le_trans (Complex.abs.add_le _ _)
      simp [AbsoluteValue.map_one]
    apply mul_le_mul h1 h2
    apply Complex.abs.nonneg
    apply le_trans _ n_ih
    apply Complex.abs.nonneg
  apply le_trans H4
  ring_nf
  conv =>
    enter [2,2,1,1]
    rw [add_comm]
  rw [Finset.prod_range_succ]
  rw [mul_comm]
  simp
  norm_cast
  simp
  linarith

theorem prod_le_prod_abs_Ico (f : ℕ → ℂ) (n m : ℕ) :
    Complex.abs (∏ i in Finset.Ico m n, (f i + 1) - 1) ≤
      ∏ i in Finset.Ico m n, (Complex.abs (f i) + 1) - 1 :=
  by
  simp_rw [Finset.prod_Ico_eq_prod_range]
  apply prod_le_prod_abs

theorem prod_le_prod_abs_Ico_ond_add (f : ℕ → ℂ) (n m : ℕ) :
    Complex.abs (∏ i in Finset.Ico m n, (1 + f i) - 1) ≤
      ∏ i in Finset.Ico m n, (1 + Complex.abs (f i)) - 1 :=
  by
  have := prod_le_prod_abs_Ico f n m
  norm_cast at *
  simp at *
  have h:(∏ i in Finset.Ico m n, (1 + f i) - 1) =(∏ i in Finset.Ico m n, (f i+ 1) - 1) := by
    congr
    ext1
    ring
  rw [h]
  have h2 : ∏ x in Finset.Ico m n, (1 + Complex.abs (f x)) - 1 = ∏ x in Finset.Ico m n,
    (Complex.abs (f x)+1) - 1 := by
    congr
    ext1
    ring
  rw [h2]
  apply this


theorem sum_prod_unif_conv (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (K : Set ℂ)
    (hf :
      TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∑ i in Finset.range n, Complex.abs (F i a))
        (fun a : ℂ => ∑' n : ℕ, Complex.abs (F n a)) Filter.atTop K)
    (hb : ∃ T : ℝ, ∀ x : ℂ, x ∈ K → ∑' n : ℕ, Complex.abs (F n x) ≤ T)
    (hs : ∀ x : ℂ, Summable fun n : ℕ => Complex.abs (F n x))
    (hp :
      ∀ x : ℂ, x ∈ K → Tendsto (fun n : ℕ => ∏ i in Finset.range n, (1 + F i x)) atTop (𝓝 (g x))) :
    TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∏ i in Finset.range n, (1 + F i a)) g Filter.atTop
      K := by
  apply UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto _ hp
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have H := tsum_unifo F K hf hs
  have H2 := unif_prod_bound F K hb hs
  obtain ⟨C, hCp, hC⟩ := H2
  have hdelta := exists_pos_mul_lt hε C
  obtain ⟨δ, hδ⟩ := hdelta
  have HH := H δ hδ.1
  obtain ⟨N, HN⟩ := HH
  refine ⟨N, ?_⟩
  intro n hn m hm x hx
  have hCm := hC (Finset.range m) x
  have hCn := hC (Finset.range n) x
  rw [dist_eq_norm]
  simp only [norm_eq_abs]
  wlog hmn : m ≤ n generalizing n m

  sorry
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



/-


theorem tsum_unifo2 (F : ℕ → ℂ → ℂ) (K : Set ℂ)
    (hf :
      TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∑ i in Finset.range n, (F i a))
        (fun a : ℂ => ∑' n : ℕ,  (F n a)) Filter.atTop K)
    (hs : ∀ x ∈ K, Summable fun n : ℕ =>  (F n x)) :
    UniformCauchySeqOn (fun n : ℕ => fun a : ℂ => (∏ i in Finset.range n, (1 + F (i) a)))
        Filter.atTop K :=by
    rw [Metric.uniformCauchySeqOn_iff]
    sorry

theorem sum_prod_unif_convf (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (K : Set ℂ)
    (hf :
      TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∑ i in Finset.range n,  (F i a))
        (fun a : ℂ => ∑' n : ℕ,  (F n a)) Filter.atTop K)
    (hb : ∃ T : ℝ, ∀ x : ℂ, x ∈ K → ∑' n : ℕ, Complex.abs (F n x) ≤ T)
    (hs : ∀ x ∈ K, Summable fun n : ℕ =>  (F n x))
    (hp :
      ∀ x : ℂ, x ∈ K → Tendsto (fun n : ℕ => ∏ i in Finset.range n, (1 + F i x)) atTop (𝓝 (g x))) :
    TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∏ i in Finset.range n, (1 + F i a)) g Filter.atTop
      K := by
    apply UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto _ hp
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    simp [dist_eq_norm]
    have H := tsum_unif2 F K hf hs
    rw [Metric.tendstoUniformlyOn_iff] at H
    simp at H
    obtain ⟨T, hT⟩ := hb
    have hdelta := exists_pos_mul_lt hε (Real.exp T)
    obtain ⟨δ, hδ⟩ := hdelta
    obtain ⟨N, HN⟩ := H δ hδ.1
    use N
    intro n hn m hm x hx
    wlog hmn : m ≤ n generalizing n m
    simp at hmn

    sorry

    rw [← Finset.prod_range_mul_prod_Ico _ hmn, ← mul_sub_one]
    simp only [AbsoluteValue.map_mul, abs_prod]

    sorry



-/


lemma logbound (z : ℂ) (hz : Complex.abs z ≤ 1/2) :
    Complex.abs (Complex.log (1 + z)) ≤ (3/2) * Complex.abs z := by sorry

lemma A1 {α : Type* } (f : ℕ → α → ℂ) (hf : Summable f) :
    TendstoUniformly (fun n : ℕ => fun a : α => ∑ i in Finset.range n, Complex.log (1 + (f i a)))
        (fun a : α => ∑' n : ℕ, Complex.log (1 + (f n a))) Filter.atTop := by sorry

variable (f : ℕ → ℂ → ℂ)



lemma A2  (f : ℕ → ℂ → ℂ) (hf : ∀ x : ℂ,  Summable fun n => Complex.log (1 + (f n x))) :
  (Complex.exp ∘ (fun a : ℂ =>   (∑' n : ℕ, Complex.log (1 + (f n a))))) =
    (fun a : ℂ => ∏' n : ℕ, (1 + (f n a))) := by
  ext a
  have := (hf a).hasSum.cexp
  apply (HasProd.tprod_eq ?_).symm

  apply this.congr
  intro b
  congr
  ext a
  simp
  apply Complex.exp_log
  sorry


lemma A4 (a: ℝ) : UniformContinuousOn cexp {x : ℂ | x.re ≤ a} := by
rw [Metric.uniformContinuousOn_iff]
intro ε hε
have : Continuous (cexp - 1) := by
  apply Continuous.sub
  apply Continuous.cexp
  exact continuous_id'
  exact continuous_one
rw [Metric.continuous_iff'] at this
simp at this
have ha : 0 < ε/(2*(Real.exp a)) := by
  have := inv_pos.mpr (Real.exp_pos a)
  ring_nf
  nlinarith
have H := this 0 (ε/(2* Real.exp a)) ha
rw [Metric.eventually_nhds_iff] at H
obtain ⟨δ, hδ⟩ := H
refine ⟨δ, hδ.1, ?_⟩
intros x _ y hy hxy
have h3 := hδ.2 (y := x -y) (by simpa using hxy)
rw [dist_eq_norm] at *
rw [ exp_zero] at h3
have : cexp x - cexp y = cexp y * (cexp (x - y) - 1) := by
    ring_nf
    rw [← exp_add]
    ring_nf
rw [this]
have hya : ‖(cexp y)‖ ≤ Real.exp a := by
  simp [Complex.abs_exp ]
  exact hy
simp only [norm_mul, gt_iff_lt]
simp at *
rw [Complex.abs_exp ] at *
have AB := mul_le_mul h3.le hya (by  exact Real.exp_nonneg y.re) (by linarith)
rw [mul_comm]
apply lt_of_le_of_lt AB
have hrr : ε / (2 * a.exp) * a.exp = ε / 2 := by
  field_simp
  ring
rw [hrr]
linarith


theorem UniformContinuousOn.comp_tendstoUniformlyOn (s : Set ℂ) (F : ℕ → ℂ → s) (f : ℂ → s) {g : ℂ → ℂ}
    (hg : UniformContinuousOn g s) (h : TendstoUniformlyOn F f atTop s) :
    TendstoUniformlyOn (fun i => fun x =>  g  (F i x)) (fun x => g (f x)) atTop s := by
  rw [uniformContinuousOn_iff_restrict] at hg
  apply (UniformContinuous.comp_tendstoUniformlyOn hg h)

theorem UniformContinuousOn.comp_tendstoUniformly (s K : Set ℂ) (F : ℕ → K → s) (f : K → s) {g : ℂ → ℂ}
    (hg : UniformContinuousOn g s) (h : TendstoUniformly F f atTop) :
    TendstoUniformly (fun i => fun x =>  g  (F i x)) (fun x => g (f x)) atTop := by
  rw [uniformContinuousOn_iff_restrict] at hg
  apply (UniformContinuous.comp_tendstoUniformly hg h)

lemma A33 (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (K : Set ℂ) (T : ℝ) (hf : TendstoUniformlyOn f g atTop K)
 (hg : ∀ x : ℂ, x ∈ K → (g x).re ≤ T) : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (n : ℕ) (x : ℂ), x ∈ K → N ≤ n →
   (f n x).re ≤ T + ε := by
  intro ε hε
  rw [Metric.tendstoUniformlyOn_iff] at hf
  simp at hf
  have hf2 := hf ε hε
  obtain ⟨N, hN⟩ := hf2
  use N
  intro n x hx hn
  have hN2 := hN n hn x hx
  simp [dist_eq_norm] at hN2
  rw [AbsoluteValue.map_sub] at hN2
  have := Complex.abs_re_le_abs ((f n x)- g x)
  have h3 := le_of_abs_le this
  have h4 := le_trans h3 hN2.le
  simp at h4
  apply le_trans h4
  have := hg x hx
  linarith


lemma A3 (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (K : Set ℂ) (hf : TendstoUniformlyOn f g atTop K)
  (hg : ∃ T : ℝ, ∀ x : ℂ, x ∈ K → (g x).re ≤ T) :
    TendstoUniformlyOn (fun n => fun x => cexp (f n x)) (cexp ∘ g) atTop K := by
  obtain ⟨T, hT⟩ := hg
  have := A33 f g K T hf hT
  rw [Metric.tendstoUniformlyOn_iff] at *
  simp at *
  have ht := this 1 (by exact Real.zero_lt_one)
  obtain ⟨δ, hδ⟩ := ht
  let F : ℕ → K → {x : ℂ | x.re ≤ T + 1} := fun n => fun x => ⟨f (n + δ) x, by
    have := hδ (n + δ) x x.2
    simp at this
    exact this⟩
  let G : K → {x : ℂ | x.re ≤ T + 1} := fun x => ⟨g x, by
    simp
    apply le_trans (hT x x.2)
    linarith⟩
  have wish : TendstoUniformly F G atTop := by
    rw [Metric.tendstoUniformly_iff]
    simp [F, G]
    intro ε hε
    have hff := hf ε hε
    obtain ⟨N2, hN2⟩ := hff
    use (max N2 δ) - δ
    intro n hn x hx
    have hN2 := hN2 (n + δ)
    rw [@Nat.sub_le_iff_le_add] at hn
    apply hN2
    apply le_trans ?_ hn
    exact Nat.le_max_left N2 δ
    apply hx
  have w2 := UniformContinuousOn.comp_tendstoUniformly  {x : ℂ | x.re ≤ T + 1} K F G (A4 (T + 1))
    wish
  simp [F,G] at w2
  rw [Metric.tendstoUniformly_iff] at *
  simp at w2
  intro ε hε
  have w3 := w2 ε hε
  obtain ⟨N2, hN2⟩ := w3
  use N2 + δ
  intro b hb x hx
  have : ∃ b' : ℕ, b = b' + δ ∧ N2 ≤ b' := by
    rw [@le_iff_exists_add] at hb
    obtain ⟨c, hc⟩ := hb
    use N2 + c
    simp only [hc, le_add_iff_nonneg_right, zero_le, and_true]
    group
  obtain ⟨b', hb', hb''⟩ := this
  rw [hb']
  apply hN2 b' hb'' x hx


lemma A3w (f : ℕ → ℂ → ℂ) (K : Set ℂ) (h : ∀ x : ℂ,  Summable fun n => Complex.log (1 + (f n x)))
    (hf : TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∑ i in Finset.range n, Complex.log (1 + (f i a)))
      (fun a : ℂ => ∑' n : ℕ, Complex.log (1 + (f n a))) Filter.atTop K)
  (hb : ∀ i : ℕ, ∀ x : ℂ, x ∈ K → ((1 + f i x) ≠ 0))
  (hg : ∃ T : ℝ, ∀ x : ℂ, x ∈ K → (∑' n : ℕ, Complex.log (1 + (f n x))).re ≤ T) :
    TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∏ i in Finset.range n, (1 + f i a))
      (fun a => ∏' i, (1 + f i a)) atTop K := by
  have := A3 (fun n : ℕ => fun a : ℂ => ∑ i in Finset.range n, (Complex.log (1 + (f i a))))
    (fun a : ℂ =>(∑' n : ℕ, Complex.log (1 + (f n a)))) K hf hg
  have := TendstoUniformlyOn.congr this
    (F' := (fun n : ℕ => fun a : ℂ => ∏ i in Finset.range n, (1 + (f i a))))
  have hr := A2 f h
  rw [← hr]
  apply this
  simp
  use 0
  simp
  intro b
  intro x hx
  simp
  rw [@exp_sum]
  congr
  ext y
  apply Complex.exp_log
  exact hb y x hx

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


lemma prodd (x : ℂ) (h0 : x ≠ 0) :
  ( ∏' i : ℕ, (1 + -x ^ 2 / (↑i + 1) ^ 2)) = (((fun t : ℂ => sin (↑π * t) / (↑π * t)) x)) := by
  rw [← Multipliable.hasProd_iff]
  rw [Multipliable.hasProd_iff_tendsto_nat]
  have := euler_sin_prod' x h0
  simp at this
  apply this
  sorry
  sorry

lemma log_of_summable (f : ℕ → ℂ) (hf : Summable f) :
    Summable (fun n : ℕ => Complex.log (1 + f n)) := by
  -- summable_norm_iff
  --rw [← summable_abs_iff ] at hf
  --apply Summable.of_norm
/-   have hff : Summable (fun n => fun x => Complex.abs (f n x)) := by
    --apply summable_abs_iff.mpr hf
    sorry
  have := Summable.of_norm_bounded (E := ℂ) (fun n => fun x => Complex.abs (f n x)) hff
 -/
  have hff : Summable (fun n => Complex.abs (f n)) := by
    sorry
  apply  Summable.of_norm_bounded (fun n => Complex.abs (f n)) hff
  intro n
  simp
  --have := Complex.norm_log_one_add_sub_self_le




  sorry



local notation "ℍ'" => {z : ℂ | 0 < Complex.im z}

theorem tendsto_locally_uniformly_euler_sin_prod' (z : ℍ') (r : ℝ) (hr : 0 < r) :
    TendstoUniformlyOn (fun n : ℕ => fun z : ℂ => ∏ j in Finset.range n, (1 + -z ^ 2 / (j + 1) ^ 2))
      (fun x => ( ∏' i : ℕ, (1 + -x ^ 2 / (↑i + 1) ^ 2))) atTop (Metric.ball z r ∩ ℍ') := by
  apply A3w

  sorry
  sorry
  sorry
  sorry


/- lemma fin0 (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (K : Set ℂ) (hf :
    TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∑ i in Finset.range n, (f i a))
      (fun a : ℂ => ∑' n : ℕ, (f n a)) Filter.atTop K)
    (hp : ∀ x : ℂ, x ∈ K → Tendsto
      (fun n : ℕ => ∏ i in Finset.range n, (1 + f i x)) atTop (𝓝 (g x)))
    (hb : ∃ T : ℝ, ∀ x : ℂ, x ∈ K → ∑' n : ℕ, Complex.abs (f n x) ≤ T) :
    TendstoUniformlyOn (fun n : ℕ =>
      fun a : ℂ => ∏ i in Finset.range n, (1 + f i a)) g Filter.atTop K := by


    sorry

lemma fin (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (K : Set ℂ) (hf :
    TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∑ i in Finset.range n, (f i a))
      (fun a : ℂ => ∑' n : ℕ, (f n a)) Filter.atTop K)
    (hp : ∀ x : ℂ, x ∈ K → Tendsto
      (fun n : ℕ => ∏ i in Finset.range n, (1 + f i x)) atTop (𝓝 (g x)))
    (hb : ∃ T : ℝ, ∀ x : ℂ, x ∈ K → ∑' n : ℕ, Complex.abs (f n x) ≤ T) :
    TendstoUniformlyOn (fun n : ℕ =>
      fun a : ℂ => ∏ i in Finset.range n, (1 + f i a)) g Filter.atTop K := by
    --have := tsum_unif2 f K hf
    /- rw [Metric.tendstoUniformlyOn_iff] at hf
    simp only [gt_iff_lt, eventually_atTop, ge_iff_le] at hf
    have hf2 := hf ((1 : ℝ)/2) (one_half_pos)
    obtain ⟨N0, hN0⟩ := hf2 -/
    have A : ∃  n : ℕ, ∀ m : ℕ, m ≤ n → ∀ x : ℂ, x ∈ K →  Complex.abs (f m x) ≤ (1/2) := by sorry
    obtain ⟨n0, hn0⟩ := A

    sorry
 -/
