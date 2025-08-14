import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.NormedSpace.MultipliableUniformlyOn
import Mathlib.Data.Complex.FiniteDimensional


open  UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical



local notation "𝕢" => Periodic.qParam

local notation "𝕢₁" => Periodic.qParam 1

noncomputable abbrev eta_q (n : ℕ) (z : ℂ) := (𝕢₁ z) ^ (n + 1)

lemma eta_q_eq_exp (n : ℕ) (z : ℂ) : eta_q n z = cexp (2 * π * Complex.I * (n + 1) * z) := by
  simp [eta_q, Periodic.qParam, ← Complex.exp_nsmul]
  ring_nf

lemma eta_q_eq_pow (n : ℕ) (z : ℂ) : eta_q n z = cexp (2 * π * Complex.I * z) ^ (n + 1) := by
  simp [eta_q, Periodic.qParam]

theorem qParam_lt_one (z : ℍ) (r : ℝ) (hr : 0 < r) :
    ‖𝕢 r z‖ < 1 := by
  simp [Periodic.qParam, norm_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero,
    sub_zero, Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re,
    coe_im, zero_sub, Real.exp_lt_one_iff]
  rw [neg_div, neg_lt_zero]
  positivity

lemma one_sub_qParam_ne_zero (r : ℝ) (hr : 0 < r) (z : ℍ) : 1 - 𝕢 r z ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have := qParam_lt_one z r
  rw [← h] at this
  simp [lt_self_iff_false] at *
  linarith

lemma one_add_eta_q_ne_zero (n : ℕ) (z : ℍ) : 1 - eta_q n z ≠ 0 := by
  rw [eta_q_eq_exp, sub_ne_zero]
  intro h
  have := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨(n + 1) • z, by
    have : 0 < (n + 1 : ℝ) := by linarith
    simpa [this] using z.2⟩
  simp [← mul_assoc] at this
  rw [← h] at this
  simp only [norm_one, lt_self_iff_false] at *

noncomputable abbrev etaProdTerm (z : ℂ) := ∏' (n : ℕ), (1 - eta_q n z)

local notation "ηₚ" => etaProdTerm

/- The eta function. Best to define it on all of ℂ since we want to take its logDeriv. -/
noncomputable def ModularForm.eta (z : ℂ) := (𝕢 24 z) * ηₚ z

local notation "η" => ModularForm.eta

theorem Summable_eta_q (z : ℍ) : Summable fun n : ℕ ↦ ‖-eta_q n z‖ := by
    simp_rw  [eta_q, eta_q_eq_pow, norm_neg, norm_pow, summable_nat_add_iff 1]
    simp only [summable_geometric_iff_norm_lt_one, norm_norm]
    apply UpperHalfPlane.norm_exp_two_pi_I_lt_one z

@[fun_prop]
lemma qParam_differentiable (n : ℝ) : Differentiable ℂ (𝕢 n) := by
    rw [show 𝕢 n = fun x => exp (2 * π * Complex.I * x / n)  by rfl]
    fun_prop

@[fun_prop]
lemma qParam_ContDiff (n : ℝ) (m : WithTop ℕ∞) : ContDiff ℂ m (𝕢 n) := by
    rw [show 𝕢 n = fun x => exp (2 * π * Complex.I * x / n)  by rfl]
    fun_prop

lemma hasProdLocallyUniformlyOn_eta :
    HasProdLocallyUniformlyOn (fun n a ↦ 1 - eta_q n a) ηₚ {x | 0 < x.im} := by
  simp_rw [sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact (isOpen_lt continuous_const Complex.continuous_im)
  intro K hK hcK
  by_cases hN : ¬ Nonempty K
  · rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
    simpa [not_nonempty_iff_eq_empty'.mp hN] using tendstoUniformlyOn_empty
  have hc : ContinuousOn (fun x ↦ ‖cexp (2 * ↑π * Complex.I * x)‖) K := by fun_prop
  obtain ⟨z, hz, hB, HB⟩ := IsCompact.exists_sSup_image_eq_and_ge hcK (by simpa using hN) hc
  apply Summable.hasProdUniformlyOn_nat_one_add hcK (Summable_eta_q ⟨z, by simpa using (hK hz)⟩)
  · filter_upwards with n x hx
    simpa only [eta_q, eta_q_eq_pow n x, norm_neg, norm_pow, coe_mk_subtype,
        eta_q_eq_pow n (⟨z, hK hz⟩ : ℍ)] using
        pow_le_pow_left₀ (by simp [norm_nonneg]) (HB x hx) (n + 1)
  · simp_rw [eta_q, Periodic.qParam]
    fun_prop

lemma tprod_ne_zero' {ι α : Type*} (x : α) (f : ι → α → ℂ) (hf : ∀ i x, 1 + f i x ≠ 0)
  (hu : ∀ x : α, Summable fun n => f n x) : (∏' i : ι, (1 + f i) x) ≠ 0 := by
  simp only [Pi.add_apply, Pi.one_apply, ne_eq]
  rw [← Complex.cexp_tsum_eq_tprod (f := fun n => 1 + f n x) (fun n => hf n x)]
  · simp only [exp_ne_zero, not_false_eq_true]
  · exact Complex.summable_log_one_add_of_summable (hu x)

theorem etaProdTerm_ne_zero (z : ℍ) : ηₚ z ≠ 0 := by
  simp only [etaProdTerm, eta_q, ne_eq]
  refine tprod_ne_zero' z (fun n x => -eta_q n x) ?_ ?_
  · refine fun i x => by simpa using one_add_eta_q_ne_zero i x
  · intro x
    simpa [eta_q, ←summable_norm_iff] using Summable_eta_q x

/--Eta is non-vanishing!-/
lemma eta_nonzero_on_UpperHalfPlane (z : ℍ) : η z ≠ 0 := by
  simpa [ModularForm.eta, Periodic.qParam] using etaProdTerm_ne_zero z

/-
lemma differentiable_eta_q (n : ℕ) : Differentiable ℂ (eta_q n) := by
  rw [show eta_q n = fun x => -exp (2 * π * Complex.I * x) ^ (n + 1) by
      ext z; exact eta_q_eq_pow n z]
  fun_prop -/

lemma logDeriv_one_sub_cexp (r : ℂ) : logDeriv (fun z ↦ 1 - r * cexp z) =
    fun z ↦ -r * cexp z / (1 - r * cexp ( z)) := by
  ext z
  simp [logDeriv]

lemma logDeriv_one_sub_mul_cexp_comp (r : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    logDeriv ((fun z ↦ 1 - r * cexp z) ∘ g) =
    fun z ↦ -r * (deriv g z) * cexp (g z) / (1 - r * cexp (g z)) := by
  ext y
  rw [logDeriv_comp (by fun_prop) (hg y), logDeriv_one_sub_cexp]
  ring


theorem one_add_eta_logDeriv_eq (z : ℂ) (i : ℕ) :
  logDeriv (fun x ↦ 1 - eta_q i x) z = 2 * ↑π * Complex.I * (↑i + 1) * -eta_q i z / (1 - eta_q i z) := by
  have h2 : (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) =
      ((fun z ↦ 1 - 1 * cexp z) ∘ fun x ↦ 2 * ↑π * Complex.I * (↑i + 1) * x) := by aesop
  have h3 : deriv (fun x : ℂ ↦ (2 * π * Complex.I * (i + 1) * x)) =
        fun _ ↦ 2 * π * Complex.I * (i + 1) := by
      ext y
      simpa using deriv_const_mul (2 * π * Complex.I * (i + 1)) (d := fun (x : ℂ) => x) (x := y)
  simp_rw [eta_q_eq_exp, h2, logDeriv_one_sub_mul_cexp_comp 1
    (g := fun x => (2 * π * Complex.I * (i + 1) * x)) (by fun_prop), h3]
  simp

lemma tsum_log_deriv_eta_q (z : ℂ) :
  ∑' (i : ℕ), logDeriv (fun x ↦ 1 - eta_q i x) z =
  ∑' n : ℕ, (2 * ↑π * Complex.I * (n + 1)) * (-eta_q n z) / (1  - eta_q n z) := by
  refine tsum_congr (fun i => ?_)
  apply one_add_eta_logDeriv_eq

lemma tsum_log_deriv_eta_q' (z : ℂ) :
  ∑' (i : ℕ), logDeriv (fun x ↦ 1 - eta_q i x) z =
   (2 * ↑π * Complex.I) * ∑' n : ℕ, (n + 1) * (-eta_q n z) / (1  - eta_q n z) := by
  rw [tsum_log_deriv_eta_q z, ← tsum_mul_left]
  congr 1
  ext i
  ring

lemma logDeriv_q (n : ℝ) (z : ℂ) : logDeriv (𝕢 n) z = 2 * ↑π * Complex.I / n := by
  have : (𝕢 n) = (fun z ↦ cexp (z)) ∘ (fun z => (2 * ↑π * Complex.I / n) * z)  := by
    ext y
    simp only [Periodic.qParam, comp_apply]
    ring_nf
  rw [this, logDeriv_comp (by fun_prop) (by fun_prop), deriv_const_mul _ (by fun_prop)]
  simp [LogDeriv_exp]

lemma logDeriv_z_term (z : ℍ) : logDeriv (𝕢 24) ↑z  =  2 * ↑π * Complex.I / 24 := by
  have : (𝕢 24) = (fun z ↦ cexp (z)) ∘ (fun z => (2 * ↑π * Complex.I / 24) * z)  := by
    ext y
    simp only [Periodic.qParam, ofReal_ofNat, comp_apply]
    ring_nf
  rw [this, logDeriv_comp (by fun_prop) (by fun_prop), deriv_const_mul _ (by fun_prop)]
  simp [LogDeriv_exp]


theorem etaProdTerm_differentiableAt (z : ℍ) : DifferentiableAt ℂ ηₚ ↑z := by
  have hD := hasProdLocallyUniformlyOn_eta.tendstoLocallyUniformlyOn_finsetRange.differentiableOn ?_
    (isOpen_lt continuous_const Complex.continuous_im)
  · rw [DifferentiableOn] at hD
    apply (hD z (by apply z.2)).differentiableAt
    · apply IsOpen.mem_nhds  (isOpen_lt continuous_const Complex.continuous_im) z.2
  · filter_upwards with b y
    apply (DifferentiableOn.finset_prod (u := Finset.range b)
      (f := fun i x => 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x))
      (by fun_prop)).congr
    intro x hx
    simp [sub_eq_add_neg, eta_q_eq_exp]

lemma eta_DifferentiableAt_UpperHalfPlane (z : ℍ) : DifferentiableAt ℂ eta ↑z := by
  apply DifferentiableAt.mul (by fun_prop) (etaProdTerm_differentiableAt z)

theorem logDeriv_tprod_eq_tsum {ι : Type*} {s : Set ℂ} (hs : IsOpen s) (x : s) {f : ι → ℂ → ℂ}
    (hf : ∀ i, f i x ≠ 0) (hd : ∀ i : ι, DifferentiableOn ℂ (f i) s)
    (hm : Summable fun i ↦ logDeriv (f i) ↑x) (htend : MultipliableLocallyUniformlyOn f s)
    (hnez : ∏' (i : ι), f i x ≠ 0) : logDeriv (∏' i : ι, f i ·) x = ∑' i : ι, logDeriv (f i) x := by
    apply symm
    rw [← Summable.hasSum_iff hm, HasSum]
    have := logDeriv_tendsto (f := fun (n : Finset ι) ↦ ∏ i ∈ n, (f i))
      (g := (∏' i : ι, f i ·)) (s := s) hs (p := atTop)
    simp only [eventually_atTop, ge_iff_le, ne_eq, forall_exists_index, Subtype.forall] at this
    conv =>
      enter [1]
      ext n
      rw [← logDeriv_prod _ _ _ (by intro i hi; apply hf i)
        (by intro i hi; apply (hd i x x.2).differentiableAt; exact IsOpen.mem_nhds hs x.2)]
    apply (this x x.2 ?_ ⊥ ?_ hnez).congr
    · intro m
      congr
      aesop
    · convert hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
        htend.hasProdLocallyUniformlyOn
      simp
    · intro b hb z hz
      apply DifferentiableAt.differentiableWithinAt
      have hp : ∀ (i : ι), i ∈ b → DifferentiableAt ℂ (f i) z := by
        exact fun i hi ↦ (hd i z hz).differentiableAt (IsOpen.mem_nhds hs hz)
      simpa using  DifferentiableAt.finset_prod hp

/- lemma eta_logDeriv (z : ℍ) : logDeriv ModularForm.eta z = (π * Complex.I / 12) * E₂ z := by
  unfold ModularForm.eta etaProdTerm
  rw [logDeriv_mul (UpperHalfPlane.coe z) _ (etaProdTerm_ne_zero z) _
    (etaProdTerm_differentiableAt z)]
  · have HG := logDeriv_tprod_eq_tsum (isOpen_lt continuous_const Complex.continuous_im) z
      (fun n x => 1 - eta_q n x) (fun i ↦ one_add_eta_q_ne_zero i z) ?_ ?_ ?_ (etaProdTerm_ne_zero z)
    rw [show z.1 = UpperHalfPlane.coe z by rfl] at HG
    rw [HG]
    · simp only [tsum_log_deriv_eta_q' z, E₂, logDeriv_z_term z, mul_neg, one_div, mul_inv_rev, Pi.smul_apply, smul_eq_mul]
      rw [G2_q_exp'', riemannZeta_two, ← (tsum_eq_tsum_sigma_pos'' z), mul_sub, sub_eq_add_neg, mul_add]
      conv =>
        enter [1,2,2,1]
        ext n
        rw [neg_div, neg_eq_neg_one_mul]
      rw [tsum_mul_left]
      have hpi : (π : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
      congr 1
      · ring_nf
        field_simp
        ring
      · field_simp
        ring_nf
        congr
        ext n
        ring_nf
    · intro i x hx
      simp_rw [eta_q_eq_exp]
      fun_prop
    · simp only [mem_setOf_eq, one_add_eta_logDeriv_eq]
      apply ((summable_nat_add_iff 1).mpr ((logDeriv_q_expo_summable (𝕢₁ z)
        (by simpa [Periodic.qParam] using exp_upperHalfPlane_lt_one z)).mul_left (-2 * π * Complex.I))).congr
      intro b
      have := one_add_eta_q_ne_zero b z
      simp only [UpperHalfPlane.coe, ne_eq, neg_mul, Nat.cast_add, Nat.cast_one, mul_neg] at *
      field_simp
      left
      ring
    · use ηₚ
      apply (hasProdLocallyUniformlyOn_eta).congr
      exact fun n ⦃x⦄ hx ↦ Eq.refl ((fun b ↦ ∏ i ∈ n, (fun n a ↦ 1 - eta_q n a) i b) x)
  · simp [ne_eq, exp_ne_zero, not_false_eq_true, Periodic.qParam]
  · fun_prop -/

/- lemma eta_logDeriv_eql (z : ℍ) : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z =
  (logDeriv ((csqrt) * η)) z := by
  have h0 : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z = ((z :ℂ)^(2 : ℤ))⁻¹ * (logDeriv η) (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    rw [logDeriv_comp, mul_comm]
    congr
    conv =>
      enter [1,1]
      intro z
      rw [neg_div]
      simp
    simp only [deriv.fun_neg', deriv_inv', neg_neg, inv_inj]
    norm_cast
    · simpa only using
      eta_DifferentiableAt_UpperHalfPlane (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)
    conv =>
      enter [2]
      ext z
      rw [neg_div]
      simp
    apply DifferentiableAt.neg
    apply DifferentiableAt.inv
    simp only [differentiableAt_fun_id]
    exact ne_zero z
  rw [h0, show ((csqrt) * η) = (fun x => (csqrt) x * η x) by rfl, logDeriv_mul]
  nth_rw 2 [logDeriv_apply]
  unfold csqrt
  have := csqrt_deriv z
  rw [this]
  simp only [one_div, neg_mul, smul_eq_mul]
  nth_rw 2 [div_eq_mul_inv]
  rw [← Complex.exp_neg, show 2⁻¹ * cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)) =
   (cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)))* 2⁻¹ by ring, ← Complex.exp_add,
   ← sub_eq_add_neg, show -(2⁻¹ * Complex.log ↑z) - 2⁻¹ * Complex.log ↑z = -Complex.log ↑z by ring, Complex.exp_neg, Complex.exp_log, eta_logDeriv z]
  have Rb := eta_logDeriv (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)
  simp only [coe_mk_subtype] at Rb
  rw [Rb]
  have E := E₂_transform z
  simp only [one_div, neg_mul, smul_eq_mul, SL_slash_def,
    modular_S_smul,
    ModularGroup.denom_S, Int.reduceNeg, zpow_neg] at *
  have h00 :  (UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos) = (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    simp [UpperHalfPlane.mk]
    ring_nf
  rw [h00] at E
  rw [← mul_assoc, mul_comm, ← mul_assoc]
  simp only [UpperHalfPlane.coe] at *
  rw [E, add_mul, add_comm]
  congr 1
  have hzne := ne_zero z
  have hI : Complex.I ≠ 0 := by
    exact I_ne_zero
  have hpi : (π : ℂ) ≠ 0 := by
    simp only [ne_eq, ofReal_eq_zero]
    exact Real.pi_ne_zero
  simp [UpperHalfPlane.coe] at hzne ⊢
  field_simp
  ring
  rw [mul_comm]
  · simpa only [UpperHalfPlane.coe, ne_eq] using (ne_zero z)
  · simp only [csqrt, one_div, ne_eq, Complex.exp_ne_zero, not_false_eq_true]
  · apply eta_nonzero_on_UpperHalfPlane z
  · unfold csqrt
    rw [show (fun a ↦ cexp (1 / 2 * Complex.log a)) = cexp ∘ (fun a ↦ 1 / 2 * Complex.log a) by rfl]
    apply DifferentiableAt.comp
    simp
    apply DifferentiableAt.const_mul
    apply Complex.differentiableAt_log
    rw [@mem_slitPlane_iff]
    right
    have hz := z.2
    simp  at hz
    exact Ne.symm (ne_of_lt hz)
  · apply eta_DifferentiableAt_UpperHalfPlane z

lemma eta_logderivs : {z : ℂ | 0 < z.im}.EqOn (logDeriv (η ∘ (fun z : ℂ => -1/z)))
  (logDeriv ((csqrt) * η)) := by
  intro z hz
  have := eta_logDeriv_eql ⟨z, hz⟩
  exact this

lemma eta_logderivs_const : ∃ z : ℂ, z ≠ 0 ∧ {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
  (z • ((csqrt) * η)) := by
  have h := eta_logderivs
  rw [logDeriv_eqOn_iff] at h
  · exact h
  · apply DifferentiableOn.comp
    pick_goal 4
    · use ({z : ℂ | 0 < z.im})
    · rw [DifferentiableOn]
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      apply eta_DifferentiableAt_UpperHalfPlane ⟨x, hx⟩
    · apply DifferentiableOn.div
      fun_prop
      fun_prop
      intro x hx
      have hx2 := ne_zero (⟨x, hx⟩ : ℍ)
      norm_cast at *
    · intro y hy
      simp
      have := UpperHalfPlane.im_inv_neg_coe_pos (⟨y, hy⟩ : ℍ)
      conv =>
        enter [2,1]
        rw [neg_div]
        rw [div_eq_mul_inv]
        simp
      simp at *
      exact this
  · apply DifferentiableOn.mul
    simp only [DifferentiableOn, mem_setOf_eq]
    intro x hx
    apply (csqrt_differentiableAt ⟨x, hx⟩).differentiableWithinAt
    simp only [DifferentiableOn, mem_setOf_eq]
    intro x hx
    apply (eta_DifferentiableAt_UpperHalfPlane ⟨x, hx⟩).differentiableWithinAt
  · use UpperHalfPlane.I
    simp only [coe_I, mem_setOf_eq, Complex.I_im, zero_lt_one]
  · exact isOpen_lt continuous_const Complex.continuous_im
  · exact convex_halfSpace_im_gt 0
  · intro x hx
    simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or]
    refine ⟨ ?_ , by apply eta_nonzero_on_UpperHalfPlane ⟨x, hx⟩⟩
    unfold csqrt
    simp only [one_div, Complex.exp_ne_zero, not_false_eq_true]
  · intro x hx
    simp only [comp_apply, ne_eq]
    have := eta_nonzero_on_UpperHalfPlane ⟨-1 / x, by simpa using pnat_div_upper 1 ⟨x, hx⟩⟩
    simpa only [ne_eq, coe_mk_subtype] using this

lemma eta_equality : {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
   ((csqrt (Complex.I))⁻¹ • ((csqrt) * η)) := by
  have h := eta_logderivs_const
  obtain ⟨z, hz, h⟩ := h
  intro x hx
  have h2 := h hx
  have hI : (Complex.I) ∈ {z : ℂ | 0 < z.im} := by
    simp only [mem_setOf_eq, Complex.I_im, zero_lt_one]
  have h3 := h hI
  simp at h3
  conv at h3 =>
    enter [2]
    rw [← mul_assoc]
  have he : η Complex.I ≠ 0 := by
    have h:=  eta_nonzero_on_UpperHalfPlane UpperHalfPlane.I
    convert h
  have hcd := (mul_eq_right₀ he).mp (_root_.id (Eq.symm h3))
  rw [mul_eq_one_iff_inv_eq₀ hz] at hcd
  rw [@inv_eq_iff_eq_inv] at hcd
  rw [hcd] at h2
  exact h2 -/
