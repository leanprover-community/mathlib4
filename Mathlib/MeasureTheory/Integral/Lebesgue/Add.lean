/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Monotone convergence theorem and addition of Lebesgue integrals

The monotone convergence theorem (aka Beppo Levi lemma) states that the Lebesgue integral and
supremum can be swapped for a pointwise monotone sequence of functions. This file first proves
several variants of this theorem, then uses it to show that the Lebesgue integral is additive
(assuming one of the functions is at least `AEMeasurable`) and respects multiplication by
a constant.
-/

namespace MeasureTheory

open Set Filter ENNReal Topology NNReal SimpleFunc

variable {α β : Type*} {m : MeasurableSpace α} {μ : Measure α}

local infixr:25 " →ₛ " => SimpleFunc

section MonotoneConvergence

/-- **Monotone convergence theorem**, version with `Measurable` functions. -/
theorem lintegral_iSup {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f) :
    ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ := by
  set c : ℝ≥0 → ℝ≥0∞ := (↑)
  set F := fun a : α => ⨆ n, f n a
  refine le_antisymm ?_ (iSup_lintegral_le _)
  rw [lintegral_eq_nnreal]
  refine iSup_le fun s => iSup_le fun hsf => ?_
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  rcases ENNReal.lt_iff_exists_coe.1 ha with ⟨r, rfl, _⟩
  have ha : r < 1 := ENNReal.coe_lt_coe.1 ha
  let rs := s.map fun a => r * a
  have eq_rs : rs.map c = (const α r : α →ₛ ℝ≥0∞) * map c s := rfl
  have eq : ∀ p, rs.map c ⁻¹' {p} = ⋃ n, rs.map c ⁻¹' {p} ∩ { a | p ≤ f n a } := by
    intro p
    rw [← inter_iUnion]; nth_rw 1 [← inter_univ (map c rs ⁻¹' {p})]
    refine Set.ext fun x => and_congr_right fun hx => (iff_of_eq (true_iff _)).2 ?_
    by_cases p_eq : p = 0
    · simp [p_eq]
    simp only [coe_map, mem_preimage, Function.comp_apply, mem_singleton_iff] at hx
    subst hx
    have : r * s x ≠ 0 := by rwa [Ne, ← ENNReal.coe_eq_zero]
    have : s x ≠ 0 := right_ne_zero_of_mul this
    have : (rs.map c) x < ⨆ n : ℕ, f n x := by
      refine lt_of_lt_of_le (ENNReal.coe_lt_coe.2 ?_) (hsf x)
      suffices r * s x < 1 * s x by simpa
      exact mul_lt_mul_of_pos_right ha (pos_iff_ne_zero.2 this)
    rcases lt_iSup_iff.1 this with ⟨i, hi⟩
    exact mem_iUnion.2 ⟨i, le_of_lt hi⟩
  have mono : ∀ r : ℝ≥0∞, Monotone fun n => rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a } := by
    intro r i j h
    refine inter_subset_inter_right _ ?_
    simp_rw [subset_def, mem_setOf]
    intro x hx
    exact le_trans hx (h_mono h x)
  have h_meas : ∀ n, MeasurableSet {a : α | map c rs a ≤ f n a} := fun n =>
    measurableSet_le (SimpleFunc.measurable _) (hf n)
  calc
    (r : ℝ≥0∞) * (s.map c).lintegral μ = ∑ r ∈ (rs.map c).range, r * μ (rs.map c ⁻¹' {r}) := by
      rw [← const_mul_lintegral, eq_rs, SimpleFunc.lintegral]
    _ = ∑ r ∈ (rs.map c).range, r * μ (⋃ n, rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) := by
      simp only [(eq _).symm]
    _ = ∑ r ∈ (rs.map c).range, ⨆ n, r * μ (rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) :=
      Finset.sum_congr rfl fun x _ => by rw [(mono x).measure_iUnion, ENNReal.mul_iSup]
    _ = ⨆ n, ∑ r ∈ (rs.map c).range, r * μ (rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) := by
      refine ENNReal.finsetSum_iSup_of_monotone fun p i j h ↦ ?_
      gcongr _ * μ ?_
      exact mono p h
    _ ≤ ⨆ n : ℕ, ((rs.map c).restrict { a | (rs.map c) a ≤ f n a }).lintegral μ := by
      gcongr with n
      rw [restrict_lintegral _ (h_meas n)]
      refine le_of_eq (Finset.sum_congr rfl fun r _ => ?_)
      congr 2 with a
      refine and_congr_right ?_
      simp +contextual
    _ ≤ ⨆ n, ∫⁻ a, f n a ∂μ := by
      simp only [← SimpleFunc.lintegral_eq_lintegral]
      gcongr with n a
      simp only [map_apply] at h_meas
      simp only [coe_map, restrict_apply _ (h_meas _), (· ∘ ·)]
      exact indicator_apply_le id

/-- **Monotone convergence theorem**, version with `AEMeasurable` functions. -/
theorem lintegral_iSup' {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ)
    (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x) : ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ := by
  simp_rw [← iSup_apply]
  let p : α → (ℕ → ℝ≥0∞) → Prop := fun _ f' => Monotone f'
  have hp : ∀ᵐ x ∂μ, p x fun i => f i x := h_mono
  have h_ae_seq_mono : Monotone (aeSeq hf p) := by
    intro n m hnm x
    by_cases hx : x ∈ aeSeqSet hf p
    · exact aeSeq.prop_of_mem_aeSeqSet hf hx hnm
    · simp only [aeSeq, hx, if_false, le_rfl]
  rw [lintegral_congr_ae (aeSeq.iSup hf hp).symm]
  simp_rw [iSup_apply]
  rw [lintegral_iSup (aeSeq.measurable hf p) h_ae_seq_mono]
  congr with n
  exact lintegral_congr_ae (aeSeq.aeSeq_n_eq_fun_n_ae hf hp n)

/-- **Monotone convergence theorem** expressed with limits. -/
theorem lintegral_tendsto_of_tendsto_of_monotone {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) μ) (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 <| F x)) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 <| ∫⁻ x, F x ∂μ) := by
  have : Monotone fun n => ∫⁻ x, f n x ∂μ := fun i j hij =>
    lintegral_mono_ae (h_mono.mono fun x hx => hx hij)
  suffices key : ∫⁻ x, F x ∂μ = ⨆ n, ∫⁻ x, f n x ∂μ by
    rw [key]
    exact tendsto_atTop_iSup this
  rw [← lintegral_iSup' hf h_mono]
  refine lintegral_congr_ae ?_
  filter_upwards [h_mono, h_tendsto] with _ hx_mono hx_tendsto using
    tendsto_nhds_unique hx_tendsto (tendsto_atTop_iSup hx_mono)

/-- Weaker version of the **monotone convergence theorem**. -/
theorem lintegral_iSup_ae {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n))
    (h_mono : ∀ n, ∀ᵐ a ∂μ, f n a ≤ f n.succ a) : ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ := by
  classical
  let ⟨s, hs⟩ := exists_measurable_superset_of_null (ae_iff.1 (ae_all_iff.2 h_mono))
  let g n a := if a ∈ s then 0 else f n a
  have g_eq_f : ∀ᵐ a ∂μ, ∀ n, g n a = f n a :=
    (measure_zero_iff_ae_nmem.1 hs.2.2).mono fun a ha n => if_neg ha
  calc
    ∫⁻ a, ⨆ n, f n a ∂μ = ∫⁻ a, ⨆ n, g n a ∂μ :=
      lintegral_congr_ae <| g_eq_f.mono fun a ha => by simp only [ha]
    _ = ⨆ n, ∫⁻ a, g n a ∂μ :=
      (lintegral_iSup (fun n => measurable_const.piecewise hs.2.1 (hf n))
        (monotone_nat_of_le_succ fun n a => ?_))
    _ = ⨆ n, ∫⁻ a, f n a ∂μ := by simp only [lintegral_congr_ae (g_eq_f.mono fun _a ha => ha _)]
  simp only [g]
  split_ifs with h
  · rfl
  · have := Set.not_mem_subset hs.1 h
    simp only [not_forall, not_le, mem_setOf_eq, not_exists, not_lt] at this
    exact this n

open Encodable in
/-- **Monotone convergence theorem** for a supremum over a directed family and indexed by a
countable type. -/
theorem lintegral_iSup_directed_of_measurable [Countable β] {f : β → α → ℝ≥0∞}
    (hf : ∀ b, Measurable (f b)) (h_directed : Directed (· ≤ ·) f) :
    ∫⁻ a, ⨆ b, f b a ∂μ = ⨆ b, ∫⁻ a, f b a ∂μ := by
  cases nonempty_encodable β
  cases isEmpty_or_nonempty β
  · simp [iSup_of_empty]
  inhabit β
  have : ∀ a, ⨆ b, f b a = ⨆ n, f (h_directed.sequence f n) a := by
    intro a
    refine le_antisymm (iSup_le fun b => ?_) (iSup_le fun n => le_iSup (fun n => f n a) _)
    exact le_iSup_of_le (encode b + 1) (h_directed.le_sequence b a)
  calc
    ∫⁻ a, ⨆ b, f b a ∂μ = ∫⁻ a, ⨆ n, f (h_directed.sequence f n) a ∂μ := by simp only [this]
    _ = ⨆ n, ∫⁻ a, f (h_directed.sequence f n) a ∂μ :=
      (lintegral_iSup (fun n => hf _) h_directed.sequence_mono)
    _ = ⨆ b, ∫⁻ a, f b a ∂μ := by
      refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun b => ?_)
      · exact le_iSup (fun b => ∫⁻ a, f b a ∂μ) _
      · exact le_iSup_of_le (encode b + 1) (lintegral_mono <| h_directed.le_sequence b)

/-- **Monotone convergence theorem** for a supremum over a directed family and indexed by a
countable type. -/
theorem lintegral_iSup_directed [Countable β] {f : β → α → ℝ≥0∞} (hf : ∀ b, AEMeasurable (f b) μ)
    (h_directed : Directed (· ≤ ·) f) : ∫⁻ a, ⨆ b, f b a ∂μ = ⨆ b, ∫⁻ a, f b a ∂μ := by
  simp_rw [← iSup_apply]
  let p : α → (β → ENNReal) → Prop := fun x f' => Directed LE.le f'
  have hp : ∀ᵐ x ∂μ, p x fun i => f i x := by
    filter_upwards [] with x i j
    obtain ⟨z, hz₁, hz₂⟩ := h_directed i j
    exact ⟨z, hz₁ x, hz₂ x⟩
  have h_ae_seq_directed : Directed LE.le (aeSeq hf p) := by
    intro b₁ b₂
    obtain ⟨z, hz₁, hz₂⟩ := h_directed b₁ b₂
    refine ⟨z, ?_, ?_⟩ <;>
      · intro x
        by_cases hx : x ∈ aeSeqSet hf p
        · repeat rw [aeSeq.aeSeq_eq_fun_of_mem_aeSeqSet hf hx]
          apply_rules [hz₁, hz₂]
        · simp only [aeSeq, hx, if_false]
          exact le_rfl
  convert lintegral_iSup_directed_of_measurable (aeSeq.measurable hf p) h_ae_seq_directed using 1
  · simp_rw [← iSup_apply]
    rw [lintegral_congr_ae (aeSeq.iSup hf hp).symm]
  · congr 1
    ext1 b
    rw [lintegral_congr_ae]
    apply EventuallyEq.symm
    exact aeSeq.aeSeq_n_eq_fun_n_ae hf hp _

/-- **Fatou's lemma**, version with `AEMeasurable` functions. -/
theorem lintegral_liminf_le' {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, AEMeasurable (f n) μ) :
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  calc
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ = ∫⁻ a, ⨆ n : ℕ, ⨅ i ≥ n, f i a ∂μ := by
      simp only [liminf_eq_iSup_iInf_of_nat]
    _ = ⨆ n : ℕ, ∫⁻ a, ⨅ i ≥ n, f i a ∂μ :=
      (lintegral_iSup' (fun _ => .biInf _ (to_countable _) (fun i _ ↦ h_meas i))
        (ae_of_all μ fun _ _ _ hnm => iInf_le_iInf_of_subset fun _ hi => le_trans hnm hi))
    _ ≤ ⨆ n : ℕ, ⨅ i ≥ n, ∫⁻ a, f i a ∂μ := iSup_mono fun _ => le_iInf₂_lintegral _
    _ = atTop.liminf fun n => ∫⁻ a, f n a ∂μ := Filter.liminf_eq_iSup_iInf_of_nat.symm

/-- **Fatou's lemma**, version with `Measurable` functions. -/
theorem lintegral_liminf_le {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, Measurable (f n)) :
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  lintegral_liminf_le' fun n => (h_meas n).aemeasurable

end MonotoneConvergence

section Add

theorem lintegral_eq_iSup_eapprox_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f a ∂μ = ⨆ n, (eapprox f n).lintegral μ :=
  calc
    ∫⁻ a, f a ∂μ = ∫⁻ a, ⨆ n, (eapprox f n : α → ℝ≥0∞) a ∂μ := by
      congr; ext a; rw [iSup_eapprox_apply hf]
    _ = ⨆ n, ∫⁻ a, (eapprox f n : α → ℝ≥0∞) a ∂μ := by
      apply lintegral_iSup
      · measurability
      · intro i j h
        exact monotone_eapprox f h
    _ = ⨆ n, (eapprox f n).lintegral μ := by
      congr; ext n; rw [(eapprox f n).lintegral_eq_lintegral]

lemma lintegral_eapprox_le_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    (eapprox f n).lintegral μ ≤ ∫⁻ x, f x ∂μ := by
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  exact le_iSup (fun n ↦ (eapprox f n).lintegral μ) n

lemma measure_support_eapprox_lt_top {f : α → ℝ≥0∞} (hf_meas : Measurable f)
    (hf : ∫⁻ x, f x ∂μ ≠ ∞) (n : ℕ) :
    μ (Function.support (eapprox f n)) < ∞ :=
  measure_support_lt_top_of_lintegral_ne_top <|
    ((lintegral_eapprox_le_lintegral hf_meas n).trans_lt hf.lt_top).ne

/-- The sum of the lower Lebesgue integrals of two functions is less than or equal to the integral
of their sum. The other inequality needs one of these functions to be (a.e.-)measurable. -/
theorem le_lintegral_add (f g : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ ≤ ∫⁻ a, f a + g a ∂μ := by
  simp only [lintegral]
  refine ENNReal.biSup_add_biSup_le' (p := fun h : α →ₛ ℝ≥0∞ => h ≤ f)
    (q := fun h : α →ₛ ℝ≥0∞ => h ≤ g) ⟨0, zero_le f⟩ ⟨0, zero_le g⟩ fun f' hf' g' hg' => ?_
  exact le_iSup₂_of_le (f' + g') (add_le_add hf' hg') (add_lintegral _ _).ge

-- Use stronger lemmas `lintegral_add_left`/`lintegral_add_right` instead
theorem lintegral_add_aux {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
  calc
    ∫⁻ a, f a + g a ∂μ =
        ∫⁻ a, (⨆ n, (eapprox f n : α → ℝ≥0∞) a) + ⨆ n, (eapprox g n : α → ℝ≥0∞) a ∂μ := by
      simp only [iSup_eapprox_apply, hf, hg]
    _ = ∫⁻ a, ⨆ n, (eapprox f n + eapprox g n : α → ℝ≥0∞) a ∂μ := by
      congr; funext a
      rw [ENNReal.iSup_add_iSup_of_monotone]
      · simp only [Pi.add_apply]
      · intro i j h
        exact monotone_eapprox _ h a
      · intro i j h
        exact monotone_eapprox _ h a
    _ = ⨆ n, (eapprox f n).lintegral μ + (eapprox g n).lintegral μ := by
      rw [lintegral_iSup]
      · congr
        funext n
        rw [← SimpleFunc.add_lintegral, ← SimpleFunc.lintegral_eq_lintegral]
        simp only [Pi.add_apply, SimpleFunc.coe_add]
      · fun_prop
      · intro i j h a
        dsimp
        gcongr <;> exact monotone_eapprox _ h _
    _ = (⨆ n, (eapprox f n).lintegral μ) + ⨆ n, (eapprox g n).lintegral μ := by
      refine (ENNReal.iSup_add_iSup_of_monotone ?_ ?_).symm <;>
        · intro i j h
          exact SimpleFunc.lintegral_mono (monotone_eapprox _ h) le_rfl
    _ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
      rw [lintegral_eq_iSup_eapprox_lintegral hf, lintegral_eq_iSup_eapprox_lintegral hg]

/-- If `f g : α → ℝ≥0∞` are two functions and one of them is (a.e.) measurable, then the Lebesgue
integral of `f + g` equals the sum of integrals. This lemma assumes that `f` is integrable, see also
`MeasureTheory.lintegral_add_right` and primed versions of these lemmas. -/
@[simp]
theorem lintegral_add_left {f : α → ℝ≥0∞} (hf : Measurable f) (g : α → ℝ≥0∞) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
  refine le_antisymm ?_ (le_lintegral_add _ _)
  rcases exists_measurable_le_lintegral_eq μ fun a => f a + g a with ⟨φ, hφm, hφ_le, hφ_eq⟩
  calc
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, φ a ∂μ := hφ_eq
    _ ≤ ∫⁻ a, f a + (φ a - f a) ∂μ := lintegral_mono fun a => le_add_tsub
    _ = ∫⁻ a, f a ∂μ + ∫⁻ a, φ a - f a ∂μ := lintegral_add_aux hf (hφm.sub hf)
    _ ≤ ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
      add_le_add_left (lintegral_mono fun a => tsub_le_iff_left.2 <| hφ_le a) _

theorem lintegral_add_left' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (g : α → ℝ≥0∞) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
  rw [lintegral_congr_ae hf.ae_eq_mk, ← lintegral_add_left hf.measurable_mk,
    lintegral_congr_ae (hf.ae_eq_mk.add (ae_eq_refl g))]

theorem lintegral_add_right' (f : α → ℝ≥0∞) {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
  simpa only [add_comm] using lintegral_add_left' hg f

/-- If `f g : α → ℝ≥0∞` are two functions and one of them is (a.e.) measurable, then the Lebesgue
integral of `f + g` equals the sum of integrals. This lemma assumes that `g` is integrable, see also
`MeasureTheory.lintegral_add_left` and primed versions of these lemmas. -/
@[simp]
theorem lintegral_add_right (f : α → ℝ≥0∞) {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
  lintegral_add_right' f hg.aemeasurable

theorem lintegral_finset_sum' (s : Finset β) {f : β → α → ℝ≥0∞}
    (hf : ∀ b ∈ s, AEMeasurable (f b) μ) :
    ∫⁻ a, ∑ b ∈ s, f b a ∂μ = ∑ b ∈ s, ∫⁻ a, f b a ∂μ := by
  classical
  induction' s using Finset.induction_on with a s has ih
  · simp
  · simp only [Finset.sum_insert has]
    rw [Finset.forall_mem_insert] at hf
    rw [lintegral_add_left' hf.1, ih hf.2]

theorem lintegral_finset_sum (s : Finset β) {f : β → α → ℝ≥0∞} (hf : ∀ b ∈ s, Measurable (f b)) :
    ∫⁻ a, ∑ b ∈ s, f b a ∂μ = ∑ b ∈ s, ∫⁻ a, f b a ∂μ :=
  lintegral_finset_sum' s fun b hb => (hf b hb).aemeasurable

theorem lintegral_tsum [Countable β] {f : β → α → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) μ) :
    ∫⁻ a, ∑' i, f i a ∂μ = ∑' i, ∫⁻ a, f i a ∂μ := by
  classical
  simp only [ENNReal.tsum_eq_iSup_sum]
  rw [lintegral_iSup_directed]
  · simp [lintegral_finset_sum' _ fun i _ => hf i]
  · intro b
    exact Finset.aemeasurable_sum _ fun i _ => hf i
  · intro s t
    use s ∪ t
    constructor
    · exact fun a => Finset.sum_le_sum_of_subset Finset.subset_union_left
    · exact fun a => Finset.sum_le_sum_of_subset Finset.subset_union_right

end Add

section Mul

@[simp]
theorem lintegral_const_mul (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ :=
  calc
    ∫⁻ a, r * f a ∂μ = ∫⁻ a, ⨆ n, (const α r * eapprox f n) a ∂μ := by
      congr
      funext a
      rw [← iSup_eapprox_apply hf, ENNReal.mul_iSup]
      simp
    _ = ⨆ n, r * (eapprox f n).lintegral μ := by
      rw [lintegral_iSup]
      · congr
        funext n
        rw [← SimpleFunc.const_mul_lintegral, ← SimpleFunc.lintegral_eq_lintegral]
      · intro n
        exact SimpleFunc.measurable _
      · intro i j h a
        exact mul_le_mul_left' (monotone_eapprox _ h _) _
    _ = r * ∫⁻ a, f a ∂μ := by rw [← ENNReal.mul_iSup, lintegral_eq_iSup_eapprox_lintegral hf]

theorem lintegral_const_mul'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ := by
  have A : ∫⁻ a, f a ∂μ = ∫⁻ a, hf.mk f a ∂μ := lintegral_congr_ae hf.ae_eq_mk
  have B : ∫⁻ a, r * f a ∂μ = ∫⁻ a, r * hf.mk f a ∂μ :=
    lintegral_congr_ae (EventuallyEq.fun_comp hf.ae_eq_mk _)
  rw [A, B, lintegral_const_mul _ hf.measurable_mk]

theorem lintegral_const_mul_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) :
    r * ∫⁻ a, f a ∂μ ≤ ∫⁻ a, r * f a ∂μ := by
  rw [lintegral, ENNReal.mul_iSup]
  refine iSup_le fun s => ?_
  rw [ENNReal.mul_iSup, iSup_le_iff]
  intro hs
  rw [← SimpleFunc.const_mul_lintegral, lintegral]
  refine le_iSup_of_le (const α r * s) (le_iSup_of_le (fun x => ?_) le_rfl)
  exact mul_le_mul_left' (hs x) _

theorem lintegral_const_mul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
    ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ := by
  by_cases h : r = 0
  · simp [h]
  apply le_antisymm _ (lintegral_const_mul_le r f)
  have rinv : r * r⁻¹ = 1 := ENNReal.mul_inv_cancel h hr
  have rinv' : r⁻¹ * r = 1 := by
    rw [mul_comm]
    exact rinv
  have := lintegral_const_mul_le (μ := μ) r⁻¹ fun x => r * f x
  simp? [(mul_assoc _ _ _).symm, rinv'] at this says
    simp only [(mul_assoc _ _ _).symm, rinv', one_mul] at this
  simpa [(mul_assoc _ _ _).symm, rinv] using mul_le_mul_left' this r

theorem lintegral_mul_const (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r := by simp_rw [mul_comm, lintegral_const_mul r hf]

theorem lintegral_mul_const'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r := by simp_rw [mul_comm, lintegral_const_mul'' r hf]

theorem lintegral_mul_const_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) :
    (∫⁻ a, f a ∂μ) * r ≤ ∫⁻ a, f a * r ∂μ := by
  simp_rw [mul_comm, lintegral_const_mul_le r f]

theorem lintegral_mul_const' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
    ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r := by simp_rw [mul_comm, lintegral_const_mul' r f hr]

/- A double integral of a product where each factor contains only one variable
  is a product of integrals -/
theorem lintegral_lintegral_mul {β} [MeasurableSpace β] {ν : Measure β} {f : α → ℝ≥0∞}
    {g : β → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) :
    ∫⁻ x, ∫⁻ y, f x * g y ∂ν ∂μ = (∫⁻ x, f x ∂μ) * ∫⁻ y, g y ∂ν := by
  simp [lintegral_const_mul'' _ hg, lintegral_mul_const'' _ hf]

end Mul

section Markov

/-- A version of **Markov's inequality** for two functions. It doesn't follow from the standard
Markov's inequality because we only assume measurability of `g`, not `f`. -/
theorem lintegral_add_mul_meas_add_le_le_lintegral {f g : α → ℝ≥0∞} (hle : f ≤ᵐ[μ] g)
    (hg : AEMeasurable g μ) (ε : ℝ≥0∞) :
    ∫⁻ a, f a ∂μ + ε * μ { x | f x + ε ≤ g x } ≤ ∫⁻ a, g a ∂μ := by
  rcases exists_measurable_le_lintegral_eq μ f with ⟨φ, hφm, hφ_le, hφ_eq⟩
  calc
    ∫⁻ x, f x ∂μ + ε * μ { x | f x + ε ≤ g x } = ∫⁻ x, φ x ∂μ + ε * μ { x | f x + ε ≤ g x } := by
      rw [hφ_eq]
    _ ≤ ∫⁻ x, φ x ∂μ + ε * μ { x | φ x + ε ≤ g x } := by
      gcongr
      exact fun x => (add_le_add_right (hφ_le _) _).trans
    _ = ∫⁻ x, φ x + indicator { x | φ x + ε ≤ g x } (fun _ => ε) x ∂μ := by
      rw [lintegral_add_left hφm, lintegral_indicator₀, setLIntegral_const]
      exact measurableSet_le (hφm.nullMeasurable.measurable'.add_const _) hg.nullMeasurable
    _ ≤ ∫⁻ x, g x ∂μ := lintegral_mono_ae (hle.mono fun x hx₁ => ?_)
  simp only [indicator_apply]; split_ifs with hx₂
  exacts [hx₂, (add_zero _).trans_le <| (hφ_le x).trans hx₁]

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
theorem mul_meas_ge_le_lintegral₀ {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ := by
  simpa only [lintegral_zero, zero_add] using
    lintegral_add_mul_meas_add_le_le_lintegral (ae_of_all _ fun x => zero_le (f x)) hf ε

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. For a version assuming
`AEMeasurable`, see `mul_meas_ge_le_lintegral₀`. -/
theorem mul_meas_ge_le_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ :=
  mul_meas_ge_le_lintegral₀ hf.aemeasurable ε

lemma meas_le_lintegral₀ {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    {s : Set α} (hs : ∀ x ∈ s, 1 ≤ f x) : μ s ≤ ∫⁻ a, f a ∂μ := by
  apply le_trans _ (mul_meas_ge_le_lintegral₀ hf 1)
  rw [one_mul]
  exact measure_mono hs

lemma lintegral_le_meas {s : Set α} {f : α → ℝ≥0∞} (hf : ∀ a, f a ≤ 1) (h'f : ∀ a ∈ sᶜ, f a = 0) :
    ∫⁻ a, f a ∂μ ≤ μ s := by
  apply (lintegral_mono (fun x ↦ ?_)).trans (lintegral_indicator_one_le s)
  by_cases hx : x ∈ s
  · simpa [hx] using hf x
  · simpa [hx] using h'f x hx

lemma setLIntegral_le_meas {s t : Set α} (hs : MeasurableSet s)
    {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, a ∈ t → f a ≤ 1)
    (hf' : ∀ a ∈ s, a ∉ t → f a = 0) : ∫⁻ a in s, f a ∂μ ≤ μ t := by
  rw [← lintegral_indicator hs]
  refine lintegral_le_meas (fun a ↦ ?_) (by aesop)
  by_cases has : a ∈ s <;> [by_cases hat : a ∈ t; skip] <;> simp [*]

theorem lintegral_eq_top_of_measure_eq_top_ne_zero {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hμf : μ {x | f x = ∞} ≠ 0) : ∫⁻ x, f x ∂μ = ∞ :=
  eq_top_iff.mpr <|
    calc
      ∞ = ∞ * μ { x | ∞ ≤ f x } := by simp [mul_eq_top, hμf]
      _ ≤ ∫⁻ x, f x ∂μ := mul_meas_ge_le_lintegral₀ hf ∞

theorem setLintegral_eq_top_of_measure_eq_top_ne_zero {f : α → ℝ≥0∞} {s : Set α}
    (hf : AEMeasurable f (μ.restrict s)) (hμf : μ ({x ∈ s | f x = ∞}) ≠ 0) :
    ∫⁻ x in s, f x ∂μ = ∞ :=
  lintegral_eq_top_of_measure_eq_top_ne_zero hf <|
    mt (eq_bot_mono <| by rw [← setOf_inter_eq_sep]; exact Measure.le_restrict_apply _ _) hμf

theorem measure_eq_top_of_lintegral_ne_top {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hμf : ∫⁻ x, f x ∂μ ≠ ∞) : μ {x | f x = ∞} = 0 :=
  of_not_not fun h => hμf <| lintegral_eq_top_of_measure_eq_top_ne_zero hf h

theorem measure_eq_top_of_setLintegral_ne_top {f : α → ℝ≥0∞} {s : Set α}
    (hf : AEMeasurable f (μ.restrict s)) (hμf : ∫⁻ x in s, f x ∂μ ≠ ∞) :
    μ ({x ∈ s | f x = ∞}) = 0 :=
  of_not_not fun h => hμf <| setLintegral_eq_top_of_measure_eq_top_ne_zero hf h

/-- **Markov's inequality**, also known as **Chebyshev's first inequality**. -/
theorem meas_ge_le_lintegral_div {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0)
    (hε' : ε ≠ ∞) : μ { x | ε ≤ f x } ≤ (∫⁻ a, f a ∂μ) / ε :=
  (ENNReal.le_div_iff_mul_le (Or.inl hε) (Or.inl hε')).2 <| by
    rw [mul_comm]
    exact mul_meas_ge_le_lintegral₀ hf ε

theorem ae_eq_of_ae_le_of_lintegral_le {f g : α → ℝ≥0∞} (hfg : f ≤ᵐ[μ] g) (hf : ∫⁻ x, f x ∂μ ≠ ∞)
    (hg : AEMeasurable g μ) (hgf : ∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ) : f =ᵐ[μ] g := by
  have : ∀ n : ℕ, ∀ᵐ x ∂μ, g x < f x + (n : ℝ≥0∞)⁻¹ := by
    intro n
    simp only [ae_iff, not_lt]
    have : ∫⁻ x, f x ∂μ + (↑n)⁻¹ * μ { x : α | f x + (n : ℝ≥0∞)⁻¹ ≤ g x } ≤ ∫⁻ x, f x ∂μ :=
      (lintegral_add_mul_meas_add_le_le_lintegral hfg hg n⁻¹).trans hgf
    rw [(ENNReal.cancel_of_ne hf).add_le_iff_nonpos_right, nonpos_iff_eq_zero, mul_eq_zero] at this
    exact this.resolve_left (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
  refine hfg.mp ((ae_all_iff.2 this).mono fun x hlt hle => hle.antisymm ?_)
  suffices Tendsto (fun n : ℕ => f x + (n : ℝ≥0∞)⁻¹) atTop (𝓝 (f x)) from
    ge_of_tendsto' this fun i => (hlt i).le
  simpa only [inv_top, add_zero] using
    tendsto_const_nhds.add (ENNReal.tendsto_inv_iff.2 ENNReal.tendsto_nat_nhds_top)

@[simp]
theorem lintegral_eq_zero_iff' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
  have : ∫⁻ _ : α, 0 ∂μ ≠ ∞ := by simp [lintegral_zero, zero_ne_top]
  ⟨fun h =>
    (ae_eq_of_ae_le_of_lintegral_le (ae_of_all _ <| zero_le f) this hf
        (h.trans lintegral_zero.symm).le).symm,
    fun h => (lintegral_congr_ae h).trans lintegral_zero⟩

@[simp]
theorem lintegral_eq_zero_iff {f : α → ℝ≥0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
  lintegral_eq_zero_iff' hf.aemeasurable

theorem setLIntegral_eq_zero_iff' {s : Set α} (hs : MeasurableSet s)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f (μ.restrict s)) :
    ∫⁻ a in s, f a ∂μ = 0 ↔ ∀ᵐ x ∂μ, x ∈ s → f x = 0 :=
  (lintegral_eq_zero_iff' hf).trans (ae_restrict_iff' hs)

theorem setLIntegral_eq_zero_iff {s : Set α} (hs : MeasurableSet s) {f : α → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ a in s, f a ∂μ = 0 ↔ ∀ᵐ x ∂μ, x ∈ s → f x = 0 :=
  setLIntegral_eq_zero_iff' hs hf.aemeasurable

theorem lintegral_pos_iff_support {f : α → ℝ≥0∞} (hf : Measurable f) :
    (0 < ∫⁻ a, f a ∂μ) ↔ 0 < μ (Function.support f) := by
  simp [pos_iff_ne_zero, hf, Filter.EventuallyEq, ae_iff, Function.support]

theorem setLintegral_pos_iff {f : α → ℝ≥0∞} (hf : Measurable f) {s : Set α} :
    0 < ∫⁻ a in s, f a ∂μ ↔ 0 < μ (Function.support f ∩ s) := by
  rw [lintegral_pos_iff_support hf, Measure.restrict_apply (measurableSet_support hf)]

theorem lintegral_strict_mono_of_ae_le_of_frequently_ae_lt {f g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h_le : f ≤ᵐ[μ] g) (h : ∃ᵐ x ∂μ, f x ≠ g x) :
    ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ := by
  contrapose! h
  simp only [not_frequently, Ne, Classical.not_not]
  exact ae_eq_of_ae_le_of_lintegral_le h_le hfi hg h

theorem lintegral_strict_mono_of_ae_le_of_ae_lt_on {f g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h_le : f ≤ᵐ[μ] g) {s : Set α} (hμs : μ s ≠ 0)
    (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) : ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ :=
  lintegral_strict_mono_of_ae_le_of_frequently_ae_lt hg hfi h_le <|
    ((frequently_ae_mem_iff.2 hμs).and_eventually h).mono fun _x hx => (hx.2 hx.1).ne

theorem lintegral_strict_mono {f g : α → ℝ≥0∞} (hμ : μ ≠ 0) (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h : ∀ᵐ x ∂μ, f x < g x) : ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ := by
  rw [Ne, ← Measure.measure_univ_eq_zero] at hμ
  refine lintegral_strict_mono_of_ae_le_of_ae_lt_on hg hfi (ae_le_of_ae_lt h) hμ ?_
  simpa using h

theorem setLIntegral_strict_mono {f g : α → ℝ≥0∞} {s : Set α} (hsm : MeasurableSet s)
    (hs : μ s ≠ 0) (hg : Measurable g) (hfi : ∫⁻ x in s, f x ∂μ ≠ ∞)
    (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) : ∫⁻ x in s, f x ∂μ < ∫⁻ x in s, g x ∂μ :=
  lintegral_strict_mono (by simp [hs]) hg.aemeasurable hfi ((ae_restrict_iff' hsm).mpr h)

theorem ae_lt_top' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (h2f : ∫⁻ x, f x ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, f x < ∞ := by
  simp_rw [ae_iff, ENNReal.not_lt_top]
  exact measure_eq_top_of_lintegral_ne_top hf h2f

theorem ae_lt_top {f : α → ℝ≥0∞} (hf : Measurable f) (h2f : ∫⁻ x, f x ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, f x < ∞ :=
  ae_lt_top' hf.aemeasurable h2f

end Markov

section Trim

variable {m m0 : MeasurableSpace α}

theorem lintegral_trim {μ : Measure α} (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : Measurable[m] f) :
    ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f a ∂μ := by
  refine
    @Measurable.ennreal_induction α m (fun f => ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f a ∂μ) ?_ ?_ ?_ f hf
  · intro c s hs
    rw [lintegral_indicator hs, lintegral_indicator (hm s hs), setLIntegral_const,
      setLIntegral_const]
    suffices h_trim_s : μ.trim hm s = μ s by rw [h_trim_s]
    exact trim_measurableSet_eq hm hs
  · intro f g _ hf _ hf_prop hg_prop
    have h_m := lintegral_add_left (μ := Measure.trim μ hm) hf g
    have h_m0 := lintegral_add_left (μ := μ) (Measurable.mono hf hm le_rfl) g
    rwa [hf_prop, hg_prop, ← h_m0] at h_m
  · intro f hf hf_mono hf_prop
    rw [lintegral_iSup hf hf_mono]
    rw [lintegral_iSup (fun n => Measurable.mono (hf n) hm le_rfl) hf_mono]
    congr with n
    exact hf_prop n

theorem lintegral_trim_ae {μ : Measure α} (hm : m ≤ m0) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f (μ.trim hm)) : ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f a ∂μ := by
  rw [lintegral_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk), lintegral_congr_ae hf.ae_eq_mk,
    lintegral_trim hm hf.measurable_mk]

end Trim

end MeasureTheory
