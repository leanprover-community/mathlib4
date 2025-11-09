/-
Copyright (c) 2025 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin, Thomas Zhu
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Topology.Compactness.PseudometrizableLindelof

/-!
# Conditional Jensen's Inequality

This file contains the conditional Jensen's inequality.

## Main Statement

* `conditional_jensen`: the conditional Jensen's inequality: in a Banach space `X` with finite
  measure `μ`, if `φ : X → ℝ` is a convex lower-semicontinuous function, then for any `f : α → X`
  such that `f` and `φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ 𝔼[φ ∘ f | m]`.

## References

* [Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.][Hytonen_VanNeerven_Veraar_Wies_2016]
-/

open MeasureTheory ProbabilityTheory TopologicalSpace Set Metric ContinuousLinearMap RCLike
open scoped ENNReal

variable {K E : Type*} [RCLike K] {s : Set E} {φ : E → ℝ}

theorem LowerSemicontinuous.isClosed_re_epigraph [TopologicalSpace E]
    (hφ_cont : LowerSemicontinuous φ) :
    IsClosed  { p : E × K | φ p.1 ≤ re p.2 } := by
  let A := {(x, (s : EReal)) | φ x ≤ s}
  have hC : { p : E × K | φ p.1 ≤ re p.2 }
    = (Prod.map (id: E → E) ((Real.toEReal ∘ re) : K → EReal))⁻¹' A := by simp [A]
  rw [hC]
  apply IsClosed.preimage
  · refine (Continuous.prodMap continuous_id ?_)
    exact continuous_coe_real_ereal.comp reCLM.cont
  · have M : Monotone Real.toEReal := by
      intro a b hab
      rw [EReal.coe_le_coe_iff]
      exact hab
    have hφ : LowerSemicontinuous (Real.toEReal ∘ φ) := Continuous.comp_lowerSemicontinuous
      continuous_coe_real_ereal hφ_cont M
    exact LowerSemicontinuous.isClosed_epigraph hφ

theorem ConvexOn.convex_re_epigraph [AddCommMonoid E] [Module ℝ E] (hφ_cvx : ConvexOn ℝ s φ) :
    Convex ℝ { p : E × K | p.1 ∈ s ∧ φ p.1 ≤ re p.2 } := by
  have lem : { p : E × K | p.1 ∈ s ∧ φ p.1 ≤ re p.2 } = (LinearMap.prodMap
    (LinearMap.id : E →ₗ[ℝ] E) reLm)⁻¹' { p : E × ℝ | p.1 ∈ s ∧ φ p.1 ≤ p.2 } := by simp
  rw [lem]
  apply Convex.linear_preimage
  exact ConvexOn.convex_epigraph hφ_cvx

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A convex lower-semicontinuous function is the supremum of a sequence of affine functions
in a separable space. -/
theorem ConvexOn.iSup_affine_eq_of_separableSpace (hφ_cont : LowerSemicontinuous φ) [Module K E]
    [SecondCountableTopology E] [ContinuousSMul K E] (hφ_cvx : ConvexOn ℝ Set.univ φ) :
    ∃ (L : ℕ → E →L[K] K) (c : ℕ → ℝ),
    ∀ x, BddAbove (Set.range (fun i ↦ (re ((L i) x) + c i)))
    ∧ (⨆ (i : ℕ), re ((L i) x) + c i = φ x) := by
  let C :=  {(x, (s : K)) | φ x ≤ re s}
  have hC₁ : Convex ℝ C := by simpa using hφ_cvx.convex_re_epigraph
  have hC₂ : IsClosed C := by simpa using hφ_cont.isClosed_re_epigraph
  have hC₃ : C.Nonempty := by refine (nonempty_of_mem (x := (0, ↑ (φ 0))) ?_); simp [C]
  rcases iInter_nat_halfSpaces_eq_of_prod (𝕜 := K) hC₁ hC₂ (.of_separableSpace _)
    with ⟨L, T, c, hLTc1, hLTc2⟩
  have lem1 (i : ℕ) (y : K) : T i y = (T i 1) * y := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul (T i) y 1, smul_eq_mul, mul_one]
  have lem2 (x : E) (y : K) (hy : φ x ≤ re y) (i : ℕ) :
    c i ≤ re (L i x) + re (T i 1) * (re y) - im (T i 1) * im (y) := by
    have hy2 : (x, y) ∈ C := by simpa [C] using hy
    rw [add_sub_assoc, ← mul_re, ← lem1 i]
    simp only [← hLTc1, mem_iInter, mem_setOf_eq, C] at hy2
    exact (hy2 i)
  have lem3 (i : ℕ) : 0 = im (T i 1) := by
    cases @I_eq_zero_or_im_I_eq_one K (by infer_instance) with
    | inl hI0 => rw [← I_im', hI0]; simp [map_zero, zero_mul]
    | inr hI1 =>
      by_contra ht
      let z : K := (φ 0) + I * ↑((c i - re (T i 1) * (φ 0) - 1) / -im (T i 1))
      have rez : re z = φ 0 := by
        rw [map_add, ofReal_re, mul_re, I_re, zero_mul, ofReal_im, mul_zero, sub_self, add_zero]
      have imz : im z = (c i - re ((T i) 1) * (φ 0) - 1) / -im ((T i) 1) := by
        rw [map_add, ofReal_im, mul_im, I_re, ofReal_re, zero_add]; simp [hI1]
      have lem31 : c i ≤ c i - 1 :=
        calc
          c i ≤ re (L i 0) + re (T i 1) * (re z) - im (T i 1) * im (z) := by grind
            _ = re (T i 1) * (φ 0) - im (T i 1) * ((c i -
                  re (T i 1) * (φ 0) - 1) / -im (T i 1)) := by simp [rez, imz]
            _ = c i - 1 := by grind
      exact not_lt_of_ge lem31 (by linarith)
  have lem4 (i : ℕ) : 0 < re ((T i) 1) := by
    by_contra! h
    rw [le_iff_eq_or_lt] at h
    cases h with
    | inl h1 =>
      -- Our goal is to show that in this case, the half spaces in hLTc1 are trivial. That is,
      -- re ((L i) x) + re ((T i) y) = 0, which contradicts with hLTc2.
      have lem411 (x : E) : c i ≤ re (L i x) := by
        simpa [h1] using (lem2 x (φ x) (by simp [ofReal_re]) i)
      have lem412 (y : K) : re (T i y) = 0 := by
        rw [lem1 i, mul_re, h1, ← lem3 i, zero_mul, zero_mul, sub_zero]
      have hC₄ : C ≠ univ := by rw [ne_univ_iff_exists_notMem]; use (0, (φ 0 - 1)); simp [C]
      have P1 := hLTc2 hC₃ hC₄ i
      simp only [← not_forall] at P1
      have P2 (x : E) (y : K) : (re ∘ L i) x + (re ∘ T i) y = 0 := by
        -- (re ∘ T i) y = 0 follows from lem412.  Notice that lem411 holds for (n • x) for any
        -- integer n. Thus, we can prove (re ∘ L i) x = 0 by using a scaling argument.
        have P21 (x : E) : re ((L i) x) = 0 := by
          have ge1 : {n | 1 ≤ n} ∈ Filter.atTop := by
            simp only [Filter.mem_atTop_sets]; use 1; exact fun _ hb => hb
          apply le_antisymm
          · have : ∀ᶠ (n : ℕ) in Filter.atTop, re (L i x) ≤ - c i / n := by
              filter_upwards [ge1] with n hn
              calc
                re (L i x)
                  = re ((L i) (((-((n : ℝ) : K))⁻¹ * -((n : ℝ) : K)) • x)) := by
                  rw (config := {occs := .pos [1]}) [← (one_smul K x), inv_mul_cancel₀]
                  simp [ne_eq, neg_eq_zero, Nat.cast_eq_zero]; linarith
                _ = (-(n : ℝ))⁻¹ * re ((L i) ((-(n : K)) • x)) := by
                  rw (config := {occs := .pos [1]}) [← smul_smul, map_smul, smul_eq_mul,
                    ← ofReal_neg, ← ofReal_inv, re_ofReal_mul, ofReal_natCast]
                _ ≤ c i / -n := by
                  rw [inv_mul_eq_div, div_le_div_right_of_neg (by simp; linarith)]
                  exact lem411 ((-(n : K) • x))
                _ = - c i / n := by rw [div_neg, neg_div]
            exact ge_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat (- c i)) this
          · have : ∀ᶠ (n : ℕ) in Filter.atTop, c i / n ≤ re (L i x) := by
              filter_upwards [ge1] with n hn
              calc
                c i / n
                  ≤ re ((L i) ((n : K) • x)) / n := by
                  rw [div_le_div_iff_of_pos_right (by simp; linarith)]; exact lem411 ((n : K) • x)
                _ = re ((n : ℝ) * (L i x)) / n := by rw [map_smul, smul_eq_mul, ← ofReal_natCast]
                _ = n * re (L i x) / n := by rw [re_ofReal_mul]
                _ = re (L i x) := by field
            exact le_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat (c i)) this
        simp [P21, lem412]
      exact P1 P2
    | inr h2 =>
      let m := max ((c i) / re (T i 1) + 1) (φ 0)
      have lem421 : φ 0 ≤ re (@ofReal K (by infer_instance) m) := by simp [m]
      have lem422 : c i ≤ re (T i 1) * m := by simpa using (lem2 0 m lem421 i)
      have lem423 : c i < c i := by
        refine lt_of_le_of_lt lem422 ((div_lt_iff_of_neg' h2).mp ?_)
        have : (c i) / re (T i 1) < ((c i) / re (T i 1) + 1) := by linarith
        exact lt_of_lt_of_le this (by simp [m])
      exact lt_irrefl (c i) lem423
  have lem5 (i : ℕ) : T i 1 = re (T i 1) := by
    apply Eq.trans (re_add_im ((T i) 1)).symm; simp [← lem3 i]
  let f := fun (y : E) ↦ (fun i ↦ re (( -(T i 1)⁻¹ • L i) y) + c i / re (T i 1))
  have hf (y : E) : BddAbove (Set.range (f y)) := by
    have (i : ℕ) : f y i ≤ φ y := by
      have : φ y ≤ re (@ofReal K (by infer_instance) (φ y)) := by simp [ofReal_re]
      have := (lem2 y (φ y)) this
      simp only [ofReal_re, ofReal_im, mul_zero, sub_zero] at this
      calc
        f y i = re (( -(T i 1)⁻¹ • L i) y) + c i / re (T i 1) := by simp [f]
            _ ≤ re (( -(T i 1)⁻¹ • L i) y) + (re (L i y) + re (T i 1) * φ y) / re (T i 1) := by
              apply add_le_add_left
              rw [div_eq_mul_inv, div_eq_mul_inv]
              apply mul_le_mul_of_nonneg_right (this i) (le_of_lt (inv_pos.mpr (lem4 i)))
            _ = re (( -(T i 1)⁻¹ • L i) y) + re (L i y) / re (T i 1)
                + re (T i 1) * φ y / re (T i 1) := by rw [add_div, add_assoc]
            _ = re (-(T i 1)⁻¹ * L i y) + re (L i y) / re (T i 1)
                + re (T i 1) / re (T i 1) * φ y := by
              simp [coe_smul', Pi.smul_apply, smul_eq_mul, mul_div_right_comm]
            _ = - (re (L i y) / re (T i 1))  + re (L i y) / re (T i 1) + 1 * φ y := by
              rw (config := {occs := .pos [1]}) [lem5 i, ← ofReal_inv, ← ofReal_neg, re_ofReal_mul,
                mul_comm, ← inv_neg, ← div_eq_mul_inv, div_neg, div_self (ne_of_gt (lem4 i))]
            _ = φ y := by rw [neg_add_cancel, zero_add, one_mul]
    use φ y; intro z hz; rcases mem_range.mp hz with ⟨i, hfi⟩; rw [← hfi]; exact this i
  refine ⟨fun i ↦ -(T i 1)⁻¹ • (L i), fun i ↦ c i / re (T i 1), fun x => ⟨hf x, ?_ ⟩⟩
  have lem6 (x : E) (s : K) : iSup (f x) ≤ re s ↔ φ x ≤ re s := by
    constructor
    · intro hxs
      have : (x,s) ∈ C := by
        rw [← hLTc1]
        simp only [mem_iInter, mem_setOf_eq]
        intro i
        have hi (i : ℕ) : (f x) i ≤ re s := by apply (ciSup_le_iff (hf x)).mp; use hxs
        calc
          c i = c i / re ((T i) 1) * re ((T i) 1) := by field_simp [ne_of_gt (lem4 i)]
            _ = - re ( -(T i 1)⁻¹ • L i x) * re (T i 1) + (re ( -(T i 1)⁻¹ • L i x)
              + c i / re (T i 1)) * re (T i 1) := by linarith
            _ = re (L i x) +  (re ( -(T i 1)⁻¹ • L i x)
              + c i / re (T i 1)) * re (T i 1) := by
              rw (config := {occs := .pos [1]}) [lem5 i]
              rw [smul_eq_mul, ← ofReal_inv, ← ofReal_neg, re_ofReal_mul]
              rw (config := {occs := .pos [2]}) [neg_mul]
              rw [neg_neg, mul_comm (re ((T i) 1))⁻¹, inv_mul_cancel_right₀ (ne_of_gt (lem4 i))]
            _ ≤ re (L i x) +  re s * re (T i 1) := by
              exact add_le_add_left (mul_le_mul_of_nonneg_right (hi i) (le_of_lt (lem4 i)))
                (re ((L i) x))
            _ = re (L i x) + re (T i s) := by
              rw [lem1 i s]
              rw (config := { occs := .neg [1]}) [lem5 i]
              rw [re_ofReal_mul, mul_comm]
      use this
    · refine fun hxs => ciSup_le fun i => ?_
      have : (x,s) ∈ C := hxs
      rw [← hLTc1, mem_iInter] at this
      have := this i
      simp only [mem_setOf_eq] at this
      calc
        re (-(T i 1)⁻¹ • L i  x) + c i / re (T i 1)
          = (- re (L i x) + c i) / re (T i 1) := by
          rw (config := {occs := .pos [1]}) [lem5 i]
          simp [-map_inv₀, -map_neg, smul_eq_mul, ← ofReal_inv, ← ofReal_neg,
            neg_mul, ← div_eq_inv_mul, ← neg_div, add_div]
        _ ≤ re (T i s) / re (T i 1) := by
          apply (div_le_div_iff_of_pos_right (lem4 i)).mpr; linarith
        _ = re s := by
          rw (config := {occs := .pos [1]}) [lem1 i s, lem5 i, re_ofReal_mul, mul_div_right_comm,
            div_eq_mul_inv, mul_inv_cancel₀ (ne_of_gt (lem4 i)), one_mul]
  apply le_antisymm
  · rw [← @ofReal_re K (by infer_instance) (φ x)]; apply (lem6 x (φ x)).mpr; simp
  · rw [← @ofReal_re K (by infer_instance) (⨆ i, re ((-(T i 1)⁻¹ • L i) x) + c i / re (T i 1))]
    apply (lem6 x (ofReal (⨆ i, re ((-(T i 1)⁻¹ • L i) x) + c i / re (T i 1)))).mp; simp [f]

variable [CompleteSpace E] {α : Type*} {f : α → E}
variable {m mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]

/-- Conditional Jensen for separable spaces. -/
private lemma conditional_jensen_of_separableSpace [SecondCountableTopology E]
    (hm : m ≤ mα) (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    ∀ᵐ a ∂μ, φ (μ[f | m] a) ≤ μ[φ ∘ f | m] a := by
  rcases hφ_cvx.iSup_affine_eq_of_separableSpace (K := ℝ) hφ_cont with ⟨L, c, hp⟩
  have py : ∀ᵐ a ∂μ, ∀ i : ℕ, re (L i (μ[f | m] a)) + c i
    = μ[re ∘ (L i) ∘ f + (fun (b : α) ↦ (c i)) | m] a := by
    rw [ae_all_iff]; intro i; apply condExp_comm_affine hm hf_int (L i) (c i)
  have pz : ∀ᵐ a ∂μ, ∀ i : ℕ, (re ∘ (L i) ∘ f + (fun (b : α) ↦ (c i))) a ≤ (φ ∘ f) a := by
    rw [ae_all_iff]; intro i; filter_upwards with a
    rw [Function.comp_apply, ← (hp (f a)).2, Pi.add_apply, Function.comp_apply, Function.comp_apply]
    apply le_ciSup (hp (f a)).1 i
  have pw : ∀ᵐ a ∂μ, ∀ i : ℕ, μ[(re ∘ (L i) ∘ f + (fun (b : α) ↦ (c i))) | m] a
    ≤ μ[φ ∘ f | m] a := by
    rw [ae_all_iff]; intro i; apply condExp_mono
    · let g := @reCLM ℝ (by infer_instance)
      have reLif_int : Integrable (fun (a : α) ↦ (re ∘ (L i)) (f a)) μ
        := integrable_comp (comp g (L i)) hf_int
      exact Integrable.add reLif_int (integrable_const (c i))
    · exact hφ_int
    · exact ae_all_iff.mp pz i
  filter_upwards [py, pw] with a
  intro hy hw
  rw [← (hp (μ[f | m] a)).right]
  apply ciSup_le
  intro i
  rw [hy i]
  apply hw i

/-- Conditional Jensen's inequality.
# TODO

Generalize this theorem to σ-finite measures.
-/
theorem conditional_jensen (hm : m ≤ mα)
    (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] := by
  classical
  borelize E
  have sep := hf_int.aestronglyMeasurable.isSeparable_ae_range
  rcases sep with ⟨t, ht, htt⟩
  let Y := (Submodule.span ℝ t).topologicalClosure
  have : CompleteSpace Y := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have : SecondCountableTopology Y := ht.span.closure.secondCountableTopology
  let φY := φ ∘ Y.subtypeL
  have hφY_cvx : ConvexOn ℝ Set.univ φY := hφ_cvx.comp_linearMap Y.subtype
  have hφY_cont : LowerSemicontinuous φY := hφ_cont.comp_continuous Y.subtypeL.cont
  have tsubY : t ⊆ Y := subset_trans Submodule.subset_span subset_closure
  have aeinY : ∀ᵐ (x : α) ∂μ, f x ∈ Y := by filter_upwards [htt] with a ha; exact tsubY ha
  let fY : α → Y := fun a => if h : f a ∈ Y then ⟨f a, h⟩ else 0
  let fX : α → E := Y.subtypeL ∘ fY
  have lem1 : f =ᵐ[μ] fX := by filter_upwards [aeinY] with a ha; simp [fX, fY, ha, reduceDIte]
  have hfX_int : Integrable fX μ := Integrable.congr hf_int lem1
  have hfY_int : Integrable fY μ := by
    constructor
    · have hs : MeasurableSet (Y : Set E) :=
        (Submodule.isClosed_topologicalClosure _).measurableSet
      have h_nonempty : (Y : Set E).Nonempty := Set.Nonempty.of_subtype
      obtain ⟨g, hg1, hg2 : ∀ x, g x ∈ Y, hg3⟩ :=
        hf_int.1.exists_stronglyMeasurable_range_subset hs h_nonempty aeinY
      use codRestrict g Y hg2
      constructor
      · rw [stronglyMeasurable_iff_measurable]
        exact hg1.measurable.codRestrict hg2
      · filter_upwards [hg3] with a ha1
        simp [fY, ha1, Set.codRestrict, dif_pos (hg2 a)]
    · apply hfX_int.2.mono
      simp [fX, Function.comp_apply, le_refl, Filter.eventually_true]
  have lem3 : μ[f | m] =ᵐ[μ] Y.subtypeL ∘ μ[fY | m] :=
    calc
      μ[f | m] =ᵐ[μ] μ[fX | m] := condExp_congr_ae lem1
      _        =ᵐ[μ] Y.subtypeL ∘ μ[fY | m] :=
        (condExp_comm_continuousLinearMap hm hfY_int Y.subtypeL).symm
  have lem2 : φ ∘ f =ᵐ[μ] φY ∘ fY := by filter_upwards [lem1] with a ha; simp [φY, ha, fX]
  have hφYfY_int : Integrable (φY ∘ fY) μ := hφ_int.congr lem2
  calc
    φ ∘ μ[f | m]
      =ᵐ[μ] φY ∘ μ[fY | m] := by filter_upwards [lem3] with a ha; simp [φY, ha]
    _ ≤ᵐ[μ] μ[φY ∘ fY | m] :=
      conditional_jensen_of_separableSpace hm hφY_cvx hφY_cont hfY_int hφYfY_int
    _ =ᵐ[μ] μ[φ ∘ f | m] := condExp_congr_ae lem2.symm
