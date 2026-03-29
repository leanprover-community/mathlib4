/-
Copyright (c) 2026 Ivo Malinowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivo Malinowski
-/
module

import Mathlib.Probability.CentralLimitTheorem
--import Mathlib.Probability.CramerWold
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Multivariate central limit theorem

We prove the central limit theorem in dimension `d : ℕ+`.

## Main statement

*

## Tags

multivariate central limit theorem
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex RealInnerProductSpace
open scoped Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {d : ℕ+} {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}

variable [IsProbabilityMeasure P]

def standardGaussianRealMultivariate : Measure (EuclideanSpace ℝ (Fin d)) :=
  Measure.map (MeasurableEquiv.toLp 2 (Fin d → ℝ)) (Measure.pi (fun _ : Fin d => gaussianReal 0 1))

lemma isProbabilityMeasure_standardGaussianRealMultivariate :
    IsProbabilityMeasure (standardGaussianRealMultivariate (d := d)) := by
  dsimp [standardGaussianRealMultivariate]
  simpa using
    (Measure.isProbabilityMeasure_map
      (f := MeasurableEquiv.toLp 2 (Fin d → ℝ))
      (μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1))
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.aemeasurable)

theorem central_limit_multivariate
    (h0 : P[X 0] = 0)
    (h1 : ∀ i j, P[(fun ω ↦ (X 0 ω i) * (X 0 ω j))] = if i = j then 1 else 0)
    (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    Tendsto
      (fun n : ℕ =>
        ProbabilityMeasure.map
          (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
          ((Finset.aemeasurable_fun_sum (Finset.range n) (fun k _ ↦ (hident k).aemeasurable_fst)).const_smul ((√n)⁻¹)))
      atTop
      (𝓝
        ((⟨standardGaussianRealMultivariate (d := d),
            isProbabilityMeasure_standardGaussianRealMultivariate (d := d)⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin d))))) := by
    have i0 : Integrable (X 0) P := by
      have h_L2 : MemLp (fun ω => X 0 ω) 2 P := by
        have hXae : ∀ n, AEMeasurable (X n) P := fun n => (hident n).aemeasurable_fst
        refine ⟨(hXae 0).aestronglyMeasurable, ?_⟩

        unfold eLpNorm
        simp [eLpNorm']
        ring_nf
        rw [ENNReal.rpow_lt_top_iff_of_pos one_half_pos]

        conv_lhs => {
          arg 2
          enter [ω]
          rw [←ofReal_norm_eq_enorm, ←ENNReal.ofReal_pow (by {simp [norm_nonneg]}), ←real_inner_self_eq_norm_sq]
          simp [inner, ←pow_two]
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ => by {simp [sq_nonneg]})]
        }

        rw [lintegral_finset_sum' _ (fun _ => by {fun_prop})]
        rw [ENNReal.sum_lt_top]
        intro i hi
        conv_lhs => {
          arg 2
          enter [a]
          rw [←Real.enorm_eq_ofReal (by simp [sq_nonneg])]
        }

        rw [←hasFiniteIntegral_def]
        refine Integrable.hasFiniteIntegral ?_
        exact Integrable.of_integral_ne_zero (by {
          simp_rw [pow_two]
          rw [h1 i i]
          simp
        })

      apply MemLp.integrable (by norm_num : 1 ≤ (2 : ENNReal)) h_L2

    let μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) :=
      ⟨standardGaussianRealMultivariate (d := d),
        isProbabilityMeasure_standardGaussianRealMultivariate (d := d)⟩

    let μn : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) :=
      fun n =>
        ProbabilityMeasure.map
          (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
          ((Finset.aemeasurable_fun_sum (Finset.range n)
            (fun k _ ↦ (hident k).aemeasurable_fst)).const_smul ((√n)⁻¹))

    change Tendsto μn atTop (𝓝 μ)
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 ?_
    intro t

    by_cases ht : t = 0
    · simp [ht]

    have h_ne : ‖t‖ ≠ 0 := by simpa [norm_eq_zero] using ht
    have : Invertible ‖t‖ := invertibleOfNonzero h_ne

    let t' : EuclideanSpace ℝ (Fin d) := ‖t‖⁻¹ • t
    let Y : ℕ → Ω → ℝ := fun i ω => ⟪X i ω, t'⟫

    have hY_ae : ∀ i, AEMeasurable (Y i) P := by
      intro i
      dsimp [Y]
      exact AEMeasurable.inner_const ((hident i).aemeasurable_fst)

    have h0_Y : P[Y 0] = 0 := by
      dsimp [Y]
      calc
        ∫ ω : Ω, ⟪X 0 ω, t'⟫ ∂P
            = ∫ ω : Ω, ⟪t', (X 0 ω)⟫ ∂P := by
                simp only [real_inner_comm]
        _   = ⟪t', P[X 0]⟫ := by
              apply integral_inner i0
        _   = ⟪t', 0⟫ := by rw [h0]
        _   = 0 := by simp

    have h1_Y : P[(Y 0) ^ 2] = 1 := by
      dsimp [Y]
      calc
        --P[fun ω => (inner ℝ (X 0 ω) t') ^ 2]
        P[fun ω => ⟪(X 0 ω), t'⟫ ^ 2]
          = ∫ ω, ∑ i, ∑ j, (t' i * t' j) * (X 0 ω i * X 0 ω j) ∂P := by
              have h_expand :
                  ∀ ω,
                    ⟪X 0 ω, t'⟫ ^ 2
                      = ∑ i, ∑ j, (t' i * t' j) * (X 0 ω i * X 0 ω j) := by
                intro ω
                rw [PiLp.inner_apply]
                conv_lhs => {
                  arg 1
                  arg 2
                  intro
                  unfold inner
                  erw [@RCLike.inner_apply ℝ _ ((X 0 ω).ofLp _ : ℝ) (t'.ofLp _ : ℝ)]
                  simp
                }
                simp [pow_two, Finset.sum_mul_sum]
                simp_rw [←mul_assoc, mul_comm, ←mul_assoc]
              simp [h_expand]
        _ = ∑ i, ∑ j, (t' i * t' j) * ∫ ω, X 0 ω i * X 0 ω j ∂P := by
            have h_L2_pi (idx : Fin d) : MemLp (fun ω => (X 0 ω).ofLp idx) 2 P := by
              constructor
              · have h_cont : Continuous (fun (x : EuclideanSpace ℝ (Fin d)) => x.ofLp idx) := by
                  fun_prop
                exact Continuous.comp_aestronglyMeasurable h_cont i0.aestronglyMeasurable
              · unfold eLpNorm
                simp [eLpNorm']
                ring_nf
                rw [ENNReal.rpow_lt_top_iff_of_pos one_half_pos]
                simp_rw [Real.enorm_eq_ofReal_abs]
                conv_lhs =>
                  arg 2
                  enter [a]
                  rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, ← abs_sq,
                    ← Real.enorm_eq_ofReal_abs, pow_two]
                rw [← hasFiniteIntegral_def]
                refine Integrable.hasFiniteIntegral ?_
                exact Integrable.of_integral_ne_zero (by
                  rw [h1 idx idx]
                  simp)

            have h_integrable_prod (i' j' : Fin d) :
                Integrable (fun ω ↦ X 0 ω i' * X 0 ω j') P := by
              apply MemLp.integrable
              rfl
              exact
                @MemLp.mul Ω _ ℝ _ P 2 2 1
                  (fun ω => X 0 ω j') (fun ω => X 0 ω i')
                  (h_L2_pi j') (h_L2_pi i') _

            rw [integral_finset_sum]
            · apply Finset.sum_congr rfl
              intro i hi
              rw [integral_finset_sum]
              · apply Finset.sum_congr rfl
                intro j hj
                rw [integral_const_mul]
              · intro j hj
                exact (h_integrable_prod i j).const_mul (t' i * t' j)
            · intro i hi
              apply MeasureTheory.integrable_finset_sum
              intro j hj
              exact (h_integrable_prod i j).const_mul (t' i * t' j)
        _ = ∑ i, ∑ j, (t' i * t' j) * (if i = j then 1 else 0) := by
            simp_rw [h1]
        _ = ∑ i, (t' i) ^ 2 := by
            simp [pow_two]
        _ = ‖t'‖ ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq]
            simp [pow_two]
        _ = 1 := by
            simp [t', norm_smul]

    have hindepY : iIndepFun Y P := by
      refine hindep.comp (fun _ x ↦ ⟪x, t'⟫) ?_
      simpa using (Measurable.inner measurable_id measurable_const)

    have hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P := by
      intro i
      refine (hident i).comp (u := fun x ↦ ⟪x, t'⟫) ?_
      simpa using (Measurable.inner measurable_id measurable_const)

    have hchar_scalar :
        Tendsto
          (fun n : ℕ => charFun (P.map (Y 0)) ((√n)⁻¹ * ‖t‖) ^ n)
          atTop
          (𝓝 (Complex.exp (-(‖t‖ ^ 2 / 2)))) := by
      simpa [mul_comm, mul_left_comm, mul_assoc, pow_two, neg_div]
        using
          (tendsto_charFun_inv_sqrt_mul_pow
            (P := P) (X := Y 0) (hY_ae 0) h0_Y h1_Y ‖t‖)

    have h_proj_sum :
        ∀ (n : ℕ) ω,
          ⟪((√n)⁻¹ • ∑ k ∈ Finset.range n, X k ω), t⟫
            = ‖t‖ * ((√n)⁻¹ * ∑ k ∈ Finset.range n, Y k ω) := by
      intro n ω
      calc
        ⟪((√n)⁻¹ • ∑ k ∈ Finset.range n, X k ω), t⟫
            = (√n)⁻¹ * ⟪∑ k ∈ Finset.range n, X k ω, t⟫ := by
                rw [inner_smul_left]
                simp
        _   = (√n)⁻¹ * ∑ k ∈ Finset.range n, ⟪X k ω, t⟫ := by
                rw [sum_inner]
        _   = (√n)⁻¹ * ∑ k ∈ Finset.range n, (‖t‖ * ⟪X k ω, t'⟫) := by
                simp [t', inner_smul_right, ← mul_assoc,
                  mul_inv_cancel_of_invertible ‖t‖]
        _   = ‖t‖ * ((√n)⁻¹ * ∑ k ∈ Finset.range n, Y k ω) := by
                dsimp [Y]
                ring_nf
                simp [Finset.mul_sum, mul_assoc]

    have h_char_μ :
        charFun μ t = Complex.exp (-(‖t‖ ^ 2 / 2)) := by
      let mInner : EuclideanSpace ℝ (Fin d) → ℝ := fun z => ⟪z, t⟫
      have hmInner : Measurable mInner :=
        Measurable.inner measurable_id measurable_const
      let hf : ℝ → ℝ := fun y => ‖t‖ * y
      have hhf : Measurable hf := Measurable.mul measurable_const measurable_id

      have h_map_rhs :
        ProbabilityMeasure.map μ hmInner.aemeasurable
          = ProbabilityMeasure.map (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) hhf.aemeasurable := by
        -- 1. Expose the raw measures
        apply Subtype.ext

        -- 2. Use `change` with the full expressions to satisfy the typeclass system
        -- without introducing opaque `let` bindings.
        change (ProbabilityMeasure.map μ hmInner.aemeasurable : Measure ℝ) =
              (ProbabilityMeasure.map (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) hhf.aemeasurable : Measure ℝ)

        -- 3. Apply extensionality
        apply Measure.ext_of_charFun
        funext u

        have hsmul :
            AEStronglyMeasurable (fun x : ℝ => Complex.exp (u * x * Complex.I))
              (gaussianReal 0 1) := by
          apply Continuous.aestronglyMeasurable
          exact continuous_exp.comp
            ((continuous_const.mul continuous_ofReal).mul continuous_const)

          -- 1. Prove continuity (which is independent of any specific measure)
        have hg_cont : Continuous (fun x : ℝ => Complex.exp (u * x * Complex.I)) := by
          exact continuous_exp.comp ((continuous_const.mul continuous_ofReal).mul continuous_const)

        rw [charFun_apply_real, charFun_apply_real]
        rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]

        conv_rhs =>
          -- 2. Call .aestronglyMeasurable on the fly for the RHS mapped measure
          rw [integral_map hhf.aemeasurable hg_cont.aestronglyMeasurable]
          simp [hf]
          arg 2
          enter [x]
          rw [← mul_assoc, ← Complex.ofReal_mul]

        conv_lhs =>
          -- 3. Call .aestronglyMeasurable on the fly for the LHS mapped measure
          rw [integral_map hmInner.aemeasurable hg_cont.aestronglyMeasurable]
          arg 2
          enter [x]
          rw [← Complex.ofReal_mul]

        dsimp [μ, standardGaussianRealMultivariate]
        -- 1. Prove continuity for the LHS composed function
        have h_cont_LHS : Continuous (fun x : EuclideanSpace ℝ (Fin d) ↦
            Complex.exp (↑(u * mInner x) * Complex.I)) := by
          fun_prop

        -- 2. Explicitly pull the integral back through the `toLp` map
        rw [integral_map (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.aemeasurable h_cont_LHS.aestronglyMeasurable]

        -- 3. NOW the measures perfectly match!
        change
          ∫ x : (Fin d → ℝ),
              Complex.exp (↑(u * ∑ i, t.ofLp i * x i) * Complex.I)
            ∂ (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1))
          = _
        simp_rw [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
        -- 1. Explicitly state the equality
        have h_prod_int :
          ∫ (x : Fin d → ℝ), ∏ i, Complex.exp (↑(u * (t.ofLp i * x i)) * Complex.I) ∂Measure.pi (fun _ ↦ gaussianReal 0 1) =
          ∏ i, ∫ (y : ℝ), Complex.exp (↑(u * (t.ofLp i * y)) * Complex.I) ∂gaussianReal 0 1 := by
          -- 2. Explicitly provide the measure so the typeclass system doesn't have to guess
          exact integral_fintype_prod_eq_prod (μ := fun _ ↦ gaussianReal 0 1)
            (fun i (y : ℝ) ↦ Complex.exp (↑(u * (t.ofLp i * y)) * Complex.I))

        -- 3. Force the rewrite
        erw [h_prod_int]

        simp_rw [← charFun_apply_real, charFun_gaussianReal]

        -- 1. Regroup the multiplication: u * (t * y) -> (u * t) * y
        -- and split the real-to-complex coercion: ↑((u * t) * y) -> ↑(u * t) * ↑y
        simp_rw [← mul_assoc, Complex.ofReal_mul]

        -- 1. Quarantine the aggressive rewrites to the left side only!
        conv_lhs => {
          enter [2]
          intro
          enter [2]
          intro
          enter [1]
          enter [1]
          rw [← Complex.ofReal_mul]
        }

        -- 2. Now BOTH sides are perfectly teed up for the characteristic function
        simp_rw [← charFun_apply_real, charFun_gaussianReal]

        -- 3. Combine the product of exponentials into the exponential of a sum
        rw [← Complex.exp_sum]
        simp
        ring
        rw [← Finset.sum_mul, ← Finset.mul_sum, ← Complex.ofReal_pow, ← Complex.ofReal_pow]
        simp [PiLp.norm_sq_eq_of_L2]
        ring

      have hcf :
          charFun (ProbabilityMeasure.map μ hmInner.aemeasurable) (1 : ℝ)
            = charFun (ProbabilityMeasure.map (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) hhf.aemeasurable) (1 : ℝ) := by
        simpa [h_map_rhs]

      -- 1. The LHS Bridge: Unfold the characteristic functions and use integral_map
      have h_LHS : charFun μ t = charFun (ProbabilityMeasure.map μ hmInner.aemeasurable) (1 : ℝ) := by
        rw [charFun_apply, ProbabilityMeasure.toMeasure_map, charFun_apply_real]
        have h_cont : Continuous (fun (y : ℝ) ↦ Complex.exp (↑(1 : ℝ) * ↑y * Complex.I)) := by fun_prop
        rw [integral_map hmInner.aemeasurable h_cont.aestronglyMeasurable]
        congr 1
        ext x
        dsimp [hmInner, mInner]
        push_cast
        simp

      -- 2. The RHS Bridge: Pull the mapped gaussian back to the standard 1D gaussian
      have h_RHS : charFun (ProbabilityMeasure.map (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) hhf.aemeasurable) (1 : ℝ) = Complex.exp (-(↑‖t‖ ^ 2 / 2)) := by
        rw [ProbabilityMeasure.toMeasure_map, charFun_apply_real]
        have h_cont : Continuous (fun (y : ℝ) ↦ Complex.exp (↑(1 : ℝ) * ↑y * Complex.I)) := by fun_prop
        rw [integral_map hhf.aemeasurable h_cont.aestronglyMeasurable]

        -- Pull in the standard 1D Gaussian characteristic function theorem
        have h_gauss := charFun_gaussianReal (μ := 0) (v := 1) (t := ‖t‖)
        rw [charFun_apply_real] at h_gauss

        -- Clean up our integral to perfectly match the LHS of h_gauss
        dsimp [hf]

        simp

        -- The integral is now a perfect match! Swap it out.
        rw [h_gauss]
        simp

      -- 3. The Final Strike: Link the LHS bridge -> hcf -> RHS bridge!
      rw [h_LHS, hcf, h_RHS]

    have h_char_μn :
        ∀ n,
          charFun (μn n) t
            = charFun (P.map (Y 0)) ((√n)⁻¹ * ‖t‖) ^ n := by
      intro n
      have hsum_ae :
          (fun ω =>
            ⟪((√n)⁻¹ • ∑ k ∈ Finset.range n, X k ω), t⟫)
          =ᵐ[P]
          (fun ω => ‖t‖ * ((√n)⁻¹ * ∑ k ∈ Finset.range n, Y k ω)) :=
        Filter.Eventually.of_forall (h_proj_sum n)

      simp only [μn, charFun]
      rw [ProbabilityMeasure.toMeasure_map]

      -- 1. Strip the ProbabilityMeasure wrapper off of P so integral_map can see it
      simp_rw [ProbabilityMeasure.coe_mk]

      -- 2. Let fun_prop prove continuity for the EXACT lambda function in the integral
      have h_cont : Continuous (fun x : EuclideanSpace ℝ (Fin d) ↦ Complex.exp (↑⟪x, t⟫ * Complex.I)) := by
        fun_prop

      -- 3. Isolate the measurability proof just to keep the rw line readable
      have h_meas : AEMeasurable ((√n)⁻¹ • fun a ↦ ∑ i ∈ Finset.range n, X i a) P :=
        (Finset.aemeasurable_fun_sum (Finset.range n)
          (fun k _ ↦ (hident k).aemeasurable_fst)).const_smul ((√n)⁻¹)

      -- 4. Now the rewrite perfectly matches both the function and the measure!
      rw [integral_map h_meas h_cont.aestronglyMeasurable]
      simp_rw [Pi.smul_apply]
      simp_rw [h_proj_sum]

      -- 1. Fold the RHS integral directly back into its charFun definition
      change _ = charFun (Measure.map (Y 0) P) ((√↑n)⁻¹ * ‖t‖) ^ n

      -- 2. Create a sub-proof to fold the LHS integral back into a charFun
      have h_LHS : ∫ (x : Ω), cexp (↑(‖t‖ * ((√↑n)⁻¹ * ∑ k ∈ Finset.range n, Y k x)) * I) ∂P =
                   charFun (Measure.map (fun ω ↦ (√↑n)⁻¹ * ∑ k ∈ Finset.range n, Y k ω) P) ‖t‖ := by
        -- Use the REAL charFun definition to avoid the inner product typeclass mismatch!
        rw [charFun_apply_real]

        -- Prove the mapped function is AEMeasurable
        have h_meas_Y : AEMeasurable (fun ω ↦ (√↑n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω) P := by
          apply AEMeasurable.mul aemeasurable_const
          exact Finset.aemeasurable_fun_sum (Finset.range n) (fun k _ ↦ hY_ae k)

        -- Notice the continuity function perfectly matches the ↑t * ↑x structure
        have h_cont_Y : Continuous (fun (x : ℝ) ↦ Complex.exp (↑‖t‖ * ↑x * Complex.I)) := by fun_prop

        -- Pull the integral back to P
        rw [integral_map h_meas_Y h_cont_Y.aestronglyMeasurable]

        -- The RHS is now cexp (↑‖t‖ * ↑(...) * I).
        -- Combine the two real coercions back into one so it exactly matches the LHS!
        simp_rw [← Complex.ofReal_mul]

      -- 3. Substitute the folded LHS
      rw [h_LHS]

      rw [charFun_inv_sqrt_mul_sum]
      · apply hindepY
      exact hidentY
    -- 1. Rewrite the sequence and the limit point using our two bridge lemmas
    simp_rw [h_char_μn, h_char_μ]

    -- 2. The goal is now character-for-character identical to the 1D scalar limit!
    exact hchar_scalar

theorem tendstoInDistribution_sqrt_inv_mul_sum {Y : Ω → (EuclideanSpace ℝ (Fin d))} (hY : HasLaw Y standardGaussianRealMultivariate P)
    (h0 : P[X 0] = 0) (h1 : ∀ i j, P[(fun ω ↦ (X 0 ω i) * (X 0 ω j))] = if i = j then 1 else 0) (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ • ∑ k ∈ Finset.range n, X k ω) atTop Y
      (fun _ ↦ P) P where
  forall_aemeasurable n :=
    .const_smul (Finset.aemeasurable_fun_sum _ fun _ _ ↦ (hident _).aemeasurable_fst) ((√n)⁻¹)
  tendsto := by
    have hclt :
        Tendsto
          (fun n : ℕ =>
            ProbabilityMeasure.map
              (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
              ((Finset.aemeasurable_fun_sum (Finset.range n) (fun k _ ↦ (hident k).aemeasurable_fst)).const_smul ((√n)⁻¹)))
          atTop
          (𝓝
            ((⟨standardGaussianRealMultivariate (d := d),
                isProbabilityMeasure_standardGaussianRealMultivariate (d := d)⟩ :
              ProbabilityMeasure (EuclideanSpace ℝ (Fin d))))) :=
      central_limit_multivariate (P := P) (d := d) (X := X) h0 h1 hindep hident

    have hmapY_eq : Measure.map Y P = standardGaussianRealMultivariate (d := d) := by
      exact hY.map_eq

    have hmapY_prob : IsProbabilityMeasure (Measure.map Y P) := by
      rw [hmapY_eq]
      exact isProbabilityMeasure_standardGaussianRealMultivariate (d := d)

    have hY' :
        (⟨Measure.map Y P, hmapY_prob⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) =
        (⟨standardGaussianRealMultivariate (d := d),
          isProbabilityMeasure_standardGaussianRealMultivariate (d := d)⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) := by
      apply Subtype.ext
      exact hmapY_eq

    simpa [hY'] using hclt
