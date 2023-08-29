/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.MeasureTheory.Covering.DensityTheorem

#align_import measure_theory.covering.liminf_limsup from "leanprover-community/mathlib"@"5f6e827d81dfbeb6151d7016586ceeb0099b9655"

/-!
# Liminf, limsup, and uniformly locally doubling measures.

This file is a place to collect lemmas about liminf and limsup for subsets of a metric space
carrying a uniformly locally doubling measure.

## Main results:

 * `blimsup_cthickening_mul_ae_eq`: the limsup of the closed thickening of a sequence of subsets
   of a metric space is unchanged almost everywhere for a uniformly locally doubling measure if the
   sequence of distances is multiplied by a positive scale factor. This is a generalisation of a
   result of Cassels, appearing as Lemma 9 on page 217 of
   [J.W.S. Cassels, *Some metrical theorems in Diophantine approximation. I*](cassels1950).
 * `blimsup_thickening_mul_ae_eq`: a variant of `blimsup_cthickening_mul_ae_eq` for thickenings
   rather than closed thickenings.

-/


open Set Filter Metric MeasureTheory TopologicalSpace

open scoped NNReal ENNReal Topology

variable {α : Type*} [MetricSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]

variable (μ : Measure α) [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]

/-- This is really an auxiliary result en route to `blimsup_cthickening_ae_le_of_eventually_mul_le`
(which is itself an auxiliary result en route to `blimsup_cthickening_mul_ae_eq`).

NB: The `: Set α` type ascription is present because of
https://github.com/leanprover-community/mathlib/issues/16932. -/
theorem blimsup_cthickening_ae_le_of_eventually_mul_le_aux (p : ℕ → Prop) {s : ℕ → Set α}
    (hs : ∀ i, IsClosed (s i)) {r₁ r₂ : ℕ → ℝ} (hr : Tendsto r₁ atTop (𝓝[>] 0)) (hrp : 0 ≤ r₁)
    {M : ℝ} (hM : 0 < M) (hM' : M < 1) (hMr : ∀ᶠ i in atTop, M * r₁ i ≤ r₂ i) :
    (blimsup (fun i => cthickening (r₁ i) (s i)) atTop p : Set α) ≤ᵐ[μ]
      (blimsup (fun i => cthickening (r₂ i) (s i)) atTop p : Set α) := by
  /- Sketch of proof:

  Assume that `p` is identically true for simplicity. Let `Y₁ i = cthickening (r₁ i) (s i)`, define
  `Y₂` similarly except using `r₂`, and let `(Z i) = ⋃_{j ≥ i} (Y₂ j)`. Our goal is equivalent to
  showing that `μ ((limsup Y₁) \ (Z i)) = 0` for all `i`.

  Assume for contradiction that `μ ((limsup Y₁) \ (Z i)) ≠ 0` for some `i` and let
  `W = (limsup Y₁) \ (Z i)`. Apply Lebesgue's density theorem to obtain a point `d` in `W` of
  density `1`. Since `d ∈ limsup Y₁`, there is a subsequence of `j ↦ Y₁ j`, indexed by
  `f 0 < f 1 < ...`, such that `d ∈ Y₁ (f j)` for all `j`. For each `j`, we may thus choose
  `w j ∈ s (f j)` such that `d ∈ B j`, where `B j = closedBall (w j) (r₁ (f j))`. Note that
  since `d` has density one, `μ (W ∩ (B j)) / μ (B j) → 1`.

  We obtain our contradiction by showing that there exists `η < 1` such that
  `μ (W ∩ (B j)) / μ (B j) ≤ η` for sufficiently large `j`. In fact we claim that `η = 1 - C⁻¹`
  is such a value where `C` is the scaling constant of `M⁻¹` for the uniformly locally doubling
  measure `μ`.

  To prove the claim, let `b j = closedBall (w j) (M * r₁ (f j))` and for given `j` consider the
  sets `b j` and `W ∩ (B j)`. These are both subsets of `B j` and are disjoint for large enough `j`
  since `M * r₁ j ≤ r₂ j` and thus `b j ⊆ Z i ⊆ Wᶜ`. We thus have:
  `μ (b j) + μ (W ∩ (B j)) ≤ μ (B j)`. Combining this with `μ (B j) ≤ C * μ (b j)` we obtain
  the required inequality. -/
  set Y₁ : ℕ → Set α := fun i => cthickening (r₁ i) (s i)
  -- ⊢ blimsup Y₁ atTop p ≤ᵐ[μ] blimsup (fun i => cthickening (r₂ i) (s i)) atTop p
  set Y₂ : ℕ → Set α := fun i => cthickening (r₂ i) (s i)
  -- ⊢ blimsup Y₁ atTop p ≤ᵐ[μ] blimsup Y₂ atTop p
  let Z : ℕ → Set α := fun i => ⋃ (j) (_ : p j ∧ i ≤ j), Y₂ j
  -- ⊢ blimsup Y₁ atTop p ≤ᵐ[μ] blimsup Y₂ atTop p
  suffices ∀ i, μ (atTop.blimsup Y₁ p \ Z i) = 0 by
    rwa [ae_le_set, @blimsup_eq_iInf_biSup_of_nat _ _ _ Y₂, iInf_eq_iInter, diff_iInter,
      measure_iUnion_null_iff]
  intros i
  -- ⊢ ↑↑μ (blimsup Y₁ atTop p \ Z i) = 0
  set W := atTop.blimsup Y₁ p \ Z i
  -- ⊢ ↑↑μ W = 0
  by_contra contra
  -- ⊢ False
  obtain ⟨d, hd, hd'⟩ : ∃ d, d ∈ W ∧ ∀ {ι : Type _} {l : Filter ι} (w : ι → α) (δ : ι → ℝ),
      Tendsto δ l (𝓝[>] 0) → (∀ᶠ j in l, d ∈ closedBall (w j) (2 * δ j)) →
        Tendsto (fun j => μ (W ∩ closedBall (w j) (δ j)) / μ (closedBall (w j) (δ j))) l (𝓝 1) :=
    Measure.exists_mem_of_measure_ne_zero_of_ae contra
      (IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ W 2)
  replace hd : d ∈ blimsup Y₁ atTop p := ((mem_diff _).mp hd).1
  -- ⊢ False
  obtain ⟨f : ℕ → ℕ, hf⟩ := exists_forall_mem_of_hasBasis_mem_blimsup' atTop_basis hd
  -- ⊢ False
  simp only [forall_and] at hf
  -- ⊢ False
  obtain ⟨hf₀ : ∀ j, d ∈ cthickening (r₁ (f j)) (s (f j)), hf₁, hf₂ : ∀ j, j ≤ f j⟩ := hf
  -- ⊢ False
  have hf₃ : Tendsto f atTop atTop :=
    tendsto_atTop_atTop.mpr fun j => ⟨f j, fun i hi => (hf₂ j).trans (hi.trans <| hf₂ i)⟩
  replace hr : Tendsto (r₁ ∘ f) atTop (𝓝[>] 0) := hr.comp hf₃
  -- ⊢ False
  replace hMr : ∀ᶠ j in atTop, M * r₁ (f j) ≤ r₂ (f j) := hf₃.eventually hMr
  -- ⊢ False
  replace hf₀ : ∀ j, ∃ w ∈ s (f j), d ∈ closedBall w (2 * r₁ (f j))
  -- ⊢ ∀ (j : ℕ), ∃ w, w ∈ s (f j) ∧ d ∈ closedBall w (2 * r₁ (f j))
  · intro j
    -- ⊢ ∃ w, w ∈ s (f j) ∧ d ∈ closedBall w (2 * r₁ (f j))
    specialize hrp (f j)
    -- ⊢ ∃ w, w ∈ s (f j) ∧ d ∈ closedBall w (2 * r₁ (f j))
    rw [Pi.zero_apply] at hrp
    -- ⊢ ∃ w, w ∈ s (f j) ∧ d ∈ closedBall w (2 * r₁ (f j))
    rcases eq_or_lt_of_le hrp with (hr0 | hrp')
    -- ⊢ ∃ w, w ∈ s (f j) ∧ d ∈ closedBall w (2 * r₁ (f j))
    · specialize hf₀ j
      -- ⊢ ∃ w, w ∈ s (f j) ∧ d ∈ closedBall w (2 * r₁ (f j))
      rw [← hr0, cthickening_zero, (hs (f j)).closure_eq] at hf₀
      -- ⊢ ∃ w, w ∈ s (f j) ∧ d ∈ closedBall w (2 * r₁ (f j))
      exact ⟨d, hf₀, by simp [← hr0]⟩
      -- 🎉 no goals
    · simpa using mem_iUnion₂.mp (cthickening_subset_iUnion_closedBall_of_lt (s (f j))
        (by positivity) (lt_two_mul_self hrp') (hf₀ j))
  choose w hw hw' using hf₀
  -- ⊢ False
  let C := IsUnifLocDoublingMeasure.scalingConstantOf μ M⁻¹
  -- ⊢ False
  have hC : 0 < C :=
    lt_of_lt_of_le zero_lt_one (IsUnifLocDoublingMeasure.one_le_scalingConstantOf μ M⁻¹)
  suffices ∃ η < (1 : ℝ≥0),
      ∀ᶠ j in atTop, μ (W ∩ closedBall (w j) (r₁ (f j))) / μ (closedBall (w j) (r₁ (f j))) ≤ η by
    obtain ⟨η, hη, hη'⟩ := this
    replace hη' : 1 ≤ η := by
      simpa only [ENNReal.one_le_coe_iff] using
        le_of_tendsto (hd' w (fun j => r₁ (f j)) hr <| eventually_of_forall hw') hη'
    exact (lt_self_iff_false _).mp (lt_of_lt_of_le hη hη')
  refine' ⟨1 - C⁻¹, tsub_lt_self zero_lt_one (inv_pos.mpr hC), _⟩
  -- ⊢ ∀ᶠ (j : ℕ) in atTop, ↑↑μ (W ∩ closedBall (w j) (r₁ (f j))) / ↑↑μ (closedBall …
  replace hC : C ≠ 0 := ne_of_gt hC
  -- ⊢ ∀ᶠ (j : ℕ) in atTop, ↑↑μ (W ∩ closedBall (w j) (r₁ (f j))) / ↑↑μ (closedBall …
  let b : ℕ → Set α := fun j => closedBall (w j) (M * r₁ (f j))
  -- ⊢ ∀ᶠ (j : ℕ) in atTop, ↑↑μ (W ∩ closedBall (w j) (r₁ (f j))) / ↑↑μ (closedBall …
  let B : ℕ → Set α := fun j => closedBall (w j) (r₁ (f j))
  -- ⊢ ∀ᶠ (j : ℕ) in atTop, ↑↑μ (W ∩ closedBall (w j) (r₁ (f j))) / ↑↑μ (closedBall …
  have h₁ : ∀ j, b j ⊆ B j := fun j =>
    closedBall_subset_closedBall (mul_le_of_le_one_left (hrp (f j)) hM'.le)
  have h₂ : ∀ j, W ∩ B j ⊆ B j := fun j => inter_subset_right W (B j)
  -- ⊢ ∀ᶠ (j : ℕ) in atTop, ↑↑μ (W ∩ closedBall (w j) (r₁ (f j))) / ↑↑μ (closedBall …
  have h₃ : ∀ᶠ j in atTop, Disjoint (b j) (W ∩ B j) := by
    apply hMr.mp
    rw [eventually_atTop]
    refine'
      ⟨i, fun j hj hj' => Disjoint.inf_right (B j) <| Disjoint.inf_right' (blimsup Y₁ atTop p) _⟩
    change Disjoint (b j) (Z i)ᶜ
    rw [disjoint_compl_right_iff_subset]
    refine' (closedBall_subset_cthickening (hw j) (M * r₁ (f j))).trans
      ((cthickening_mono hj' _).trans fun a ha => _)
    simp only [mem_iUnion, exists_prop]
    exact ⟨f j, ⟨hf₁ j, hj.le.trans (hf₂ j)⟩, ha⟩
  have h₄ : ∀ᶠ j in atTop, μ (B j) ≤ C * μ (b j) :=
    (hr.eventually (IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul'
      μ M hM)).mono fun j hj => hj (w j)
  refine' (h₃.and h₄).mono fun j hj₀ => _
  -- ⊢ ↑↑μ (W ∩ closedBall (w j) (r₁ (f j))) / ↑↑μ (closedBall (w j) (r₁ (f j))) ≤  …
  change μ (W ∩ B j) / μ (B j) ≤ ↑(1 - C⁻¹)
  -- ⊢ ↑↑μ (W ∩ B j) / ↑↑μ (B j) ≤ ↑(1 - C⁻¹)
  rcases eq_or_ne (μ (B j)) ∞ with (hB | hB); · simp [hB]
  -- ⊢ ↑↑μ (W ∩ B j) / ↑↑μ (B j) ≤ ↑(1 - C⁻¹)
                                                -- 🎉 no goals
  apply ENNReal.div_le_of_le_mul
  -- ⊢ ↑↑μ (W ∩ B j) ≤ ↑(1 - C⁻¹) * ↑↑μ (B j)
  rw [ENNReal.coe_sub, ENNReal.coe_one, ENNReal.sub_mul fun _ _ => hB, one_mul]
  -- ⊢ ↑↑μ (W ∩ B j) ≤ ↑↑μ (B j) - ↑C⁻¹ * ↑↑μ (B j)
  replace hB : ↑C⁻¹ * μ (B j) ≠ ∞
  -- ⊢ ↑C⁻¹ * ↑↑μ (B j) ≠ ⊤
  · refine' ENNReal.mul_ne_top _ hB
    -- ⊢ ↑C⁻¹ ≠ ⊤
    rwa [ENNReal.coe_inv hC, Ne.def, ENNReal.inv_eq_top, ENNReal.coe_eq_zero]
    -- 🎉 no goals
  obtain ⟨hj₁ : Disjoint (b j) (W ∩ B j), hj₂ : μ (B j) ≤ C * μ (b j)⟩ := hj₀
  -- ⊢ ↑↑μ (W ∩ B j) ≤ ↑↑μ (B j) - ↑C⁻¹ * ↑↑μ (B j)
  replace hj₂ : ↑C⁻¹ * μ (B j) ≤ μ (b j)
  -- ⊢ ↑C⁻¹ * ↑↑μ (B j) ≤ ↑↑μ (b j)
  · rw [ENNReal.coe_inv hC, ← ENNReal.div_eq_inv_mul]
    -- ⊢ ↑↑μ (B j) / ↑C ≤ ↑↑μ (b j)
    exact ENNReal.div_le_of_le_mul' hj₂
    -- 🎉 no goals
  have hj₃ : ↑C⁻¹ * μ (B j) + μ (W ∩ B j) ≤ μ (B j) := by
    refine' le_trans (add_le_add_right hj₂ _) _
    rw [← measure_union' hj₁ measurableSet_closedBall]
    exact measure_mono (union_subset (h₁ j) (h₂ j))
  replace hj₃ := tsub_le_tsub_right hj₃ (↑C⁻¹ * μ (B j))
  -- ⊢ ↑↑μ (W ∩ B j) ≤ ↑↑μ (B j) - ↑C⁻¹ * ↑↑μ (B j)
  rwa [ENNReal.add_sub_cancel_left hB] at hj₃
  -- 🎉 no goals
#align blimsup_cthickening_ae_le_of_eventually_mul_le_aux blimsup_cthickening_ae_le_of_eventually_mul_le_aux

/-- This is really an auxiliary result en route to `blimsup_cthickening_mul_ae_eq`.

NB: The `: Set α` type ascription is present because of
https://github.com/leanprover-community/mathlib/issues/16932. -/
theorem blimsup_cthickening_ae_le_of_eventually_mul_le (p : ℕ → Prop) {s : ℕ → Set α} {M : ℝ}
    (hM : 0 < M) {r₁ r₂ : ℕ → ℝ} (hr : Tendsto r₁ atTop (𝓝[>] 0))
    (hMr : ∀ᶠ i in atTop, M * r₁ i ≤ r₂ i) :
    (blimsup (fun i => cthickening (r₁ i) (s i)) atTop p : Set α) ≤ᵐ[μ]
      (blimsup (fun i => cthickening (r₂ i) (s i)) atTop p : Set α) := by
  let R₁ i := max 0 (r₁ i)
  -- ⊢ blimsup (fun i => cthickening (r₁ i) (s i)) atTop p ≤ᵐ[μ] blimsup (fun i =>  …
  let R₂ i := max 0 (r₂ i)
  -- ⊢ blimsup (fun i => cthickening (r₁ i) (s i)) atTop p ≤ᵐ[μ] blimsup (fun i =>  …
  have hRp : 0 ≤ R₁ := fun i => le_max_left 0 (r₁ i)
  -- ⊢ blimsup (fun i => cthickening (r₁ i) (s i)) atTop p ≤ᵐ[μ] blimsup (fun i =>  …
  replace hMr : ∀ᶠ i in atTop, M * R₁ i ≤ R₂ i
  -- ⊢ ∀ᶠ (i : ℕ) in atTop, M * R₁ i ≤ R₂ i
  · refine' hMr.mono fun i hi => _
    -- ⊢ M * R₁ i ≤ R₂ i
    rw [mul_max_of_nonneg _ _ hM.le, mul_zero]
    -- ⊢ max 0 (M * r₁ i) ≤ R₂ i
    exact max_le_max (le_refl 0) hi
    -- 🎉 no goals
  simp_rw [← cthickening_max_zero (r₁ _), ← cthickening_max_zero (r₂ _)]
  -- ⊢ blimsup (fun i => cthickening (max 0 (r₁ i)) (s i)) atTop p ≤ᵐ[μ] blimsup (f …
  cases' le_or_lt 1 M with hM' hM'
  -- ⊢ blimsup (fun i => cthickening (max 0 (r₁ i)) (s i)) atTop p ≤ᵐ[μ] blimsup (f …
  · apply HasSubset.Subset.eventuallyLE
    -- ⊢ blimsup (fun i => cthickening (max 0 (r₁ i)) (s i)) atTop p ⊆ blimsup (fun i …
    change _ ≤ _
    -- ⊢ blimsup (fun i => cthickening (max 0 (r₁ i)) (s i)) atTop p ≤ blimsup (fun i …
    refine' mono_blimsup' (hMr.mono fun i hi _ => cthickening_mono _ (s i))
    -- ⊢ max 0 (r₁ i) ≤ max 0 (r₂ i)
    exact (le_mul_of_one_le_left (hRp i) hM').trans hi
    -- 🎉 no goals
  · simp only [← @cthickening_closure _ _ _ (s _)]
    -- ⊢ blimsup (fun i => cthickening (max 0 (r₁ i)) (closure (s i))) atTop p ≤ᵐ[μ]  …
    have hs : ∀ i, IsClosed (closure (s i)) := fun i => isClosed_closure
    -- ⊢ blimsup (fun i => cthickening (max 0 (r₁ i)) (closure (s i))) atTop p ≤ᵐ[μ]  …
    exact blimsup_cthickening_ae_le_of_eventually_mul_le_aux μ p hs
      (tendsto_nhds_max_right hr) hRp hM hM' hMr
#align blimsup_cthickening_ae_le_of_eventually_mul_le blimsup_cthickening_ae_le_of_eventually_mul_le

/-- Given a sequence of subsets `sᵢ` of a metric space, together with a sequence of radii `rᵢ`
such that `rᵢ → 0`, the set of points which belong to infinitely many of the closed
`rᵢ`-thickenings of `sᵢ` is unchanged almost everywhere for a uniformly locally doubling measure if
the `rᵢ` are all scaled by a positive constant.

This lemma is a generalisation of Lemma 9 appearing on page 217 of
[J.W.S. Cassels, *Some metrical theorems in Diophantine approximation. I*](cassels1950).

See also `blimsup_thickening_mul_ae_eq`.

NB: The `: Set α` type ascription is present because of
https://github.com/leanprover-community/mathlib/issues/16932. -/
theorem blimsup_cthickening_mul_ae_eq (p : ℕ → Prop) (s : ℕ → Set α) {M : ℝ} (hM : 0 < M)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) :
    (blimsup (fun i => cthickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ]
      (blimsup (fun i => cthickening (r i) (s i)) atTop p : Set α) := by
  have : ∀ (p : ℕ → Prop) {r : ℕ → ℝ} (_ : Tendsto r atTop (𝓝[>] 0)),
      (blimsup (fun i => cthickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ]
        (blimsup (fun i => cthickening (r i) (s i)) atTop p : Set α) := by
    clear p hr r; intro p r hr
    have hr' : Tendsto (fun i => M * r i) atTop (𝓝[>] 0) := by
      convert TendstoNhdsWithinIoi.const_mul hM hr <;> simp only [mul_zero]
    refine' eventuallyLE_antisymm_iff.mpr ⟨_, _⟩
    · exact blimsup_cthickening_ae_le_of_eventually_mul_le μ p (inv_pos.mpr hM) hr'
        (eventually_of_forall fun i => by rw [inv_mul_cancel_left₀ hM.ne' (r i)])
    · exact blimsup_cthickening_ae_le_of_eventually_mul_le μ p hM hr
        (eventually_of_forall fun i => le_refl _)
  let r' : ℕ → ℝ := fun i => if 0 < r i then r i else 1 / ((i : ℝ) + 1)
  -- ⊢ blimsup (fun i => cthickening (M * r i) (s i)) atTop p =ᵐ[μ] blimsup (fun i  …
  have hr' : Tendsto r' atTop (𝓝[>] 0) := by
    refine' tendsto_nhdsWithin_iff.mpr
      ⟨Tendsto.if' hr tendsto_one_div_add_atTop_nhds_0_nat, eventually_of_forall fun i => _⟩
    by_cases hi : 0 < r i
    · simp [hi]
    · simp only [hi, one_div, mem_Ioi, if_false, inv_pos]; positivity
  have h₀ : ∀ i, p i ∧ 0 < r i → cthickening (r i) (s i) = cthickening (r' i) (s i) := by
    rintro i ⟨-, hi⟩; congr! 1; change r i = ite (0 < r i) (r i) _; simp [hi]
  have h₁ : ∀ i, p i ∧ 0 < r i → cthickening (M * r i) (s i) = cthickening (M * r' i) (s i) := by
    rintro i ⟨-, hi⟩; simp only [hi, mul_ite, if_true]
  have h₂ : ∀ i, p i ∧ r i ≤ 0 → cthickening (M * r i) (s i) = cthickening (r i) (s i) := by
    rintro i ⟨-, hi⟩
    have hi' : M * r i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM.le hi
    rw [cthickening_of_nonpos hi, cthickening_of_nonpos hi']
  have hp : p = fun i => p i ∧ 0 < r i ∨ p i ∧ r i ≤ 0 := by
    ext i; simp [← and_or_left, lt_or_le 0 (r i)]
  rw [hp, blimsup_or_eq_sup, blimsup_or_eq_sup]
  -- ⊢ ((blimsup (fun i => cthickening (M * r i) (s i)) atTop fun i => p i ∧ 0 < r  …
  simp only [sup_eq_union]
  -- ⊢ ((blimsup (fun i => cthickening (M * r i) (s i)) atTop fun i => p i ∧ 0 < r  …
  rw [blimsup_congr (eventually_of_forall h₀), blimsup_congr (eventually_of_forall h₁),
    blimsup_congr (eventually_of_forall h₂)]
  exact ae_eq_set_union (this (fun i => p i ∧ 0 < r i) hr') (ae_eq_refl _)
  -- 🎉 no goals
#align blimsup_cthickening_mul_ae_eq blimsup_cthickening_mul_ae_eq

theorem blimsup_cthickening_ae_eq_blimsup_thickening {p : ℕ → Prop} {s : ℕ → Set α} {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) (hr' : ∀ᶠ i in atTop, p i → 0 < r i) :
    (blimsup (fun i => cthickening (r i) (s i)) atTop p : Set α) =ᵐ[μ]
      (blimsup (fun i => thickening (r i) (s i)) atTop p : Set α) := by
  refine' eventuallyLE_antisymm_iff.mpr ⟨_, HasSubset.Subset.eventuallyLE (_ : _ ≤ _)⟩
  -- ⊢ blimsup (fun i => cthickening (r i) (s i)) atTop p ≤ᵐ[μ] blimsup (fun i => t …
  · rw [eventuallyLE_congr (blimsup_cthickening_mul_ae_eq μ p s (@one_half_pos ℝ _) r hr).symm
      EventuallyEq.rfl]
    apply HasSubset.Subset.eventuallyLE
    -- ⊢ blimsup (fun i => cthickening (1 / 2 * r i) (s i)) atTop p ⊆ blimsup (fun i  …
    change _ ≤ _
    -- ⊢ blimsup (fun i => cthickening (1 / 2 * r i) (s i)) atTop p ≤ blimsup (fun i  …
    refine' mono_blimsup' (hr'.mono fun i hi pi => cthickening_subset_thickening' (hi pi) _ (s i))
    -- ⊢ 1 / 2 * r i < r i
    nlinarith [hi pi]
    -- 🎉 no goals
  · exact mono_blimsup fun i _ => thickening_subset_cthickening _ _
    -- 🎉 no goals
#align blimsup_cthickening_ae_eq_blimsup_thickening blimsup_cthickening_ae_eq_blimsup_thickening

/-- An auxiliary result en route to `blimsup_thickening_mul_ae_eq`. -/
theorem blimsup_thickening_mul_ae_eq_aux (p : ℕ → Prop) (s : ℕ → Set α) {M : ℝ} (hM : 0 < M)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) (hr' : ∀ᶠ i in atTop, p i → 0 < r i) :
    (blimsup (fun i => thickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ]
      (blimsup (fun i => thickening (r i) (s i)) atTop p : Set α) := by
  have h₁ := blimsup_cthickening_ae_eq_blimsup_thickening (s := s) μ hr hr'
  -- ⊢ blimsup (fun i => thickening (M * r i) (s i)) atTop p =ᵐ[μ] blimsup (fun i = …
  have h₂ := blimsup_cthickening_mul_ae_eq μ p s hM r hr
  -- ⊢ blimsup (fun i => thickening (M * r i) (s i)) atTop p =ᵐ[μ] blimsup (fun i = …
  replace hr : Tendsto (fun i => M * r i) atTop (𝓝 0); · convert hr.const_mul M; simp
  -- ⊢ Tendsto (fun i => M * r i) atTop (𝓝 0)
                                                         -- ⊢ 0 = M * 0
                                                                                 -- 🎉 no goals
  replace hr' : ∀ᶠ i in atTop, p i → 0 < M * r i := hr'.mono fun i hi hip => mul_pos hM (hi hip)
  -- ⊢ blimsup (fun i => thickening (M * r i) (s i)) atTop p =ᵐ[μ] blimsup (fun i = …
  have h₃ := blimsup_cthickening_ae_eq_blimsup_thickening (s := s) μ hr hr'
  -- ⊢ blimsup (fun i => thickening (M * r i) (s i)) atTop p =ᵐ[μ] blimsup (fun i = …
  exact h₃.symm.trans (h₂.trans h₁)
  -- 🎉 no goals
#align blimsup_thickening_mul_ae_eq_aux blimsup_thickening_mul_ae_eq_aux

/-- Given a sequence of subsets `sᵢ` of a metric space, together with a sequence of radii `rᵢ`
such that `rᵢ → 0`, the set of points which belong to infinitely many of the
`rᵢ`-thickenings of `sᵢ` is unchanged almost everywhere for a uniformly locally doubling measure if
the `rᵢ` are all scaled by a positive constant.

This lemma is a generalisation of Lemma 9 appearing on page 217 of
[J.W.S. Cassels, *Some metrical theorems in Diophantine approximation. I*](cassels1950).

See also `blimsup_cthickening_mul_ae_eq`.

NB: The `: Set α` type ascription is present because of
https://github.com/leanprover-community/mathlib/issues/16932. -/
theorem blimsup_thickening_mul_ae_eq (p : ℕ → Prop) (s : ℕ → Set α) {M : ℝ} (hM : 0 < M) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) :
    (blimsup (fun i => thickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ]
      (blimsup (fun i => thickening (r i) (s i)) atTop p : Set α) := by
  let q : ℕ → Prop := fun i => p i ∧ 0 < r i
  -- ⊢ blimsup (fun i => thickening (M * r i) (s i)) atTop p =ᵐ[μ] blimsup (fun i = …
  have h₁ : blimsup (fun i => thickening (r i) (s i)) atTop p =
      blimsup (fun i => thickening (r i) (s i)) atTop q := by
    refine' blimsup_congr' (eventually_of_forall fun i h => _)
    replace hi : 0 < r i; · contrapose! h; apply thickening_of_nonpos h
    simp only [hi, iff_self_and, imp_true_iff]
  have h₂ : blimsup (fun i => thickening (M * r i) (s i)) atTop p =
      blimsup (fun i => thickening (M * r i) (s i)) atTop q := by
    refine' blimsup_congr' (eventually_of_forall fun i h => _)
    replace h : 0 < r i; · rw [← zero_lt_mul_left hM]; contrapose! h; apply thickening_of_nonpos h
    simp only [h, iff_self_and, imp_true_iff]
  rw [h₁, h₂]
  -- ⊢ blimsup (fun i => thickening (M * r i) (s i)) atTop q =ᵐ[μ] blimsup (fun i = …
  exact blimsup_thickening_mul_ae_eq_aux μ q s hM r hr (eventually_of_forall fun i hi => hi.2)
  -- 🎉 no goals
#align blimsup_thickening_mul_ae_eq blimsup_thickening_mul_ae_eq
