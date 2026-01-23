/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/
import Mathlib.Analysis.Complex.DivisorConvergence
import Mathlib.Analysis.Complex.DivisorFiber

/-!
# Fiber/complement splitting for divisor-indexed partial products

This file defines finitary “partial products” of Weierstrass factors indexed by the divisor, and
develops the corresponding fiber/complement splitting. It also defines the complement canonical
product (replacing fiber factors by `1`) and proves its convergence/holomorphy properties.
-/

noncomputable section

open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

/-!
## Partial products as a named function

This is a convenience API: many later arguments about multiplicities/quotients are easier to write
using a named partial product function rather than repeating `∏ p ∈ s, ...`.
-/

/-- Finite partial product of Weierstrass factors indexed by a finset of divisor indices. -/
noncomputable def divisorPartialProduct (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)

@[simp] lemma divisorPartialProduct_def (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) :
    divisorPartialProduct m f s z = ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p) :=
  rfl

/-!
## Splitting finite partial products into fiber vs complement

This is the finitary “fiber × complement” split.
-/

/-- The partial product over indices *not* in the fiber over `z₀` (implemented via an `if`). -/
noncomputable def divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ := by
    classical
    exact  ∏ p ∈ s, if p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ then (1 : ℂ)
        else weierstrassFactor m (z / divisorZeroIndex₀_val p)

@[simp] lemma divisorComplementPartialProduct_def
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) :
    divisorComplementPartialProduct m f z₀ s z =
      ∏ p ∈ s, if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
        else weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
  classical
  simp [divisorComplementPartialProduct, mem_divisorZeroIndex₀_fiberFinset]

/-!
## Complement canonical product (fiber factors removed)

For a fixed point `z₀`, we often want to split the infinite product into a finite “fiber part”
(`val = z₀`, accounting for the multiplicity) and an infinite “complement part” (all other indices).

To keep the definition total and Mathlib-idiomatic, we implement the complement part by inserting
the neutral element `1` on the fiber indices.
-/

/-- The infinite product over indices *not* in the fiber over `z₀` (the “complement” canonical
product). -/
noncomputable def divisorComplementCanonicalProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (z : ℂ) : ℂ := by
    classical
    exact  ∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        if p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ then (1 : ℂ)
        else weierstrassFactor m (z / divisorZeroIndex₀_val p)

/-- The factor used in the complement canonical product: it is `1` on the fiber over `z₀`, and
otherwise the Weierstrass factor `weierstrassFactor m (z / p)`. -/
noncomputable def divisorComplementFactor
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) : ℂ := by
    classical
    exact if p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ then (1 : ℂ)
      else weierstrassFactor m (z / divisorZeroIndex₀_val p)

/-!
## Convergence/holomorphy of the complement canonical product

This is the same M-test argument as for `divisorCanonicalProduct`, but with finitely many factors
replaced by `1`. We keep the same summability hypothesis.
-/

theorem hasProdUniformlyOn_divisorComplementCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) {K : Set ℂ} (hK : IsCompact K)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdUniformlyOn (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        divisorComplementFactor m f z₀ p z) (divisorComplementCanonicalProduct m f z₀)
      K := by
  classical
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  set R : ℝ := max R0 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hnormK : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)
  let term : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ := fun p z =>
    divisorComplementFactor m f z₀ p z
  let g : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ := fun p z => term p z - 1
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀_val p‖ := by
    have hfin :
        ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ 2 * R} :
          Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀_val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ∀ z ∈ K, ‖g p z‖ ≤ u p := by
    filter_upwards [h_big] with p hp z hzK
    by_cases hpF : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀
    · have hval : divisorZeroIndex₀_val p = z₀ :=
        (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hpF
      have hu0 : 0 ≤ u p := by
        dsimp [u]
        refine mul_nonneg ?_ ?_
        · nlinarith [pow_nonneg (show 0 ≤ R from le_of_lt hRpos) (m + 1)]
        · exact pow_nonneg (inv_nonneg.2 (norm_nonneg _)) (m + 1)
      simp [g, term, divisorComplementFactor, hval, hu0, sub_eq_add_neg]
    · have hzle : ‖z‖ ≤ R := hnormK z hzK
      have hz_div : ‖z / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) := by
        have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
        have hinv : ‖divisorZeroIndex₀_val p‖⁻¹ < (2 * R)⁻¹ := by
          simpa [one_div] using (one_div_lt_one_div_of_lt h2R_pos hp)
        have hmul_le : ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ ≤ R * ‖divisorZeroIndex₀_val p‖⁻¹ := by
          refine mul_le_mul_of_nonneg_right hzle ?_
          exact inv_nonneg.2 (norm_nonneg _)
        have hmul_lt : R * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
          mul_lt_mul_of_pos_left hinv hRpos
        have hlt : ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
          lt_of_le_of_lt hmul_le hmul_lt
        have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
          have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
          have : R * (2 * R)⁻¹ = R / (2 * R) := by simp [div_eq_mul_inv]
          rw [this]
          field_simp [hRne]
        have hnorm : ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
          simp [div_eq_mul_inv]
        have hzlt : ‖z / divisorZeroIndex₀_val p‖ < (1 / 2 : ℝ) := by
          calc
            ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := hnorm
            _ < R * (2 * R)⁻¹ := hlt
            _ = (1 / 2 : ℝ) := hRhalf
        exact le_of_lt hzlt
      have hE : ‖weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1‖ ≤
            4 * ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) :=
        weierstrassFactor_sub_one_pow_bound (m := m) (z := z / divisorZeroIndex₀_val p) hz_div
      have hz_pow : ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) ≤
            (R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
        have : ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
          simp [div_eq_mul_inv]
        rw [this]
        have : (‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹) ^ (m + 1) =
            ‖z‖ ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
          simp [mul_pow]
        rw [this]
        have hzle_pow : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
          pow_le_pow_left₀ (norm_nonneg z) hzle (m + 1)
        gcongr
      dsimp [g, term, u]
      simp [divisorComplementFactor, hpF] at *
      nlinarith [hE, hz_pow]
  have hcts : ∀ p, ContinuousOn (g p) K := by
    intro p
    by_cases hpF : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀
    · have hval : divisorZeroIndex₀_val p = z₀ :=
        (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hpF
      simpa [g, term, divisorComplementFactor, hval, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using
        (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℂ)) K)
    · have hvalne : divisorZeroIndex₀_val p ≠ z₀ :=
        (not_mem_divisorZeroIndex₀_fiberFinset_iff_val_ne (f := f) z₀ p).1 hpF
      have hcontE : Continuous (fun z : ℂ => weierstrassFactor m z) := by
        have hcontPL : Continuous (fun z : ℂ => partialLogSum m z) := by
          classical
          unfold partialLogSum
          refine continuous_finset_sum _ ?_
          intro k hk
          have hpow : Continuous fun z : ℂ => z ^ (k + 1) := continuous_pow (k + 1)
          simpa [div_eq_mul_inv] using hpow.mul continuous_const
        have hsub : Continuous fun z : ℂ => (1 : ℂ) - z := continuous_const.sub continuous_id
        have hexp : Continuous fun z : ℂ => Complex.exp (partialLogSum m z) :=
          Complex.continuous_exp.comp hcontPL
        simpa [weierstrassFactor] using hsub.mul hexp
      have hdiv : Continuous fun z : ℂ => z / divisorZeroIndex₀_val p := by
        simpa [div_eq_mul_inv] using (continuous_id.mul continuous_const)
      have hcont : Continuous fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p) :=
        hcontE.comp hdiv
      have : ContinuousOn (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1) K :=
        (hcont.continuousOn.sub continuous_const.continuousOn)
      simpa [g, term, divisorComplementFactor, mem_divisorZeroIndex₀_fiberFinset, hvalne] using this
  have hprod :
      HasProdUniformlyOn (fun p z ↦ 1 + g p z) (fun z ↦ ∏' p, (1 + g p z)) K := by
    simpa using
      Summable.hasProdUniformlyOn_one_add (f := g) (u := u) (K := K) hK hu hBound hcts
  have hterm :
      HasProdUniformlyOn (fun p z ↦ term p z) (fun z ↦ ∏' p, term p z) K := by
    simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hprod
  refine hterm.congr_right ?_
  intro z hz
  classical
  simp [term, divisorComplementCanonicalProduct, divisorComplementFactor]

theorem hasProdLocallyUniformlyOn_divisorComplementCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdLocallyUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        divisorComplementFactor m f z₀ p z)
      (divisorComplementCanonicalProduct m f z₀)
      (Set.univ : Set ℂ) := by
  classical
  refine hasProdLocallyUniformlyOn_of_forall_compact
      (f := fun p z => divisorComplementFactor m f z₀ p z)
      (g := divisorComplementCanonicalProduct m f z₀) (s := (Set.univ : Set ℂ))
      isOpen_univ ?_
  intro K hKU hK
  simpa using
    (hasProdUniformlyOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀)
      (K := K) hK h_sum)

theorem tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    TendstoLocallyUniformlyOn
      (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
        divisorComplementPartialProduct m f z₀ s)
      (divisorComplementCanonicalProduct m f z₀)
      Filter.atTop
      (Set.univ : Set ℂ) := by
  classical
  have hprod :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
          divisorComplementFactor m f z₀ p z)
        (divisorComplementCanonicalProduct m f z₀)
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorComplementCanonicalProduct_univ (m := m) (f := f)
      (z₀ := z₀) h_sum
  have h :
      TendstoLocallyUniformlyOn
        (fun (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) =>
          ∏ p ∈ s,
            if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
            else weierstrassFactor m (z / divisorZeroIndex₀_val p))
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) := by
    simpa [HasProdLocallyUniformlyOn, divisorComplementFactor, mem_divisorZeroIndex₀_fiberFinset]
      using hprod
  refine h.congr (G := fun s z => divisorComplementPartialProduct m f z₀ s z) ?_
  intro s z hz
  simp [divisorComplementPartialProduct_def]

theorem differentiableOn_divisorComplementCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀) (Set.univ : Set ℂ) := by
  classical
  have hloc :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s)
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) :=
    tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ (m := m) (f := f)
      (z₀ := z₀) h_sum
  have hF :
      ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in Filter.atTop,
        DifferentiableOn ℂ (divisorComplementPartialProduct m f z₀ s) (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    have hdiff : Differentiable ℂ (divisorComplementPartialProduct m f z₀ s) := by
      let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
        fun p z =>
          if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
          else weierstrassFactor m (z / divisorZeroIndex₀_val p)
      have hΦ : ∀ p ∈ s, Differentiable ℂ (Φ p) := by
        intro p hp
        classical
        by_cases hval : divisorZeroIndex₀_val p = z₀
        · simp [Φ, hval]
        · have hdiv : Differentiable ℂ (fun z : ℂ => z / divisorZeroIndex₀_val p) := by
            simp [div_eq_mul_inv]
          simpa [Φ, hval] using (differentiable_weierstrassFactor m).comp hdiv
      have hEq : (fun z : ℂ => ∏ p ∈ s, Φ p z) = divisorComplementPartialProduct m f z₀ s := by
        ext z
        simp [Φ, divisorComplementPartialProduct_def]
      have : Differentiable ℂ (fun z : ℂ => ∏ p ∈ s, Φ p z) := by
        simpa using (Differentiable.fun_finset_prod (𝕜 := ℂ) (f := Φ) (u := s) hΦ)
      simpa [hEq] using this
    simpa using hdiff.differentiableOn
  haveI : (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))).NeBot :=
    Filter.atTop_neBot
  exact hloc.differentiableOn hF isOpen_univ

lemma divisorPartialProduct_eq_fiber_mul_complement_of_subset
    (m : ℕ) (f : ℂ → ℂ) (z₀ z : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s) :
    divisorPartialProduct m f s z =
      divisorPartialProduct m f (divisorZeroIndex₀_fiberFinset (f := f) z₀) z *
        divisorComplementPartialProduct m f z₀ s z := by
  classical
  let fiber : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    divisorZeroIndex₀_fiberFinset (f := f) z₀
  let P : divisorZeroIndex₀ f (Set.univ : Set ℂ) → Prop := fun p => p ∈ fiber
  let term : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ :=
    fun p => weierstrassFactor m (z / divisorZeroIndex₀_val p)
  have hfilter : s.filter P = fiber := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr ⟨hs hp, hp⟩
  have hsplit :
      (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) = ∏ p ∈ s, term p := by
    simpa [term] using
      (Finset.prod_filter_mul_prod_filter_not (s := s) (p := P) (f := term))
  have hP : (∏ p ∈ s with P p, term p) = divisorPartialProduct m f fiber z := by
    have hg : ∀ x ∈ s \ fiber, (if x ∈ fiber then term x else (1 : ℂ)) = 1 := by
      intro x hx
      have hxnot : x ∉ fiber := (Finset.mem_sdiff.mp hx).2
      simp [hxnot]
    have hfg :
        ∀ x ∈ fiber, term x = (if x ∈ fiber then term x else (1 : ℂ)) := by
      intro x hx
      simp [hx]
    have hsub := (Finset.prod_subset_one_on_sdiff (s₁ := fiber) (s₂ := s)
        (f := term) (g := fun x => if x ∈ fiber then term x else (1 : ℂ)) hs hg hfg)
    simpa [divisorPartialProduct, term, P, fiber, Finset.prod_filter] using hsub.symm
  have hnotP : (∏ p ∈ s with ¬ P p, term p) = divisorComplementPartialProduct m f z₀ s z := by
    simp [divisorComplementPartialProduct, term, P, fiber, Finset.prod_filter]
  have hsplit' : ∏ p ∈ s, term p = (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) :=
    hsplit.symm
  calc
    divisorPartialProduct m f s z
        = ∏ p ∈ s, term p := by simp [divisorPartialProduct, term]
    _ = (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) := hsplit'
    _ = divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z := by
      simp [hP, hnotP, fiber]

lemma divisorComplementPartialProduct_ne_zero_on_ball
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    ∀ z ∈ Metric.ball z₀ ε,
      divisorComplementPartialProduct m f z₀ s z ≠ 0 := by
  classical
  intro z hz
  have hfac :
      ∀ p ∈ s,
        (if p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ then (1 : ℂ)
          else weierstrassFactor m (z / divisorZeroIndex₀_val p)) ≠ 0 := by
    intro p hp
    by_cases hpF : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀
    · simp [hpF]
    · have : weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 :=
        weierstrassFactor_div_ne_zero_on_ball_of_not_mem_fiberFinset
          (m := m) (f := f) (z₀ := z₀) (ε := ε) hball p hpF z hz
      simp [hpF, this]
  simpa [divisorComplementPartialProduct, Finset.prod_ne_zero_iff] using hfac

theorem eventually_eq_fiber_mul_divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∀ z : ℂ,
        divisorPartialProduct m f s z =
          divisorPartialProduct m f (divisorZeroIndex₀_fiberFinset (f := f) z₀) z *
            divisorComplementPartialProduct m f z₀ s z := by
  classical
  refine (eventually_atTop_subset_fiberFinset (f := f) z₀).mono ?_
  intro s hs z
  simpa using
    (divisorPartialProduct_eq_fiber_mul_complement_of_subset (m := m) (f := f) (z₀ := z₀)
      (z := z) (s := s) hs)

end Complex.Hadamard
