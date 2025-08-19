/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.RCLike.Basic
/-!
# Mean value theorem

In this file we prove Cauchy's and Lagrange's mean value theorems, and deduce some corollaries.

Cauchy's mean value theorem says that for two functions `f` and `g`
that are continuous on `[a, b]` and are differentiable on `(a, b)`,
there exists a point `c ∈ (a, b)` such that `f' c / g' c = (f b - f a) / (g b - g a)`.
We formulate this theorem with both sides multiplied by the denominators,
see `exists_ratio_hasDerivAt_eq_ratio_slope`,
in order to avoid auxiliary conditions like `g' c ≠ 0`.

Lagrange's mean value theorem, see `exists_hasDerivAt_eq_slope`,
says that for a function `f` that is continuous on `[a, b]` and is differentiable on `(a, b)`,
there exists a point `c ∈ (a, b)` such that `f' c = (f b - f a) / (b - a)`.

Lagrange's MVT implies that `(f b - f a) / (b - a) > C`
provided that `f' c > C` for all `c ∈ (a, b)`, see `mul_sub_lt_image_sub_of_lt_deriv`,
and other theorems for `>` / `≥` / `<` / `≤`.

In case `C = 0`, we deduce that a function with a positive derivative is strictly monotone,
see `strictMonoOn_of_deriv_pos` and nearby theorems for other types of monotonicity.

We also prove that a real function whose derivative tends to infinity from the right at a point
is not differentiable on the right at that point, and similarly differentiability on the left.

## Main results


* `exists_ratio_hasDerivAt_eq_ratio_slope` and `exists_ratio_deriv_eq_ratio_slope` :
  Cauchy's Mean Value Theorem.

* `exists_hasDerivAt_eq_slope` and `exists_deriv_eq_slope` : Lagrange's Mean Value Theorem.

* `domain_mvt` : Lagrange's Mean Value Theorem, applied to a segment in a convex domain.

* `Convex.image_sub_lt_mul_sub_of_deriv_lt`, `Convex.mul_sub_lt_image_sub_of_lt_deriv`,
  `Convex.image_sub_le_mul_sub_of_deriv_le`, `Convex.mul_sub_le_image_sub_of_le_deriv`,
  if `∀ x, C (</≤/>/≥) (f' x)`, then `C * (y - x) (</≤/>/≥) (f y - f x)` whenever `x < y`.

* `monotoneOn_of_deriv_nonneg`, `antitoneOn_of_deriv_nonpos`,
  `strictMono_of_deriv_pos`, `strictAnti_of_deriv_neg` :
  if the derivative of a function is non-negative/non-positive/positive/negative, then
  the function is monotone/antitone/strictly monotone/strictly monotonically
  decreasing.

* `convexOn_of_deriv`, `convexOn_of_deriv2_nonneg` : if the derivative of a function
  is increasing or its second derivative is nonnegative, then the original function is convex.

-/

open Set Function Filter
open scoped Topology

/-! ### Functions `[a, b] → ℝ`. -/

section Interval

-- Declare all variables here to make sure they come in a correct order
variable (f f' : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
  (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hfd : DifferentiableOn ℝ f (Ioo a b))
  (g g' : ℝ → ℝ) (hgc : ContinuousOn g (Icc a b)) (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
  (hgd : DifferentiableOn ℝ g (Ioo a b))

include hab hfc hff' hgc hgg' in
/-- Cauchy's **Mean Value Theorem**, `HasDerivAt` version. -/
theorem exists_ratio_hasDerivAt_eq_ratio_slope :
    ∃ c ∈ Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c := by
  let h x := (g b - g a) * f x - (f b - f a) * g x
  have hI : h a = h b := by simp only [h]; ring
  let h' x := (g b - g a) * f' x - (f b - f a) * g' x
  have hhh' : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x := fun x hx ↦
    ((hff' x hx).const_mul (g b - g a)).sub ((hgg' x hx).const_mul (f b - f a))
  have hhc : ContinuousOn h (Icc a b) :=
    (continuousOn_const.mul hfc).sub (continuousOn_const.mul hgc)
  rcases exists_hasDerivAt_eq_zero hab hhc hI hhh' with ⟨c, cmem, hc⟩
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩

include hab in
/-- Cauchy's **Mean Value Theorem**, extended `HasDerivAt` version. -/
theorem exists_ratio_hasDerivAt_eq_ratio_slope' {lfa lga lfb lgb : ℝ}
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 lfa)) (hga : Tendsto g (𝓝[>] a) (𝓝 lga))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 lfb)) (hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)) :
    ∃ c ∈ Ioo a b, (lgb - lga) * f' c = (lfb - lfa) * g' c := by
  let h x := (lgb - lga) * f x - (lfb - lfa) * g x
  have hha : Tendsto h (𝓝[>] a) (𝓝 <| lgb * lfa - lfb * lga) := by
    have : Tendsto h (𝓝[>] a) (𝓝 <| (lgb - lga) * lfa - (lfb - lfa) * lga) :=
      (tendsto_const_nhds.mul hfa).sub (tendsto_const_nhds.mul hga)
    convert this using 2
    ring
  have hhb : Tendsto h (𝓝[<] b) (𝓝 <| lgb * lfa - lfb * lga) := by
    have : Tendsto h (𝓝[<] b) (𝓝 <| (lgb - lga) * lfb - (lfb - lfa) * lgb) :=
      (tendsto_const_nhds.mul hfb).sub (tendsto_const_nhds.mul hgb)
    convert this using 2
    ring
  let h' x := (lgb - lga) * f' x - (lfb - lfa) * g' x
  have hhh' : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x := by
    intro x hx
    exact ((hff' x hx).const_mul _).sub ((hgg' x hx).const_mul _)
  rcases exists_hasDerivAt_eq_zero' hab hha hhb hhh' with ⟨c, cmem, hc⟩
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩

include hab hfc hff' in
/-- Lagrange's Mean Value Theorem, `HasDerivAt` version -/
theorem exists_hasDerivAt_eq_slope : ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) := by
  obtain ⟨c, cmem, hc⟩ : ∃ c ∈ Ioo a b, (b - a) * f' c = (f b - f a) * 1 :=
    exists_ratio_hasDerivAt_eq_ratio_slope f f' hab hfc hff' id 1 continuousOn_id
      fun x _ ↦ hasDerivAt_id x
  use c, cmem
  rwa [mul_one, mul_comm, ← eq_div_iff (sub_ne_zero.2 hab.ne')] at hc

include hab hfc hgc hgd hfd in
/-- Cauchy's Mean Value Theorem, `deriv` version. -/
theorem exists_ratio_deriv_eq_ratio_slope :
    ∃ c ∈ Ioo a b, (g b - g a) * deriv f c = (f b - f a) * deriv g c :=
  exists_ratio_hasDerivAt_eq_ratio_slope f (deriv f) hab hfc
    (fun x hx ↦ ((hfd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt) g
    (deriv g) hgc fun x hx ↦
    ((hgd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt

include hab in
/-- Cauchy's Mean Value Theorem, extended `deriv` version. -/
theorem exists_ratio_deriv_eq_ratio_slope' {lfa lga lfb lgb : ℝ}
    (hdf : DifferentiableOn ℝ f <| Ioo a b) (hdg : DifferentiableOn ℝ g <| Ioo a b)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 lfa)) (hga : Tendsto g (𝓝[>] a) (𝓝 lga))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 lfb)) (hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)) :
    ∃ c ∈ Ioo a b, (lgb - lga) * deriv f c = (lfb - lfa) * deriv g c :=
  exists_ratio_hasDerivAt_eq_ratio_slope' _ _ hab _ _
    (fun x hx ↦ ((hdf x hx).differentiableAt <| Ioo_mem_nhds hx.1 hx.2).hasDerivAt)
    (fun x hx ↦ ((hdg x hx).differentiableAt <| Ioo_mem_nhds hx.1 hx.2).hasDerivAt) hfa hga hfb hgb

include hab hfc hfd in
/-- Lagrange's **Mean Value Theorem**, `deriv` version. -/
theorem exists_deriv_eq_slope : ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_hasDerivAt_eq_slope f (deriv f) hab hfc fun x hx ↦
    ((hfd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt

include hab hfc hfd in
/-- Lagrange's **Mean Value Theorem**, `deriv` version. -/
theorem exists_deriv_eq_slope' : ∃ c ∈ Ioo a b, deriv f c = slope f a b := by
  rw [slope_def_field]
  exact exists_deriv_eq_slope f hab hfc hfd

/-- A real function whose derivative tends to infinity from the right at a point is not
differentiable on the right at that point. -/
theorem not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi (f : ℝ → ℝ) {a : ℝ}
    (hf : Tendsto (deriv f) (𝓝[>] a) atTop) : ¬ DifferentiableWithinAt ℝ f (Ioi a) a := by
  replace hf : Tendsto (derivWithin f (Ioi a)) (𝓝[>] a) atTop := by
    refine hf.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    have : Ioi a ∈ 𝓝 x := by simp [← mem_interior_iff_mem_nhds, hx]
    exact (derivWithin_of_mem_nhds this).symm
  by_cases hcont_at_a : ContinuousWithinAt f (Ici a) a
  case neg =>
    intro hcontra
    have := hcontra.continuousWithinAt
    rw [← ContinuousWithinAt.diff_iff this] at hcont_at_a
    simp at hcont_at_a
  case pos =>
    intro hdiff
    replace hdiff := hdiff.hasDerivWithinAt
    rw [hasDerivWithinAt_iff_tendsto_slope, Set.diff_singleton_eq_self notMem_Ioi_self] at hdiff
    have h₀ : ∀ᶠ b in 𝓝[>] a,
        ∀ x ∈ Ioc a b, max (derivWithin f (Ioi a) a + 1) 0 < derivWithin f (Ioi a) x := by
      rw [(nhdsGT_basis a).eventually_iff]
      rw [(nhdsGT_basis a).tendsto_left_iff] at hf
      obtain ⟨b, hab, hb⟩ := hf (Ioi (max (derivWithin f (Ioi a) a + 1) 0)) (Ioi_mem_atTop _)
      refine ⟨b, hab, fun x hx z hz ↦ ?_⟩
      simp only [MapsTo, mem_Ioo, mem_Ioi, and_imp] at hb
      exact hb hz.1 <| hz.2.trans_lt hx.2
    have h₁ : ∀ᶠ b in 𝓝[>] a, slope f a b < derivWithin f (Ioi a) a + 1 := by
      rw [(nhds_basis_Ioo _).tendsto_right_iff] at hdiff
      specialize hdiff ⟨derivWithin f (Ioi a) a - 1, derivWithin f (Ioi a) a + 1⟩ <| by simp
      filter_upwards [hdiff] with z hz using hz.2
    have hcontra : ∀ᶠ _ in 𝓝[>] a, False := by
      filter_upwards [h₀, h₁, eventually_mem_nhdsWithin] with b hb hslope (hab : a < b)
      have hdiff' : DifferentiableOn ℝ f (Ioc a b) := fun z hz ↦ by
        refine DifferentiableWithinAt.mono (t := Ioi a) ?_ Ioc_subset_Ioi_self
        have : derivWithin f (Ioi a) z ≠ 0 := ne_of_gt <| by
          simp_all only [and_imp, mem_Ioc, max_lt_iff]
        exact differentiableWithinAt_of_derivWithin_ne_zero this
      have hcont_Ioc : ∀ z ∈ Ioc a b, ContinuousWithinAt f (Icc a b) z := by
        intro z hz''
        refine (hdiff'.continuousOn z hz'').mono_of_mem_nhdsWithin ?_
        have hfinal : 𝓝[Ioc a b] z = 𝓝[Icc a b] z := by
          refine nhdsWithin_eq_nhdsWithin' (s := Ioi a) (Ioi_mem_nhds hz''.1) ?_
          simp only [Ioc_inter_Ioi, le_refl, sup_of_le_left]
          ext y
          exact ⟨fun h ↦ ⟨mem_Icc_of_Ioc h, mem_of_mem_inter_left h⟩, fun ⟨H1, H2⟩ ↦ ⟨H2, H1.2⟩⟩
        rw [← hfinal]
        exact self_mem_nhdsWithin
      have hcont : ContinuousOn f (Icc a b) := by
        intro z hz
        by_cases hz' : z = a
        · rw [hz']
          exact hcont_at_a.mono Icc_subset_Ici_self
        · exact hcont_Ioc z ⟨lt_of_le_of_ne hz.1 (Ne.symm hz'), hz.2⟩
      obtain ⟨x, hx₁, hx₂⟩ :=
        exists_deriv_eq_slope' f hab hcont (hdiff'.mono (Ioo_subset_Ioc_self))
      specialize hb x ⟨hx₁.1, le_of_lt hx₁.2⟩
      replace hx₂ : derivWithin f (Ioi a) x = slope f a b := by
        have : Ioi a ∈ 𝓝 x := by simp [← mem_interior_iff_mem_nhds, hx₁.1]
        rwa [derivWithin_of_mem_nhds this]
      rw [hx₂, max_lt_iff] at hb
      linarith
    simp [Filter.eventually_false_iff_eq_bot, ← notMem_closure_iff_nhdsWithin_eq_bot] at hcontra

/-- A real function whose derivative tends to minus infinity from the right at a point is not
differentiable on the right at that point -/
theorem not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi (f : ℝ → ℝ) {a : ℝ}
    (hf : Tendsto (deriv f) (𝓝[>] a) atBot) : ¬ DifferentiableWithinAt ℝ f (Ioi a) a := by
  intro h
  have hf' : Tendsto (deriv (-f)) (𝓝[>] a) atTop := by
    rw [deriv.neg']
    exact tendsto_neg_atBot_atTop.comp hf
  exact not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi (-f) hf' h.neg

/-- A real function whose derivative tends to minus infinity from the left at a point is not
differentiable on the left at that point -/
theorem not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio (f : ℝ → ℝ) {a : ℝ}
    (hf : Tendsto (deriv f) (𝓝[<] a) atBot) : ¬ DifferentiableWithinAt ℝ f (Iio a) a := by
  let f' := f ∘ Neg.neg
  have hderiv : deriv f' =ᶠ[𝓝[>] (-a)] -(deriv f ∘ Neg.neg) := by
    rw [atBot_basis.tendsto_right_iff] at hf
    specialize hf (-1) trivial
    rw [(nhdsLT_basis a).eventually_iff] at hf
    rw [EventuallyEq, (nhdsGT_basis (-a)).eventually_iff]
    obtain ⟨b, hb₁, hb₂⟩ := hf
    refine ⟨-b, by linarith, fun x hx ↦ ?_⟩
    simp only [Pi.neg_apply, Function.comp_apply]
    suffices deriv f' x = deriv f (-x) * deriv (Neg.neg : ℝ → ℝ) x by simpa using this
    refine deriv_comp x (differentiableAt_of_deriv_ne_zero ?_) (by fun_prop)
    rw [mem_Ioo] at hx
    have h₁ : -x ∈ Ioo b a := ⟨by linarith, by linarith⟩
    have h₂ : deriv f (-x) ≤ -1 := hb₂ h₁
    exact ne_of_lt (by linarith)
  have hmain : ¬ DifferentiableWithinAt ℝ f' (Ioi (-a)) (-a) := by
    refine not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi f' <| Tendsto.congr' hderiv.symm ?_
    refine Tendsto.comp (g := -deriv f) ?_ tendsto_neg_nhdsGT_neg
    exact Tendsto.comp (g := Neg.neg) tendsto_neg_atBot_atTop hf
  intro h
  have : DifferentiableWithinAt ℝ f' (Ioi (-a)) (-a) := by
    refine DifferentiableWithinAt.comp (g := f) (f := Neg.neg) (t := Iio a) (-a) ?_ ?_ ?_
    · simp [h]
    · fun_prop
    · intro x
      simp [neg_lt]
  exact hmain this

/-- A real function whose derivative tends to infinity from the left at a point is not
differentiable on the left at that point -/
theorem not_differentiableWithinAt_of_deriv_tendsto_atTop_Iio (f : ℝ → ℝ) {a : ℝ}
    (hf : Tendsto (deriv f) (𝓝[<] a) atTop) : ¬ DifferentiableWithinAt ℝ f (Iio a) a := by
  intro h
  have hf' : Tendsto (deriv (-f)) (𝓝[<] a) atBot := by
    rw [deriv.neg']
    exact tendsto_neg_atTop_atBot.comp hf
  exact not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio (-f) hf' h.neg

end Interval

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C < f'`, then
`f` grows faster than `C * x` on `D`, i.e., `C * (y - x) < f y - f x` whenever `x, y ∈ D`,
`x < y`. -/
theorem Convex.mul_sub_lt_image_sub_of_lt_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (hf'_gt : ∀ x ∈ interior D, C < deriv f x) :
    ∀ᵉ (x ∈ D) (y ∈ D), x < y → C * (y - x) < f y - f x := by
  intro x hx y hy hxy
  have hxyD : Icc x y ⊆ D := hD.ordConnected.out hx hy
  have hxyD' : Ioo x y ⊆ interior D :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')
  have : C < (f y - f x) / (y - x) := ha ▸ hf'_gt _ (hxyD' a_mem)
  exact (lt_div_iff₀ (sub_pos.2 hxy)).1 this

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C < f'`, then `f` grows faster than
`C * x`, i.e., `C * (y - x) < f y - f x` whenever `x < y`. -/
theorem mul_sub_lt_image_sub_of_lt_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (hf'_gt : ∀ x, C < deriv f x) ⦃x y⦄ (hxy : x < y) : C * (y - x) < f y - f x :=
  convex_univ.mul_sub_lt_image_sub_of_lt_deriv hf.continuous.continuousOn hf.differentiableOn
    (fun x _ ↦ hf'_gt x) x trivial y trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C ≤ f'`, then
`f` grows at least as fast as `C * x` on `D`, i.e., `C * (y - x) ≤ f y - f x` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem Convex.mul_sub_le_image_sub_of_le_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (hf'_ge : ∀ x ∈ interior D, C ≤ deriv f x) :
    ∀ᵉ (x ∈ D) (y ∈ D), x ≤ y → C * (y - x) ≤ f y - f x := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with hxy' | hxy'
  · rw [hxy', sub_self, sub_self, mul_zero]
  have hxyD : Icc x y ⊆ D := hD.ordConnected.out hx hy
  have hxyD' : Ioo x y ⊆ interior D :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy' (hf.mono hxyD) (hf'.mono hxyD')
  have : C ≤ (f y - f x) / (y - x) := ha ▸ hf'_ge _ (hxyD' a_mem)
  exact (le_div_iff₀ (sub_pos.2 hxy')).1 this

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C ≤ f'`, then `f` grows at least as fast
as `C * x`, i.e., `C * (y - x) ≤ f y - f x` whenever `x ≤ y`. -/
theorem mul_sub_le_image_sub_of_le_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (hf'_ge : ∀ x, C ≤ deriv f x) ⦃x y⦄ (hxy : x ≤ y) : C * (y - x) ≤ f y - f x :=
  convex_univ.mul_sub_le_image_sub_of_le_deriv hf.continuous.continuousOn hf.differentiableOn
    (fun x _ ↦ hf'_ge x) x trivial y trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' < C`, then
`f` grows slower than `C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x, y ∈ D`,
`x < y`. -/
theorem Convex.image_sub_lt_mul_sub_of_deriv_lt {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (lt_hf' : ∀ x ∈ interior D, deriv f x < C) (x : ℝ) (hx : x ∈ D) (y : ℝ) (hy : y ∈ D)
    (hxy : x < y) : f y - f x < C * (y - x) :=
  have hf'_gt : ∀ x ∈ interior D, -C < deriv (fun y ↦ -f y) x := fun x hx ↦ by
    rw [deriv.fun_neg, neg_lt_neg_iff]
    exact lt_hf' x hx
  by linarith [hD.mul_sub_lt_image_sub_of_lt_deriv hf.neg hf'.neg hf'_gt x hx y hy hxy]

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' < C`, then `f` grows slower than
`C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x < y`. -/
theorem image_sub_lt_mul_sub_of_deriv_lt {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (lt_hf' : ∀ x, deriv f x < C) ⦃x y⦄ (hxy : x < y) : f y - f x < C * (y - x) :=
  convex_univ.image_sub_lt_mul_sub_of_deriv_lt hf.continuous.continuousOn hf.differentiableOn
    (fun x _ ↦ lt_hf' x) x trivial y trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' ≤ C`, then
`f` grows at most as fast as `C * x` on `D`, i.e., `f y - f x ≤ C * (y - x)` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem Convex.image_sub_le_mul_sub_of_deriv_le {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (le_hf' : ∀ x ∈ interior D, deriv f x ≤ C) (x : ℝ) (hx : x ∈ D) (y : ℝ) (hy : y ∈ D)
    (hxy : x ≤ y) : f y - f x ≤ C * (y - x) :=
  have hf'_ge : ∀ x ∈ interior D, -C ≤ deriv (fun y ↦ -f y) x := fun x hx ↦ by
    rw [deriv.fun_neg, neg_le_neg_iff]
    exact le_hf' x hx
  by linarith [hD.mul_sub_le_image_sub_of_le_deriv hf.neg hf'.neg hf'_ge x hx y hy hxy]

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' ≤ C`, then `f` grows at most as fast
as `C * x`, i.e., `f y - f x ≤ C * (y - x)` whenever `x ≤ y`. -/
theorem image_sub_le_mul_sub_of_deriv_le {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (le_hf' : ∀ x, deriv f x ≤ C) ⦃x y⦄ (hxy : x ≤ y) : f y - f x ≤ C * (y - x) :=
  convex_univ.image_sub_le_mul_sub_of_deriv_le hf.continuous.continuousOn hf.differentiableOn
    (fun x _ ↦ le_hf' x) x trivial y trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is positive, then
`f` is a strictly monotone function on `D`.
Note that we don't require differentiability explicitly as it already implied by the derivative
being strictly positive. -/
theorem strictMonoOn_of_deriv_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, 0 < deriv f x) : StrictMonoOn f D := by
  intro x hx y hy
  have : DifferentiableOn ℝ f (interior D) := fun z hz ↦
    (differentiableAt_of_deriv_ne_zero (hf' z hz).ne').differentiableWithinAt
  simpa only [zero_mul, sub_pos] using
    hD.mul_sub_lt_image_sub_of_lt_deriv hf this hf' x hx y hy

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is positive, then
`f` is a strictly monotone function.
Note that we don't require differentiability explicitly as it already implied by the derivative
being strictly positive. -/
theorem strictMono_of_deriv_pos {f : ℝ → ℝ} (hf' : ∀ x, 0 < deriv f x) : StrictMono f :=
  strictMonoOn_univ.1 <| strictMonoOn_of_deriv_pos convex_univ (fun z _ ↦
    (differentiableAt_of_deriv_ne_zero (hf' z).ne').differentiableWithinAt.continuousWithinAt)
    fun x _ ↦ hf' x

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is strictly positive,
then `f` is a strictly monotone function on `D`. -/
lemma strictMonoOn_of_hasDerivWithinAt_pos {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : ∀ x ∈ interior D, 0 < f' x) : StrictMonoOn f D :=
  strictMonoOn_of_deriv_pos hD hf fun x hx ↦ by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is strictly positive, then
`f` is a strictly monotone function. -/
lemma strictMono_of_hasDerivAt_pos {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, 0 < f' x) : StrictMono f :=
  strictMono_of_deriv_pos fun x ↦ by rw [(hf _).deriv]; exact hf' _

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonnegative, then
`f` is a monotone function on `D`. -/
theorem monotoneOn_of_deriv_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_nonneg : ∀ x ∈ interior D, 0 ≤ deriv f x) : MonotoneOn f D := fun x hx y hy hxy ↦ by
  simpa only [zero_mul, sub_nonneg] using
    hD.mul_sub_le_image_sub_of_le_deriv hf hf' hf'_nonneg x hx y hy hxy

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonnegative, then
`f` is a monotone function. -/
theorem monotone_of_deriv_nonneg {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : ∀ x, 0 ≤ deriv f x) :
    Monotone f :=
  monotoneOn_univ.1 <|
    monotoneOn_of_deriv_nonneg convex_univ hf.continuous.continuousOn hf.differentiableOn fun x _ ↦
      hf' x

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonnegative, then
`f` is a monotone function on `D`. -/
lemma monotoneOn_of_hasDerivWithinAt_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : ∀ x ∈ interior D, 0 ≤ f' x) : MonotoneOn f D :=
  monotoneOn_of_deriv_nonneg hD hf (fun _ hx ↦ (hf' _ hx).differentiableWithinAt) fun x hx ↦ by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonnegative, then
`f` is a monotone function. -/
lemma monotone_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : 0 ≤ f') : Monotone f :=
  monotone_of_deriv_nonneg (fun _ ↦ (hf _).differentiableAt) fun x ↦ by
    rw [(hf _).deriv]; exact hf' _

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is negative, then
`f` is a strictly antitone function on `D`. -/
theorem strictAntiOn_of_deriv_neg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, deriv f x < 0) : StrictAntiOn f D :=
  fun x hx y ↦ by
  simpa only [zero_mul, sub_lt_zero] using
    hD.image_sub_lt_mul_sub_of_deriv_lt hf
      (fun z hz ↦ (differentiableAt_of_deriv_ne_zero (hf' z hz).ne).differentiableWithinAt) hf' x
      hx y

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is negative, then
`f` is a strictly antitone function.
Note that we don't require differentiability explicitly as it already implied by the derivative
being strictly negative. -/
theorem strictAnti_of_deriv_neg {f : ℝ → ℝ} (hf' : ∀ x, deriv f x < 0) : StrictAnti f :=
  strictAntiOn_univ.1 <| strictAntiOn_of_deriv_neg convex_univ
      (fun z _ ↦
        (differentiableAt_of_deriv_ne_zero (hf' z).ne).differentiableWithinAt.continuousWithinAt)
      fun x _ ↦ hf' x

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is strictly positive,
then `f` is a strictly monotone function on `D`. -/
lemma strictAntiOn_of_hasDerivWithinAt_neg {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : ∀ x ∈ interior D, f' x < 0) : StrictAntiOn f D :=
  strictAntiOn_of_deriv_neg hD hf fun x hx ↦ by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is strictly positive, then
`f` is a strictly monotone function. -/
lemma strictAnti_of_hasDerivAt_neg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, f' x < 0) : StrictAnti f :=
  strictAnti_of_deriv_neg fun x ↦ by rw [(hf _).deriv]; exact hf' _

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonpositive, then
`f` is an antitone function on `D`. -/
theorem antitoneOn_of_deriv_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_nonpos : ∀ x ∈ interior D, deriv f x ≤ 0) : AntitoneOn f D := fun x hx y hy hxy ↦ by
  simpa only [zero_mul, sub_nonpos] using
    hD.image_sub_le_mul_sub_of_deriv_le hf hf' hf'_nonpos x hx y hy hxy

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonpositive, then
`f` is an antitone function. -/
theorem antitone_of_deriv_nonpos {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : ∀ x, deriv f x ≤ 0) :
    Antitone f :=
  antitoneOn_univ.1 <|
    antitoneOn_of_deriv_nonpos convex_univ hf.continuous.continuousOn hf.differentiableOn fun x _ ↦
      hf' x

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonpositive, then
`f` is an antitone function on `D`. -/
lemma antitoneOn_of_hasDerivWithinAt_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : ∀ x ∈ interior D, f' x ≤ 0) : AntitoneOn f D :=
  antitoneOn_of_deriv_nonpos hD hf (fun _ hx ↦ (hf' _ hx).differentiableWithinAt) fun x hx ↦ by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonpositive, then `f` is an antitone
function. -/
lemma antitone_of_hasDerivAt_nonpos {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : f' ≤ 0) : Antitone f :=
  antitone_of_deriv_nonpos (fun _ ↦ (hf _).differentiableAt) fun x ↦ by
    rw [(hf _).deriv]; exact hf' _

/-! ### Functions `f : E → ℝ` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lagrange's **Mean Value Theorem**, applied to convex domains. -/
theorem domain_mvt {f : E → ℝ} {s : Set E} {x y : E} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ∃ z ∈ segment ℝ x y, f y - f x = f' z (y - x) := by
  -- Use `g = AffineMap.lineMap x y` to parametrize the segment
  set g : ℝ → E := fun t ↦ AffineMap.lineMap x y t
  set I := Icc (0 : ℝ) 1
  have hsub : Ioo (0 : ℝ) 1 ⊆ I := Ioo_subset_Icc_self
  have hmaps : MapsTo g I s := hs.mapsTo_lineMap xs ys
  -- The one-variable function `f ∘ g` has derivative `f' (g t) (y - x)` at each `t ∈ I`
  have hfg : ∀ t ∈ I, HasDerivWithinAt (f ∘ g) (f' (g t) (y - x)) I t := fun t ht ↦
    (hf _ (hmaps ht)).comp_hasDerivWithinAt t AffineMap.hasDerivWithinAt_lineMap hmaps
  -- apply 1-variable mean value theorem to pullback
  have hMVT : ∃ t ∈ Ioo (0 : ℝ) 1, f' (g t) (y - x) = (f (g 1) - f (g 0)) / (1 - 0) := by
    refine exists_hasDerivAt_eq_slope (f ∘ g) _ (by norm_num) ?_ ?_
    · exact fun t Ht ↦ (hfg t Ht).continuousWithinAt
    · exact fun t Ht ↦ (hfg t <| hsub Ht).hasDerivAt (Icc_mem_nhds Ht.1 Ht.2)
  -- reinterpret on domain
  rcases hMVT with ⟨t, Ht, hMVT'⟩
  rw [segment_eq_image_lineMap, exists_mem_image]
  refine ⟨t, hsub Ht, ?_⟩
  simpa [g] using hMVT'.symm
