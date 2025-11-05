/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Logarithmic Derivatives

We define the logarithmic derivative of a function f as `deriv f / f`. We then prove some basic
facts about this, including how it changes under multiplication and composition.

-/

noncomputable section

open Filter Function Set

open scoped Topology

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

/-- The logarithmic derivative of a function defined as `deriv f /f`. Note that it will be zero
at `x` if `f` is not DifferentiableAt `x`. -/
def logDeriv (f : 𝕜 → 𝕜') :=
  deriv f / f

theorem logDeriv_apply (f : 𝕜 → 𝕜') (x : 𝕜) : logDeriv f x = deriv f x / f x := rfl

lemma logDeriv_eq_zero_of_not_differentiableAt (f : 𝕜 → 𝕜') (x : 𝕜) (h : ¬DifferentiableAt 𝕜 f x) :
    logDeriv f x = 0 := by
  simp only [logDeriv_apply, deriv_zero_of_not_differentiableAt h, zero_div]

@[simp]
theorem logDeriv_id (x : 𝕜) : logDeriv id x = 1 / x := by
  simp [logDeriv_apply]

@[simp] theorem logDeriv_id' (x : 𝕜) : logDeriv (·) x = 1 / x := logDeriv_id x

@[simp]
theorem logDeriv_const (a : 𝕜') : logDeriv (fun _ : 𝕜 ↦ a) = 0 := by
  ext
  simp [logDeriv_apply]

theorem logDeriv_mul {f g : 𝕜 → 𝕜'} (x : 𝕜) (hf : f x ≠ 0) (hg : g x ≠ 0)
    (hdf : DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x) :
      logDeriv (fun z => f z * g z) x = logDeriv f x + logDeriv g x := by
  simp [field, logDeriv_apply, *]

theorem logDeriv_div {f g : 𝕜 → 𝕜'} (x : 𝕜) (hf : f x ≠ 0) (hg : g x ≠ 0)
    (hdf : DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x) :
    logDeriv (fun z => f z / g z) x = logDeriv f x - logDeriv g x := by
  simp [field, logDeriv_apply, *]

theorem logDeriv_mul_const {f : 𝕜 → 𝕜'} (x : 𝕜) (a : 𝕜') (ha : a ≠ 0) :
    logDeriv (fun z => f z * a) x = logDeriv f x := by
  simp only [logDeriv_apply, deriv_mul_const_field, mul_div_mul_right _ _ ha]

theorem logDeriv_const_mul {f : 𝕜 → 𝕜'} (x : 𝕜) (a : 𝕜') (ha : a ≠ 0) :
    logDeriv (fun z => a * f z) x = logDeriv f x := by
  simp only [logDeriv_apply, deriv_const_mul_field, mul_div_mul_left _ _ ha]

/-- The logarithmic derivative of a finite product is the sum of the logarithmic derivatives. -/
theorem logDeriv_prod {ι : Type*} (s : Finset ι) (f : ι → 𝕜 → 𝕜') (x : 𝕜) (hf : ∀ i ∈ s, f i x ≠ 0)
    (hd : ∀ i ∈ s, DifferentiableAt 𝕜 (f i) x) :
    logDeriv (∏ i ∈ s, f i ·) x = ∑ i ∈ s, logDeriv (f i) x := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.forall_mem_cons] at hf hd
    simp_rw [Finset.prod_cons, Finset.sum_cons]
    rw [logDeriv_mul, ih hf.2 hd.2]
    · exact hf.1
    · simpa [Finset.prod_eq_zero_iff] using hf.2
    · exact hd.1
    · exact .fun_finset_prod hd.2

lemma logDeriv_fun_zpow {f : 𝕜 → 𝕜'} {x : 𝕜} (hdf : DifferentiableAt 𝕜 f x) (n : ℤ) :
    logDeriv (f · ^ n) x = n * logDeriv f x := by
  rcases eq_or_ne n 0 with rfl | hn; · simp
  rcases eq_or_ne (f x) 0 with hf | hf
  · simp [logDeriv_apply, zero_zpow, *]
  · rw [logDeriv_apply, ← comp_def (·^n), deriv_comp _ (differentiableAt_zpow.2 <| .inl hf) hdf,
      deriv_zpow, logDeriv_apply]
    simp [field, zpow_sub_one₀ hf]

lemma logDeriv_fun_pow {f : 𝕜 → 𝕜'} {x : 𝕜} (hdf : DifferentiableAt 𝕜 f x) (n : ℕ) :
    logDeriv (f · ^ n) x = n * logDeriv f x :=
  mod_cast logDeriv_fun_zpow hdf n

@[simp]
lemma logDeriv_zpow (x : 𝕜) (n : ℤ) : logDeriv (· ^ n) x = n / x := by
  rw [logDeriv_fun_zpow (by fun_prop), logDeriv_id', mul_one_div]

@[simp]
lemma logDeriv_pow (x : 𝕜) (n : ℕ) : logDeriv (· ^ n) x = n / x :=
  mod_cast logDeriv_zpow x n

@[simp] lemma logDeriv_inv (x : 𝕜) : logDeriv (·⁻¹) x = -1 / x := by
  simpa using logDeriv_zpow x (-1)

theorem logDeriv_comp {f : 𝕜' → 𝕜'} {g : 𝕜 → 𝕜'} {x : 𝕜} (hf : DifferentiableAt 𝕜' f (g x))
    (hg : DifferentiableAt 𝕜 g x) : logDeriv (f ∘ g) x = logDeriv f (g x) * deriv g x := by
  simp only [logDeriv, Pi.div_apply, deriv_comp _ hf hg, comp_apply]
  ring

lemma logDeriv_eqOn_iff [IsRCLikeNormedField 𝕜] {f g : 𝕜 → 𝕜'} {s : Set 𝕜}
    (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hs2 : IsOpen s) (hsc : IsPreconnected s) (hgn : ∀ x ∈ s, g x ≠ 0) (hfn : ∀ x ∈ s, f x ≠ 0) :
    EqOn (logDeriv f) (logDeriv g) s ↔ ∃ z : 𝕜', z ≠ 0 ∧ EqOn f (z • g) s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨t, ht⟩
  · simpa using ⟨1, one_ne_zero⟩
  · constructor
    · refine fun h ↦ ⟨f t * (g t)⁻¹, by grind, fun y hy ↦ ?_⟩
      have hderiv : s.EqOn (deriv (f * g⁻¹)) (deriv f * g⁻¹ - f * deriv g / g ^ 2) := by
        intro z hz
        rw [deriv_mul (hf.differentiableAt (hs2.mem_nhds hz)) ((hg.differentiableAt
          (hs2.mem_nhds hz)).inv (hgn z hz))]
        simp only [Pi.inv_apply, show g⁻¹ = (fun x => x⁻¹) ∘ g by rfl, deriv_inv, neg_mul,
          deriv_comp z (differentiableAt_inv (hgn z hz)) (hg.differentiableAt (hs2.mem_nhds hz)),
          mul_neg, Pi.sub_apply, Pi.mul_apply, comp_apply, Pi.div_apply, Pi.pow_apply]
        ring
      have hfg : EqOn (deriv (f * g⁻¹)) 0 s := hderiv.trans fun z hz ↦ by
        simp only [Pi.sub_apply, Pi.mul_apply, Pi.inv_apply, Pi.div_apply, Pi.pow_apply,
          Pi.zero_apply]
        grind [logDeriv_apply, Pi.div_apply]
      letI := IsRCLikeNormedField.rclike 𝕜
      obtain ⟨a, ha⟩ := hs2.exists_is_const_of_deriv_eq_zero hsc (hf.mul (hg.inv hgn)) hfg
      grind [Pi.mul_apply, Pi.inv_apply, Pi.smul_apply, smul_eq_mul]
    · rintro ⟨z, hz0, hz⟩ x hx
      simp [logDeriv_apply, hz.deriv hs2 hx, hz hx, deriv_const_smul _
        (hg.differentiableAt (hs2.mem_nhds hx)), mul_div_mul_left (deriv g x) (g x) hz0]
