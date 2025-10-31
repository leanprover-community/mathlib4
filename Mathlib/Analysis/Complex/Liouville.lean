/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Module.Completion

/-!
# Liouville's theorem

In this file we prove Liouville's theorem: if `f : E → F` is complex differentiable on the whole
space and its range is bounded, then the function is a constant. Various versions of this theorem
are formalized in `Differentiable.apply_eq_apply_of_bounded`,
`Differentiable.exists_const_forall_eq_of_bounded`, and
`Differentiable.exists_eq_const_of_bounded`.

The proof is based on the Cauchy integral formula for the derivative of an analytic function, see
`Complex.deriv_eq_smul_circleIntegral`.
-/

open TopologicalSpace Metric Set Filter Asymptotics Function MeasureTheory Bornology

open scoped Topology Filter NNReal Real

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : Type v} [NormedAddCommGroup F]
  [NormedSpace ℂ F]

local postfix:100 "̂" => UniformSpace.Completion

namespace Complex

/-- Cauchy's Estimate. -/
private theorem norm_deriv_le_aux [CompleteSpace F] {c : ℂ} {R C : ℝ} {f : ℂ → F} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖deriv f c‖ ≤ C / R := by
  have hp : ∀ z ∈ sphere c R, ‖(z - c) ^ (-2 : ℤ) • f z‖ ≤ C / (R * R) :=
    fun z (hz : ‖z - c‖ = R) => by
    simpa [-mul_inv_rev, norm_smul, hz, zpow_two, ← div_eq_inv_mul] using
      (div_le_div_iff_of_pos_right (mul_pos hR hR)).2 (hC z hz)
  have hq : deriv f c = (2 * π * I)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-2 : ℤ) • f z := by
    calc
      deriv f c = (2 * π * I)⁻¹ • (2 * π * I) • deriv f c := by
                rw [smul_comm, smul_inv_smul₀]; simp
              _ = (2 * π * I)⁻¹ • ∮ z in C(c, R), (1 / (z - c) ^ 2) • f z := by
                congr; exact (DiffContOnCl.deriv_eq_smul_circleIntegral hR hf).symm
              _ = (2 * π * I)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-2 : ℤ) • f z := by field_simp
  calc
    ‖deriv f c‖ = ‖(2 * π * I)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-2 : ℤ) • f z‖ :=
      congr_arg norm hq
    _ ≤ R * (C / (R * R)) :=
      (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hp)
    _ = C / R := by rw [mul_div_left_comm, div_self_mul_self', div_eq_mul_inv]

theorem norm_iteratedDeriv_le_aux [CompleteSpace F] {c : ℂ} {R C : ℝ} {n : ℕ} {f : ℂ → F}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c R)) (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖iteratedDeriv n f c‖ ≤ n.factorial * C / R ^ n := by
  have hp : ∀ z ∈ sphere c R, ‖(z - c)⁻¹ ^ (n + 1) • f z‖ ≤ C / (R ^ n  * R) :=
    fun z (hz : ‖z - c‖ = R) => by
    have := (div_le_div_iff_of_pos_right (mul_pos (pow_pos hR n) hR)).2 (hC z hz)
    simp [norm_smul, norm_pow, norm_inv, hz, ← div_eq_inv_mul]
    exact this
  have hq : iteratedDeriv n f c = n.factorial  •
    (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c)⁻¹ ^ (n + 1) • f z := by
    calc
      iteratedDeriv n f c = n.factorial • (2 * π * I)⁻¹ • (2 * π * I / n.factorial) •
        iteratedDeriv n f c := by sorry
      _ = n.factorial • (2 * π * I)⁻¹ •  (∮ z in C(c, R), (1 / (z - c) ^ (n + 1)) • f z) := by
                congr; exact (DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul hR n hf).symm
      _ = n.factorial • (2 * π * I)⁻¹ • ∮ z in C(c, R), (z - c)⁻¹ ^ (n + 1) • f z := by simp
  calc
    ‖iteratedDeriv n f c‖ = ‖n.factorial • (2 * π * I)⁻¹ •
      ∮ z in C(c, R), (z - c)⁻¹ ^ (n + 1) • f z‖ := congr_arg norm hq
    _ ≤ n.factorial * (R * (C / (R ^ (n + 1)))) := by
      simp only [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul]
      have := (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hp)
      refine mul_le_mul_of_nonneg_left this (?_ : (0 : ℝ) ≤ n.factorial)
      exact_mod_cast ((Nat.factorial_pos n).le)
    _ = n.factorial * C / R ^ n := by
      grind

/-- If `f` is complex differentiable on an open disc of radius `R > 0`, is continuous on its
closure, and its values on the boundary circle of this disc are bounded from above by `C`, then the
norm of its derivative at the center is at most `C / R`. -/
theorem norm_deriv_le_of_forall_mem_sphere_norm_le {c : ℂ} {R C : ℝ} {f : ℂ → F} (hR : 0 < R)
    (hd : DiffContOnCl ℂ f (ball c R)) (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖deriv f c‖ ≤ C / R := by
  set e : F →L[ℂ] F̂ := UniformSpace.Completion.toComplL
  have : HasDerivAt (e ∘ f) (e (deriv f c)) c :=
    e.hasFDerivAt.comp_hasDerivAt c
      (hd.differentiableAt isOpen_ball <| mem_ball_self hR).hasDerivAt
  calc
    ‖deriv f c‖ = ‖deriv (e ∘ f) c‖ := by
      rw [this.deriv]
      exact (UniformSpace.Completion.norm_coe _).symm
    _ ≤ C / R :=
      norm_deriv_le_aux hR (e.differentiable.comp_diffContOnCl hd) fun z hz =>
        (UniformSpace.Completion.norm_coe _).trans_le (hC z hz)

/-- An auxiliary lemma for Liouville's theorem `Differentiable.apply_eq_apply_of_bounded`. -/
theorem liouville_theorem_aux {f : ℂ → F} (hf : Differentiable ℂ f) (hb : IsBounded (range f))
    (z w : ℂ) : f z = f w := by
  suffices ∀ c, deriv f c = 0 from is_const_of_deriv_eq_zero hf this z w
  clear z w; intro c
  obtain ⟨C, C₀, hC⟩ : ∃ C > (0 : ℝ), ∀ z, ‖f z‖ ≤ C := by
    rcases isBounded_iff_forall_norm_le.1 hb with ⟨C, hC⟩
    exact
      ⟨max C 1, lt_max_iff.2 (Or.inr zero_lt_one), fun z =>
        (hC (f z) (mem_range_self _)).trans (le_max_left _ _)⟩
  refine norm_le_zero_iff.1 (le_of_forall_gt_imp_ge_of_dense fun ε ε₀ => ?_)
  calc
    ‖deriv f c‖ ≤ C / (C / ε) :=
      norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos C₀ ε₀) hf.diffContOnCl fun z _ => hC z
    _ = ε := div_div_cancel₀ C₀.lt.ne'

end Complex

namespace Differentiable

open Complex

/-- **Liouville's theorem**: a complex differentiable bounded function `f : E → F` is a constant. -/
theorem apply_eq_apply_of_bounded {f : E → F} (hf : Differentiable ℂ f) (hb : IsBounded (range f))
    (z w : E) : f z = f w := by
  set g : ℂ → F := f ∘ fun t : ℂ => t • (w - z) + z
  suffices g 0 = g 1 by simpa [g]
  apply liouville_theorem_aux
  exacts [hf.comp ((differentiable_id.smul_const (w - z)).add_const z),
    hb.subset (range_comp_subset_range _ _)]

/-- **Liouville's theorem**: a complex differentiable bounded function is a constant. -/
theorem exists_const_forall_eq_of_bounded {f : E → F} (hf : Differentiable ℂ f)
    (hb : IsBounded (range f)) : ∃ c, ∀ z, f z = c :=
  ⟨f 0, fun _ => hf.apply_eq_apply_of_bounded hb _ _⟩

/-- **Liouville's theorem**: a complex differentiable bounded function is a constant. -/
theorem exists_eq_const_of_bounded {f : E → F} (hf : Differentiable ℂ f)
    (hb : IsBounded (range f)) : ∃ c, f = const E c :=
  (hf.exists_const_forall_eq_of_bounded hb).imp fun _ => funext

/-- A corollary of Liouville's theorem where the function tends to a finite value at infinity
(i.e., along `Filter.cocompact`, which in proper spaces coincides with `Bornology.cobounded`). -/
theorem eq_const_of_tendsto_cocompact [Nontrivial E] {f : E → F} (hf : Differentiable ℂ f) {c : F}
    (hb : Tendsto f (cocompact E) (𝓝 c)) : f = Function.const E c := by
  have h_bdd : Bornology.IsBounded (Set.range f) := by
    obtain ⟨s, hs, hs_bdd⟩ := Metric.exists_isBounded_image_of_tendsto hb
    obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs
    apply ht.image hf.continuous |>.isBounded.union hs_bdd |>.subset
    simpa [Set.image_union, Set.image_univ] using Set.image_mono <| calc
      Set.univ = t ∪ tᶜ := t.union_compl_self.symm
      _        ⊆ t ∪ s  := by gcongr
  obtain ⟨c', hc'⟩ := hf.exists_eq_const_of_bounded h_bdd
  convert hc'
  exact tendsto_nhds_unique hb (by simpa [hc'] using tendsto_const_nhds)

/-- A corollary of Liouville's theorem where the function tends to a finite value at infinity
(i.e., along `Filter.cocompact`, which in proper spaces coincides with `Bornology.cobounded`). -/
theorem apply_eq_of_tendsto_cocompact [Nontrivial E] {f : E → F} (hf : Differentiable ℂ f) {c : F}
    (x : E) (hb : Tendsto f (cocompact E) (𝓝 c)) : f x = c :=
  congr($(hf.eq_const_of_tendsto_cocompact hb) x)

end Differentiable
