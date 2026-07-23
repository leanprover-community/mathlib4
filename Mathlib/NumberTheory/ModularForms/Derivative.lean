/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# Derivatives of modular forms

This file defines normalized derivative $D = \frac{1}{2\pi i} \frac{d}{dz}$
and (Ramanujan-)Serre derivative $\partial_k := D - \frac{k}{12} E_2$ of modular forms.

## Main Definitions and Theorems

- `normalizedDerivOfComplex`: $D = \frac{1}{2\pi i} \frac{d}{dz}$
- `serreDerivative`: $\partial_k F := D F - \frac{k}{12} E_2 F$
- `serreDerivative_slash_equivariant`: Serre derivative is equivariant under the slash action.
- `serreDerivativeMF`: the Serre derivative preserves modularity, i.e. for a subgroup `Γ` of
  `SL(2, ℤ)` it maps a weight `k` level `Γ` modular form to a weight `k + 2` level `Γ` modular form.

TODO:
- Use the above to prove Ramanujan's identities. See [here](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/main/SpherePacking/ModularForms/RamanujanIdentities.lean)
  for `sorry`-free proofs.
-/

open UpperHalfPlane hiding I
open Real Complex
open scoped Manifold MatrixGroups ModularForm Topology

namespace Derivative

@[expose] public noncomputable section

/--
Normalized derivative $D = \frac{1}{2\pi i} \frac{d}{dz}$.
-/
def normalizedDerivOfComplex (F : ℍ → ℂ) (z : ℍ) : ℂ := (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z

/-- We denote the normalized derivative by `D`. -/
scoped notation "D" => normalizedDerivOfComplex

/--
The derivative operator `D` preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `D F` is also MDifferentiable.
-/
theorem normalizedDerivOfComplex_mdifferentiable {F : ℍ → ℂ} (hF : MDiff F) : MDiff (D F) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hF ⊢
  let c : ℂ := (2 * π * I)⁻¹
  have hDeriv : DifferentiableOn ℂ (fun z ↦ c * deriv (F ∘ ofComplex) z) upperHalfPlaneSet := by
    simpa [c] using (hF.deriv isOpen_upperHalfPlaneSet).const_mul ((2 * π * I)⁻¹)
  refine hDeriv.congr ?_
  intro z hz
  simp [normalizedDerivOfComplex, c, Function.comp_apply, ofComplex_apply_of_im_pos hz]

/-!
Basic properties of normalized derivative.
-/
@[simp]
theorem normalizedDerivOfComplex_add (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    D (F + G) = D F + D G := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [normalizedDerivOfComplex, Pi.add_apply]
  rw [show (F + G) ∘ ofComplex = F ∘ ofComplex + G ∘ ofComplex from rfl,
    deriv_add hFz hGz, mul_add]

@[simp]
theorem normalizedDerivOfComplex_sub (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    D (F - G) = D F - D G := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [normalizedDerivOfComplex, Pi.sub_apply]
  rw [show (F - G) ∘ ofComplex = F ∘ ofComplex - G ∘ ofComplex from rfl,
    deriv_sub hFz hGz, mul_sub]

@[simp]
theorem normalizedDerivOfComplex_const (c : ℂ) : D (fun _ ↦ c) = 0 := by
  ext z
  change (2 * π * I)⁻¹ * deriv (fun _ : ℂ ↦ c) (z : ℂ) = 0
  simp [deriv_const]

@[simp]
theorem normalizedDerivOfComplex_smul (c : ℂ) (F : ℍ → ℂ) (hF : MDiff F) : D (c • F) = c • D F := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  simp only [normalizedDerivOfComplex, Pi.smul_apply, smul_eq_mul]
  rw [show (c • F) ∘ ofComplex = c • (F ∘ ofComplex) from rfl,
    deriv_const_smul c hFz, smul_eq_mul]
  ring

@[simp]
theorem normalizedDerivOfComplex_neg (F : ℍ → ℂ) (hF : MDiff F) : D (-F) = -D F := by
  have : -F = (-1 : ℂ) • F := by ext; simp
  rw [this, normalizedDerivOfComplex_smul _ _ hF]
  ext
  simp

@[simp]
theorem normalizedDerivOfComplex_mul (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    D (F * G) = D F * G + F * D G := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [normalizedDerivOfComplex, Pi.add_apply, Pi.mul_apply]
  rw [show (F * G) ∘ ofComplex = (F ∘ ofComplex) * (G ∘ ofComplex) from rfl,
    deriv_mul hFz hGz]
  simp [Function.comp_apply, ofComplex_apply]
  ring

@[simp]
theorem normalizedDerivOfComplex_pow (F : ℍ → ℂ) (n : ℕ) (hF : MDiff F) :
    D (F ^ n) = n * F ^ (n - 1) * D F := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  simp only [normalizedDerivOfComplex, Pi.mul_apply, Pi.pow_apply]
  rw [show (F ^ n) ∘ ofComplex = (F ∘ ofComplex) ^ n from rfl, deriv_pow hFz n]
  simp [Function.comp_apply, ofComplex_apply]
  ring

/--
Serre derivative of weight $k$.
-/
def serreDerivative (k : ℂ) (F : ℍ → ℂ) (z : ℍ) : ℂ :=
  D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z

@[simp]
lemma serreDerivative_apply (k : ℂ) (F : ℍ → ℂ) (z : ℍ) :
    serreDerivative k F z = D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z := rfl

@[simp]
lemma serreDerivative_eq (k : ℂ) (F : ℍ → ℂ) :
    serreDerivative k F = fun z ↦ D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z := rfl

/-!
Basic properties of Serre derivative.
-/
theorem serreDerivative_add (k : ℂ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serreDerivative k (F + G) = serreDerivative k F + serreDerivative k G := by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_add F G hF hG]
  ring_nf

theorem serreDerivative_sub (k : ℂ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serreDerivative k (F - G) = serreDerivative k F - serreDerivative k G := by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_sub F G hF hG]
  ring_nf

theorem serreDerivative_smul (k : ℂ) (c : ℂ) (F : ℍ → ℂ) (hF : MDiff F) :
    serreDerivative k (c • F) = c • (serreDerivative k F) := by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_smul c F hF, smul_eq_mul]
  ring_nf

theorem serreDerivative_mul (k₁ k₂ : ℂ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serreDerivative (k₁ + k₂) (F * G) =
      (serreDerivative k₁ F) * G + F * (serreDerivative k₂ G) := by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_mul F G hF hG]
  ring_nf

/--
The Serre derivative preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `serreDerivative k F` is also MDifferentiable.
-/
theorem serreDerivative_mdifferentiable {F : ℍ → ℂ} (k : ℂ) (hF : MDiff F) :
    MDiff (serreDerivative k F) := by
  refine (normalizedDerivOfComplex_mdifferentiable hF).sub ?_
  convert!
    (MDifferentiable.mul mdifferentiable_const (E2_mdifferentiable.mul hF) :
      MDiff (fun z ↦ (k * 12⁻¹) * (EisensteinSeries.E2 z * F z)))
  simp [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm]

open ModularGroup

/-- How `D` interacts with the slash action. -/
lemma normalizedDerivOfComplex_slash {k : ℤ} {F : ℍ → ℂ} (hF : MDiff F)
    {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) :
    D (F ∣[k] g) = fun z : ℍ ↦ (g.val.det : ℂ)⁻¹ * (D F ∣[k + 2] g) z -
      (k : ℂ) * (2 * π * I)⁻¹ * (g 1 0 / denom g z) * (F ∣[k] g) z := by
  have hdet : g.det.val = g.val.det := Matrix.GeneralLinearGroup.val_det_apply g
  have hdetℂ : (g.val.det : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg.ne'
  have hσ (x) : σ g x = x := by grind [σ, ContinuousAlgEquiv.refl_apply]
  ext z
  simp only [normalizedDerivOfComplex, ModularForm.slash_apply]
  have hz := denom_ne_zero g z
  have h_smul : HasDerivAt (fun w ↦ ↑(g • ofComplex w) : ℂ → ℂ)
      ((g.val.det : ℂ) / denom g z ^ 2) ↑z := (hasStrictDerivAt_smul hg z).hasDerivAt
  have h_F : HasDerivAt (F ∘ ofComplex) (deriv (F ∘ ofComplex) ↑(g • ofComplex (z : ℂ)))
      ↑(g • ofComplex (z : ℂ)) :=
    (ofComplex_apply z).symm ▸ (mdifferentiableAt_iff.mp (hF (g • z))).hasDerivAt
  have h_denom : HasDerivAt (fun w ↦ (denom g w) ^ (-k))
      (-k * (g 1 0 : ℂ) * (denom g z) ^ (-k - 1)) ↑z := by
    simpa using hasDerivAt_denom_zpow g (-k) z
  have hcomp : ((F ∣[k] g) ∘ ofComplex) =ᶠ[𝓝 ↑z]
      fun w ↦ (g.val.det : ℂ) ^ (k - 1) *
        ((F ∘ ofComplex) ↑(g • ofComplex w) * (denom g w) ^ (-k)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    grind [ofComplex_apply_of_im_pos, ofComplex_apply, ModularForm.slash_apply]
  rw [((((h_F.comp (z : ℂ) h_smul).mul h_denom).const_mul _).congr_of_eventuallyEq hcomp).deriv]
  simp only [hσ, hdet, abs_of_pos hg, ofComplex_apply, Function.comp_apply]
  rw [show k + 2 - 1 = (k - 1) + 2 by ring, show -(k + 2) = -k + -2 by ring,
    zpow_add₀ hdetℂ, zpow_add₀ hz, zpow_sub_one₀ hz]
  field

/-- The `SL(2, ℤ)` case of `normalizedDerivOfComplex_slash`, where the determinant factor is `1`. -/
lemma normalizedDerivOfComplex_SL_slash {k : ℤ} {F : ℍ → ℂ} (hF : MDiff F) {γ : SL(2, ℤ)} :
    D (F ∣[k] γ) = (D F ∣[k + 2] γ) -
      (fun z : ℍ ↦ (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z) := by
  have hdet : (γ : GL (Fin 2) ℝ).val.det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; simp
  ext z
  have := congrFun
    (normalizedDerivOfComplex_slash (k := k) hF (g := (γ : GL (Fin 2) ℝ)) (by grind)) z
  rw [hdet] at this
  simpa [ModularForm.SL_slash] using this

/--
Serre derivative is equivariant under the slash action. More precisely,
$\partial_k (F ∣[k] γ) = (\partial_k F) ∣[k + 2] \gamma$ for all $\gamma \in SL(2, \mathbb{Z})$.
-/
theorem serreDerivative_slash_equivariant {k : ℤ} {F : ℍ → ℂ} (hF : MDiff F) {γ : SL(2, ℤ)} :
    serreDerivative k F ∣[k + 2] γ = serreDerivative k (F ∣[k] γ) := by
  ext z
  have hLHS : (serreDerivative (k : ℂ) F ∣[k + 2] γ) z =
      (D F ∣[k + 2] γ) z - ↑k * 12⁻¹ * ((EisensteinSeries.E2 ∣[(2 : ℤ)] γ) z * (F ∣[k] γ) z) := by
    grind [ModularForm.SL_slash_apply, serreDerivative_apply, Pi.mul_apply,
      congrFun (ModularForm.mul_slash_SL2 2 k γ EisensteinSeries.E2 F) z]
  have hDz : (D (F ∣[k] γ)) z = (D F ∣[k + 2] γ) z -
      (k * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z) := by
    simp [normalizedDerivOfComplex_SL_slash hF]
  have hE2z : (EisensteinSeries.E2 ∣[(2 : ℤ)] γ) z =
      EisensteinSeries.E2 z - 1 / (2 * riemannZeta 2) * EisensteinSeries.D2 γ z := by
    simp [EisensteinSeries.E2_slash_action]
  grind [serreDerivative_apply, EisensteinSeries.D2, riemannZeta_two, I_sq]

/--
As a corollary, if `F` is invariant under the slash action of weight `k`, then
`serreDerivative k F` is invariant under the slash action of weight `k + 2`.
-/
theorem serreDerivative_slash_invariant {k : ℤ} {F : ℍ → ℂ} (hF : MDiff F) {γ : SL(2, ℤ)}
    (h : F ∣[k] γ = F) :
    serreDerivative k F ∣[k + 2] γ = serreDerivative k F := by
  grind [serreDerivative_slash_equivariant]

/-!
Boundedness of the normalized derivative and Serre derivative at infinity.
-/

/-- A Cauchy estimate for the normalized derivative: if `F` is holomorphic on `ℍ` and bounded by
`M` at every point with imaginary part at least `z.im / 2`, then `‖D F z‖ ≤ M / (π * z.im)`. -/
private lemma norm_normalizedDerivOfComplex_le {F : ℍ → ℂ} (hF : MDiff F) {z : ℍ} {M : ℝ}
    (hM : ∀ w : ℍ, z.im / 2 ≤ w.im → ‖F w‖ ≤ M) : ‖D F z‖ ≤ M / (π * z.im) := by
  have h2 : 0 < z.im / 2 := half_pos z.im_pos
  have him : ∀ w ∈ Metric.closedBall (z : ℂ) (z.im / 2), z.im / 2 ≤ w.im := fun w hw => by
    have h := (abs_im_le_norm (w - (z : ℂ))).trans (mem_closedBall_iff_norm.mp hw)
    rw [Complex.sub_im, UpperHalfPlane.coe_im, abs_le] at h
    linarith [h.1]
  have hd : ‖deriv (F ∘ ofComplex) (z : ℂ)‖ ≤ M / (z.im / 2) := by
    refine norm_deriv_le_of_forall_mem_sphere_norm_le h2
      ((UpperHalfPlane.mdifferentiable_iff.mp hF).diffContOnCl_ball fun w hw =>
        h2.trans_le (him w hw)) fun w hw => ?_
    have hwim := him w (Metric.sphere_subset_closedBall hw)
    rw [Function.comp_apply, ofComplex_apply_of_im_pos (h2.trans_le hwim)]
    exact hM _ hwim
  calc ‖D F z‖ = (2 * π)⁻¹ * ‖deriv (F ∘ ofComplex) (z : ℂ)‖ := by
        simp [normalizedDerivOfComplex, Real.pi_pos.le]
    _ ≤ (2 * π)⁻¹ * (M / (z.im / 2)) := by gcongr
    _ = M / (π * z.im) := by ring

/-- The normalized derivative `D F` of a holomorphic function `F` that is bounded at infinity is
again bounded at infinity. This is a Cauchy estimate: differentiating loses at most a factor
of `1 / z.im`. -/
theorem normalizedDerivOfComplex_isBoundedAtImInfty {F : ℍ → ℂ} (hF : MDiff F)
    (hb : IsBoundedAtImInfty F) : IsBoundedAtImInfty (D F) := by
  rw [isBoundedAtImInfty_iff] at hb ⊢
  obtain ⟨M, A, hMA⟩ := hb
  refine ⟨M / π, max (2 * A) 1, fun z hz => ?_⟩
  obtain ⟨hzA, hz1⟩ := max_le_iff.mp hz
  have hM : 0 ≤ M := (norm_nonneg _).trans (hMA z (by linarith))
  calc ‖D F z‖ ≤ M / (π * z.im) :=
        norm_normalizedDerivOfComplex_le hF fun w hw => hMA w (by linarith)
    _ ≤ M / π := by gcongr; exact le_mul_of_one_le_right Real.pi_pos.le hz1

/-- The Serre derivative of a holomorphic function that is bounded at infinity is again bounded at
infinity. -/
theorem serreDerivative_isBoundedAtImInfty {F : ℍ → ℂ} (k : ℂ) (hF : MDiff F)
    (hb : IsBoundedAtImInfty F) : IsBoundedAtImInfty (serreDerivative k F) :=
  Asymptotics.IsBigO.sub (normalizedDerivOfComplex_isBoundedAtImInfty hF hb) <|
    ((Filter.const_boundedAtFilter atImInfty (k * 12⁻¹)).mul
      EisensteinSeries.isBoundedAtImInfty_E2).mul hb

/--
The Serre derivative preserves modularity: if `f` is a modular form of weight `k` for a subgroup
`Γ` of `SL(2, ℤ)`, then `∂ₖ f` is a modular form of weight `k + 2` for `Γ`.
-/
noncomputable def serreDerivativeMF {Γ : Subgroup (GL (Fin 2) ℝ)} (k : ℤ)
    (f : ModularForm Γ k) (hΓ : Γ ≤ 𝒮ℒ := by exact le_rfl) : ModularForm Γ (k + 2) where
  toSlashInvariantForm :=
    { toFun := serreDerivative (k : ℂ) f
      slash_action_eq' := fun g hg => by
        obtain ⟨γ, rfl⟩ := hΓ hg
        exact serreDerivative_slash_invariant f.holo' (f.slash_action_eq' _ hg) }
  holo' := serreDerivative_mdifferentiable (k : ℂ) f.holo'
  bdd_at_cusps' {c} hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z (hc.mono hΓ)]
    intro γ hγ
    rw [serreDerivative_slash_equivariant (F := (f : ℍ → ℂ)) f.holo']
    exact serreDerivative_isBoundedAtImInfty (k : ℂ) (f.holo'.slash k γ)
      ((OnePoint.isBoundedAt_iff_forall_SL2Z (hc.mono hΓ)).mp (f.bdd_at_cusps' hc) γ hγ)

end

end Derivative
