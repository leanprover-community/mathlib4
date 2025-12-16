/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Algebra.Group.Action.Sum
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

open UpperHalfPlane

variable (𝒢 : Subgroup (GL (Fin 2) ℝ))

/-- The quotient `𝒢 \ ℍ`, where `𝒢` is a subgroup of `GL(2, ℝ)`. -/
def OpenModularCurve : Type := MulAction.orbitRel.Quotient 𝒢 ℍ

/-- The quotient `𝒢 \ ℍ⋆`, where `𝒢` is a subgroup of `GL(2, ℝ)` and `ℍ⋆` denotes the union of
`ℍ` and the cusps of `𝒢`. -/
def CompletedModularCurve : Type := (OpenModularCurve 𝒢) ⊕ CuspOrbits 𝒢

private lemma order_comp_smul {f : ℍ → ℂ} {τ : ℍ} {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val)
    (hf : MeromorphicAt (f ∘ ofComplex) (g • τ).1) :
    meromorphicOrderAt (fun z : ℂ ↦ f (g • ofComplex z)) τ.1 =
      meromorphicOrderAt (fun z : ℂ ↦ f (ofComplex z)) (g • τ).1 := by
  let G (z : ℂ) : ℂ := ↑(g • ofComplex z)
  let F (z : ℂ) : ℂ := f (ofComplex z)
  have : (fun z : ℂ ↦ f (g • ofComplex z)) = F ∘ G := by ext; simp [F, G]
  rw [this, meromorphicOrderAt_comp_of_deriv_ne_zero]
  · congr 1
    simp only [G]
    congr 2
    exact τ.ofComplex_apply
  · convert hf
    simp only [G]
    congr 2
    exact τ.ofComplex_apply
  · apply DifferentiableOn.analyticAt (s := upperHalfPlaneSet)
    · suffices DifferentiableOn ℂ (fun z ↦ num g z / denom g z) upperHalfPlaneSet by
        refine this.congr fun z (hz : 0 < z.im) ↦ ?_
        simp only [G, coe_smul, σ, if_pos hg, RingHom.id_apply]
        simp [ofComplex_apply_eq_ite, hz]
      unfold num denom
      apply DifferentiableOn.div
      · fun_prop
      · fun_prop
      · exact fun z hz ↦ denom_ne_zero_of_im g hz.ne'
    · exact isOpen_upperHalfPlaneSet.mem_nhds τ.property
  · sorry
