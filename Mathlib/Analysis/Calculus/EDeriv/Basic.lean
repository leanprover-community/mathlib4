/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Sam Lindauer
-/
import Mathlib.Analysis.NormedSpace.Alternating.Uncurry.Fin
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Exterior derivative of a differential form

In this file we define the exterior derivative of a differential form.
Under certain smoothness assumptions, we prove that this operation is linear in the form
and the second exterior derivative of a form is zero.
-/

open Filter ContinuousAlternatingMap Set
open scoped Topology

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n m k : ℕ} {r : WithTop ℕ∞}
  {ω ω₁ ω₂ : E → E [⋀^Fin n]→L[𝕜] F} {s t : Set E} {x : E}

/-- Exterior derivative of a differential form. -/
noncomputable def ederiv (ω : E → E [⋀^Fin n]→L[𝕜] F) (x : E) : E [⋀^Fin (n + 1)]→L[𝕜] F :=
  .uncurryFin (fderiv 𝕜 ω x)

/- Exterior derivative of a differential form within a set. -/
noncomputable def ederivWithin (ω : E → E [⋀^Fin n]→L[𝕜] F) (s : Set E) (x : E) :
    E [⋀^Fin (n + 1)]→L[𝕜] F :=
  .uncurryFin (fderivWithin 𝕜 ω s x)

@[simp]
theorem ederivWithin_univ (ω : E → E [⋀^Fin n]→L[𝕜] F) :
    ederivWithin ω univ = ederiv ω := by
  ext1 x
  rw[ederivWithin, ederiv, fderivWithin_univ]

theorem ederivWithin_add (hsx : UniqueDiffWithinAt 𝕜 s x)
    (hω₁ : DifferentiableWithinAt 𝕜 ω₁ s x) (hω₂ : DifferentiableWithinAt 𝕜 ω₂ s x) :
    ederivWithin (ω₁ + ω₂) s x = ederivWithin ω₁ s x + ederivWithin ω₂ s x := by
  simp [ederivWithin, fderivWithin_add hsx hω₁ hω₂, uncurryFin_add]

theorem ederivWithin_fun_add (hsx : UniqueDiffWithinAt 𝕜 s x)
    (hω₁ : DifferentiableWithinAt 𝕜 ω₁ s x) (hω₂ : DifferentiableWithinAt 𝕜 ω₂ s x) :
    ederivWithin (fun x ↦ ω₁ x + ω₂ x) s x = ederivWithin ω₁ s x + ederivWithin ω₂ s x :=
  ederivWithin_add hsx hω₁ hω₂

theorem ederiv_add (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜 ω₂ x) :
    ederiv (ω₁ + ω₂) x = ederiv ω₁ x + ederiv ω₂ x := by
  simp [← ederivWithin_univ, ederivWithin_add, *, DifferentiableAt.differentiableWithinAt]

theorem ederiv_fun_add (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜 ω₂ x) :
    ederiv (fun x ↦ ω₁ x + ω₂ x) x = ederiv ω₁ x + ederiv ω₂ x :=
  ederiv_add hω₁ hω₂

theorem ederivWithin_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F) (hsx : UniqueDiffWithinAt 𝕜 s x) :
    ederivWithin (c • ω) s x = c • ederivWithin ω s x := by
  simp [ederivWithin, fderivWithin_const_smul_of_field, hsx, uncurryFin_smul]

theorem ederivWithin_fun_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F)
    (hsx : UniqueDiffWithinAt 𝕜 s x) :
    ederivWithin (fun x ↦ c • ω x) s x = c • ederivWithin ω s x :=
  ederivWithin_smul c ω hsx

theorem ederiv_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F) : ederiv (c • ω) x = c • ederiv ω x := by
  simp [← ederivWithin_univ, ederivWithin_smul]

theorem ederiv_fun_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F) :
    ederiv (c • ω) x = c • ederiv ω x :=
  ederiv_smul c ω

/-- Exterior derivative of a 0-form given by a function `f` within a set
is the 1-form given by the derivative of `f` within the set. -/
theorem ederivWithin_constOfIsEmpty (f : E → F) (hs : UniqueDiffWithinAt 𝕜 s x) :
    ederivWithin (fun x ↦ constOfIsEmpty 𝕜 E (Fin 0) (f x)) s x =
      .ofSubsingleton _ _ _ (0 : Fin 1) (fderivWithin 𝕜 f s x) := by
  simp only [ederivWithin, ← constOfIsEmptyLIE_apply, ← Function.comp_def _ f,
    (constOfIsEmptyLIE 𝕜 E F (Fin 0)).comp_fderivWithin hs,
    uncurryFin_constOfIsEmptyLIE_comp]

/-- Exterior derivative of a 0-form given by a function `f`
is the 1-form given by the derivative of `f`. -/
theorem ederiv_constOfIsEmpty (f : E → F) (x : E) :
    ederiv (fun x ↦ constOfIsEmpty 𝕜 E (Fin 0) (f x)) x =
      .ofSubsingleton _ _ _ (0 : Fin 1) (fderiv 𝕜 f x) := by
  simp [← ederivWithin_univ, ederivWithin_constOfIsEmpty, fderivWithin_univ]

theorem Filter.EventuallyEq.ederivWithin_eq (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x) :
    ederivWithin ω₁ s x = ederivWithin ω₂ s x := by
  simp only [ederivWithin, uncurryFin, hs.fderivWithin_eq hx]

theorem Filter.EventuallyEq.ederivWithin_eq_of_mem (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : x ∈ s) :
    ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  hs.ederivWithin_eq (mem_of_mem_nhdsWithin hx hs :)

theorem Filter.EventuallyEq.ederivWithin_eq_of_insert (hs : ω₁ =ᶠ[𝓝[insert x s] x] ω₂) :
    ederivWithin ω₁ s x = ederivWithin ω₂ s x := by
  apply Filter.EventuallyEq.ederivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
  exact (mem_of_mem_nhdsWithin (mem_insert x s) hs :)

theorem Filter.EventuallyEq.ederivWithin' (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (ht : t ⊆ s) :
    ederivWithin ω₁ t =ᶠ[𝓝[s] x] ederivWithin ω₂ t :=
  (eventually_eventually_nhdsWithin.2 hs).mp <| eventually_mem_nhdsWithin.mono fun _y hys hs =>
    EventuallyEq.ederivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)

protected theorem Filter.EventuallyEq.ederivWithin (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) :
    ederivWithin ω₁ s =ᶠ[𝓝[s] x] ederivWithin ω₂ s :=
  hs.ederivWithin' .rfl

theorem Filter.EventuallyEq.ederivWithin_eq_nhds (h : ω₁ =ᶠ[𝓝 x] ω₂) :
    ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  (h.filter_mono nhdsWithin_le_nhds).ederivWithin_eq h.self_of_nhds

theorem ederivWithin_congr (hs : EqOn ω₁ ω₂ s) (hx : ω₁ x = ω₂ x) :
    ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).ederivWithin_eq hx

theorem ederivWithin_congr' (hs : EqOn ω₁ ω₂ s) (hx : x ∈ s) :
    ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  ederivWithin_congr hs (hs hx)

protected theorem Filter.EventuallyEq.ederiv (h : ω₁ =ᶠ[𝓝 x] ω₂) :
    ederiv ω₁ =ᶠ[𝓝 x] ederiv ω₂ := by
  simp only [← nhdsWithin_univ, ← ederivWithin_univ] at *
  exact h.ederivWithin

theorem Filter.EventuallyEq.ederiv_eq (h : ω₁ =ᶠ[𝓝 x] ω₂) : ederiv ω₁ x = ederiv ω₂ x :=
  h.ederiv.self_of_nhds

theorem ederivWithin_apply (h : DifferentiableWithinAt 𝕜 ω s x) (hs : UniqueDiffWithinAt 𝕜 s x)
    (v : Fin (n + 1) → E) :
    ederivWithin ω s x v = ∑ i, (-1) ^ i.val • fderivWithin 𝕜 (ω · (i.removeNth v)) s x (v i) := by
  simp [ederivWithin, ContinuousAlternatingMap.uncurryFin_apply,
    fderivWithin_continuousAlternatingMap_apply_const_apply, *]

theorem ederiv_apply (h : DifferentiableAt 𝕜 ω x) (v : Fin (n + 1) → E) :
    ederiv ω x v = ∑ i, (-1) ^ i.val • fderiv 𝕜 (ω · (i.removeNth v)) x (v i) := by
  simp [← ederivWithin_univ, ederivWithin_apply h.differentiableWithinAt]

/-- Second exterior derivative of a sufficiently smooth differential form is zero. -/
theorem ederivWithin_ederivWithin_apply (hω : ContDiffWithinAt 𝕜 r ω s x)
    (hr : minSmoothness 𝕜 2 ≤ r) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ closure (interior s))
    (h'x : x ∈ s) : ederivWithin (ederivWithin ω s) s x = 0 := calc
  ederivWithin (ederivWithin ω s) s x =
    uncurryFin (fderivWithin 𝕜 (fun y ↦ uncurryFin (fderivWithin 𝕜 ω s y)) s x) := rfl
  _ = uncurryFin (uncurryFinCLM _ _ _ ∘L fderivWithin 𝕜 (fderivWithin 𝕜 ω s) s x) := by
    congr 1
    have : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 ω s) s x := by
      refine (hω.fderivWithin_right hs ?_ h'x).differentiableWithinAt le_rfl
      exact le_minSmoothness.trans hr
    exact (uncurryFinCLM _ _ _).hasFDerivAt.comp_hasFDerivWithinAt x this.hasFDerivWithinAt
      |>.fderivWithin (hs.uniqueDiffWithinAt h'x)
  _ = 0 := uncurryFin_uncurryFinCLM_comp_of_symmetric <| hω.isSymmSndFDerivWithinAt hr hs hx h'x

/-- Second exterior derivative of a sufficiently smooth differential form is zero. -/
theorem ederivWithin_ederivWithin_eqOn (hω : ContDiffOn 𝕜 r ω s) (hr : minSmoothness 𝕜 2 ≤ r)
    (hs : UniqueDiffOn 𝕜 s) :
    EqOn (ederivWithin (ederivWithin ω s) s) 0 (s ∩ closure (interior s)) := by
  rintro x ⟨h'x, hx⟩
  exact ederivWithin_ederivWithin_apply (hω.contDiffWithinAt h'x) hr hs hx h'x

/-- Second exterior derivative of a sufficiently smooth differential form is zero. -/
theorem ederiv_ederiv_apply (hω : ContDiffAt 𝕜 r ω x) (hr : minSmoothness 𝕜 2 ≤ r) :
    ederiv (ederiv ω) x = 0 := by
  simp only [← ederivWithin_univ]
  apply ederivWithin_ederivWithin_apply (s := univ) hω.contDiffWithinAt hr <;> simp

/-- Second exterior derivative of a sufficiently smooth differential form is zero. -/
theorem ederiv_ederiv (h : ContDiff 𝕜 r ω) (hr : minSmoothness 𝕜 2 ≤ r) : ederiv (ederiv ω) = 0 :=
  funext fun _ ↦ ederiv_ederiv_apply h.contDiffAt hr
