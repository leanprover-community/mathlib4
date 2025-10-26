/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Sam Lindauer
-/
import Mathlib.Analysis.NormedSpace.Alternating.Uncurry.Fin
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Exterior derivative of a differential form on a normed space

In this file we define the exterior derivative of a differential form on a normed space.
Under certain smoothness assumptions, we prove that this operation is linear in the form
and the second exterior derivative of a form is zero.

We represent a differential `n`-form on `E` taking values in `F` as `E → E [⋀^Fin n]→L[𝕜] F`.

## Implementation notes

There are a few competing definitions of the exterior derivative of a differential form
that differ from each other by a normalization factor.
We use the following one:

$$
dω(x; v_0, \dots, v_n) = \sum_{i=0}^n (-1)^i D_x ω(x; v_0, \dots, \widehat{v_i}, \dots, v_n) · v_i
$$

where $$\widehat{v_i}$$ means that we omit this element of the tuple, see `extDeriv_apply`.

## TODO

- Introduce notation for:
  - an unbundled `n`-form on a normed space;
  - a bundled `C^r`-smooth `n`-form on a normed space;
  - same for manifolds (not defined yet).
- Introduce bundled `C^r`-smooth `n`-forms on normed spaces and manifolds.
  - Discuss the future API and the use cases that need to be covered on Zulip.
  - Introduce new types & notation, copy the API.
- Add shorter and more readable definitions (or abbreviations?)
  for `0`-forms (`constOfIsEmpty`) and `1`-forms (`ofSubsingleton`),
  sync with the API for `ContinuousMultilinearMap`.
-/

open Filter ContinuousAlternatingMap Set
open scoped Topology

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n m k : ℕ} {r : WithTop ℕ∞}
  {ω ω₁ ω₂ : E → E [⋀^Fin n]→L[𝕜] F} {s t : Set E} {x : E}

/-- Exterior derivative of a differential form.

There are a few competing definitions of the exterior derivative of a differential form
that differ from each other by a normalization factor.
We use the following one:

$$
dω(x; v_0, \dots, v_n) = \sum_{i=0}^n (-1)^i D_x ω(x; v_0, \dots, \widehat{v_i}, \dots, v_n) · v_i
$$

where $$\widehat{v_i}$$ means that we omit this element of the tuple, see `extDeriv_apply`.
-/
noncomputable def extDeriv (ω : E → E [⋀^Fin n]→L[𝕜] F) (x : E) : E [⋀^Fin (n + 1)]→L[𝕜] F :=
  .alternatizeUncurryFin (fderiv 𝕜 ω x)

/-- Exterior derivative of a differential form within a set.

There are a few competing definitions of the exterior derivative of a differential form
that differ from each other by a normalization factor.
We use the following one:

$$
dω(x; v_0, \dots, v_n) = \sum_{i=0}^n (-1)^i D_x ω(x; v_0, \dots, \widehat{v_i}, \dots, v_n) · v_i
$$

where $$\widehat{v_i}$$ means that we omit this element of the tuple, see `extDerivWithin_apply`.
-/
noncomputable def extDerivWithin (ω : E → E [⋀^Fin n]→L[𝕜] F) (s : Set E) (x : E) :
    E [⋀^Fin (n + 1)]→L[𝕜] F :=
  .alternatizeUncurryFin (fderivWithin 𝕜 ω s x)

@[simp]
theorem extDerivWithin_univ (ω : E → E [⋀^Fin n]→L[𝕜] F) :
    extDerivWithin ω univ = extDeriv ω := by
  ext1 x
  rw [extDerivWithin, extDeriv, fderivWithin_univ]

theorem extDerivWithin_add (hsx : UniqueDiffWithinAt 𝕜 s x)
    (hω₁ : DifferentiableWithinAt 𝕜 ω₁ s x) (hω₂ : DifferentiableWithinAt 𝕜 ω₂ s x) :
    extDerivWithin (ω₁ + ω₂) s x = extDerivWithin ω₁ s x + extDerivWithin ω₂ s x := by
  simp [extDerivWithin, fderivWithin_add hsx hω₁ hω₂, alternatizeUncurryFin_add]

theorem extDerivWithin_fun_add (hsx : UniqueDiffWithinAt 𝕜 s x)
    (hω₁ : DifferentiableWithinAt 𝕜 ω₁ s x) (hω₂ : DifferentiableWithinAt 𝕜 ω₂ s x) :
    extDerivWithin (fun x ↦ ω₁ x + ω₂ x) s x = extDerivWithin ω₁ s x + extDerivWithin ω₂ s x :=
  extDerivWithin_add hsx hω₁ hω₂

theorem extDeriv_add (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜 ω₂ x) :
    extDeriv (ω₁ + ω₂) x = extDeriv ω₁ x + extDeriv ω₂ x := by
  simp [← extDerivWithin_univ, extDerivWithin_add, *, DifferentiableAt.differentiableWithinAt]

theorem extDeriv_fun_add (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜 ω₂ x) :
    extDeriv (fun x ↦ ω₁ x + ω₂ x) x = extDeriv ω₁ x + extDeriv ω₂ x :=
  extDeriv_add hω₁ hω₂

theorem extDerivWithin_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F) (hsx : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin (c • ω) s x = c • extDerivWithin ω s x := by
  simp [extDerivWithin, fderivWithin_const_smul_of_field, hsx, alternatizeUncurryFin_smul]

theorem extDerivWithin_fun_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F)
    (hsx : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin (fun x ↦ c • ω x) s x = c • extDerivWithin ω s x :=
  extDerivWithin_smul c ω hsx

theorem extDeriv_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F) :
    extDeriv (c • ω) x = c • extDeriv ω x := by
  simp [← extDerivWithin_univ, extDerivWithin_smul]

theorem extDeriv_fun_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F) :
    extDeriv (c • ω) x = c • extDeriv ω x :=
  extDeriv_smul c ω

/-- The exterior derivative of a `0`-form given by a function `f` within a set
is the 1-form given by the derivative of `f` within the set. -/
theorem extDerivWithin_constOfIsEmpty (f : E → F) (hs : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin (fun x ↦ constOfIsEmpty 𝕜 E (Fin 0) (f x)) s x =
      .ofSubsingleton _ _ _ (0 : Fin 1) (fderivWithin 𝕜 f s x) := by
  simp only [extDerivWithin, ← constOfIsEmptyLIE_apply, ← Function.comp_def _ f,
    (constOfIsEmptyLIE 𝕜 E F (Fin 0)).comp_fderivWithin hs,
    alternatizeUncurryFin_constOfIsEmptyLIE_comp]

/-- The exterior derivative of a `0`-form given by a function `f`
is the 1-form given by the derivative of `f`. -/
theorem extDeriv_constOfIsEmpty (f : E → F) (x : E) :
    extDeriv (fun x ↦ constOfIsEmpty 𝕜 E (Fin 0) (f x)) x =
      .ofSubsingleton _ _ _ (0 : Fin 1) (fderiv 𝕜 f x) := by
  simp [← extDerivWithin_univ, extDerivWithin_constOfIsEmpty, fderivWithin_univ]

theorem Filter.EventuallyEq.extDerivWithin_eq (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x := by
  simp only [extDerivWithin, alternatizeUncurryFin, hs.fderivWithin_eq hx]

theorem Filter.EventuallyEq.extDerivWithin_eq_of_mem (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : x ∈ s) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  hs.extDerivWithin_eq (mem_of_mem_nhdsWithin hx hs :)

theorem Filter.EventuallyEq.extDerivWithin_eq_of_insert (hs : ω₁ =ᶠ[𝓝[insert x s] x] ω₂) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x := by
  apply Filter.EventuallyEq.extDerivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
  exact (mem_of_mem_nhdsWithin (mem_insert x s) hs :)

theorem Filter.EventuallyEq.extDerivWithin' (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (ht : t ⊆ s) :
    extDerivWithin ω₁ t =ᶠ[𝓝[s] x] extDerivWithin ω₂ t :=
  (eventually_eventually_nhdsWithin.2 hs).mp <| eventually_mem_nhdsWithin.mono fun _y hys hs =>
    EventuallyEq.extDerivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)

protected theorem Filter.EventuallyEq.extDerivWithin (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) :
    extDerivWithin ω₁ s =ᶠ[𝓝[s] x] extDerivWithin ω₂ s :=
  hs.extDerivWithin' .rfl

theorem Filter.EventuallyEq.extDerivWithin_eq_nhds (h : ω₁ =ᶠ[𝓝 x] ω₂) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  (h.filter_mono nhdsWithin_le_nhds).extDerivWithin_eq h.self_of_nhds

theorem extDerivWithin_congr (hs : EqOn ω₁ ω₂ s) (hx : ω₁ x = ω₂ x) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).extDerivWithin_eq hx

theorem extDerivWithin_congr' (hs : EqOn ω₁ ω₂ s) (hx : x ∈ s) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  extDerivWithin_congr hs (hs hx)

protected theorem Filter.EventuallyEq.extDeriv (h : ω₁ =ᶠ[𝓝 x] ω₂) :
    extDeriv ω₁ =ᶠ[𝓝 x] extDeriv ω₂ := by
  simp only [← nhdsWithin_univ, ← extDerivWithin_univ] at *
  exact h.extDerivWithin

theorem Filter.EventuallyEq.extDeriv_eq (h : ω₁ =ᶠ[𝓝 x] ω₂) : extDeriv ω₁ x = extDeriv ω₂ x :=
  h.extDeriv.self_of_nhds

theorem extDerivWithin_apply (h : DifferentiableWithinAt 𝕜 ω s x) (hs : UniqueDiffWithinAt 𝕜 s x)
    (v : Fin (n + 1) → E) :
    extDerivWithin ω s x v =
      ∑ i, (-1) ^ i.val • fderivWithin 𝕜 (ω · (i.removeNth v)) s x (v i) := by
  simp [extDerivWithin, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    fderivWithin_continuousAlternatingMap_apply_const_apply, *]

theorem extDeriv_apply (h : DifferentiableAt 𝕜 ω x) (v : Fin (n + 1) → E) :
    extDeriv ω x v = ∑ i, (-1) ^ i.val • fderiv 𝕜 (ω · (i.removeNth v)) x (v i) := by
  simp [← extDerivWithin_univ, extDerivWithin_apply h.differentiableWithinAt]

/-- The second exterior derivative of a sufficiently smooth differential form is zero. -/
theorem extDerivWithin_extDerivWithin_apply (hω : ContDiffWithinAt 𝕜 r ω s x)
    (hr : minSmoothness 𝕜 2 ≤ r) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ closure (interior s))
    (h'x : x ∈ s) : extDerivWithin (extDerivWithin ω s) s x = 0 := calc
  extDerivWithin (extDerivWithin ω s) s x
    = alternatizeUncurryFin (fderivWithin 𝕜 (fun y ↦
        alternatizeUncurryFin (fderivWithin 𝕜 ω s y)) s x) := rfl
  _ = alternatizeUncurryFin (alternatizeUncurryFinCLM _ _ _ ∘L
        fderivWithin 𝕜 (fderivWithin 𝕜 ω s) s x) := by
    congr 1
    have : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 ω s) s x := by
      refine (hω.fderivWithin_right hs ?_ h'x).differentiableWithinAt le_rfl
      exact le_minSmoothness.trans hr
    exact alternatizeUncurryFinCLM _ _ _ |>.hasFDerivAt.comp_hasFDerivWithinAt x
      this.hasFDerivWithinAt |>.fderivWithin (hs.uniqueDiffWithinAt h'x)
  _ = 0 := alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric <|
    hω.isSymmSndFDerivWithinAt hr hs hx h'x

/-- The second exterior derivative of a sufficiently smooth differential form is zero. -/
theorem extDerivWithin_extDerivWithin_eqOn (hω : ContDiffOn 𝕜 r ω s) (hr : minSmoothness 𝕜 2 ≤ r)
    (hs : UniqueDiffOn 𝕜 s) :
    EqOn (extDerivWithin (extDerivWithin ω s) s) 0 (s ∩ closure (interior s)) := by
  rintro x ⟨h'x, hx⟩
  exact extDerivWithin_extDerivWithin_apply (hω.contDiffWithinAt h'x) hr hs hx h'x

/-- The second exterior derivative of a sufficiently smooth differential form is zero. -/
theorem extDeriv_extDeriv_apply (hω : ContDiffAt 𝕜 r ω x) (hr : minSmoothness 𝕜 2 ≤ r) :
    extDeriv (extDeriv ω) x = 0 := by
  simp only [← extDerivWithin_univ]
  apply extDerivWithin_extDerivWithin_apply (s := univ) hω.contDiffWithinAt hr <;> simp

/-- The second exterior derivative of a sufficiently smooth differential form is zero. -/
theorem extDeriv_extDeriv (h : ContDiff 𝕜 r ω) (hr : minSmoothness 𝕜 2 ≤ r) :
    extDeriv (extDeriv ω) = 0 :=
  funext fun _ ↦ extDeriv_extDeriv_apply h.contDiffAt hr
