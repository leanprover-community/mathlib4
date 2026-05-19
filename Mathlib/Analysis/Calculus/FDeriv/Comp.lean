/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The derivative of a composition (chain rule)

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
composition of functions (the chain rule).
-/

public section


open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
variable {f g : E → F} {f' g' : E →L[𝕜] F} {x : E} {s : Set E} {L : Filter (E × E)}

section Composition

/-!
### Derivative of the composition of two functions

For composition lemmas, we put `x` explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition. -/


variable (x)

theorem HasFDerivAtFilter.comp {g : F → G} {g' : F →L[𝕜] G} {L' : Filter (F × F)}
    (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFilter f f' L)
    (hL : Tendsto (Prod.map f f) L L') :
    HasFDerivAtFilter (g ∘ f) (g' ∘L f') L := by
  -- This proof can be golfed a lot. However, it should be left this way for readability.
  refine .of_isLittleOTVS <| calc
    (fun p ↦ (g ∘ f) p.1 - (g ∘ f) p.2 - (g' ∘L f') (p.1 - p.2))
      = fun p ↦ (g (f p.1) - g (f p.2) - g' (f p.1 - f p.2)) +
          g' (f p.1 - f p.2 - f' (p.1 - p.2)) := by
      ext; simp
    _ =o[𝕜; L] (fun p ↦ p.1 - p.2) := .add ?Hg ?Hf
  case Hg => calc (fun p ↦ g (f p.1) - g (f p.2) - g' (f p.1 - f p.2))
    _ =o[𝕜; L] (fun p ↦ f p.1 - f p.2) :=
      hg.isLittleOTVS.comp_tendsto hL
    _ =O[𝕜; L] (fun p ↦ p.1 - p.2) := hf.isBigOTVS_sub
  case Hf => calc (fun p ↦ g' (f p.1 - f p.2 - f' (p.1 - p.2)))
    _ =O[𝕜; L] (fun p ↦ f p.1 - f p.2 - f' (p.1 - p.2)) := g'.isBigOTVS_comp
    _ =o[𝕜; L] (fun p ↦ p.1 - p.2) := hf.isLittleOTVS

/-- The chain rule for derivatives in the sense of strict differentiability. -/
@[fun_prop]
protected theorem HasStrictFDerivAt.comp {g : F → G} {g' : F →L[𝕜] G}
    (hg : HasStrictFDerivAt g g' (f x)) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => g (f x)) (g'.comp f') x :=
  HasFDerivAtFilter.comp hg hf <| hf.continuousAt.tendsto.prodMap_nhds hf.continuousAt.tendsto

@[fun_prop]
theorem HasFDerivWithinAt.comp {g : F → G} {g' : F →L[𝕜] G} {t : Set F}
    (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasFDerivWithinAt (g ∘ f) (g'.comp f') s x :=
  HasFDerivAtFilter.comp hg hf <| .prodMap (hf.continuousWithinAt.tendsto_nhdsWithin hst) <|
    tendsto_pure_pure ..

@[fun_prop]
theorem HasFDerivAt.comp_hasFDerivWithinAt {g : F → G} {g' : F →L[𝕜] G}
    (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (g ∘ f) (g'.comp f') s x :=
  hg.hasFDerivWithinAt.comp x hf (mapsTo_univ _ _)

@[fun_prop]
theorem HasFDerivWithinAt.comp_of_tendsto {g : F → G} {g' : F →L[𝕜] G} {t : Set F}
    (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt f f' s x)
    (hst : Tendsto f (𝓝[s] x) (𝓝[t] f x)) : HasFDerivWithinAt (g ∘ f) (g'.comp f') s x :=
  HasFDerivAtFilter.comp hg hf <| hst.prodMap <| tendsto_pure_pure ..

theorem HasFDerivWithinAt.comp_hasFDerivAt {g : F → G} {g' : F →L[𝕜] G} {t : Set F}
    (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivAt f f' x)
    (ht : ∀ᶠ x' in 𝓝 x, f x' ∈ t) : HasFDerivAt (g ∘ f) (g' ∘L f') x :=
  HasFDerivAtFilter.comp hg hf <| .prodMap (tendsto_nhdsWithin_iff.mpr ⟨hf.continuousAt, ht⟩) <|
    tendsto_pure_pure ..

theorem HasFDerivWithinAt.comp_hasFDerivAt_of_eq {g : F → G} {g' : F →L[𝕜] G} {t : Set F} {y : F}
    (hg : HasFDerivWithinAt g g' t y) (hf : HasFDerivAt f f' x)
    (ht : ∀ᶠ x' in 𝓝 x, f x' ∈ t) (hy : y = f x) : HasFDerivAt (g ∘ f) (g' ∘L f') x := by
  subst y; exact hg.comp_hasFDerivAt x hf ht

/-- The chain rule. -/
@[fun_prop]
theorem HasFDerivAt.comp {g : F → G} {g' : F →L[𝕜] G} (hg : HasFDerivAt g g' (f x))
    (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp f') x :=
  HasFDerivAtFilter.comp hg hf <| hf.continuousAt.tendsto.prodMap <| tendsto_pure_pure ..

@[fun_prop]
theorem DifferentiableWithinAt.comp {g : F → G} {t : Set F}
    (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x)
    (h : MapsTo f s t) : DifferentiableWithinAt 𝕜 (g ∘ f) s x :=
  (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h).differentiableWithinAt

@[fun_prop]
theorem DifferentiableWithinAt.comp' {g : F → G} {t : Set F}
    (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono inter_subset_left) inter_subset_right

@[fun_prop]
theorem DifferentiableAt.fun_comp' {f : E → F} {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (fun x ↦ g (f x)) x :=
  (hg.hasFDerivAt.comp x hf.hasFDerivAt).differentiableAt

@[fun_prop]
theorem DifferentiableAt.comp {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x :=
  (hg.hasFDerivAt.comp x hf.hasFDerivAt).differentiableAt

@[fun_prop]
theorem DifferentiableAt.comp_differentiableWithinAt {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (g ∘ f) s x :=
  hg.differentiableWithinAt.comp x hf (mapsTo_univ _ _)

theorem fderivWithin_comp {g : F → G} {t : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g ∘ f) s x = (fderivWithin 𝕜 g t (f x)).comp (fderivWithin 𝕜 f s x) :=
  (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h).fderivWithin hxs

theorem fderivWithin_comp_of_eq {g : F → G} {t : Set F} {y : F}
    (hg : DifferentiableWithinAt 𝕜 g t y) (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t)
    (hxs : UniqueDiffWithinAt 𝕜 s x) (hy : f x = y) :
    fderivWithin 𝕜 (g ∘ f) s x = (fderivWithin 𝕜 g t (f x)).comp (fderivWithin 𝕜 f s x) := by
  subst hy; exact fderivWithin_comp _ hg hf h hxs

/-- A variant for the derivative of a composition, written without `∘`. -/
theorem fderivWithin_comp' {g : F → G} {t : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y ↦ g (f y)) s x
      = (fderivWithin 𝕜 g t (f x)).comp (fderivWithin 𝕜 f s x) :=
  fderivWithin_comp _ hg hf h hxs

/-- A variant for the derivative of a composition, written without `∘`. -/
theorem fderivWithin_comp_of_eq' {g : F → G} {t : Set F} {y : F}
    (hg : DifferentiableWithinAt 𝕜 g t y) (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t)
    (hxs : UniqueDiffWithinAt 𝕜 s x) (hy : f x = y) :
    fderivWithin 𝕜 (fun y ↦ g (f y)) s x
      = (fderivWithin 𝕜 g t (f x)).comp (fderivWithin 𝕜 f s x) := by
  subst hy; exact fderivWithin_comp _ hg hf h hxs

/-- A version of `fderivWithin_comp` that is useful to rewrite the composition of two derivatives
  into a single derivative. This version always applies, but creates a new side-goal `f x = y`. -/
theorem fderivWithin_fderivWithin {g : F → G} {f : E → F} {x : E} {y : F} {s : Set E} {t : Set F}
    (hg : DifferentiableWithinAt 𝕜 g t y) (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t)
    (hxs : UniqueDiffWithinAt 𝕜 s x) (hy : f x = y) (v : E) :
    fderivWithin 𝕜 g t y (fderivWithin 𝕜 f s x v) = fderivWithin 𝕜 (g ∘ f) s x v := by
  subst y
  rw [fderivWithin_comp x hg hf h hxs, coe_comp', Function.comp_apply]

/-- Ternary version of `fderivWithin_comp`, with equality assumptions of basepoints added, in
  order to apply more easily as a rewrite from right-to-left. -/
theorem fderivWithin_comp₃ {g' : G → G'} {g : F → G} {t : Set F} {u : Set G} {y : F} {y' : G}
    (hg' : DifferentiableWithinAt 𝕜 g' u y') (hg : DifferentiableWithinAt 𝕜 g t y)
    (hf : DifferentiableWithinAt 𝕜 f s x) (h2g : MapsTo g t u) (h2f : MapsTo f s t) (h3g : g y = y')
    (h3f : f x = y) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g' ∘ g ∘ f) s x =
      (fderivWithin 𝕜 g' u y').comp ((fderivWithin 𝕜 g t y).comp (fderivWithin 𝕜 f s x)) := by
  substs h3g h3f
  exact (hg'.hasFDerivWithinAt.comp x (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h2f) <|
    h2g.comp h2f).fderivWithin hxs

theorem fderiv_comp {g : F → G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (g ∘ f) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) :=
  (hg.hasFDerivAt.comp x hf.hasFDerivAt).fderiv

/-- A variant for the derivative of a composition, written without `∘`. -/
theorem fderiv_comp' {g : F → G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun y ↦ g (f y)) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) :=
  fderiv_comp x hg hf

theorem fderiv_comp_fderivWithin {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g ∘ f) s x = (fderiv 𝕜 g (f x)).comp (fderivWithin 𝕜 f s x) :=
  (hg.hasFDerivAt.comp_hasFDerivWithinAt x hf.hasFDerivWithinAt).fderivWithin hxs

@[fun_prop]
theorem DifferentiableOn.fun_comp {g : F → G} {t : Set F} (hg : DifferentiableOn 𝕜 g t)
    (hf : DifferentiableOn 𝕜 f s) (st : MapsTo f s t) :
    DifferentiableOn 𝕜 (fun x ↦ g (f x)) s :=
  fun x hx => DifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

@[fun_prop]
theorem DifferentiableOn.comp {g : F → G} {t : Set F} (hg : DifferentiableOn 𝕜 g t)
    (hf : DifferentiableOn 𝕜 f s) (st : MapsTo f s t) : DifferentiableOn 𝕜 (g ∘ f) s :=
  fun x hx => DifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

@[fun_prop]
theorem Differentiable.fun_comp {g : F → G} (hg : Differentiable 𝕜 g) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 (fun x ↦ g (f x)) :=
  fun x => DifferentiableAt.comp x (hg (f x)) (hf x)

@[fun_prop]
theorem Differentiable.comp {g : F → G} (hg : Differentiable 𝕜 g) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 (g ∘ f) :=
  fun x => DifferentiableAt.comp x (hg (f x)) (hf x)

@[fun_prop]
theorem Differentiable.comp_differentiableOn {g : F → G} (hg : Differentiable 𝕜 g)
    (hf : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (g ∘ f) s :=
  hg.differentiableOn.comp hf (mapsTo_univ _ _)


@[fun_prop]
protected theorem Differentiable.iterate {f : E → E} (hf : Differentiable 𝕜 f) (n : ℕ) :
    Differentiable 𝕜 f^[n] :=
  Nat.recOn n differentiable_id fun _ ihn => ihn.comp hf

@[fun_prop]
protected theorem DifferentiableOn.iterate {f : E → E} (hf : DifferentiableOn 𝕜 f s)
    (hs : MapsTo f s s) (n : ℕ) : DifferentiableOn 𝕜 f^[n] s :=
  Nat.recOn n differentiableOn_id fun _ ihn => ihn.comp hf hs

variable {x}

protected theorem HasFDerivAtFilter.iterate {f : E → E} {f' : E →L[𝕜] E}
    (hf : HasFDerivAtFilter f f' L) (hL : Tendsto (Prod.map f f) L L) (n : ℕ) :
    HasFDerivAtFilter f^[n] (f' ^ n) L := by
  induction n with
  | zero => exact hasFDerivAtFilter_id L
  | succ n ihn =>
    rw [Function.iterate_succ, pow_succ]
    exact ihn.comp hf hL

@[fun_prop]
protected theorem HasFDerivAt.iterate {f : E → E} {f' : E →L[𝕜] E} (hf : HasFDerivAt f f' x)
    (hx : f x = x) (n : ℕ) : HasFDerivAt f^[n] (f' ^ n) x := by
  refine HasFDerivAtFilter.iterate hf ?_ n
  simpa [hx] using hf.continuousAt.tendsto.prodMap (tendsto_pure_pure f x)

@[fun_prop]
protected theorem HasFDerivWithinAt.iterate {f : E → E} {f' : E →L[𝕜] E}
    (hf : HasFDerivWithinAt f f' s x) (hx : f x = x) (hs : MapsTo f s s) (n : ℕ) :
    HasFDerivWithinAt f^[n] (f' ^ n) s x := by
  refine HasFDerivAtFilter.iterate hf ?_ n
  simpa [hx] using hf.continuousWithinAt.tendsto_nhdsWithin hs |>.prodMap (tendsto_pure_pure f x)

@[fun_prop]
protected theorem HasStrictFDerivAt.iterate {f : E → E} {f' : E →L[𝕜] E}
    (hf : HasStrictFDerivAt f f' x) (hx : f x = x) (n : ℕ) :
    HasStrictFDerivAt f^[n] (f' ^ n) x := by
  refine HasFDerivAtFilter.iterate hf ?_ n
  simpa [hx, ContinuousAt] using hf.continuousAt.prodMap' hf.continuousAt

@[fun_prop]
protected theorem DifferentiableAt.iterate {f : E → E} (hf : DifferentiableAt 𝕜 f x) (hx : f x = x)
    (n : ℕ) : DifferentiableAt 𝕜 f^[n] x :=
  (hf.hasFDerivAt.iterate hx n).differentiableAt

@[fun_prop]
protected theorem DifferentiableWithinAt.iterate {f : E → E} (hf : DifferentiableWithinAt 𝕜 f s x)
    (hx : f x = x) (hs : MapsTo f s s) (n : ℕ) : DifferentiableWithinAt 𝕜 f^[n] s x :=
  (hf.hasFDerivWithinAt.iterate hx hs n).differentiableWithinAt

end Composition

end
