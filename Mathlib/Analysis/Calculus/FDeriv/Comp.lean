/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic

#align_import analysis.calculus.fderiv.comp from "leanprover-community/mathlib"@"e3fb84046afd187b710170887195d50bada934ee"

/-!
# The derivative of a composition (chain rule)

For detailed documentation of the Fréchet derivative,
see the module docstring of `Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
composition of functions (the chain rule).
-/


open Filter Asymptotics ContinuousLinearMap Set Metric

open scoped Classical
open Topology NNReal Filter Asymptotics ENNReal

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
variable {f f₀ f₁ g : E → F}
variable {f' f₀' f₁' g' : E →L[𝕜] F}
variable (e : E →L[𝕜] F)
variable {x : E}
variable {s t : Set E}
variable {L L₁ L₂ : Filter E}

section Composition

/-!
### Derivative of the composition of two functions

For composition lemmas, we put `x` explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition. -/


variable (x)

theorem HasFDerivAtFilter.comp {g : F → G} {g' : F →L[𝕜] G} {L' : Filter F}
    (hg : HasFDerivAtFilter g g' (f x) L') (hf : HasFDerivAtFilter f f' x L) (hL : Tendsto f L L') :
    HasFDerivAtFilter (g ∘ f) (g'.comp f') x L := by
  let eq₁ := (g'.isBigO_comp _ _).trans_isLittleO hf.isLittleO
  let eq₂ := (hg.isLittleO.comp_tendsto hL).trans_isBigO hf.isBigO_sub
  refine .of_isLittleO <| eq₂.triangle <| eq₁.congr_left fun x' => ?_
  simp
#align has_fderiv_at_filter.comp HasFDerivAtFilter.comp

/- A readable version of the previous theorem, a general form of the chain rule. -/
example {g : F → G} {g' : F →L[𝕜] G} (hg : HasFDerivAtFilter g g' (f x) (L.map f))
    (hf : HasFDerivAtFilter f f' x L) : HasFDerivAtFilter (g ∘ f) (g'.comp f') x L := by
  have :=
    calc
      (fun x' => g (f x') - g (f x) - g' (f x' - f x)) =o[L] fun x' => f x' - f x :=
        hg.isLittleO.comp_tendsto le_rfl
      _ =O[L] fun x' => x' - x := hf.isBigO_sub
  refine .of_isLittleO <| this.triangle ?_
  calc
    (fun x' : E => g' (f x' - f x) - g'.comp f' (x' - x))
    _ =ᶠ[L] fun x' => g' (f x' - f x - f' (x' - x)) := eventually_of_forall fun x' => by simp
    _ =O[L] fun x' => f x' - f x - f' (x' - x) := g'.isBigO_comp _ _
    _ =o[L] fun x' => x' - x := hf.isLittleO

@[fun_prop]
theorem HasFDerivWithinAt.comp {g : F → G} {g' : F →L[𝕜] G} {t : Set F}
    (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasFDerivWithinAt (g ∘ f) (g'.comp f') s x :=
  HasFDerivAtFilter.comp x hg hf <| hf.continuousWithinAt.tendsto_nhdsWithin hst
#align has_fderiv_within_at.comp HasFDerivWithinAt.comp

@[fun_prop]
theorem HasFDerivAt.comp_hasFDerivWithinAt {g : F → G} {g' : F →L[𝕜] G}
    (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (g ∘ f) (g'.comp f') s x :=
  hg.comp x hf hf.continuousWithinAt
#align has_fderiv_at.comp_has_fderiv_within_at HasFDerivAt.comp_hasFDerivWithinAt

@[fun_prop]
theorem HasFDerivWithinAt.comp_of_mem {g : F → G} {g' : F →L[𝕜] G} {t : Set F}
    (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt f f' s x)
    (hst : Tendsto f (𝓝[s] x) (𝓝[t] f x)) : HasFDerivWithinAt (g ∘ f) (g'.comp f') s x :=
  HasFDerivAtFilter.comp x hg hf hst
#align has_fderiv_within_at.comp_of_mem HasFDerivWithinAt.comp_of_mem

/-- The chain rule. -/
@[fun_prop]
theorem HasFDerivAt.comp {g : F → G} {g' : F →L[𝕜] G} (hg : HasFDerivAt g g' (f x))
    (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp f') x :=
  HasFDerivAtFilter.comp x hg hf hf.continuousAt
#align has_fderiv_at.comp HasFDerivAt.comp

@[fun_prop]
theorem DifferentiableWithinAt.comp {g : F → G} {t : Set F}
    (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x)
    (h : MapsTo f s t) : DifferentiableWithinAt 𝕜 (g ∘ f) s x :=
  (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h).differentiableWithinAt
#align differentiable_within_at.comp DifferentiableWithinAt.comp

@[fun_prop]
theorem DifferentiableWithinAt.comp' {g : F → G} {t : Set F}
    (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono inter_subset_left) inter_subset_right
#align differentiable_within_at.comp' DifferentiableWithinAt.comp'

@[fun_prop]
theorem DifferentiableAt.comp {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x :=
  (hg.hasFDerivAt.comp x hf.hasFDerivAt).differentiableAt
#align differentiable_at.comp DifferentiableAt.comp

@[fun_prop]
theorem DifferentiableAt.comp_differentiableWithinAt {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (g ∘ f) s x :=
  hg.differentiableWithinAt.comp x hf (mapsTo_univ _ _)
#align differentiable_at.comp_differentiable_within_at DifferentiableAt.comp_differentiableWithinAt

theorem fderivWithin.comp {g : F → G} {t : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g ∘ f) s x = (fderivWithin 𝕜 g t (f x)).comp (fderivWithin 𝕜 f s x) :=
  (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h).fderivWithin hxs
#align fderiv_within.comp fderivWithin.comp

/-- A version of `fderivWithin.comp` that is useful to rewrite the composition of two derivatives
  into a single derivative. This version always applies, but creates a new side-goal `f x = y`. -/
theorem fderivWithin_fderivWithin {g : F → G} {f : E → F} {x : E} {y : F} {s : Set E} {t : Set F}
    (hg : DifferentiableWithinAt 𝕜 g t y) (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t)
    (hxs : UniqueDiffWithinAt 𝕜 s x) (hy : f x = y) (v : E) :
    fderivWithin 𝕜 g t y (fderivWithin 𝕜 f s x v) = fderivWithin 𝕜 (g ∘ f) s x v := by
  subst y
  rw [fderivWithin.comp x hg hf h hxs, coe_comp', Function.comp_apply]
#align fderiv_within_fderiv_within fderivWithin_fderivWithin

/-- Ternary version of `fderivWithin.comp`, with equality assumptions of basepoints added, in
  order to apply more easily as a rewrite from right-to-left. -/
theorem fderivWithin.comp₃ {g' : G → G'} {g : F → G} {t : Set F} {u : Set G} {y : F} {y' : G}
    (hg' : DifferentiableWithinAt 𝕜 g' u y') (hg : DifferentiableWithinAt 𝕜 g t y)
    (hf : DifferentiableWithinAt 𝕜 f s x) (h2g : MapsTo g t u) (h2f : MapsTo f s t) (h3g : g y = y')
    (h3f : f x = y) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g' ∘ g ∘ f) s x =
      (fderivWithin 𝕜 g' u y').comp ((fderivWithin 𝕜 g t y).comp (fderivWithin 𝕜 f s x)) := by
  substs h3g h3f
  exact (hg'.hasFDerivWithinAt.comp x (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h2f) <|
    h2g.comp h2f).fderivWithin hxs
#align fderiv_within.comp₃ fderivWithin.comp₃

theorem fderiv.comp {g : F → G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (g ∘ f) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) :=
  (hg.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
#align fderiv.comp fderiv.comp

theorem fderiv.comp_fderivWithin {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g ∘ f) s x = (fderiv 𝕜 g (f x)).comp (fderivWithin 𝕜 f s x) :=
  (hg.hasFDerivAt.comp_hasFDerivWithinAt x hf.hasFDerivWithinAt).fderivWithin hxs
#align fderiv.comp_fderiv_within fderiv.comp_fderivWithin

@[fun_prop]
theorem DifferentiableOn.comp {g : F → G} {t : Set F} (hg : DifferentiableOn 𝕜 g t)
    (hf : DifferentiableOn 𝕜 f s) (st : MapsTo f s t) : DifferentiableOn 𝕜 (g ∘ f) s :=
  fun x hx => DifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st
#align differentiable_on.comp DifferentiableOn.comp

@[fun_prop]
theorem Differentiable.comp {g : F → G} (hg : Differentiable 𝕜 g) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 (g ∘ f) :=
  fun x => DifferentiableAt.comp x (hg (f x)) (hf x)
#align differentiable.comp Differentiable.comp

@[fun_prop]
theorem Differentiable.comp_differentiableOn {g : F → G} (hg : Differentiable 𝕜 g)
    (hf : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (g ∘ f) s :=
  hg.differentiableOn.comp hf (mapsTo_univ _ _)
#align differentiable.comp_differentiable_on Differentiable.comp_differentiableOn

/-- The chain rule for derivatives in the sense of strict differentiability. -/
@[fun_prop]
protected theorem HasStrictFDerivAt.comp {g : F → G} {g' : F →L[𝕜] G}
    (hg : HasStrictFDerivAt g g' (f x)) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => g (f x)) (g'.comp f') x :=
  ((hg.comp_tendsto (hf.continuousAt.prod_map' hf.continuousAt)).trans_isBigO
      hf.isBigO_sub).triangle <| by
    simpa only [g'.map_sub, f'.coe_comp'] using (g'.isBigO_comp _ _).trans_isLittleO hf
#align has_strict_fderiv_at.comp HasStrictFDerivAt.comp

@[fun_prop]
protected theorem Differentiable.iterate {f : E → E} (hf : Differentiable 𝕜 f) (n : ℕ) :
    Differentiable 𝕜 f^[n] :=
  Nat.recOn n differentiable_id fun _ ihn => ihn.comp hf
#align differentiable.iterate Differentiable.iterate

@[fun_prop]
protected theorem DifferentiableOn.iterate {f : E → E} (hf : DifferentiableOn 𝕜 f s)
    (hs : MapsTo f s s) (n : ℕ) : DifferentiableOn 𝕜 f^[n] s :=
  Nat.recOn n differentiableOn_id fun _ ihn => ihn.comp hf hs
#align differentiable_on.iterate DifferentiableOn.iterate

variable {x}

protected theorem HasFDerivAtFilter.iterate {f : E → E} {f' : E →L[𝕜] E}
    (hf : HasFDerivAtFilter f f' x L) (hL : Tendsto f L L) (hx : f x = x) (n : ℕ) :
    HasFDerivAtFilter f^[n] (f' ^ n) x L := by
  induction' n with n ihn
  · exact hasFDerivAtFilter_id x L
  · rw [Function.iterate_succ, pow_succ]
    rw [← hx] at ihn
    exact ihn.comp x hf hL
#align has_fderiv_at_filter.iterate HasFDerivAtFilter.iterate

@[fun_prop]
protected theorem HasFDerivAt.iterate {f : E → E} {f' : E →L[𝕜] E} (hf : HasFDerivAt f f' x)
    (hx : f x = x) (n : ℕ) : HasFDerivAt f^[n] (f' ^ n) x := by
  refine HasFDerivAtFilter.iterate hf ?_ hx n
  -- Porting note: was `convert hf.continuousAt`
  convert hf.continuousAt.tendsto
  exact hx.symm
#align has_fderiv_at.iterate HasFDerivAt.iterate

@[fun_prop]
protected theorem HasFDerivWithinAt.iterate {f : E → E} {f' : E →L[𝕜] E}
    (hf : HasFDerivWithinAt f f' s x) (hx : f x = x) (hs : MapsTo f s s) (n : ℕ) :
    HasFDerivWithinAt f^[n] (f' ^ n) s x := by
  refine HasFDerivAtFilter.iterate hf ?_ hx n
  rw [_root_.nhdsWithin] -- Porting note: Added `rw` to get rid of an error
  convert tendsto_inf.2 ⟨hf.continuousWithinAt, _⟩
  exacts [hx.symm, (tendsto_principal_principal.2 hs).mono_left inf_le_right]
#align has_fderiv_within_at.iterate HasFDerivWithinAt.iterate

@[fun_prop]
protected theorem HasStrictFDerivAt.iterate {f : E → E} {f' : E →L[𝕜] E}
    (hf : HasStrictFDerivAt f f' x) (hx : f x = x) (n : ℕ) :
    HasStrictFDerivAt f^[n] (f' ^ n) x := by
  induction' n with n ihn
  · exact hasStrictFDerivAt_id x
  · rw [Function.iterate_succ, pow_succ]
    rw [← hx] at ihn
    exact ihn.comp x hf
#align has_strict_fderiv_at.iterate HasStrictFDerivAt.iterate

@[fun_prop]
protected theorem DifferentiableAt.iterate {f : E → E} (hf : DifferentiableAt 𝕜 f x) (hx : f x = x)
    (n : ℕ) : DifferentiableAt 𝕜 f^[n] x :=
  (hf.hasFDerivAt.iterate hx n).differentiableAt
#align differentiable_at.iterate DifferentiableAt.iterate

@[fun_prop]
protected theorem DifferentiableWithinAt.iterate {f : E → E} (hf : DifferentiableWithinAt 𝕜 f s x)
    (hx : f x = x) (hs : MapsTo f s s) (n : ℕ) : DifferentiableWithinAt 𝕜 f^[n] s x :=
  (hf.hasFDerivWithinAt.iterate hx hs n).differentiableWithinAt
#align differentiable_within_at.iterate DifferentiableWithinAt.iterate

end Composition

end
