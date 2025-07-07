/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Star operations on derivatives

This file contains the usual formulas (and existence assertions) for the derivative of the star
operation.

Most of the results in this file only apply when the field that the derivative is respect to has a
trivial star operation; which as should be expected rules out `𝕜 = 𝕜`. The exceptions are
`HasDerivAt.conj_conj` and `DifferentiableAt.conj_conj`, showing that `conj ∘ f ∘ conj` is
differentiable when `f` is (and giving a formula for its derivative).
-/

universe u v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [StarRing 𝕜]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [StarAddMonoid F] [StarModule 𝕜 F]
  [ContinuousStar F] {f : 𝕜 → F} {f' : F} {x : 𝕜}

/-! ### Derivative of `x ↦ star x` -/

section TrivialStar

variable [TrivialStar 𝕜] {s : Set 𝕜} {L : Filter 𝕜}

protected nonrec theorem HasDerivAtFilter.star (h : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun x => star (f x)) (star f') x L := by
  simpa using h.star.hasDerivAtFilter

protected nonrec theorem HasDerivWithinAt.star (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => star (f x)) (star f') s x :=
  h.star

protected nonrec theorem HasDerivAt.star (h : HasDerivAt f f' x) :
    HasDerivAt (fun x => star (f x)) (star f') x :=
  h.star

protected nonrec theorem HasStrictDerivAt.star (h : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => star (f x)) (star f') x := by simpa using h.star.hasStrictDerivAt

protected theorem derivWithin.star :
    derivWithin (fun y => star (f y)) s x = star (derivWithin f s x) := by
  by_cases hxs : UniqueDiffWithinAt 𝕜 s x
  · exact DFunLike.congr_fun (fderivWithin_star hxs) _
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hxs]

protected theorem deriv.star : deriv (fun y => star (f y)) x = star (deriv f x) :=
  DFunLike.congr_fun fderiv_star _

@[simp]
protected theorem deriv.star' : (deriv fun y => star (f y)) = fun x => star (deriv f x) :=
  funext fun _ => deriv.star

end TrivialStar

section NontrivialStar

variable [NormedStarGroup 𝕜]

open scoped ComplexConjugate

/-- If `f` has derivative `f'` at `z`, then `star ∘ f ∘ conj` has derivative `star f'` at
`conj z`. -/
lemma HasDerivAt.star_conj {f : 𝕜 → F} {f' : F} (hf : HasDerivAt f f' x) :
    HasDerivAt (star ∘ f ∘ conj) (star f') (conj x) := by
  rw [hasDerivAt_iff_hasFDerivAt]
  convert hf.hasFDerivAt.star_star
  ext
  simp

/-- A function `f` has derivative `f'` at `z` iff `star ∘ f ∘ conj` has derivative `star f'` at
`conj z`. -/
lemma hasDerivAt_star_conj_iff {f : 𝕜 → F} {x : 𝕜} {f' : F} :
    HasDerivAt (star ∘ f ∘ conj) (star f') (conj x) ↔ HasDerivAt f f' x :=
  ⟨fun hf ↦ by convert hf.star_conj <;> simp [Function.comp_def],
  fun hf ↦ hf.star_conj⟩

/-- If `f` has derivative `f'` at `z`, then `conj ∘ f ∘ conj` has derivative `conj f'` at
`conj z`. -/
lemma HasDerivAt.conj_conj {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivAt f f' x) :
    HasDerivAt (conj ∘ f ∘ conj) (conj f') (conj x) :=
  hf.star_conj

/-- A function `f` has derivative `f'` at `z` iff `conj ∘ f ∘ conj` has derivative `conj f'` at
`conj z`. -/
lemma hasDerivAt_conj_conj_iff {f : 𝕜 → 𝕜} {x f' : 𝕜} :
    HasDerivAt (conj ∘ f ∘ conj) (conj f') (conj x) ↔ HasDerivAt f f' x :=
  hasDerivAt_star_conj_iff

/-- If `f` is differentiable at `conj z`, then `star ∘ f ∘ conj` is differentiable at `z`. -/
lemma DifferentiableAt.star_conj {f : 𝕜 → F} (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (star ∘ f ∘ conj) (conj x) :=
  hf.star_star

/-- A function `f` is differentiable at `conj z` iff `star ∘ f ∘ conj` is differentiable at `z`. -/
lemma differentiableAt_star_conj_iff {f : 𝕜 → F} :
    DifferentiableAt 𝕜 (star ∘ f ∘ conj) (conj x) ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun hf ↦ by convert hf.star_conj <;> simp [Function.comp_def], fun hf ↦ hf.star_star⟩

/-- If `f` is differentiable at `conj z`, then `conj ∘ f ∘ conj` is differentiable at `z`. -/
lemma DifferentiableAt.conj_conj {f : 𝕜 → 𝕜} (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (star ∘ f ∘ conj) (conj x) :=
  hf.star_star

/-- A function `f` is differentiable at `conj z` iff `conj ∘ f ∘ conj` is differentiable at `z`. -/
lemma differentiableAt_conj_conj_iff {f : 𝕜 → 𝕜} :
    DifferentiableAt 𝕜 (conj ∘ f ∘ conj) (conj x) ↔ DifferentiableAt 𝕜 f x :=
  differentiableAt_star_conj_iff

/--
The derivative of `star ∘ f ∘ conj` is `star ∘ deriv f ∘ conj`, allowing for the possibility that
both sides have the junk value `0`.
-/
@[simp]
lemma deriv_star_conj {f : 𝕜 → F} :
    deriv (star ∘ f ∘ conj) = star ∘ deriv f ∘ conj := by
  ext z
  by_cases hf : DifferentiableAt 𝕜 f (conj z)
  · have hd := hf.hasDerivAt.star_conj.deriv
    simp only [Function.comp_def, RingHomCompTriple.comp_apply, RingHom.id_apply,
      Function.comp_apply] at hd ⊢
    exact hd
  · simp only [Function.comp_apply, hf, not_false_eq_true, deriv_zero_of_not_differentiableAt,
      star_zero]
    apply deriv_zero_of_not_differentiableAt
    contrapose! hf
    rw[← RCLike.conj_conj z] at hf
    rwa[← differentiableAt_star_conj_iff]

/--
The derivative of `conj ∘ f ∘ conj` is `conj ∘ deriv f ∘ conj`, allowing for the possibility that
both sides have the junk value `0`.
-/
@[simp]
lemma deriv_conj_conj {f : 𝕜 → 𝕜} :
    deriv (conj ∘ f ∘ conj) = conj ∘ deriv f ∘ conj := deriv_star_conj

end NontrivialStar
