/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel, Yury Kudryashov, Anatole Dedecker
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add

#align_import analysis.calculus.deriv.add from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# One-dimensional derivatives of sums etc

In this file we prove formulas about derivatives of `f + g`, `-f`, `f - g`, and `∑ i, f i x` for
functions from the base field to a normed space over this field.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative
-/

universe u v w

open Classical Topology BigOperators Filter ENNReal

open Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {f f₀ f₁ g : 𝕜 → F}

variable {f' f₀' f₁' g' : F}

variable {x : 𝕜}

variable {s t : Set 𝕜}

variable {L : Filter 𝕜}

section Add

/-! ### Derivative of the sum of two functions -/


nonrec theorem HasDerivAtFilter.add (hf : HasDerivAtFilter f f' x L)
    (hg : HasDerivAtFilter g g' x L) : HasDerivAtFilter (fun y => f y + g y) (f' + g') x L := by
  simpa using (hf.add hg).hasDerivAtFilter

nonrec theorem HasStrictDerivAt.add (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
    HasStrictDerivAt (fun y => f y + g y) (f' + g') x := by simpa using (hf.add hg).hasStrictDerivAt

nonrec theorem HasDerivWithinAt.add (hf : HasDerivWithinAt f f' s x)
    (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (fun y => f y + g y) (f' + g') s x :=
  hf.add hg

nonrec theorem HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f x + g x) (f' + g') x :=
  hf.add hg

theorem derivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (fun y => f y + g y) s x = derivWithin f s x + derivWithin g s x :=
  (hf.hasDerivWithinAt.add hg.hasDerivWithinAt).derivWithin hxs

@[simp]
theorem deriv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun y => f y + g y) x = deriv f x + deriv g x :=
  (hf.hasDerivAt.add hg.hasDerivAt).deriv

-- porting note: new theorem
theorem HasStrictDerivAt.add_const (c : F) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun y ↦ f y + c) f' x :=
  add_zero f' ▸ hf.add (hasStrictDerivAt_const x c)

theorem HasDerivAtFilter.add_const (hf : HasDerivAtFilter f f' x L) (c : F) :
    HasDerivAtFilter (fun y => f y + c) f' x L :=
  add_zero f' ▸ hf.add (hasDerivAtFilter_const x L c)

nonrec theorem HasDerivWithinAt.add_const (hf : HasDerivWithinAt f f' s x) (c : F) :
    HasDerivWithinAt (fun y => f y + c) f' s x :=
  hf.add_const c

nonrec theorem HasDerivAt.add_const (hf : HasDerivAt f f' x) (c : F) :
    HasDerivAt (fun x => f x + c) f' x :=
  hf.add_const c

theorem derivWithin_add_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => f y + c) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_add_const hxs]

theorem deriv_add_const (c : F) : deriv (fun y => f y + c) x = deriv f x := by
  simp only [deriv, fderiv_add_const]

@[simp]
theorem deriv_add_const' (c : F) : (deriv fun y => f y + c) = deriv f :=
  funext fun _ => deriv_add_const c

-- porting note: new theorem
theorem HasStrictDerivAt.const_add (c : F) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun y ↦ c + f y) f' x :=
  zero_add f' ▸ (hasStrictDerivAt_const x c).add hf

theorem HasDerivAtFilter.const_add (c : F) (hf : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun y => c + f y) f' x L :=
  zero_add f' ▸ (hasDerivAtFilter_const x L c).add hf

nonrec theorem HasDerivWithinAt.const_add (c : F) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun y => c + f y) f' s x :=
  hf.const_add c

nonrec theorem HasDerivAt.const_add (c : F) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => c + f x) f' x :=
  hf.const_add c

theorem derivWithin_const_add (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => c + f y) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_const_add hxs]

theorem deriv_const_add (c : F) : deriv (fun y => c + f y) x = deriv f x := by
  simp only [deriv, fderiv_const_add]

@[simp]
theorem deriv_const_add' (c : F) : (deriv fun y => c + f y) = deriv f :=
  funext fun _ => deriv_const_add c

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/


open BigOperators

variable {ι : Type*} {u : Finset ι} {A : ι → 𝕜 → F} {A' : ι → F}

theorem HasDerivAtFilter.sum (h : ∀ i ∈ u, HasDerivAtFilter (A i) (A' i) x L) :
    HasDerivAtFilter (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x L := by
  simpa [ContinuousLinearMap.sum_apply] using (HasFDerivAtFilter.sum h).hasDerivAtFilter

theorem HasStrictDerivAt.sum (h : ∀ i ∈ u, HasStrictDerivAt (A i) (A' i) x) :
    HasStrictDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x := by
  simpa [ContinuousLinearMap.sum_apply] using (HasStrictFDerivAt.sum h).hasStrictDerivAt

theorem HasDerivWithinAt.sum (h : ∀ i ∈ u, HasDerivWithinAt (A i) (A' i) s x) :
    HasDerivWithinAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) s x :=
  HasDerivAtFilter.sum h

theorem HasDerivAt.sum (h : ∀ i ∈ u, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x :=
  HasDerivAtFilter.sum h

theorem derivWithin_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    derivWithin (fun y => ∑ i in u, A i y) s x = ∑ i in u, derivWithin (A i) s x :=
  (HasDerivWithinAt.sum fun i hi => (h i hi).hasDerivWithinAt).derivWithin hxs

@[simp]
theorem deriv_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    deriv (fun y => ∑ i in u, A i y) x = ∑ i in u, deriv (A i) x :=
  (HasDerivAt.sum fun i hi => (h i hi).hasDerivAt).deriv

end Sum

section Neg

/-! ### Derivative of the negative of a function -/

nonrec theorem HasDerivAtFilter.neg (h : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun x => -f x) (-f') x L := by simpa using h.neg.hasDerivAtFilter

nonrec theorem HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => -f x) (-f') s x :=
  h.neg

nonrec theorem HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (fun x => -f x) (-f') x :=
  h.neg

nonrec theorem HasStrictDerivAt.neg (h : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => -f x) (-f') x := by simpa using h.neg.hasStrictDerivAt

theorem derivWithin.neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun y => -f y) s x = -derivWithin f s x := by
  simp only [derivWithin, fderivWithin_neg hxs, ContinuousLinearMap.neg_apply]

theorem deriv.neg : deriv (fun y => -f y) x = -deriv f x := by
  simp only [deriv, fderiv_neg, ContinuousLinearMap.neg_apply]

@[simp]
theorem deriv.neg' : (deriv fun y => -f y) = fun x => -deriv f x :=
  funext fun _ => deriv.neg

end Neg

section Neg2

/-! ### Derivative of the negation function (i.e `Neg.neg`) -/

variable (s x L)

theorem hasDerivAtFilter_neg : HasDerivAtFilter Neg.neg (-1) x L :=
  HasDerivAtFilter.neg <| hasDerivAtFilter_id _ _

theorem hasDerivWithinAt_neg : HasDerivWithinAt Neg.neg (-1) s x :=
  hasDerivAtFilter_neg _ _

theorem hasDerivAt_neg : HasDerivAt Neg.neg (-1) x :=
  hasDerivAtFilter_neg _ _

theorem hasDerivAt_neg' : HasDerivAt (fun x => -x) (-1) x :=
  hasDerivAtFilter_neg _ _

theorem hasStrictDerivAt_neg : HasStrictDerivAt Neg.neg (-1) x :=
  HasStrictDerivAt.neg <| hasStrictDerivAt_id _

theorem deriv_neg : deriv Neg.neg x = -1 :=
  HasDerivAt.deriv (hasDerivAt_neg x)

@[simp]
theorem deriv_neg' : deriv (Neg.neg : 𝕜 → 𝕜) = fun _ => -1 :=
  funext deriv_neg

@[simp]
theorem deriv_neg'' : deriv (fun x : 𝕜 => -x) x = -1 :=
  deriv_neg x

theorem derivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin Neg.neg s x = -1 :=
  (hasDerivWithinAt_neg x s).derivWithin hxs

theorem differentiable_neg : Differentiable 𝕜 (Neg.neg : 𝕜 → 𝕜) :=
  Differentiable.neg differentiable_id

theorem differentiableOn_neg : DifferentiableOn 𝕜 (Neg.neg : 𝕜 → 𝕜) s :=
  DifferentiableOn.neg differentiableOn_id

end Neg2

section Sub

/-! ### Derivative of the difference of two functions -/

theorem HasDerivAtFilter.sub (hf : HasDerivAtFilter f f' x L) (hg : HasDerivAtFilter g g' x L) :
    HasDerivAtFilter (fun x => f x - g x) (f' - g') x L := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

nonrec theorem HasDerivWithinAt.sub (hf : HasDerivWithinAt f f' s x)
    (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (fun x => f x - g x) (f' - g') s x :=
  hf.sub hg

nonrec theorem HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f x - g x) (f' - g') x :=
  hf.sub hg

theorem HasStrictDerivAt.sub (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
    HasStrictDerivAt (fun x => f x - g x) (f' - g') x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem derivWithin_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (fun y => f y - g y) s x = derivWithin f s x - derivWithin g s x :=
  (hf.hasDerivWithinAt.sub hg.hasDerivWithinAt).derivWithin hxs

@[simp]
theorem deriv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun y => f y - g y) x = deriv f x - deriv g x :=
  (hf.hasDerivAt.sub hg.hasDerivAt).deriv

theorem HasDerivAtFilter.sub_const (hf : HasDerivAtFilter f f' x L) (c : F) :
    HasDerivAtFilter (fun x => f x - c) f' x L := by
  simpa only [sub_eq_add_neg] using hf.add_const (-c)

nonrec theorem HasDerivWithinAt.sub_const (hf : HasDerivWithinAt f f' s x) (c : F) :
    HasDerivWithinAt (fun x => f x - c) f' s x :=
  hf.sub_const c

nonrec theorem HasDerivAt.sub_const (hf : HasDerivAt f f' x) (c : F) :
    HasDerivAt (fun x => f x - c) f' x :=
  hf.sub_const c

theorem derivWithin_sub_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => f y - c) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_sub_const hxs]

theorem deriv_sub_const (c : F) : deriv (fun y => f y - c) x = deriv f x := by
  simp only [deriv, fderiv_sub_const]

theorem HasDerivAtFilter.const_sub (c : F) (hf : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun x => c - f x) (-f') x L := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c

nonrec theorem HasDerivWithinAt.const_sub (c : F) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => c - f x) (-f') s x :=
  hf.const_sub c

theorem HasStrictDerivAt.const_sub (c : F) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => c - f x) (-f') x := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c

nonrec theorem HasDerivAt.const_sub (c : F) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => c - f x) (-f') x :=
  hf.const_sub c

theorem derivWithin_const_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => c - f y) s x = -derivWithin f s x := by
  simp [derivWithin, fderivWithin_const_sub hxs]

theorem deriv_const_sub (c : F) : deriv (fun y => c - f y) x = -deriv f x := by
  simp only [← derivWithin_univ,
    derivWithin_const_sub (uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 _ _)]

end Sub
