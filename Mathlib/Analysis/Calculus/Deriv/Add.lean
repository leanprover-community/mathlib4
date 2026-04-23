/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel, Yury Kudryashov, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Init
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# One-dimensional derivatives of sums etc

In this file we prove formulas about derivatives of `f + g`, `-f`, `f - g`, and `∑ i, f i x` for
functions from the base field to a normed space over this field.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative
-/

public section

universe u v w

open scoped Topology Filter ENNReal

open Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f g : 𝕜 → F}
variable {f' g' : F}
variable {x : 𝕜} {s : Set 𝕜} {L : Filter (𝕜 × 𝕜)}

section Add

/-! ### Derivative of the sum of two functions -/

@[to_fun]
theorem HasDerivAtFilter.add (hf : HasDerivAtFilter f f' L)
    (hg : HasDerivAtFilter g g' L) : HasDerivAtFilter (f + g) (f' + g') L := by
  simpa using (hf.hasFDerivAtFilter.add hg.hasFDerivAtFilter).hasDerivAtFilter

@[to_fun]
theorem HasStrictDerivAt.add (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
    HasStrictDerivAt (f + g) (f' + g') x :=
  HasDerivAtFilter.add hf hg

@[to_fun]
theorem HasDerivWithinAt.add (hf : HasDerivWithinAt f f' s x)
    (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (f + g) (f' + g') s x :=
  HasDerivAtFilter.add hf hg

@[to_fun]
theorem HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (f + g) (f' + g') x :=
  HasDerivAtFilter.add hf hg

theorem derivWithin_fun_add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (fun y ↦ f y + g y) s x = derivWithin f s x + derivWithin g s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hf.hasDerivWithinAt.add hg.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

theorem derivWithin_add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (f + g) s x = derivWithin f s x + derivWithin g s x :=
  derivWithin_fun_add hf hg

@[simp]
theorem deriv_fun_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun y ↦ f y + g y) x = deriv f x + deriv g x :=
  (hf.hasDerivAt.add hg.hasDerivAt).deriv

@[simp]
theorem deriv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (f + g) x = deriv f x + deriv g x :=
  (hf.hasDerivAt.add hg.hasDerivAt).deriv

@[simp]
theorem hasDerivAtFilter_add_const_iff (c : F) :
    HasDerivAtFilter (f · + c) f' L ↔ HasDerivAtFilter f f' L :=
  hasFDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivAtFilter.add_const⟩ := hasDerivAtFilter_add_const_iff

@[simp]
theorem hasStrictDerivAt_add_const_iff (c : F) :
    HasStrictDerivAt (f · + c) f' x ↔ HasStrictDerivAt f f' x :=
  hasDerivAtFilter_add_const_iff c

alias ⟨_, HasStrictDerivAt.add_const⟩ := hasStrictDerivAt_add_const_iff

@[simp]
theorem hasDerivWithinAt_add_const_iff (c : F) :
    HasDerivWithinAt (f · + c) f' s x ↔ HasDerivWithinAt f f' s x :=
  hasDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivWithinAt.add_const⟩ := hasDerivWithinAt_add_const_iff

@[simp]
theorem hasDerivAt_add_const_iff (c : F) : HasDerivAt (f · + c) f' x ↔ HasDerivAt f f' x :=
  hasDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivAt.add_const⟩ := hasDerivAt_add_const_iff

theorem derivWithin_add_const (c : F) :
    derivWithin (fun y ↦ f y + c) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_add_const]

theorem deriv_add_const (c : F) : deriv (fun y ↦ f y + c) x = deriv f x := by
  simp only [deriv, fderiv_add_const]

@[simp]
theorem deriv_add_const' (c : F) : (deriv fun y ↦ f y + c) = deriv f :=
  funext fun _ ↦ deriv_add_const c

theorem hasDerivAtFilter_const_add_iff (c : F) :
    HasDerivAtFilter (c + f ·) f' L ↔ HasDerivAtFilter f f' L :=
  hasFDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivAtFilter.const_add⟩ := hasDerivAtFilter_const_add_iff

@[simp]
theorem hasStrictDerivAt_const_add_iff (c : F) :
    HasStrictDerivAt (c + f ·) f' x ↔ HasStrictDerivAt f f' x :=
  hasDerivAtFilter_const_add_iff c

alias ⟨_, HasStrictDerivAt.const_add⟩ := hasStrictDerivAt_const_add_iff

@[simp]
theorem hasDerivWithinAt_const_add_iff (c : F) :
    HasDerivWithinAt (c + f ·) f' s x ↔ HasDerivWithinAt f f' s x :=
  hasDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivWithinAt.const_add⟩ := hasDerivWithinAt_const_add_iff

@[simp]
theorem hasDerivAt_const_add_iff (c : F) : HasDerivAt (c + f ·) f' x ↔ HasDerivAt f f' x :=
  hasDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivAt.const_add⟩ := hasDerivAt_const_add_iff

theorem derivWithin_const_add (c : F) :
    derivWithin (c + f ·) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_const_add]

@[simp]
theorem derivWithin_const_add_fun (c : F) :
    derivWithin (c + f ·) = derivWithin f := by
  ext
  apply derivWithin_const_add

theorem deriv_const_add (c : F) : deriv (c + f ·) x = deriv f x := by
  simp only [deriv, fderiv_const_add]

@[simp]
theorem deriv_const_add' (c : F) : (deriv (c + f ·)) = deriv f :=
  funext fun _ ↦ deriv_const_add c

lemma differentiableAt_comp_add_const {a b : 𝕜} :
    DifferentiableAt 𝕜 (fun x ↦ f (x + b)) a ↔ DifferentiableAt 𝕜 f (a + b) := by
  grind [add_comm, differentiableAt_comp_add_left]

lemma differentiableAt_iff_comp_const_add {a b : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x ↦ f (b + x)) (-b + a) := by
  simp [differentiableAt_comp_add_left]

lemma differentiableAt_iff_comp_add_const {a b : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x ↦ f (x + b)) (a - b) := by
  simp [differentiableAt_comp_add_const]

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/

variable {ι : Type*} {u : Finset ι} {A : ι → 𝕜 → F} {A' : ι → F}

theorem HasDerivAtFilter.fun_sum (h : ∀ i ∈ u, HasDerivAtFilter (A i) (A' i) L) :
    HasDerivAtFilter (fun y ↦ ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) L := by
  simpa using (HasFDerivAtFilter.fun_sum h).hasDerivAtFilter

theorem HasDerivAtFilter.sum (h : ∀ i ∈ u, HasDerivAtFilter (A i) (A' i) L) :
    HasDerivAtFilter (∑ i ∈ u, A i) (∑ i ∈ u, A' i) L := by
  convert HasDerivAtFilter.fun_sum h
  simp

theorem HasStrictDerivAt.fun_sum (h : ∀ i ∈ u, HasStrictDerivAt (A i) (A' i) x) :
    HasStrictDerivAt (fun y ↦ ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x :=
  HasDerivAtFilter.fun_sum h

theorem HasStrictDerivAt.sum (h : ∀ i ∈ u, HasStrictDerivAt (A i) (A' i) x) :
    HasStrictDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x :=
  HasDerivAtFilter.sum h

theorem HasDerivWithinAt.fun_sum (h : ∀ i ∈ u, HasDerivWithinAt (A i) (A' i) s x) :
    HasDerivWithinAt (fun y ↦ ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) s x :=
  HasDerivAtFilter.fun_sum h

theorem HasDerivWithinAt.sum (h : ∀ i ∈ u, HasDerivWithinAt (A i) (A' i) s x) :
    HasDerivWithinAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) s x :=
  HasDerivAtFilter.sum h

theorem HasDerivAt.fun_sum (h : ∀ i ∈ u, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (fun y ↦ ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x :=
  HasDerivAtFilter.fun_sum h

theorem HasDerivAt.sum (h : ∀ i ∈ u, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x :=
  HasDerivAtFilter.sum h

theorem derivWithin_fun_sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    derivWithin (fun y ↦ ∑ i ∈ u, A i y) s x = ∑ i ∈ u, derivWithin (A i) s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.fun_sum fun i hi ↦ (h i hi).hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

theorem derivWithin_sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    derivWithin (∑ i ∈ u, A i) s x = ∑ i ∈ u, derivWithin (A i) s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.sum fun i hi ↦ (h i hi).hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[simp]
theorem deriv_fun_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    deriv (fun y ↦ ∑ i ∈ u, A i y) x = ∑ i ∈ u, deriv (A i) x :=
  (HasDerivAt.fun_sum fun i hi ↦ (h i hi).hasDerivAt).deriv

@[simp]
theorem deriv_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    deriv (∑ i ∈ u, A i) x = ∑ i ∈ u, deriv (A i) x :=
  (HasDerivAt.sum fun i hi ↦ (h i hi).hasDerivAt).deriv

end Sum

section Neg

/-! ### Derivative of the negative of a function -/

@[to_fun]
theorem HasDerivAtFilter.neg (h : HasDerivAtFilter f f' L) :
    HasDerivAtFilter (-f) (-f') L := by simpa using (HasFDerivAtFilter.neg h).hasDerivAtFilter

@[to_fun]
theorem HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (-f) (-f') s x :=
  HasDerivAtFilter.neg h

@[to_fun]
theorem HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (-f) (-f') x :=
  HasDerivAtFilter.neg h

@[to_fun]
theorem HasStrictDerivAt.neg (h : HasStrictDerivAt f f' x) : HasStrictDerivAt (-f) (-f') x :=
  HasDerivAtFilter.neg h

@[to_fun]
theorem derivWithin.neg : derivWithin (-f) s x = -derivWithin f s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · simp only [derivWithin, fderivWithin_neg hsx, ContinuousLinearMap.neg_apply]
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[to_fun]
theorem deriv.neg : deriv (-f) x = -deriv f x := by
  simp only [deriv, fderiv_neg, ContinuousLinearMap.neg_apply]

@[to_fun (attr := simp)]
theorem deriv.neg' : (deriv (-f)) = fun x ↦ -deriv f x :=
  funext fun _ ↦ deriv.neg

end Neg

section Neg2

/-! ### Derivative of the negation function (i.e `Neg.neg`) -/

variable (s x L)

theorem hasDerivAtFilter_neg : HasDerivAtFilter Neg.neg (-1) L :=
  HasDerivAtFilter.neg <| hasDerivAtFilter_id _

theorem hasDerivWithinAt_neg : HasDerivWithinAt Neg.neg (-1) s x :=
  hasDerivAtFilter_neg _

theorem hasDerivAt_neg : HasDerivAt Neg.neg (-1) x :=
  hasDerivAtFilter_neg _

theorem hasDerivAt_neg' : HasDerivAt (fun x ↦ -x) (-1) x :=
  hasDerivAtFilter_neg _

theorem hasStrictDerivAt_neg : HasStrictDerivAt Neg.neg (-1) x :=
  HasStrictDerivAt.neg <| hasStrictDerivAt_id _

theorem deriv_neg : deriv Neg.neg x = -1 :=
  HasDerivAt.deriv (hasDerivAt_neg x)

@[simp]
theorem deriv_neg' : deriv (Neg.neg : 𝕜 → 𝕜) = fun _ ↦ -1 :=
  funext deriv_neg

@[simp]
theorem deriv_neg'' : deriv (fun x : 𝕜 ↦ -x) x = -1 :=
  deriv_neg x

theorem derivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin Neg.neg s x = -1 :=
  (hasDerivWithinAt_neg x s).derivWithin hxs

theorem differentiable_neg : Differentiable 𝕜 (Neg.neg : 𝕜 → 𝕜) :=
  Differentiable.neg differentiable_id

theorem differentiableOn_neg : DifferentiableOn 𝕜 (Neg.neg : 𝕜 → 𝕜) s :=
  DifferentiableOn.neg differentiableOn_id

lemma differentiableAt_comp_neg {a : 𝕜} :
    DifferentiableAt 𝕜 (fun x ↦ f (-x)) a ↔ DifferentiableAt 𝕜 f (-a) := by
  refine ⟨fun H ↦ ?_, fun H ↦ H.comp a differentiable_neg.differentiableAt⟩
  convert ((neg_neg a).symm ▸ H).comp (-a) differentiable_neg.differentiableAt
  ext
  simp only [Function.comp_apply, neg_neg]

lemma differentiableAt_iff_comp_neg {a : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x ↦ f (-x)) (-a) := by
  simp_rw [← differentiableAt_comp_neg, neg_neg]

end Neg2

section Sub

/-! ### Derivative of the difference of two functions -/

@[to_fun]
theorem HasDerivAtFilter.sub (hf : HasDerivAtFilter f f' L) (hg : HasDerivAtFilter g g' L) :
    HasDerivAtFilter (f - g) (f' - g') L := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun]
theorem HasDerivWithinAt.sub (hf : HasDerivWithinAt f f' s x)
    (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (f - g) (f' - g') s x :=
  HasDerivAtFilter.sub hf hg

@[to_fun]
theorem HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (f - g) (f' - g') x :=
  HasDerivAtFilter.sub hf hg

@[to_fun]
theorem HasStrictDerivAt.sub (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
    HasStrictDerivAt (f - g) (f' - g') x :=
  HasDerivAtFilter.sub hf hg

theorem derivWithin_fun_sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (fun y ↦ f y - g y) s x = derivWithin f s x - derivWithin g s x := by
  simp only [sub_eq_add_neg, derivWithin_fun_add hf hg.fun_neg, derivWithin.fun_neg]

theorem derivWithin_sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (f - g) s x = derivWithin f s x - derivWithin g s x :=
  derivWithin_fun_sub hf hg

@[simp]
theorem deriv_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun y ↦ f y - g y) x = deriv f x - deriv g x :=
  (hf.hasDerivAt.sub hg.hasDerivAt).deriv

@[simp]
theorem deriv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (f - g) x = deriv f x - deriv g x :=
  (hf.hasDerivAt.sub hg.hasDerivAt).deriv

@[simp]
theorem hasDerivAtFilter_sub_const_iff (c : F) :
    HasDerivAtFilter (fun x ↦ f x - c) f' L ↔ HasDerivAtFilter f f' L :=
  hasFDerivAtFilter_sub_const_iff c

alias ⟨_, HasDerivAtFilter.sub_const⟩ := hasDerivAtFilter_sub_const_iff

@[simp]
theorem hasDerivWithinAt_sub_const_iff (c : F) :
    HasDerivWithinAt (f · - c) f' s x ↔ HasDerivWithinAt f f' s x :=
  hasDerivAtFilter_sub_const_iff c

alias ⟨_, HasDerivWithinAt.sub_const⟩ := hasDerivWithinAt_sub_const_iff

@[simp]
theorem hasDerivAt_sub_const_iff (c : F) : HasDerivAt (f · - c) f' x ↔ HasDerivAt f f' x :=
  hasDerivAtFilter_sub_const_iff c

alias ⟨_, HasDerivAt.sub_const⟩ := hasDerivAt_sub_const_iff

theorem derivWithin_sub_const (c : F) :
    derivWithin (fun y ↦ f y - c) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_sub_const]

@[simp]
theorem derivWithin_sub_const_fun (c : F) : derivWithin (f · - c) = derivWithin f := by
  ext
  apply derivWithin_sub_const

theorem deriv_sub_const (c : F) : deriv (fun y ↦ f y - c) x = deriv f x := by
  simp only [deriv, fderiv_sub_const]

@[simp]
theorem deriv_sub_const_fun (c : F) : deriv (f · - c) = deriv f := by
  ext
  apply deriv_sub_const

theorem HasDerivAtFilter.const_sub (c : F) (hf : HasDerivAtFilter f f' L) :
    HasDerivAtFilter (fun x ↦ c - f x) (-f') L := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c

theorem HasDerivWithinAt.const_sub (c : F) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x ↦ c - f x) (-f') s x :=
  HasDerivAtFilter.const_sub c hf

theorem HasStrictDerivAt.const_sub (c : F) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x ↦ c - f x) (-f') x :=
  HasDerivAtFilter.const_sub c hf

nonrec theorem HasDerivAt.const_sub (c : F) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x ↦ c - f x) (-f') x :=
  hf.const_sub c

theorem derivWithin_const_sub (c : F) :
    derivWithin (fun y ↦ c - f y) s x = -derivWithin f s x := by
  simp [sub_eq_add_neg, derivWithin.fun_neg]

theorem deriv_const_sub (c : F) : deriv (fun y ↦ c - f y) x = -deriv f x := by
  simp only [← derivWithin_univ, derivWithin_const_sub]

lemma differentiableAt_comp_sub_const {a b : 𝕜} :
    DifferentiableAt 𝕜 (fun x ↦ f (x - b)) a ↔ DifferentiableAt 𝕜 f (a - b) := by
  simp [sub_eq_add_neg, differentiableAt_comp_add_const]

lemma differentiableAt_comp_const_sub {a b : 𝕜} :
    DifferentiableAt 𝕜 (fun x ↦ f (b - x)) a ↔ DifferentiableAt 𝕜 f (b - a) := by
  refine ⟨fun H ↦ ?_, fun H ↦ H.comp a (differentiable_id.const_sub _).differentiableAt⟩
  convert ((sub_sub_cancel _ a).symm ▸ H).comp (b - a)
    (differentiable_id.const_sub _).differentiableAt
  ext
  simp

lemma differentiableAt_iff_comp_sub_const {a b : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x ↦ f (x - b)) (a + b) := by
  simp [sub_eq_add_neg, differentiableAt_comp_add_const]

lemma differentiableAt_iff_comp_const_sub {a b : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x ↦ f (b - x)) (b - a) := by
  simp [differentiableAt_comp_const_sub]

end Sub
