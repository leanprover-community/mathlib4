/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang, Zaiwen Wen
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Gradient calculus rules

## Main results

This file contains the following parts of gradient.
* the chain rule for the `g : 𝕜 → 𝕜` composed with `f : F → 𝕜`.
* the gradient for the sum of two functions.
* the gradient for finite sum of functions.
* the gradient for the sum of a constant and a function.
* the gradient for the difference of two functions.
* the gradient for the difference of a constant and a function.
* the gradient for the product of two functions.
* the gradient for the product of a constant and a function.
-/

public section

noncomputable section

open Topology InnerProductSpace Set

variable {𝕜 F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {f : F → 𝕜} {f' x : F} {L : Filter F} {s : Set F}

local notation "∇" => gradient

section Composition

/-! ### Gradient of a composition -/

open Set Filter

variable {g : 𝕜 → 𝕜} {g' : 𝕜}
variable {L' : Filter 𝕜} {t : Set 𝕜}

theorem HasGradientAtFilter.comp
    (hg : HasGradientAtFilter g g' (f x) L') (hf : HasGradientAtFilter f f' x L)
    (hL : Tendsto f L L') : HasGradientAtFilter (g ∘ f) (g' • f') x L := by
  rw [HasGradientAtFilter, map_smulₛₗ]
  exact hg.hasDerivAtFilter.comp_hasFDerivAtFilter hf
    (hL.prodMap (Filter.tendsto_pure_pure f x))

theorem HasGradientWithinAt.comp
    (hg : HasGradientWithinAt g g' t (f x)) (hf : HasGradientWithinAt f f' s x)
    (hst : MapsTo f s t) : HasGradientWithinAt (g ∘ f) (g' • f') s x :=
  HasGradientAtFilter.comp hg hf <| hf.continuousWithinAt.tendsto_nhdsWithin hst

theorem HasGradientAt.comp_hasGradientWithinAt
    (hg : HasGradientAt g g' (f x)) (hf : HasGradientWithinAt f f' s x) :
    HasGradientWithinAt (g ∘ f) (g' • f') s x :=
  hg.comp hf hf.continuousWithinAt

theorem HasGradientWithinAt.comp_of_mem
    (hg : HasGradientWithinAt g g' t (f x)) (hf : HasGradientWithinAt f f' s x)
    (hst : Tendsto f (𝓝[s] x) (𝓝[t] f x)) : HasGradientWithinAt (g ∘ f) (g' • f') s x :=
  HasGradientAtFilter.comp hg hf hst

/-- The chain rule. -/
theorem HasGradientAt.comp (hg : HasGradientAt g g' (f x))
    (hf : HasGradientAt f f' x) : HasGradientAt (g ∘ f) (g' • f') x :=
  HasGradientAtFilter.comp hg hf hf.continuousAt

theorem gradient.comp (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) :
    ∇ (g ∘ f) x = (∇ g (f x)) • (∇ f x) :=
  (hg.hasGradientAt.comp hf.hasGradientAt).gradient

end Composition

section ConstSmul

/-! ### Gradient of a scalar multiple -/

open Set Filter

theorem HasGradientAtFilter.const_smul (h : HasGradientAtFilter f f' x L) (c : 𝕜) :
    HasGradientAtFilter (fun x ↦ c • f x) ((starRingEnd 𝕜) c • f') x L := by
  rw [HasGradientAtFilter, map_smulₛₗ, RingHomCompTriple.comp_apply, RingHom.id_apply]
  exact HasFDerivAtFilter.const_smul h c

theorem HasGradientWithinAt.const_smul (h : HasGradientWithinAt f f' s x) (c : 𝕜) :
    HasGradientWithinAt (fun x ↦ c • f x) ((starRingEnd 𝕜) c • f') s x :=
  HasGradientAtFilter.const_smul h c

theorem HasGradientAt.const_smul (h : HasGradientAt f f' x) (c : 𝕜) :
    HasGradientAt (fun x ↦ c • f x) ((starRingEnd 𝕜) c • f') x :=
  HasGradientAtFilter.const_smul h c

theorem gradient_const_smul (h : DifferentiableAt 𝕜 f x) (c : 𝕜) :
    ∇ (fun y ↦ c • f y) x = (starRingEnd 𝕜) c • ∇ f x :=
  (h.hasGradientAt.const_smul c).gradient

variable [InnerProductSpace ℝ F] {f : F → ℝ} (c : ℝ)

theorem HasGradientAtFilter.const_smul' (h : HasGradientAtFilter f f' x L) :
    HasGradientAtFilter (fun x ↦ c • f x) (c • f') x L := h.const_smul c

theorem HasGradientWithinAt.const_smul' (h : HasGradientWithinAt f f' s x) :
    HasGradientWithinAt (fun x ↦ c • f x) (c • f') s x :=
  HasGradientWithinAt.const_smul h c

theorem HasGradientAt.const_smul' (h : HasGradientAt f f' x) :
    HasGradientAt (fun x ↦ c • f x) (c • f') x :=
  HasGradientAt.const_smul h c

end ConstSmul

section Add

/-! ### Gradient of a sum -/

variable {f' : F} {g : F → 𝕜} {x : F} {g' : F}
variable {L : Filter F} {f : F → 𝕜} {L' : Filter 𝕜} {t : Set 𝕜}

theorem HasGradientAtFilter.add (hf : HasGradientAtFilter f f' x L)
    (hg : HasGradientAtFilter g g' x L) :
    HasGradientAtFilter (fun y ↦ f y + g y) (f' + g') x L := by
  rw [HasGradientAtFilter, map_add]
  exact HasFDerivAtFilter.add hf hg

theorem HasGradientWithinAt.add (hf : HasGradientWithinAt f f' s x)
    (hg : HasGradientWithinAt g g' s x) :
    HasGradientWithinAt (fun y ↦ f y + g y) (f' + g') s x :=
  HasGradientAtFilter.add hf hg

theorem HasGradientAt.add (hf : HasGradientAt f f' x) (hg : HasGradientAt g g' x) :
    HasGradientAt (fun x ↦ f x + g x) (f' + g') x :=
  HasGradientAtFilter.add hf hg

theorem gradient_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    ∇ (fun y ↦ f y + g y) x = ∇ f x + ∇ g x :=
  (hf.hasGradientAt.add hg.hasGradientAt).gradient

theorem HasGradientAtFilter.add_const (hf : HasGradientAtFilter f f' x L) (c : 𝕜) :
    HasGradientAtFilter (fun y ↦ f y + c) f' x L :=
  add_zero f' ▸ hf.add (hasGradientAtFilter_const _ _ _)

theorem HasGradientWithinAt.add_const (hf : HasGradientWithinAt f f' s x) (c : 𝕜) :
    HasGradientWithinAt (fun y ↦ f y + c) f' s x :=
  HasGradientAtFilter.add_const hf c

theorem HasGradientAt.add_const (hf : HasGradientAt f f' x) (c : 𝕜) :
    HasGradientAt (fun x ↦ f x + c) f' x :=
  HasGradientAtFilter.add_const hf c

@[simp] theorem gradient_add_const (c : 𝕜) : ∇ (fun y ↦ f y + c) x = ∇ f x := by
  unfold gradient
  simp only [EmbeddingLike.apply_eq_iff_eq]
  exact fderiv_add_const c

theorem HasGradientAtFilter.const_add (hf : HasGradientAtFilter f f' x L) (c : 𝕜) :
    HasGradientAtFilter (fun y ↦ c + f y) f' x L :=
  zero_add f' ▸ (hasGradientAtFilter_const _ _ _).add hf

theorem HasGradientWithinAt.const_add (hf : HasGradientWithinAt f f' s x) (c : 𝕜) :
    HasGradientWithinAt (fun y ↦ c + f y) f' s x :=
  HasGradientAtFilter.const_add hf c

theorem HasGradientAt.const_add (hf : HasGradientAt f f' x) (c : 𝕜) :
    HasGradientAt (fun x ↦ c + f x) f' x :=
  HasGradientAtFilter.const_add hf c

@[simp] theorem gradient_const_add (c : 𝕜) : ∇ (fun y ↦ c + f y) x = ∇ f x := by
  simp only [add_comm c, gradient_add_const]

end Add

section Sum

/-! ### Gradient of a finite sum of functions -/


open BigOperators Asymptotics

variable {ι : Type*} {u : Finset ι} {A : ι → F → 𝕜} {A' : ι → F}

theorem HasGradientAtFilter.sum (h : ∀ i ∈ u, HasGradientAtFilter (A i) (A' i) x L) :
    HasGradientAtFilter (fun y ↦ ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x L := by
  rw [HasGradientAtFilter, map_sum, ← Finset.sum_fn u A]
  exact HasFDerivAtFilter.sum h

theorem HasGradientWithinAt.sum (h : ∀ i ∈ u, HasGradientWithinAt (A i) (A' i) s x) :
    HasGradientWithinAt (fun y ↦ ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) s x :=
  HasGradientAtFilter.sum h

theorem HasGradientAt.sum (h : ∀ i ∈ u, HasGradientAt (A i) (A' i) x) :
    HasGradientAt (fun y ↦ ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x :=
  HasGradientAtFilter.sum h

theorem gradient_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    ∇ (fun y ↦ ∑ i ∈ u, A i y) x = ∑ i ∈ u, ∇ (A i) x :=
  (HasGradientAt.sum fun i hi ↦ (h i hi).hasGradientAt).gradient

end Sum

section Neg

/-! ### Gradient of the negative of a function -/

theorem HasGradientAtFilter.neg (h : HasGradientAtFilter f f' x L) :
    HasGradientAtFilter (fun x ↦ -f x) (-f') x L := by
  rw [HasGradientAtFilter, map_neg]
  exact HasFDerivAtFilter.neg h

theorem HasGradientWithinAt.neg (h : HasGradientWithinAt f f' s x) :
    HasGradientWithinAt (fun x ↦ -f x) (-f') s x :=
  HasGradientAtFilter.neg h

theorem HasGradientAt.neg (h : HasGradientAt f f' x) :
    HasGradientAt (fun x ↦ -f x) (-f') x :=
  HasGradientAtFilter.neg h

@[simp] theorem gradient_neg : ∇ (fun y ↦ - f y) x = - ∇ f x := by
  unfold gradient
  rw [← Pi.neg_def f, fderiv_neg, map_neg]

end Neg

section Sub

/-! ### Gradient of the difference of two functions -/

variable {f' : F} {g : F → 𝕜} {x : F} {g' : F}
variable {L : Filter F} {f : F → 𝕜} {L' : Filter 𝕜} {t : Set 𝕜}

theorem HasGradientAtFilter.sub (hf : HasGradientAtFilter f f' x L)
    (hg : HasGradientAtFilter g g' x L) :
    HasGradientAtFilter (fun x ↦ f x - g x) (f' - g') x L := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasGradientWithinAt.sub (hf : HasGradientWithinAt f f' s x)
    (hg : HasGradientWithinAt g g' s x) :
    HasGradientWithinAt (fun x ↦ f x - g x) (f' - g') s x :=
  HasGradientAtFilter.sub hf hg

theorem HasGradientAt.sub (hf : HasGradientAt f f' x) (hg : HasGradientAt g g' x) :
    HasGradientAt (fun x ↦ f x - g x) (f' - g') x :=
  HasGradientAtFilter.sub hf hg

theorem gradient_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    ∇ (fun y ↦ f y - g y) x = ∇ f x - ∇ g x :=
  (hf.hasGradientAt.sub hg.hasGradientAt).gradient

theorem HasGradientAtFilter.sub_const (hf : HasGradientAtFilter f f' x L) (c : 𝕜) :
    HasGradientAtFilter (fun x ↦ f x - c) f' x L := by
  simpa only [sub_eq_add_neg] using hf.add_const (-c)

theorem HasGradientWithinAt.sub_const (hf : HasGradientWithinAt f f' s x) (c : 𝕜) :
    HasGradientWithinAt (fun x ↦ f x - c) f' s x :=
  HasGradientAtFilter.sub_const hf c

theorem HasGradientAt.sub_const (hf : HasGradientAt f f' x) (c : 𝕜) :
    HasGradientAt (fun x ↦ f x - c) f' x :=
  HasGradientAtFilter.sub_const hf c

@[simp] theorem gradient_sub_const (c : 𝕜) : ∇ (fun y ↦ f y - c) x = ∇ f x := by
  simp only [sub_eq_add_neg, gradient_add_const]

theorem HasGradientAtFilter.const_sub (hf : HasGradientAtFilter f f' x L) (c : 𝕜) :
    HasGradientAtFilter (fun x ↦ c - f x) (-f') x L := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c

theorem HasGradientWithinAt.const_sub (hf : HasGradientWithinAt f f' s x) (c : 𝕜) :
    HasGradientWithinAt (fun x ↦ c - f x) (-f') s x :=
  HasGradientAtFilter.const_sub hf c

theorem HasGradientAt.const_sub (hf : HasGradientAt f f' x) (c : 𝕜) :
    HasGradientAt (fun x ↦ c - f x) (-f') x :=
  HasGradientAtFilter.const_sub hf c

@[simp] theorem gradient_const_sub (c : 𝕜) : ∇ (fun y ↦ c - f y) x = - ∇ f x := by
  calc
    ∇ (fun y ↦ c - f y) x = ∇ (fun y ↦ - f y + c) x := by
      congr with x
      rw [sub_eq_neg_add]
    _ = - ∇ f x := by rw [gradient_add_const c, gradient_neg]

end Sub

section Mul

/-! ### Gradient of a product -/

variable {a' b' c' d' : F} {a b c d : F → 𝕜} {x : F}

open ContinuousLinearMap

lemma smul_toDual_add_smul_toDual_eq_toDual :
    c x • (toDual 𝕜 F) d' + d x • (toDual 𝕜 F) c' =
      (toDual 𝕜 F) ((starRingEnd 𝕜) (c x) • d' + (starRingEnd 𝕜) (d x) • c') := by
  simp only [map_add, map_smulₛₗ, RingHomCompTriple.comp_apply, RingHom.id_apply]

theorem HasGradientAt.mul (hc : HasGradientAt c c' x) (hd : HasGradientAt d d' x) :
    HasGradientAt (fun y ↦ c y * d y)
    ((starRingEnd 𝕜) (c x) • d' + (starRingEnd 𝕜) (d x) • c') x := by
  rw [hasGradientAt_iff_hasFDerivAt, ← smul_toDual_add_smul_toDual_eq_toDual]
  rw [hasGradientAt_iff_hasFDerivAt] at hc hd
  exact hc.mul hd

theorem HasGradientWithinAt.mul (hc : HasGradientWithinAt c c' s x)
    (hd : HasGradientWithinAt d d' s x) :
    HasGradientWithinAt (fun y ↦ c y * d y) ((starRingEnd 𝕜) (c x) • d'
      + (starRingEnd 𝕜) (d x) • c') s x := by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt, ← smul_toDual_add_smul_toDual_eq_toDual]
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt] at hc hd
  exact hc.mul hd

theorem gradient_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    ∇ (fun y ↦ c y * d y) x = (starRingEnd 𝕜) (c x) • ∇ d x
      + (starRingEnd 𝕜) (d x) • ∇ c x :=
  (hc.hasGradientAt.mul hd.hasGradientAt).gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {a' b' c' d' : E} {a b c d : E → ℝ} {x : E} {s : Set E}

theorem HasGradientAt.mul' (hc : HasGradientAt c c' x) (hd : HasGradientAt d d' x) :
    HasGradientAt (fun y ↦ c y * d y) ((c x) • d' + (d x) • c') x :=
  HasGradientAt.mul hc hd

theorem HasGradientWithinAt.mul' (hc : HasGradientWithinAt c c' s x)
    (hd : HasGradientWithinAt d d' s x) :
    HasGradientWithinAt (fun y ↦ c y * d y) ((c x) • d' + (d x) • c') s x :=
  hc.mul hd

theorem gradient_mul' (hc : DifferentiableAt ℝ c x) (hd : DifferentiableAt ℝ d x) :
    ∇ (fun y ↦ c y * d y) x = (c x) • ∇ d x + (d x) • ∇ c x :=
  gradient_mul hc hd

end Mul

section Mul_const

/-! ### Gradient of a product with a constant -/

variable {c' a' : F} {c a : F → 𝕜} {x : F} (d b : 𝕜)

theorem HasGradientWithinAt.mul_const (hc : HasGradientWithinAt c c' s x) :
    HasGradientWithinAt (fun y ↦ c y * d) ((starRingEnd 𝕜) d • c') s x := by
  simpa using hc.mul (hasGradientWithinAt_const x s d)

theorem HasGradientAt.mul_const (hc : HasGradientAt c c' x) :
    HasGradientAt (fun y ↦ c y * d) ((starRingEnd 𝕜) d • c') x := by
  simpa using hc.mul (hasGradientAt_const x d)

theorem gradient_mul_const (hc : DifferentiableAt 𝕜 c x) :
    ∇ (fun y ↦ c y * d) x = (starRingEnd 𝕜) d • ∇ c x :=
  (hc.hasGradientAt.mul_const d).gradient

theorem HasGradientWithinAt.const_mul (ha : HasGradientWithinAt a a' s x) :
    HasGradientWithinAt (fun y ↦ b * a y) ((starRingEnd 𝕜) b • a') s x := by
  simpa using (hasGradientWithinAt_const x s b).mul ha

theorem HasGradientAt.const_mul (ha : HasGradientAt a a' x) :
    HasGradientAt (fun y ↦ b * a y) ((starRingEnd 𝕜) b • a') x := by
  simpa using (hasGradientAt_const x b).mul ha

theorem gradient_const_mul (ha : DifferentiableAt 𝕜 a x) :
    ∇ (fun y ↦ b * a y) x = (starRingEnd 𝕜) b • ∇ a x :=
  (ha.hasGradientAt.const_mul b).gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {c' a' : E} {c a : E → ℝ} {x : E} {s : Set E} (d b : ℝ)

theorem HasGradientWithinAt.mul_const' (hc : HasGradientWithinAt c c' s x) :
    HasGradientWithinAt (fun y ↦ c y * d) (d • c') s x :=
  HasGradientWithinAt.mul_const d hc

theorem HasGradientAt.mul_const' (hc : HasGradientAt c c' x) :
    HasGradientAt (fun y ↦ c y * d) (d • c') x :=
  HasGradientAt.mul_const d hc

theorem gradient_mul_const' (hc : DifferentiableAt ℝ c x) :
    ∇ (fun y ↦ c y * d) x = d • ∇ c x :=
  gradient_mul_const d hc

theorem HasGradientWithinAt.const_mul' (ha : HasGradientWithinAt a a' s x) :
    HasGradientWithinAt (fun y ↦ b * a y) (b • a') s x :=
  HasGradientWithinAt.const_mul b ha

theorem HasGradientAt.const_mul' (ha : HasGradientAt a a' x) :
    HasGradientAt (fun y ↦ b * a y) (b • a') x :=
  HasGradientAt.const_mul b ha

theorem gradient_const_mul' (ha : DifferentiableAt ℝ a x) :
    ∇ (fun y ↦ b * a y) x = b • ∇ a x :=
  gradient_const_mul b ha

end Mul_const
