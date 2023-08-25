/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

#align_import analysis.calculus.deriv.basic from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!

# Line derivatives
-/

universe u v w

noncomputable section

open scoped Topology BigOperators Filter ENNReal

open Filter Asymptotics Set

open ContinuousLinearMap (smulRight smulRight_one_eq_iff)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Module

variable (𝕜)
variable {E : Type w} [AddCommGroup E] [Module 𝕜 E]

/-- `f` has the derivative `f'` at the point `x` along the direction `v` in the set `s`.
That is, `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0` and `x + t v ∈ s`.
Note that this definition is less well behaved that the total Fréchet derivative, which
should generally be favored over this one. -/
def HasLineDerivWithinAt (f : E → F) (f' : F) (s : Set E) (x : E) (v : E) :=
  HasDerivWithinAt (fun t ↦ f (x + t • v)) f' ((fun t ↦ x + t • v) ⁻¹' s) (0 : 𝕜)

/-- `f` has the derivative `f'` at the point `x` along the direction `v`.
That is, `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0`.
Note that this definition is less well behaved that the total Fréchet derivative, which
should generally be favored over this one. -/
def HasLineDerivAt (f : E → F) (f' : F) (x : E) (v : E) :=
  HasDerivAt (fun t ↦ f (x + t • v)) f' (0 : 𝕜)

/-- `f` is line-differentiable at the point `x` in the direction `v` in the set `s` if there
exists `f'` such that `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0` and `x + t v ∈ s`.
-/
def LineDifferentiableWithinAt (f : E → F) (s : Set E) (x : E) (v : E) : Prop :=
  DifferentiableWithinAt 𝕜 (fun t ↦ f (x + t • v)) ((fun t ↦ x + t • v) ⁻¹' s) (0 : 𝕜)

/-- `f` is line-differentiable at the point `x` in the direction `v` if there
exists `f'` such that `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0`. -/
def LineDifferentiableAt (f : E → F) (x : E) (v : E) : Prop :=
  DifferentiableAt 𝕜 (fun t ↦ f (x + t • v)) (0 : 𝕜)

/-- Line derivative of `f` at the point `x` in the direction `v` within the set `s`, if it exists.
Zero otherwise.

If the line derivative exists (i.e., `∃ f', HasLineDerivWithinAt 𝕜 f f' s x v`), then
`f (x + t v) = f x + t lineDerivWithin 𝕜 f s x v + o (t)` when `t` tends to `0` and `x + t v ∈ s`.
-/
def lineDerivWithin (f : E → F) (s : Set E) (x : E) (v : E) : F :=
  derivWithin (fun t ↦ f (x + t • v)) ((fun t ↦ x + t • v) ⁻¹' s) (0 : 𝕜)

/-- Line derivative of `f` at the point `x` in the direction `v`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', HasLineDerivAt 𝕜 f f' x v`), then
`f (x + t v) = f x + t lineDerivWithin 𝕜 f x v + o (t)` when `t` tends to `0` and `x + t v ∈ s`.
-/
def lineDeriv (f : E → F) (x : E) (v : E) : F :=
  deriv (fun t ↦ f (x + t • v)) (0 : 𝕜)

variable {𝕜}
variable {f f₁ : E → F} {f' f₀' f₁' : F} {s t : Set E} {x v : E}

lemma HasLineDerivWithinAt.mono (hf : HasLineDerivWithinAt 𝕜 f f' s x v) (hst : t ⊆ s) :
    HasLineDerivWithinAt 𝕜 f f' t x v :=
  HasDerivWithinAt.mono hf (preimage_mono hst)

lemma HasLineDerivAt.hasLineDerivWithinAt (hf : HasLineDerivAt 𝕜 f f' x v) (s : Set E) :
    HasLineDerivWithinAt 𝕜 f f' s x v :=
  HasDerivAt.hasDerivWithinAt hf

lemma HasLineDerivWithinAt.lineDifferentiableWithinAt (hf : HasLineDerivWithinAt 𝕜 f f' s x v) :
    LineDifferentiableWithinAt 𝕜 f s x v :=
  HasDerivWithinAt.differentiableWithinAt hf

theorem HasLineDerivAt.lineDifferentiableAt (hf : HasLineDerivAt 𝕜 f f' x v) :
    LineDifferentiableAt 𝕜 f x v :=
  HasDerivAt.differentiableAt hf

theorem LineDifferentiableWithinAt.hasLineDerivWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x v) :
    HasLineDerivWithinAt 𝕜 f (lineDerivWithin 𝕜 f s x v) s x v :=
  DifferentiableWithinAt.hasDerivWithinAt h

theorem LineDifferentiableAt.hasLineDerivAt (h : LineDifferentiableAt 𝕜 f x v) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v :=
  DifferentiableAt.hasDerivAt h

@[simp] lemma hasLineDerivWithinAt_univ :
    HasLineDerivWithinAt 𝕜 f f' univ x v ↔ HasLineDerivAt 𝕜 f f' x v := by
  simp only [HasLineDerivWithinAt, HasLineDerivAt, preimage_univ, hasDerivWithinAt_univ]

theorem lineDerivWithin_zero_of_not_lineDifferentiableWithinAt
    (h : ¬LineDifferentiableWithinAt 𝕜 f s x v) :
    lineDerivWithin 𝕜 f s x v = 0 :=
  derivWithin_zero_of_not_differentiableWithinAt h

theorem lineDeriv_zero_of_not_lineDifferentiableAt (h : ¬LineDifferentiableAt 𝕜 f x v) :
    lineDeriv 𝕜 f x v = 0 :=
  deriv_zero_of_not_differentiableAt h

theorem hasLineDerivAt_iff_isLittleO_nhds_zero :
    HasLineDerivAt 𝕜 f f' x v ↔
      (fun t : 𝕜 => f (x + t • v) - f x - t • f') =o[𝓝 0] fun t => t := by
  simp only [HasLineDerivAt, hasDerivAt_iff_isLittleO_nhds_zero, zero_add, zero_smul, add_zero]

theorem HasLineDerivAt.unique (h₀ : HasLineDerivAt 𝕜 f f₀' x v) (h₁ : HasLineDerivAt 𝕜 f f₁' x v) :
    f₀' = f₁' :=
  HasDerivAt.unique h₀ h₁




end Module

theorem ContinuousWithinAt.preimage_mem_nhdsWithin''
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β} {x : α} {y : β}
    {s t : Set β} (h : ContinuousWithinAt f (f ⁻¹' s) x) (ht : t ∈ 𝓝[s] y) (hxy : y = f x) :
    f ⁻¹' t ∈ 𝓝[f ⁻¹' s] x := by
  rw [hxy] at ht
  exact h.preimage_mem_nhdsWithin' (nhdsWithin_mono _ (image_preimage_subset f s) ht)

section NormedSpace

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f f₁ : E → F} {f' : F} {s t : Set E} {x v : E} {L : E →L[𝕜] F}

theorem HasLineDerivWithinAt.mono_of_mem
    (h : HasLineDerivWithinAt 𝕜 f f' t x v) (hst : t ∈ 𝓝[s] x) :
    HasLineDerivWithinAt 𝕜 f f' s x v := by
  apply HasDerivWithinAt.mono_of_mem h
  apply ContinuousWithinAt.preimage_mem_nhdsWithin'' _ hst (by simp)
  apply Continuous.continuousWithinAt; continuity

theorem HasLineDerivWithinAt.hasLineDerivAt
    (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : s ∈ 𝓝 x) :
    HasLineDerivAt 𝕜 f f' x v := by
  rw [← hasLineDerivWithinAt_univ]
  rw [← nhdsWithin_univ] at hs
  exact h.mono_of_mem hs

theorem LineDifferentiableWithinAt.lineDifferentiableAt (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (hs : s ∈ 𝓝 x) : LineDifferentiableAt 𝕜 f x v :=
  (h.hasLineDerivWithinAt.hasLineDerivAt hs).lineDifferentiableAt

lemma HasLineDerivWithinAt.congr_of_eventuallyEq (hf : HasLineDerivWithinAt 𝕜 f f' s x v)
    (h'f : f =ᶠ[𝓝[s] x] f₁) (hx : f x = f₁ x) : HasLineDerivWithinAt 𝕜 f₁ f' s x v := by
  apply HasDerivWithinAt.congr_of_eventuallyEq hf _ (by simp [hx])
  have A : Continuous (fun (t : 𝕜) ↦ x + t • v) := by continuity
  filter_upwards [A.continuousWithinAt.preimage_mem_nhdsWithin'' h'f (by simp)]
    with t ht using Eq.symm ht

lemma HasLineDerivWithinAt.congr (hf : HasLineDerivWithinAt 𝕜 f f' s x v)
    (h'f : ∀ y ∈ s, f y = f₁ y) (hx : f x = f₁ x) : HasLineDerivWithinAt 𝕜 f₁ f' s x v :=
  hf.congr_of_eventuallyEq (eventuallyEq_nhdsWithin_of_eqOn h'f) hx

lemma HasFDerivWithinAt.hasLineDerivWithinAt (hf : HasFDerivWithinAt f L s x) :
    HasLineDerivWithinAt 𝕜 f (L v) s x v := by
  let F := fun (t : 𝕜) ↦ x + t • v
  rw [show x = F (0 : 𝕜) by simp] at hf
  have A : HasDerivWithinAt F (0 + (1 : 𝕜) • v) (F ⁻¹' s) 0 :=
    ((hasDerivAt_const (0 : 𝕜) x).add ((hasDerivAt_id' (0 : 𝕜)).smul_const v)).hasDerivWithinAt
  simp only [one_smul, zero_add] at A
  exact hf.comp_hasDerivWithinAt (x := (0 : 𝕜)) A (mapsTo_preimage F s)

lemma HasFDerivAt.hasLineDerivAt (hf : HasFDerivAt f L x) :
    HasLineDerivAt 𝕜 f (L v) x v := by
  rw [← hasLineDerivWithinAt_univ]
  exact hf.hasFDerivWithinAt.hasLineDerivWithinAt

end NormedSpace


section NormedSpaceAgain

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f f₁ : E → F} {f' : F} {s t : Set E} {x v : E} {L : E →L[𝕜] F}





protected theorem HasLineDerivAt.lineDeriv (h : HasLineDerivAt 𝕜 f f' x v) :
    lineDeriv 𝕜 f x v = f' := by
  rw [h.unique h.lineDifferentiableAt.hasLineDerivAt]


theorem LineDifferentiableWithinAt.mono (h : LineDifferentiableWithinAt 𝕜 f t x v) (st : s ⊆ t) :
    LineDifferentiableWithinAt 𝕜 f s x v :=
  (h.hasLineDerivWithinAt.mono st).lineDifferentiableWithinAt

theorem LineDifferentiableWithinAt.mono_of_mem (h : LineDifferentiableWithinAt 𝕜 f s x v) {t : Set E}
    (hst : s ∈ 𝓝[t] x) : LineDifferentiableWithinAt 𝕜 f t x v :=
  (h.hasLineDerivWithinAt.mono_of_mem hst).lineDifferentiableWithinAt

theorem differentiableWithinAt_univ : LineDifferentiableWithinAt 𝕜 f univ x ↔ LineDifferentiableAt 𝕜 f x :=
  by simp only [DifferentiableWithinAt, hasLineDerivWithinAt_univ, LineDifferentiableAt]
#align differentiable_within_at_univ differentiableWithinAt_univ

theorem differentiableWithinAt_inter (ht : t ∈ 𝓝 x) :
    LineDifferentiableWithinAt 𝕜 f (s ∩ t) x ↔ LineDifferentiableWithinAt 𝕜 f s x := by
  simp only [DifferentiableWithinAt, hasLineDerivWithinAt_inter ht]
#align differentiable_within_at_inter differentiableWithinAt_inter

#exit

theorem differentiableWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    LineDifferentiableWithinAt 𝕜 f (s ∩ t) x ↔ LineDifferentiableWithinAt 𝕜 f s x := by
  simp only [DifferentiableWithinAt, hasLineDerivWithinAt_inter' ht]
#align differentiable_within_at_inter' differentiableWithinAt_inter'

theorem LineDifferentiableAt.differentiableWithinAt (h : LineDifferentiableAt 𝕜 f x) :
    LineDifferentiableWithinAt 𝕜 f s x :=
  (differentiableWithinAt_univ.2 h).mono (subset_univ _)
#align differentiable_at.differentiable_within_at LineDifferentiableAt.differentiableWithinAt

theorem LineDifferentiable.differentiableAt (h : LineDifferentiable 𝕜 f) : LineDifferentiableAt 𝕜 f x :=
  h x
#align differentiable.differentiable_at LineDifferentiable.differentiableAt

protected theorem LineDifferentiableAt.lineDerivWithin (h : LineDifferentiableAt 𝕜 f x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : lineDerivWithin 𝕜 f s x = lineDeriv 𝕜 f x :=
  h.hasLineDerivAt.hasLineDerivWithinAt.lineDerivWithin hxs
#align differentiable_at.lineDeriv_within LineDifferentiableAt.lineDerivWithin

theorem LineDifferentiableOn.mono (h : LineDifferentiableOn 𝕜 f t) (st : s ⊆ t) : LineDifferentiableOn 𝕜 f s :=
  fun x hx => (h x (st hx)).mono st
#align differentiable_on.mono LineDifferentiableOn.mono

theorem differentiableOn_univ : LineDifferentiableOn 𝕜 f univ ↔ LineDifferentiable 𝕜 f := by
  simp only [DifferentiableOn, LineDifferentiable, differentiableWithinAt_univ, mem_univ,
    forall_true_left]
#align differentiable_on_univ differentiableOn_univ

theorem LineDifferentiable.differentiableOn (h : LineDifferentiable 𝕜 f) : LineDifferentiableOn 𝕜 f s :=
  (differentiableOn_univ.2 h).mono (subset_univ _)
#align differentiable.differentiable_on LineDifferentiable.differentiableOn

theorem differentiableOn_of_locally_differentiableOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ LineDifferentiableOn 𝕜 f (s ∩ u)) :
    LineDifferentiableOn 𝕜 f s := by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (differentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)
#align differentiable_on_of_locally_differentiable_on differentiableOn_of_locally_differentiableOn

theorem lineDerivWithin_of_mem (st : t ∈ 𝓝[s] x) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : LineDifferentiableWithinAt 𝕜 f t x) : lineDerivWithin 𝕜 f s x = lineDerivWithin 𝕜 f t x :=
  ((DifferentiableWithinAt.hasLineDerivWithinAt h).mono_of_mem st).lineDerivWithin ht
#align lineDeriv_within_of_mem lineDerivWithin_of_mem

theorem lineDerivWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : LineDifferentiableWithinAt 𝕜 f t x) : lineDerivWithin 𝕜 f s x = lineDerivWithin 𝕜 f t x :=
  lineDerivWithin_of_mem (nhdsWithin_mono _ st self_mem_nhdsWithin) ht h
#align lineDeriv_within_subset lineDerivWithin_subset

theorem lineDerivWithin_inter (ht : t ∈ 𝓝 x) : lineDerivWithin 𝕜 f (s ∩ t) x = lineDerivWithin 𝕜 f s x := by
  simp only [lineDerivWithin, hasLineDerivWithinAt_inter ht]
#align lineDeriv_within_inter lineDerivWithin_inter

theorem lineDerivWithin_of_mem_nhds (h : s ∈ 𝓝 x) : lineDerivWithin 𝕜 f s x = lineDeriv 𝕜 f x := by
  simp only [lineDeriv, lineDerivWithin, HasLineDerivAt, HasLineDerivWithinAt, nhdsWithin_eq_nhds.2 h]
#align lineDeriv_within_of_mem_nhds lineDerivWithin_of_mem_nhds

@[simp]
theorem lineDerivWithin_univ : lineDerivWithin 𝕜 f univ = lineDeriv 𝕜 f :=
  funext fun _ => lineDerivWithin_of_mem_nhds univ_mem
#align lineDeriv_within_univ lineDerivWithin_univ

theorem lineDerivWithin_of_open (hs : IsOpen s) (hx : x ∈ s) : lineDerivWithin 𝕜 f s x = lineDeriv 𝕜 f x :=
  lineDerivWithin_of_mem_nhds (hs.mem_nhds hx)
#align lineDeriv_within_of_open lineDerivWithin_of_open

theorem lineDerivWithin_eq_lineDeriv (hs : UniqueDiffWithinAt 𝕜 s x) (h : LineDifferentiableAt 𝕜 f x) :
    lineDerivWithin 𝕜 f s x = lineDeriv 𝕜 f x := by
  rw [← lineDerivWithin_univ]
  exact lineDerivWithin_subset (subset_univ _) hs h.differentiableWithinAt
#align lineDeriv_within_eq_lineDeriv lineDerivWithin_eq_lineDeriv

theorem lineDeriv_mem_iff {f : E → F} {s : Set (E →L[𝕜] F)} {x : E} :
    lineDeriv 𝕜 f x ∈ s ↔
      LineDifferentiableAt 𝕜 f x ∧ lineDeriv 𝕜 f x ∈ s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0 : E →L[𝕜] F) ∈ s :=
  by by_cases hx : LineDifferentiableAt 𝕜 f x <;> simp [lineDeriv_zero_of_not_differentiableAt, *]
#align lineDeriv_mem_iff lineDeriv_mem_iff

theorem lineDerivWithin_mem_iff {f : E → F} {t : Set E} {s : Set (E →L[𝕜] F)} {x : E} :
    lineDerivWithin 𝕜 f t x ∈ s ↔
      LineDifferentiableWithinAt 𝕜 f t x ∧ lineDerivWithin 𝕜 f t x ∈ s ∨
        ¬DifferentiableWithinAt 𝕜 f t x ∧ (0 : E →L[𝕜] F) ∈ s := by
  by_cases hx : LineDifferentiableWithinAt 𝕜 f t x <;>
    simp [lineDerivWithin_zero_of_not_differentiableWithinAt, *]
#align lineDeriv_within_mem_iff lineDerivWithin_mem_iff

theorem Asymptotics.IsBigO.hasLineDerivWithinAt {s : Set E} {x₀ : E} {n : ℕ}
    (h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) (hx₀ : x₀ ∈ s) (hn : 1 < n) :
    HasLineDerivWithinAt f (0 : E →L[𝕜] F) s x₀ := by
  simp_rw [HasLineDerivWithinAt, HasLineDerivAtFilter,
    h.eq_zero_of_norm_pow_within hx₀ <| zero_lt_one.trans hn, zero_apply, sub_zero,
    h.trans_isLittleO ((isLittleO_pow_sub_sub x₀ hn).mono nhdsWithin_le_nhds)]
set_option linter.uppercaseLean3 false in
#align asymptotics.is_O.has_lineDeriv_within_at Asymptotics.IsBigO.hasLineDerivWithinAt

theorem Asymptotics.IsBigO.hasLineDerivAt {x₀ : E} {n : ℕ} (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n)
    (hn : 1 < n) : HasLineDerivAt 𝕜 f (0 : E →L[𝕜] F) x₀ := by
  rw [← nhdsWithin_univ] at h
  exact (h.hasLineDerivWithinAt (mem_univ _) hn).hasLineDerivAt_of_univ
set_option linter.uppercaseLean3 false in
#align asymptotics.is_O.has_lineDeriv_at Asymptotics.IsBigO.hasLineDerivAt

nonrec theorem HasLineDerivWithinAt.isBigO {f : E → F} {s : Set E} {x₀ : E} {f' : E →L[𝕜] F}
    (h : HasLineDerivWithinAt f f' s x₀) : (fun x => f x - f x₀) =O[𝓝[s] x₀] fun x => x - x₀ := by
  simpa only [sub_add_cancel] using h.isBigO.add (isBigO_sub f' (𝓝[s] x₀) x₀)
set_option linter.uppercaseLean3 false in
#align has_lineDeriv_within_at.is_O HasLineDerivWithinAt.isBigO

nonrec theorem HasLineDerivAt.isBigO {f : E → F} {x₀ : E} {f' : E →L[𝕜] F} (h : HasLineDerivAt 𝕜 f f' x v₀) :
    (fun x => f x - f x₀) =O[𝓝 x₀] fun x => x - x₀ := by
  simpa only [sub_add_cancel] using h.isBigO.add (isBigO_sub f' (𝓝 x₀) x₀)
set_option linter.uppercaseLean3 false in
#align has_lineDeriv_at.is_O HasLineDerivAt.isBigO

end LineDerivProperties

section Continuous

/-! ### Deducing continuity from differentiability -/


theorem HasLineDerivAtFilter.tendsto_nhds (hL : L ≤ 𝓝 x) (h : HasLineDerivAtFilter f f' x L) :
    Tendsto f L (𝓝 (f x)) := by
  have : Tendsto (fun x' => f x' - f x) L (𝓝 0) := by
    refine' h.isBigO_sub.trans_tendsto (Tendsto.mono_left _ hL)
    rw [← sub_self x]
    exact tendsto_id.sub tendsto_const_nhds
  have := this.add (@tendsto_const_nhds _ _ _ (f x) _)
  rw [zero_add (f x)] at this
  exact this.congr (by simp only [sub_add_cancel, eq_self_iff_true, forall_const])
#align has_lineDeriv_at_filter.tendsto_nhds HasLineDerivAtFilter.tendsto_nhds

theorem HasLineDerivWithinAt.continuousWithinAt (h : HasLineDerivWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasLineDerivAtFilter.tendsto_nhds inf_le_left h
#align has_lineDeriv_within_at.continuous_within_at HasLineDerivWithinAt.continuousWithinAt

theorem HasLineDerivAt.continuousAt (h : HasLineDerivAt 𝕜 f f' x v) : ContinuousAt f x :=
  HasLineDerivAtFilter.tendsto_nhds le_rfl h
#align has_lineDeriv_at.continuous_at HasLineDerivAt.continuousAt

theorem LineDifferentiableWithinAt.continuousWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x) :
    ContinuousWithinAt f s x :=
  let ⟨_, hf'⟩ := h
  hf'.continuousWithinAt
#align differentiable_within_at.continuous_within_at LineDifferentiableWithinAt.continuousWithinAt

theorem LineDifferentiableAt.continuousAt (h : LineDifferentiableAt 𝕜 f x) : ContinuousAt f x :=
  let ⟨_, hf'⟩ := h
  hf'.continuousAt
#align differentiable_at.continuous_at LineDifferentiableAt.continuousAt

theorem LineDifferentiableOn.continuousOn (h : LineDifferentiableOn 𝕜 f s) : ContinuousOn f s := fun x hx =>
  (h x hx).continuousWithinAt
#align differentiable_on.continuous_on LineDifferentiableOn.continuousOn

theorem LineDifferentiable.continuous (h : LineDifferentiable 𝕜 f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (h x).continuousAt
#align differentiable.continuous LineDifferentiable.continuous

protected theorem HasStrictLineDerivAt.continuousAt (hf : HasStrictLineDerivAt f f' x) :
    ContinuousAt f x :=
  hf.hasLineDerivAt.continuousAt
#align has_strict_lineDeriv_at.continuous_at HasStrictLineDerivAt.continuousAt

theorem HasStrictLineDerivAt.isBigO_sub_rev {f' : E ≃L[𝕜] F}
    (hf : HasStrictLineDerivAt f (f' : E →L[𝕜] F) x) :
    (fun p : E × E => p.1 - p.2) =O[𝓝 (x, x)] fun p : E × E => f p.1 - f p.2 :=
  ((f'.isBigO_comp_rev _ _).trans (hf.trans_isBigO (f'.isBigO_comp_rev _ _)).right_isBigO_add).congr
    (fun _ => rfl) fun _ => sub_add_cancel _ _
set_option linter.uppercaseLean3 false in
#align has_strict_lineDeriv_at.is_O_sub_rev HasStrictLineDerivAt.isBigO_sub_rev

theorem HasLineDerivAtFilter.isBigO_sub_rev (hf : HasLineDerivAtFilter f f' x L) {C}
    (hf' : AntilipschitzWith C f') : (fun x' => x' - x) =O[L] fun x' => f x' - f x :=
  have : (fun x' => x' - x) =O[L] fun x' => f' (x' - x) :=
    isBigO_iff.2 ⟨C, eventually_of_forall fun _ => ZeroHomClass.bound_of_antilipschitz f' hf' _⟩
  (this.trans (hf.trans_isBigO this).right_isBigO_add).congr (fun _ => rfl) fun _ =>
    sub_add_cancel _ _
set_option linter.uppercaseLean3 false in
#align has_lineDeriv_at_filter.is_O_sub_rev HasLineDerivAtFilter.isBigO_sub_rev

end Continuous

section congr

/-! ### congr properties of the derivative -/
theorem hasLineDerivWithinAt_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasLineDerivWithinAt f f' s x ↔ HasLineDerivWithinAt f f' t x :=
  calc
    HasLineDerivWithinAt f f' s x ↔ HasLineDerivWithinAt f f' (s \ {y}) x :=
      (hasLineDerivWithinAt_diff_singleton _).symm
    _ ↔ HasLineDerivWithinAt f f' (t \ {y}) x := by
      suffices 𝓝[s \ {y}] x = 𝓝[t \ {y}] x by simp only [HasLineDerivWithinAt, this]
      simpa only [set_eventuallyEq_iff_inf_principal, ← nhdsWithin_inter', diff_eq,
        inter_comm] using h
    _ ↔ HasLineDerivWithinAt f f' t x := hasLineDerivWithinAt_diff_singleton _
#align has_lineDeriv_within_at_congr_set' hasLineDerivWithinAt_congr_set'

theorem hasLineDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    HasLineDerivWithinAt f f' s x ↔ HasLineDerivWithinAt f f' t x :=
  hasLineDerivWithinAt_congr_set' x <| h.filter_mono inf_le_left
#align has_lineDeriv_within_at_congr_set hasLineDerivWithinAt_congr_set

theorem differentiableWithinAt_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    LineDifferentiableWithinAt 𝕜 f s x ↔ LineDifferentiableWithinAt 𝕜 f t x :=
  exists_congr fun _ => hasLineDerivWithinAt_congr_set' _ h
#align differentiable_within_at_congr_set' differentiableWithinAt_congr_set'

theorem differentiableWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    LineDifferentiableWithinAt 𝕜 f s x ↔ LineDifferentiableWithinAt 𝕜 f t x :=
  exists_congr fun _ => hasLineDerivWithinAt_congr_set h
#align differentiable_within_at_congr_set differentiableWithinAt_congr_set

theorem lineDerivWithin_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    lineDerivWithin 𝕜 f s x = lineDerivWithin 𝕜 f t x := by
  simp only [lineDerivWithin, hasLineDerivWithinAt_congr_set' y h]
#align lineDeriv_within_congr_set' lineDerivWithin_congr_set'

theorem lineDerivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : lineDerivWithin 𝕜 f s x = lineDerivWithin 𝕜 f t x :=
  lineDerivWithin_congr_set' x <| h.filter_mono inf_le_left
#align lineDeriv_within_congr_set lineDerivWithin_congr_set

theorem lineDerivWithin_eventually_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    lineDerivWithin 𝕜 f s =ᶠ[𝓝 x] lineDerivWithin 𝕜 f t :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => lineDerivWithin_congr_set' y
#align lineDeriv_within_eventually_congr_set' lineDerivWithin_eventually_congr_set'

theorem lineDerivWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    lineDerivWithin 𝕜 f s =ᶠ[𝓝 x] lineDerivWithin 𝕜 f t :=
  lineDerivWithin_eventually_congr_set' x <| h.filter_mono inf_le_left
#align lineDeriv_within_eventually_congr_set lineDerivWithin_eventually_congr_set

theorem Filter.EventuallyEq.hasStrictLineDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) (h' : ∀ y, f₀' y = f₁' y) :
    HasStrictLineDerivAt f₀ f₀' x ↔ HasStrictLineDerivAt f₁ f₁' x := by
  refine' isLittleO_congr ((h.prod_mk_nhds h).mono _) (eventually_of_forall fun _ => _root_.rfl)
  rintro p ⟨hp₁, hp₂⟩
  simp only [*]
#align filter.eventually_eq.has_strict_lineDeriv_at_iff Filter.EventuallyEq.hasStrictLineDerivAt_iff

theorem HasStrictLineDerivAt.congr_lineDeriv (h : HasStrictLineDerivAt f f' x) (h' : f' = g') :
    HasStrictLineDerivAt f g' x :=
  h' ▸ h

theorem HasLineDerivAt.congr_lineDeriv (h : HasLineDerivAt 𝕜 f f' x v) (h' : f' = g') : HasLineDerivAt 𝕜 f g' x :=
  h' ▸ h

theorem HasLineDerivWithinAt.congr_lineDeriv (h : HasLineDerivWithinAt f f' s x) (h' : f' = g') :
    HasLineDerivWithinAt f g' s x :=
  h' ▸ h

theorem HasStrictLineDerivAt.congr_of_eventuallyEq (h : HasStrictLineDerivAt f f' x)
    (h₁ : f =ᶠ[𝓝 x] f₁) : HasStrictLineDerivAt f₁ f' x :=
  (h₁.hasStrictLineDerivAt_iff fun _ => rfl).1 h
#align has_strict_lineDeriv_at.congr_of_eventually_eq HasStrictLineDerivAt.congr_of_eventuallyEq

theorem Filter.EventuallyEq.hasLineDerivAtFilter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
    (h₁ : ∀ x, f₀' x = f₁' x) : HasLineDerivAtFilter f₀ f₀' x L ↔ HasLineDerivAtFilter f₁ f₁' x L :=
  isLittleO_congr (h₀.mono fun y hy => by simp only [hy, h₁, hx])
    (eventually_of_forall fun _ => _root_.rfl)
#align filter.eventually_eq.has_lineDeriv_at_filter_iff Filter.EventuallyEq.hasLineDerivAtFilter_iff

theorem HasLineDerivAtFilter.congr_of_eventuallyEq (h : HasLineDerivAtFilter f f' x L) (hL : f₁ =ᶠ[L] f)
    (hx : f₁ x = f x) : HasLineDerivAtFilter f₁ f' x L :=
  (hL.hasLineDerivAtFilter_iff hx fun _ => rfl).2 h
#align has_lineDeriv_at_filter.congr_of_eventually_eq HasLineDerivAtFilter.congr_of_eventuallyEq

theorem Filter.EventuallyEq.hasLineDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    HasLineDerivAt 𝕜 f₀ f' x ↔ HasLineDerivAt 𝕜 f₁ f' x :=
  h.hasLineDerivAtFilter_iff h.eq_of_nhds fun _ => _root_.rfl
#align filter.eventually_eq.has_lineDeriv_at_iff Filter.EventuallyEq.hasLineDerivAt_iff

theorem Filter.EventuallyEq.differentiableAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    LineDifferentiableAt 𝕜 f₀ x ↔ LineDifferentiableAt 𝕜 f₁ x :=
  exists_congr fun _ => h.hasLineDerivAt_iff
#align filter.eventually_eq.differentiable_at_iff Filter.EventuallyEq.differentiableAt_iff

theorem Filter.EventuallyEq.hasLineDerivWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    HasLineDerivWithinAt f₀ f' s x ↔ HasLineDerivWithinAt f₁ f' s x :=
  h.hasLineDerivAtFilter_iff hx fun _ => _root_.rfl
#align filter.eventually_eq.has_lineDeriv_within_at_iff Filter.EventuallyEq.hasLineDerivWithinAt_iff

theorem Filter.EventuallyEq.hasLineDerivWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
    HasLineDerivWithinAt f₀ f' s x ↔ HasLineDerivWithinAt f₁ f' s x :=
  h.hasLineDerivWithinAt_iff (h.eq_of_nhdsWithin hx)
#align filter.eventually_eq.has_lineDeriv_within_at_iff_of_mem Filter.EventuallyEq.hasLineDerivWithinAt_iff_of_mem

theorem Filter.EventuallyEq.differentiableWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    LineDifferentiableWithinAt 𝕜 f₀ s x ↔ LineDifferentiableWithinAt 𝕜 f₁ s x :=
  exists_congr fun _ => h.hasLineDerivWithinAt_iff hx
#align filter.eventually_eq.differentiable_within_at_iff Filter.EventuallyEq.differentiableWithinAt_iff

theorem Filter.EventuallyEq.differentiableWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
    LineDifferentiableWithinAt 𝕜 f₀ s x ↔ LineDifferentiableWithinAt 𝕜 f₁ s x :=
  h.differentiableWithinAt_iff (h.eq_of_nhdsWithin hx)
#align filter.eventually_eq.differentiable_within_at_iff_of_mem Filter.EventuallyEq.differentiableWithinAt_iff_of_mem

theorem HasLineDerivWithinAt.congr_mono (h : HasLineDerivWithinAt f f' s x) (ht : EqOn f₁ f t)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasLineDerivWithinAt f₁ f' t x :=
  HasLineDerivAtFilter.congr_of_eventuallyEq (h.mono h₁) (Filter.mem_inf_of_right ht) hx
#align has_lineDeriv_within_at.congr_mono HasLineDerivWithinAt.congr_mono

theorem HasLineDerivWithinAt.congr (h : HasLineDerivWithinAt f f' s x) (hs : EqOn f₁ f s)
    (hx : f₁ x = f x) : HasLineDerivWithinAt f₁ f' s x :=
  h.congr_mono hs hx (Subset.refl _)
#align has_lineDeriv_within_at.congr HasLineDerivWithinAt.congr

theorem HasLineDerivWithinAt.congr' (h : HasLineDerivWithinAt f f' s x) (hs : EqOn f₁ f s) (hx : x ∈ s) :
    HasLineDerivWithinAt f₁ f' s x :=
  h.congr hs (hs hx)
#align has_lineDeriv_within_at.congr' HasLineDerivWithinAt.congr'

theorem HasLineDerivWithinAt.congr_of_eventuallyEq (h : HasLineDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasLineDerivWithinAt f₁ f' s x :=
  HasLineDerivAtFilter.congr_of_eventuallyEq h h₁ hx
#align has_lineDeriv_within_at.congr_of_eventually_eq HasLineDerivWithinAt.congr_of_eventuallyEq

theorem HasLineDerivAt.congr_of_eventuallyEq (h : HasLineDerivAt 𝕜 f f' x v) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasLineDerivAt 𝕜 f₁ f' x :=
  HasLineDerivAtFilter.congr_of_eventuallyEq h h₁ (mem_of_mem_nhds h₁ : _)
#align has_lineDeriv_at.congr_of_eventually_eq HasLineDerivAt.congr_of_eventuallyEq

theorem LineDifferentiableWithinAt.congr_mono (h : LineDifferentiableWithinAt 𝕜 f s x) (ht : EqOn f₁ f t)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : LineDifferentiableWithinAt 𝕜 f₁ t x :=
  (HasLineDerivWithinAt.congr_mono h.hasLineDerivWithinAt ht hx h₁).differentiableWithinAt
#align differentiable_within_at.congr_mono LineDifferentiableWithinAt.congr_mono

theorem LineDifferentiableWithinAt.congr (h : LineDifferentiableWithinAt 𝕜 f s x) (ht : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : LineDifferentiableWithinAt 𝕜 f₁ s x :=
  LineDifferentiableWithinAt.congr_mono h ht hx (Subset.refl _)
#align differentiable_within_at.congr LineDifferentiableWithinAt.congr

theorem LineDifferentiableWithinAt.congr_of_eventuallyEq (h : LineDifferentiableWithinAt 𝕜 f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : LineDifferentiableWithinAt 𝕜 f₁ s x :=
  (h.hasLineDerivWithinAt.congr_of_eventuallyEq h₁ hx).differentiableWithinAt
#align differentiable_within_at.congr_of_eventually_eq LineDifferentiableWithinAt.congr_of_eventuallyEq

theorem LineDifferentiableOn.congr_mono (h : LineDifferentiableOn 𝕜 f s) (h' : ∀ x ∈ t, f₁ x = f x)
    (h₁ : t ⊆ s) : LineDifferentiableOn 𝕜 f₁ t := fun x hx => (h x (h₁ hx)).congr_mono h' (h' x hx) h₁
#align differentiable_on.congr_mono LineDifferentiableOn.congr_mono

theorem LineDifferentiableOn.congr (h : LineDifferentiableOn 𝕜 f s) (h' : ∀ x ∈ s, f₁ x = f x) :
    LineDifferentiableOn 𝕜 f₁ s := fun x hx => (h x hx).congr h' (h' x hx)
#align differentiable_on.congr LineDifferentiableOn.congr

theorem differentiableOn_congr (h' : ∀ x ∈ s, f₁ x = f x) :
    LineDifferentiableOn 𝕜 f₁ s ↔ LineDifferentiableOn 𝕜 f s :=
  ⟨fun h => LineDifferentiableOn.congr h fun y hy => (h' y hy).symm, fun h =>
    LineDifferentiableOn.congr h h'⟩
#align differentiable_on_congr differentiableOn_congr

theorem LineDifferentiableAt.congr_of_eventuallyEq (h : LineDifferentiableAt 𝕜 f x) (hL : f₁ =ᶠ[𝓝 x] f) :
    LineDifferentiableAt 𝕜 f₁ x :=
  hL.differentiableAt_iff.2 h
#align differentiable_at.congr_of_eventually_eq LineDifferentiableAt.congr_of_eventuallyEq

theorem LineDifferentiableWithinAt.lineDerivWithin_congr_mono (h : LineDifferentiableWithinAt 𝕜 f s x)
    (hs : EqOn f₁ f t) (hx : f₁ x = f x) (hxt : UniqueDiffWithinAt 𝕜 t x) (h₁ : t ⊆ s) :
    lineDerivWithin 𝕜 f₁ t x = lineDerivWithin 𝕜 f s x :=
  (HasLineDerivWithinAt.congr_mono h.hasLineDerivWithinAt hs hx h₁).lineDerivWithin hxt
#align differentiable_within_at.lineDeriv_within_congr_mono LineDifferentiableWithinAt.lineDerivWithin_congr_mono

theorem Filter.EventuallyEq.lineDerivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    lineDerivWithin 𝕜 f₁ s x = lineDerivWithin 𝕜 f s x := by
  simp only [lineDerivWithin, hs.hasLineDerivWithinAt_iff hx]
#align filter.eventually_eq.lineDeriv_within_eq Filter.EventuallyEq.lineDerivWithin_eq

theorem Filter.EventuallyEq.lineDeriv_within' (hs : f₁ =ᶠ[𝓝[s] x] f) (ht : t ⊆ s) :
    lineDerivWithin 𝕜 f₁ t =ᶠ[𝓝[s] x] lineDerivWithin 𝕜 f t :=
  (eventually_nhdsWithin_nhdsWithin.2 hs).mp <|
    eventually_mem_nhdsWithin.mono fun _y hys hs =>
      EventuallyEq.lineDerivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)
#align filter.eventually_eq.lineDeriv_within' Filter.EventuallyEq.lineDeriv_within'

protected theorem Filter.EventuallyEq.lineDerivWithin (hs : f₁ =ᶠ[𝓝[s] x] f) :
    lineDerivWithin 𝕜 f₁ s =ᶠ[𝓝[s] x] lineDerivWithin 𝕜 f s :=
  hs.lineDeriv_within' Subset.rfl
#align filter.eventually_eq.lineDeriv_within Filter.EventuallyEq.lineDerivWithin

theorem Filter.EventuallyEq.lineDerivWithin_eq_nhds (h : f₁ =ᶠ[𝓝 x] f) :
    lineDerivWithin 𝕜 f₁ s x = lineDerivWithin 𝕜 f s x :=
  (h.filter_mono nhdsWithin_le_nhds).lineDerivWithin_eq h.self_of_nhds
#align filter.eventually_eq.lineDeriv_within_eq_nhds Filter.EventuallyEq.lineDerivWithin_eq_nhds

theorem lineDerivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) :
    lineDerivWithin 𝕜 f₁ s x = lineDerivWithin 𝕜 f s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).lineDerivWithin_eq hx
#align lineDeriv_within_congr lineDerivWithin_congr

theorem lineDerivWithin_congr' (hs : EqOn f₁ f s) (hx : x ∈ s) :
    lineDerivWithin 𝕜 f₁ s x = lineDerivWithin 𝕜 f s x :=
  lineDerivWithin_congr hs (hs hx)
#align lineDeriv_within_congr' lineDerivWithin_congr'

theorem Filter.EventuallyEq.lineDeriv_eq (h : f₁ =ᶠ[𝓝 x] f) : lineDeriv 𝕜 f₁ x = lineDeriv 𝕜 f x := by
  rw [← lineDerivWithin_univ, ← lineDerivWithin_univ, h.lineDerivWithin_eq_nhds]
#align filter.eventually_eq.lineDeriv_eq Filter.EventuallyEq.lineDeriv_eq

protected theorem Filter.EventuallyEq.lineDeriv (h : f₁ =ᶠ[𝓝 x] f) : lineDeriv 𝕜 f₁ =ᶠ[𝓝 x] lineDeriv 𝕜 f :=
  h.eventuallyEq_nhds.mono fun _ h => h.lineDeriv_eq
#align filter.eventually_eq.lineDeriv Filter.EventuallyEq.lineDeriv

end congr

section id

/-! ### Derivative of the identity -/


theorem hasStrictLineDerivAt_id (x : E) : HasStrictLineDerivAt id (id 𝕜 E) x :=
  (isLittleO_zero _ _).congr_left <| by simp
#align has_strict_lineDeriv_at_id hasStrictLineDerivAt_id

theorem hasLineDerivAtFilter_id (x : E) (L : Filter E) : HasLineDerivAtFilter id (id 𝕜 E) x L :=
  (isLittleO_zero _ _).congr_left <| by simp
#align has_lineDeriv_at_filter_id hasLineDerivAtFilter_id

theorem hasLineDerivWithinAt_id (x : E) (s : Set E) : HasLineDerivWithinAt id (id 𝕜 E) s x :=
  hasLineDerivAtFilter_id _ _
#align has_lineDeriv_within_at_id hasLineDerivWithinAt_id

theorem hasLineDerivAt_id (x : E) : HasLineDerivAt id (id 𝕜 E) x :=
  hasLineDerivAtFilter_id _ _
#align has_lineDeriv_at_id hasLineDerivAt_id

@[simp]
theorem differentiableAt_id : LineDifferentiableAt 𝕜 id x :=
  (hasLineDerivAt_id x).differentiableAt
#align differentiable_at_id differentiableAt_id

@[simp]
theorem differentiableAt_id' : LineDifferentiableAt 𝕜 (fun x => x) x :=
  (hasLineDerivAt_id x).differentiableAt
#align differentiable_at_id' differentiableAt_id'

theorem differentiableWithinAt_id : LineDifferentiableWithinAt 𝕜 id s x :=
  differentiableAt_id.differentiableWithinAt
#align differentiable_within_at_id differentiableWithinAt_id

@[simp]
theorem differentiable_id : LineDifferentiable 𝕜 (id : E → E) := fun _ => differentiableAt_id
#align differentiable_id differentiable_id

@[simp]
theorem differentiable_id' : LineDifferentiable 𝕜 fun x : E => x := fun _ => differentiableAt_id
#align differentiable_id' differentiable_id'

theorem differentiableOn_id : LineDifferentiableOn 𝕜 id s :=
  differentiable_id.differentiableOn
#align differentiable_on_id differentiableOn_id

@[simp]
theorem lineDeriv_id : lineDeriv 𝕜 id x = id 𝕜 E :=
  HasLineDerivAt.lineDeriv (hasLineDerivAt_id x)
#align lineDeriv_id lineDeriv_id

@[simp]
theorem lineDeriv_id' : lineDeriv 𝕜 (fun x : E => x) x = ContinuousLinearMap.id 𝕜 E :=
  lineDeriv_id
#align lineDeriv_id' lineDeriv_id'

theorem lineDerivWithin_id (hxs : UniqueDiffWithinAt 𝕜 s x) : lineDerivWithin 𝕜 id s x = id 𝕜 E := by
  rw [DifferentiableAt.lineDerivWithin differentiableAt_id hxs]
  exact lineDeriv_id
#align lineDeriv_within_id lineDerivWithin_id

theorem lineDerivWithin_id' (hxs : UniqueDiffWithinAt 𝕜 s x) :
    lineDerivWithin 𝕜 (fun x : E => x) s x = ContinuousLinearMap.id 𝕜 E :=
  lineDerivWithin_id hxs
#align lineDeriv_within_id' lineDerivWithin_id'

end id

section Const

/-! ### Derivative of a constant function -/


theorem hasStrictLineDerivAt_const (c : F) (x : E) :
    HasStrictLineDerivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
  (isLittleO_zero _ _).congr_left fun _ => by simp only [zero_apply, sub_self]
#align has_strict_lineDeriv_at_const hasStrictLineDerivAt_const

theorem hasLineDerivAtFilter_const (c : F) (x : E) (L : Filter E) :
    HasLineDerivAtFilter (fun _ => c) (0 : E →L[𝕜] F) x L :=
  (isLittleO_zero _ _).congr_left fun _ => by simp only [zero_apply, sub_self]
#align has_lineDeriv_at_filter_const hasLineDerivAtFilter_const

theorem hasLineDerivWithinAt_const (c : F) (x : E) (s : Set E) :
    HasLineDerivWithinAt (fun _ => c) (0 : E →L[𝕜] F) s x :=
  hasLineDerivAtFilter_const _ _ _
#align has_lineDeriv_within_at_const hasLineDerivWithinAt_const

theorem hasLineDerivAt_const (c : F) (x : E) : HasLineDerivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
  hasLineDerivAtFilter_const _ _ _
#align has_lineDeriv_at_const hasLineDerivAt_const

@[simp]
theorem differentiableAt_const (c : F) : LineDifferentiableAt 𝕜 (fun _ => c) x :=
  ⟨0, hasLineDerivAt_const c x⟩
#align differentiable_at_const differentiableAt_const

theorem differentiableWithinAt_const (c : F) : LineDifferentiableWithinAt 𝕜 (fun _ => c) s x :=
  LineDifferentiableAt.differentiableWithinAt (differentiableAt_const _)
#align differentiable_within_at_const differentiableWithinAt_const

theorem lineDeriv_const_apply (c : F) : lineDeriv 𝕜 (fun _ => c) x = 0 :=
  HasLineDerivAt.lineDeriv (hasLineDerivAt_const c x)
#align lineDeriv_const_apply lineDeriv_const_apply

@[simp]
theorem lineDeriv_const (c : F) : (lineDeriv 𝕜 fun _ : E => c) = 0 := by
  ext m
  rw [lineDeriv_const_apply]
  rfl
#align lineDeriv_const lineDeriv_const

theorem lineDerivWithin_const_apply (c : F) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    lineDerivWithin 𝕜 (fun _ => c) s x = 0 := by
  rw [DifferentiableAt.lineDerivWithin (differentiableAt_const _) hxs]
  exact lineDeriv_const_apply _
#align lineDeriv_within_const_apply lineDerivWithin_const_apply

@[simp]
theorem differentiable_const (c : F) : LineDifferentiable 𝕜 fun _ : E => c := fun _ =>
  differentiableAt_const _
#align differentiable_const differentiable_const

theorem differentiableOn_const (c : F) : LineDifferentiableOn 𝕜 (fun _ => c) s :=
  (differentiable_const _).differentiableOn
#align differentiable_on_const differentiableOn_const

theorem hasLineDerivWithinAt_singleton (f : E → F) (x : E) :
    HasLineDerivWithinAt f (0 : E →L[𝕜] F) {x} x := by
  simp only [HasLineDerivWithinAt, nhdsWithin_singleton, HasLineDerivAtFilter, isLittleO_pure,
    ContinuousLinearMap.zero_apply, sub_self]
#align has_lineDeriv_within_at_singleton hasLineDerivWithinAt_singleton

theorem hasLineDerivAt_of_subsingleton [h : Subsingleton E] (f : E → F) (x : E) :
    HasLineDerivAt 𝕜 f (0 : E →L[𝕜] F) x := by
  rw [← hasLineDerivWithinAt_univ, subsingleton_univ.eq_singleton_of_mem (mem_univ x)]
  exact hasLineDerivWithinAt_singleton f x
#align has_lineDeriv_at_of_subsingleton hasLineDerivAt_of_subsingleton

theorem differentiableOn_empty : LineDifferentiableOn 𝕜 f ∅ := fun _ => False.elim
#align differentiable_on_empty differentiableOn_empty

theorem differentiableOn_singleton : LineDifferentiableOn 𝕜 f {x} :=
  forall_eq.2 (hasLineDerivWithinAt_singleton f x).differentiableWithinAt
#align differentiable_on_singleton differentiableOn_singleton

theorem Set.Subsingleton.differentiableOn (hs : s.Subsingleton) : LineDifferentiableOn 𝕜 f s :=
  hs.induction_on differentiableOn_empty fun _ => differentiableOn_singleton
#align set.subsingleton.differentiable_on Set.Subsingleton.differentiableOn

theorem hasLineDerivAt_zero_of_eventually_const (c : F) (hf : f =ᶠ[𝓝 x] fun _ => c) :
    HasLineDerivAt 𝕜 f (0 : E →L[𝕜] F) x :=
  (hasLineDerivAt_const _ _).congr_of_eventuallyEq hf
#align has_lineDeriv_at_zero_of_eventually_const hasLineDerivAt_zero_of_eventually_const

end Const

end

/-! ### Support of derivatives -/

section Support

open Function

variable (𝕜 : Type*) {E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {x : E}

theorem HasStrictLineDerivAt.of_not_mem_tsupport (h : x ∉ tsupport f) :
    HasStrictLineDerivAt f (0 : E →L[𝕜] F) x := by
  rw [not_mem_tsupport_iff_eventuallyEq] at h
  exact (hasStrictLineDerivAt_const (0 : F) x).congr_of_eventuallyEq h.symm

theorem HasLineDerivAt.of_not_mem_tsupport (h : x ∉ tsupport f) :
    HasLineDerivAt 𝕜 f (0 : E →L[𝕜] F) x :=
  (HasStrictLineDerivAt.of_not_mem_tsupport 𝕜 h).hasLineDerivAt

theorem HasLineDerivWithinAt.of_not_mem_tsupport (h : x ∉ tsupport f) :
    HasLineDerivWithinAt f (0 : E →L[𝕜] F) s x :=
  (HasLineDerivAt.of_not_mem_tsupport 𝕜 h).hasLineDerivWithinAt

theorem lineDeriv_of_not_mem_tsupport (h : x ∉ tsupport f) : lineDeriv 𝕜 f x = 0 :=
  (HasLineDerivAt.of_not_mem_tsupport 𝕜 h).lineDeriv

theorem support_lineDeriv_subset : support (lineDeriv 𝕜 f) ⊆ tsupport f := fun x ↦ by
  rw [← not_imp_not, nmem_support]
  exact lineDeriv_of_not_mem_tsupport _
#align support_lineDeriv_subset support_lineDeriv_subset

theorem tsupport_lineDeriv_subset : tsupport (lineDeriv 𝕜 f) ⊆ tsupport f :=
  closure_minimal (support_lineDeriv_subset 𝕜) isClosed_closure
#align tsupport_lineDeriv_subset tsupport_lineDeriv_subset

protected theorem HasCompactSupport.lineDeriv (hf : HasCompactSupport f) :
    HasCompactSupport (lineDeriv 𝕜 f) :=
  hf.mono' <| support_lineDeriv_subset 𝕜
#align has_compact_support.lineDeriv HasCompactSupport.lineDeriv

end Support




#exit

variable {f f₀ f₁ g : E → F}

variable {f' f₀' f₁' g' : F}

variable {x : 𝕜}

variable {s t : Set 𝕜}

variable {L L₁ L₂ : Filter 𝕜}

/-- Expressing `HasLineDerivAtFilter f f' x L` in terms of `HasDerivAtFilter` -/
theorem hasLineDerivAtFilter_iff_hasDerivAtFilter {f' : 𝕜 →L[𝕜] F} :
    HasLineDerivAtFilter f f' x L ↔ HasDerivAtFilter f (f' 1) x L := by simp [HasDerivAtFilter]
#align has_lineDeriv_at_filter_iff_has_deriv_at_filter hasLineDerivAtFilter_iff_hasDerivAtFilter

theorem HasLineDerivAtFilter.hasDerivAtFilter {f' : 𝕜 →L[𝕜] F} :
    HasLineDerivAtFilter f f' x L → HasDerivAtFilter f (f' 1) x L :=
  hasLineDerivAtFilter_iff_hasDerivAtFilter.mp
#align has_lineDeriv_at_filter.has_deriv_at_filter HasLineDerivAtFilter.hasDerivAtFilter

/-- Expressing `HasLineDerivWithinAt f f' s x` in terms of `HasDerivWithinAt` -/
theorem hasLineDerivWithinAt_iff_hasDerivWithinAt {f' : 𝕜 →L[𝕜] F} :
    HasLineDerivWithinAt f f' s x ↔ HasDerivWithinAt f (f' 1) s x :=
  hasLineDerivAtFilter_iff_hasDerivAtFilter
#align has_lineDeriv_within_at_iff_has_deriv_within_at hasLineDerivWithinAt_iff_hasDerivWithinAt

/-- Expressing `HasDerivWithinAt f f' s x` in terms of `HasLineDerivWithinAt` -/
theorem hasDerivWithinAt_iff_hasLineDerivWithinAt {f' : F} :
    HasDerivWithinAt f f' s x ↔ HasLineDerivWithinAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
  Iff.rfl
#align has_deriv_within_at_iff_has_lineDeriv_within_at hasDerivWithinAt_iff_hasLineDerivWithinAt

theorem HasLineDerivWithinAt.hasDerivWithinAt {f' : 𝕜 →L[𝕜] F} :
    HasLineDerivWithinAt f f' s x → HasDerivWithinAt f (f' 1) s x :=
  hasLineDerivWithinAt_iff_hasDerivWithinAt.mp
#align has_lineDeriv_within_at.has_deriv_within_at HasLineDerivWithinAt.hasDerivWithinAt

theorem HasDerivWithinAt.hasLineDerivWithinAt {f' : F} :
    HasDerivWithinAt f f' s x → HasLineDerivWithinAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
  hasDerivWithinAt_iff_hasLineDerivWithinAt.mp
#align has_deriv_within_at.has_lineDeriv_within_at HasDerivWithinAt.hasLineDerivWithinAt

/-- Expressing `HasLineDerivAt 𝕜 f f' x v` in terms of `HasDerivAt` -/
theorem hasLineDerivAt_iff_hasDerivAt {f' : 𝕜 →L[𝕜] F} : HasLineDerivAt 𝕜 f f' x v ↔ HasDerivAt f (f' 1) x :=
  hasLineDerivAtFilter_iff_hasDerivAtFilter
#align has_lineDeriv_at_iff_has_deriv_at hasLineDerivAt_iff_hasDerivAt

theorem HasLineDerivAt.hasDerivAt {f' : 𝕜 →L[𝕜] F} : HasLineDerivAt 𝕜 f f' x v → HasDerivAt f (f' 1) x :=
  hasLineDerivAt_iff_hasDerivAt.mp
#align has_lineDeriv_at.has_deriv_at HasLineDerivAt.hasDerivAt

theorem hasStrictLineDerivAt_iff_hasStrictDerivAt {f' : 𝕜 →L[𝕜] F} :
    HasStrictLineDerivAt f f' x ↔ HasStrictDerivAt f (f' 1) x := by
  simp [HasStrictDerivAt, HasStrictLineDerivAt]
#align has_strict_lineDeriv_at_iff_has_strict_deriv_at hasStrictLineDerivAt_iff_hasStrictDerivAt

protected theorem HasStrictLineDerivAt.hasStrictDerivAt {f' : 𝕜 →L[𝕜] F} :
    HasStrictLineDerivAt f f' x → HasStrictDerivAt f (f' 1) x :=
  hasStrictLineDerivAt_iff_hasStrictDerivAt.mp
#align has_strict_lineDeriv_at.has_strict_deriv_at HasStrictLineDerivAt.hasStrictDerivAt

theorem hasStrictDerivAt_iff_hasStrictLineDerivAt :
    HasStrictDerivAt f f' x ↔ HasStrictLineDerivAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
  Iff.rfl
#align has_strict_deriv_at_iff_has_strict_lineDeriv_at hasStrictDerivAt_iff_hasStrictLineDerivAt

alias hasStrictDerivAt_iff_hasStrictLineDerivAt ↔ HasStrictDerivAt.hasStrictLineDerivAt _
#align has_strict_deriv_at.has_strict_lineDeriv_at HasStrictDerivAt.hasStrictLineDerivAt

/-- Expressing `HasDerivAt f f' x` in terms of `HasLineDerivAt` -/
theorem hasDerivAt_iff_hasLineDerivAt {f' : F} :
    HasDerivAt f f' x ↔ HasLineDerivAt 𝕜 f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
  Iff.rfl
#align has_deriv_at_iff_has_lineDeriv_at hasDerivAt_iff_hasLineDerivAt

alias hasDerivAt_iff_hasLineDerivAt ↔ HasDerivAt.hasLineDerivAt _
#align has_deriv_at.has_lineDeriv_at HasDerivAt.hasLineDerivAt

theorem derivWithin_zero_of_not_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) :
    derivWithin f s x = 0 := by
  unfold derivWithin
  rw [lineDerivWithin_zero_of_not_differentiableWithinAt h]
  simp
#align deriv_within_zero_of_not_differentiable_within_at derivWithin_zero_of_not_differentiableWithinAt

theorem differentiableWithinAt_of_derivWithin_ne_zero (h : derivWithin f s x ≠ 0) :
    LineDifferentiableWithinAt 𝕜 f s x :=
  not_imp_comm.1 derivWithin_zero_of_not_differentiableWithinAt h
#align differentiable_within_at_of_deriv_within_ne_zero differentiableWithinAt_of_derivWithin_ne_zero

theorem deriv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0 := by
  unfold deriv
  rw [lineDeriv_zero_of_not_differentiableAt h]
  simp
#align deriv_zero_of_not_differentiable_at deriv_zero_of_not_differentiableAt

theorem differentiableAt_of_deriv_ne_zero (h : deriv f x ≠ 0) : LineDifferentiableAt 𝕜 f x :=
  not_imp_comm.1 deriv_zero_of_not_differentiableAt h
#align differentiable_at_of_deriv_ne_zero differentiableAt_of_deriv_ne_zero

theorem UniqueDiffWithinAt.eq_deriv (s : Set 𝕜) (H : UniqueDiffWithinAt 𝕜 s x)
    (h : HasDerivWithinAt f f' s x) (h₁ : HasDerivWithinAt f f₁' s x) : f' = f₁' :=
  smulRight_one_eq_iff.mp <| UniqueDiffWithinAt.eq H h h₁
#align unique_diff_within_at.eq_deriv UniqueDiffWithinAt.eq_deriv

theorem hasDerivAtFilter_iff_isLittleO :
    HasDerivAtFilter f f' x L ↔ (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[L] fun x' => x' - x :=
  Iff.rfl
#align has_deriv_at_filter_iff_is_o hasDerivAtFilter_iff_isLittleO

theorem hasDerivAtFilter_iff_tendsto :
    HasDerivAtFilter f f' x L ↔
      Tendsto (fun x' : 𝕜 => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) L (𝓝 0) :=
  hasLineDerivAtFilter_iff_tendsto
#align has_deriv_at_filter_iff_tendsto hasDerivAtFilter_iff_tendsto

theorem hasDerivWithinAt_iff_isLittleO :
    HasDerivWithinAt f f' s x ↔
      (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝[s] x] fun x' => x' - x :=
  Iff.rfl
#align has_deriv_within_at_iff_is_o hasDerivWithinAt_iff_isLittleO

theorem hasDerivWithinAt_iff_tendsto :
    HasDerivWithinAt f f' s x ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝[s] x) (𝓝 0) :=
  hasLineDerivAtFilter_iff_tendsto
#align has_deriv_within_at_iff_tendsto hasDerivWithinAt_iff_tendsto

theorem hasDerivAt_iff_isLittleO :
    HasDerivAt f f' x ↔ (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝 x] fun x' => x' - x :=
  Iff.rfl
#align has_deriv_at_iff_is_o hasDerivAt_iff_isLittleO

theorem hasDerivAt_iff_tendsto :
    HasDerivAt f f' x ↔ Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝 x) (𝓝 0) :=
  hasLineDerivAtFilter_iff_tendsto
#align has_deriv_at_iff_tendsto hasDerivAt_iff_tendsto

theorem HasDerivAtFilter.isBigO_sub (h : HasDerivAtFilter f f' x L) :
    (fun x' => f x' - f x) =O[L] fun x' => x' - x :=
  HasLineDerivAtFilter.isBigO_sub h
set_option linter.uppercaseLean3 false in
#align has_deriv_at_filter.is_O_sub HasDerivAtFilter.isBigO_sub

nonrec theorem HasDerivAtFilter.isBigO_sub_rev (hf : HasDerivAtFilter f f' x L) (hf' : f' ≠ 0) :
    (fun x' => x' - x) =O[L] fun x' => f x' - f x :=
  suffices AntilipschitzWith ‖f'‖₊⁻¹ (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') from hf.isBigO_sub_rev this
  AddMonoidHomClass.antilipschitz_of_bound (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') fun x => by
    simp [norm_smul, ← div_eq_inv_mul, mul_div_cancel _ (mt norm_eq_zero.1 hf')]
set_option linter.uppercaseLean3 false in
#align has_deriv_at_filter.is_O_sub_rev HasDerivAtFilter.isBigO_sub_rev

theorem HasStrictDerivAt.hasDerivAt (h : HasStrictDerivAt f f' x) : HasDerivAt f f' x :=
  h.hasLineDerivAt
#align has_strict_deriv_at.has_deriv_at HasStrictDerivAt.hasDerivAt

theorem hasDerivWithinAt_congr_set' {s t : Set 𝕜} (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasDerivWithinAt f f' s x ↔ HasDerivWithinAt f f' t x :=
  hasLineDerivWithinAt_congr_set' y h
#align has_deriv_within_at_congr_set' hasDerivWithinAt_congr_set'

theorem hasDerivWithinAt_congr_set {s t : Set 𝕜} (h : s =ᶠ[𝓝 x] t) :
    HasDerivWithinAt f f' s x ↔ HasDerivWithinAt f f' t x :=
  hasLineDerivWithinAt_congr_set h
#align has_deriv_within_at_congr_set hasDerivWithinAt_congr_set

alias hasDerivWithinAt_congr_set ↔ HasDerivWithinAt.congr_set _
#align has_deriv_within_at.congr_set HasDerivWithinAt.congr_set

@[simp]
theorem hasDerivWithinAt_diff_singleton :
    HasDerivWithinAt f f' (s \ {x}) x ↔ HasDerivWithinAt f f' s x :=
  hasLineDerivWithinAt_diff_singleton _
#align has_deriv_within_at_diff_singleton hasDerivWithinAt_diff_singleton

@[simp]
theorem hasDerivWithinAt_Ioi_iff_Ici [PartialOrder 𝕜] :
    HasDerivWithinAt f f' (Ioi x) x ↔ HasDerivWithinAt f f' (Ici x) x := by
  rw [← Ici_diff_left, hasDerivWithinAt_diff_singleton]
#align has_deriv_within_at_Ioi_iff_Ici hasDerivWithinAt_Ioi_iff_Ici

alias hasDerivWithinAt_Ioi_iff_Ici ↔ HasDerivWithinAt.Ici_of_Ioi HasDerivWithinAt.Ioi_of_Ici
#align has_deriv_within_at.Ici_of_Ioi HasDerivWithinAt.Ici_of_Ioi
#align has_deriv_within_at.Ioi_of_Ici HasDerivWithinAt.Ioi_of_Ici

@[simp]
theorem hasDerivWithinAt_Iio_iff_Iic [PartialOrder 𝕜] :
    HasDerivWithinAt f f' (Iio x) x ↔ HasDerivWithinAt f f' (Iic x) x := by
  rw [← Iic_diff_right, hasDerivWithinAt_diff_singleton]
#align has_deriv_within_at_Iio_iff_Iic hasDerivWithinAt_Iio_iff_Iic

alias hasDerivWithinAt_Iio_iff_Iic ↔ HasDerivWithinAt.Iic_of_Iio HasDerivWithinAt.Iio_of_Iic
#align has_deriv_within_at.Iic_of_Iio HasDerivWithinAt.Iic_of_Iio
#align has_deriv_within_at.Iio_of_Iic HasDerivWithinAt.Iio_of_Iic

theorem HasDerivWithinAt.Ioi_iff_Ioo [LinearOrder 𝕜] [OrderClosedTopology 𝕜] {x y : 𝕜} (h : x < y) :
    HasDerivWithinAt f f' (Ioo x y) x ↔ HasDerivWithinAt f f' (Ioi x) x :=
  hasLineDerivWithinAt_inter <| Iio_mem_nhds h
#align has_deriv_within_at.Ioi_iff_Ioo HasDerivWithinAt.Ioi_iff_Ioo

alias HasDerivWithinAt.Ioi_iff_Ioo ↔ HasDerivWithinAt.Ioi_of_Ioo HasDerivWithinAt.Ioo_of_Ioi
#align has_deriv_within_at.Ioi_of_Ioo HasDerivWithinAt.Ioi_of_Ioo
#align has_deriv_within_at.Ioo_of_Ioi HasDerivWithinAt.Ioo_of_Ioi

theorem hasDerivAt_iff_isLittleO_nhds_zero :
    HasDerivAt f f' x ↔ (fun h => f (x + h) - f x - h • f') =o[𝓝 0] fun h => h :=
  hasLineDerivAt_iff_isLittleO_nhds_zero
#align has_deriv_at_iff_is_o_nhds_zero hasDerivAt_iff_isLittleO_nhds_zero

theorem HasDerivAtFilter.mono (h : HasDerivAtFilter f f' x L₂) (hst : L₁ ≤ L₂) :
    HasDerivAtFilter f f' x L₁ :=
  HasLineDerivAtFilter.mono h hst
#align has_deriv_at_filter.mono HasDerivAtFilter.mono

theorem HasDerivWithinAt.mono (h : HasDerivWithinAt f f' t x) (hst : s ⊆ t) :
    HasDerivWithinAt f f' s x :=
  HasLineDerivWithinAt.mono h hst
#align has_deriv_within_at.mono HasDerivWithinAt.mono

theorem HasDerivWithinAt.mono_of_mem (h : HasDerivWithinAt f f' t x) (hst : t ∈ 𝓝[s] x) :
    HasDerivWithinAt f f' s x :=
  HasLineDerivWithinAt.mono_of_mem h hst
#align has_deriv_within_at.mono_of_mem HasDerivWithinAt.mono_of_mem

theorem HasDerivAt.hasDerivAtFilter (h : HasDerivAt f f' x) (hL : L ≤ 𝓝 x) :
    HasDerivAtFilter f f' x L :=
  HasLineDerivAt.hasLineDerivAtFilter h hL
#align has_deriv_at.has_deriv_at_filter HasDerivAt.hasDerivAtFilter

theorem HasDerivAt.hasDerivWithinAt (h : HasDerivAt f f' x) : HasDerivWithinAt f f' s x :=
  HasLineDerivAt.hasLineDerivWithinAt h
#align has_deriv_at.has_deriv_within_at HasDerivAt.hasDerivWithinAt

theorem HasDerivWithinAt.differentiableWithinAt (h : HasDerivWithinAt f f' s x) :
    LineDifferentiableWithinAt 𝕜 f s x :=
  HasLineDerivWithinAt.differentiableWithinAt h
#align has_deriv_within_at.differentiable_within_at HasDerivWithinAt.differentiableWithinAt

theorem HasDerivAt.differentiableAt (h : HasDerivAt f f' x) : LineDifferentiableAt 𝕜 f x :=
  HasLineDerivAt.differentiableAt h
#align has_deriv_at.differentiable_at HasDerivAt.differentiableAt

@[simp]
theorem hasDerivWithinAt_univ : HasDerivWithinAt f f' univ x ↔ HasDerivAt f f' x :=
  hasLineDerivWithinAt_univ
#align has_deriv_within_at_univ hasDerivWithinAt_univ

theorem HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : HasDerivAt f f₁' x) : f₀' = f₁' :=
  smulRight_one_eq_iff.mp <| h₀.hasLineDerivAt.unique h₁
#align has_deriv_at.unique HasDerivAt.unique

theorem hasDerivWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    HasDerivWithinAt f f' (s ∩ t) x ↔ HasDerivWithinAt f f' s x :=
  hasLineDerivWithinAt_inter' h
#align has_deriv_within_at_inter' hasDerivWithinAt_inter'

theorem hasDerivWithinAt_inter (h : t ∈ 𝓝 x) :
    HasDerivWithinAt f f' (s ∩ t) x ↔ HasDerivWithinAt f f' s x :=
  hasLineDerivWithinAt_inter h
#align has_deriv_within_at_inter hasDerivWithinAt_inter

theorem HasDerivWithinAt.union (hs : HasDerivWithinAt f f' s x) (ht : HasDerivWithinAt f f' t x) :
    HasDerivWithinAt f f' (s ∪ t) x :=
  hs.hasLineDerivWithinAt.union ht.hasLineDerivWithinAt
#align has_deriv_within_at.union HasDerivWithinAt.union

theorem HasDerivWithinAt.nhdsWithin (h : HasDerivWithinAt f f' s x) (ht : s ∈ 𝓝[t] x) :
    HasDerivWithinAt f f' t x :=
  (hasDerivWithinAt_inter' ht).1 (h.mono (inter_subset_right _ _))
#align has_deriv_within_at.nhds_within HasDerivWithinAt.nhdsWithin

theorem HasDerivWithinAt.hasDerivAt (h : HasDerivWithinAt f f' s x) (hs : s ∈ 𝓝 x) :
    HasDerivAt f f' x :=
  HasLineDerivWithinAt.hasLineDerivAt h hs
#align has_deriv_within_at.has_deriv_at HasDerivWithinAt.hasDerivAt

theorem LineDifferentiableWithinAt.hasDerivWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x) :
    HasDerivWithinAt f (derivWithin f s x) s x :=
  h.hasLineDerivWithinAt.hasDerivWithinAt
#align differentiable_within_at.has_deriv_within_at LineDifferentiableWithinAt.hasDerivWithinAt

theorem LineDifferentiableAt.hasDerivAt (h : LineDifferentiableAt 𝕜 f x) : HasDerivAt f (deriv f x) x :=
  h.hasLineDerivAt.hasDerivAt
#align differentiable_at.has_deriv_at LineDifferentiableAt.hasDerivAt

@[simp]
theorem hasDerivAt_deriv_iff : HasDerivAt f (deriv f x) x ↔ LineDifferentiableAt 𝕜 f x :=
  ⟨fun h => h.differentiableAt, fun h => h.hasDerivAt⟩
#align has_deriv_at_deriv_iff hasDerivAt_deriv_iff

@[simp]
theorem hasDerivWithinAt_derivWithin_iff :
    HasDerivWithinAt f (derivWithin f s x) s x ↔ LineDifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => h.differentiableWithinAt, fun h => h.hasDerivWithinAt⟩
#align has_deriv_within_at_deriv_within_iff hasDerivWithinAt_derivWithin_iff

theorem LineDifferentiableOn.hasDerivAt (h : LineDifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasDerivAt f (deriv f x) x :=
  (h.hasLineDerivAt hs).hasDerivAt
#align differentiable_on.has_deriv_at LineDifferentiableOn.hasDerivAt

theorem HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x = f' :=
  h.differentiableAt.hasDerivAt.unique h
#align has_deriv_at.deriv HasDerivAt.deriv

theorem deriv_eq {f' : 𝕜 → F} (h : ∀ x, HasDerivAt f (f' x) x) : deriv f = f' :=
  funext fun x => (h x).deriv
#align deriv_eq deriv_eq

theorem HasDerivWithinAt.derivWithin (h : HasDerivWithinAt f f' s x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f' :=
  hxs.eq_deriv _ h.differentiableWithinAt.hasDerivWithinAt h
#align has_deriv_within_at.deriv_within HasDerivWithinAt.derivWithin

theorem lineDerivWithin_derivWithin : (lineDerivWithin 𝕜 f s x : 𝕜 → F) 1 = derivWithin f s x :=
  rfl
#align lineDeriv_within_deriv_within lineDerivWithin_derivWithin

theorem derivWithin_lineDerivWithin :
    smulRight (1 : 𝕜 →L[𝕜] 𝕜) (derivWithin f s x) = lineDerivWithin 𝕜 f s x := by simp [derivWithin]
#align deriv_within_lineDeriv_within derivWithin_lineDerivWithin

theorem lineDeriv_deriv : (lineDeriv 𝕜 f x : 𝕜 → F) 1 = deriv f x :=
  rfl
#align lineDeriv_deriv lineDeriv_deriv

theorem deriv_lineDeriv : smulRight (1 : 𝕜 →L[𝕜] 𝕜) (deriv f x) = lineDeriv 𝕜 f x := by simp [deriv]
#align deriv_lineDeriv deriv_lineDeriv

theorem LineDifferentiableAt.derivWithin (h : LineDifferentiableAt 𝕜 f x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = deriv f x := by
  unfold derivWithin deriv
  rw [h.lineDerivWithin hxs]
#align differentiable_at.deriv_within LineDifferentiableAt.derivWithin

theorem HasDerivWithinAt.deriv_eq_zero (hd : HasDerivWithinAt f 0 s x)
    (H : UniqueDiffWithinAt 𝕜 s x) : deriv f x = 0 :=
  (em' (DifferentiableAt 𝕜 f x)).elim deriv_zero_of_not_differentiableAt fun h =>
    H.eq_deriv _ h.hasDerivAt.hasDerivWithinAt hd
#align has_deriv_within_at.deriv_eq_zero HasDerivWithinAt.deriv_eq_zero

theorem derivWithin_of_mem (st : t ∈ 𝓝[s] x) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : LineDifferentiableWithinAt 𝕜 f t x) : derivWithin f s x = derivWithin f t x :=
  ((DifferentiableWithinAt.hasDerivWithinAt h).mono_of_mem st).derivWithin ht
#align deriv_within_of_mem derivWithin_of_mem

theorem derivWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : LineDifferentiableWithinAt 𝕜 f t x) : derivWithin f s x = derivWithin f t x :=
  ((DifferentiableWithinAt.hasDerivWithinAt h).mono st).derivWithin ht
#align deriv_within_subset derivWithin_subset

theorem derivWithin_congr_set' (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    derivWithin f s x = derivWithin f t x := by simp only [derivWithin, lineDerivWithin_congr_set' y h]
#align deriv_within_congr_set' derivWithin_congr_set'

theorem derivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : derivWithin f s x = derivWithin f t x := by
  simp only [derivWithin, lineDerivWithin_congr_set h]
#align deriv_within_congr_set derivWithin_congr_set

@[simp]
theorem derivWithin_univ : derivWithin f univ = deriv f := by
  ext
  unfold derivWithin deriv
  rw [lineDerivWithin_univ]
#align deriv_within_univ derivWithin_univ

theorem derivWithin_inter (ht : t ∈ 𝓝 x) : derivWithin f (s ∩ t) x = derivWithin f s x := by
  unfold derivWithin
  rw [lineDerivWithin_inter ht]
#align deriv_within_inter derivWithin_inter

theorem derivWithin_of_open (hs : IsOpen s) (hx : x ∈ s) : derivWithin f s x = deriv f x := by
  unfold derivWithin
  rw [lineDerivWithin_of_open hs hx]
  rfl
#align deriv_within_of_open derivWithin_of_open

theorem deriv_mem_iff {f : 𝕜 → F} {s : Set F} {x : 𝕜} :
    deriv f x ∈ s ↔
      LineDifferentiableAt 𝕜 f x ∧ deriv f x ∈ s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0 : F) ∈ s :=
  by by_cases hx : LineDifferentiableAt 𝕜 f x <;> simp [deriv_zero_of_not_differentiableAt, *]
#align deriv_mem_iff deriv_mem_iff

theorem derivWithin_mem_iff {f : 𝕜 → F} {t : Set 𝕜} {s : Set F} {x : 𝕜} :
    derivWithin f t x ∈ s ↔
      LineDifferentiableWithinAt 𝕜 f t x ∧ derivWithin f t x ∈ s ∨
        ¬DifferentiableWithinAt 𝕜 f t x ∧ (0 : F) ∈ s := by
  by_cases hx : LineDifferentiableWithinAt 𝕜 f t x <;>
    simp [derivWithin_zero_of_not_differentiableWithinAt, *]
#align deriv_within_mem_iff derivWithin_mem_iff

theorem differentiableWithinAt_Ioi_iff_Ici [PartialOrder 𝕜] :
    LineDifferentiableWithinAt 𝕜 f (Ioi x) x ↔ LineDifferentiableWithinAt 𝕜 f (Ici x) x :=
  ⟨fun h => h.hasDerivWithinAt.Ici_of_Ioi.differentiableWithinAt, fun h =>
    h.hasDerivWithinAt.Ioi_of_Ici.differentiableWithinAt⟩
#align differentiable_within_at_Ioi_iff_Ici differentiableWithinAt_Ioi_iff_Ici

-- Golfed while splitting the file
theorem derivWithin_Ioi_eq_Ici {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E)
    (x : ℝ) : derivWithin f (Ioi x) x = derivWithin f (Ici x) x := by
  by_cases H : LineDifferentiableWithinAt ℝ f (Ioi x) x
  · have A := H.hasDerivWithinAt.Ici_of_Ioi
    have B := (differentiableWithinAt_Ioi_iff_Ici.1 H).hasDerivWithinAt
    simpa using (uniqueDiffOn_Ici x).eq left_mem_Ici A B
  · rw [derivWithin_zero_of_not_differentiableWithinAt H,
      derivWithin_zero_of_not_differentiableWithinAt]
    rwa [differentiableWithinAt_Ioi_iff_Ici] at H
#align deriv_within_Ioi_eq_Ici derivWithin_Ioi_eq_Ici

section congr

/-! ### Congruence properties of derivatives -/

theorem Filter.EventuallyEq.hasDerivAtFilter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
    (h₁ : f₀' = f₁') : HasDerivAtFilter f₀ f₀' x L ↔ HasDerivAtFilter f₁ f₁' x L :=
  h₀.hasLineDerivAtFilter_iff hx (by simp [h₁])
#align filter.eventually_eq.has_deriv_at_filter_iff Filter.EventuallyEq.hasDerivAtFilter_iff

theorem HasDerivAtFilter.congr_of_eventuallyEq (h : HasDerivAtFilter f f' x L) (hL : f₁ =ᶠ[L] f)
    (hx : f₁ x = f x) : HasDerivAtFilter f₁ f' x L := by rwa [hL.hasDerivAtFilter_iff hx rfl]
#align has_deriv_at_filter.congr_of_eventually_eq HasDerivAtFilter.congr_of_eventuallyEq

theorem HasDerivWithinAt.congr_mono (h : HasDerivWithinAt f f' s x) (ht : ∀ x ∈ t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasDerivWithinAt f₁ f' t x :=
  HasLineDerivWithinAt.congr_mono h ht hx h₁
#align has_deriv_within_at.congr_mono HasDerivWithinAt.congr_mono

theorem HasDerivWithinAt.congr (h : HasDerivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
  h.congr_mono hs hx (Subset.refl _)
#align has_deriv_within_at.congr HasDerivWithinAt.congr

theorem HasDerivWithinAt.congr_of_mem (h : HasDerivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : x ∈ s) : HasDerivWithinAt f₁ f' s x :=
  h.congr hs (hs _ hx)
#align has_deriv_within_at.congr_of_mem HasDerivWithinAt.congr_of_mem

theorem HasDerivWithinAt.congr_of_eventuallyEq (h : HasDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
  HasDerivAtFilter.congr_of_eventuallyEq h h₁ hx
#align has_deriv_within_at.congr_of_eventually_eq HasDerivWithinAt.congr_of_eventuallyEq

theorem HasDerivWithinAt.congr_of_eventuallyEq_of_mem (h : HasDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : HasDerivWithinAt f₁ f' s x :=
  h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)
#align has_deriv_within_at.congr_of_eventually_eq_of_mem HasDerivWithinAt.congr_of_eventuallyEq_of_mem

theorem HasDerivAt.congr_of_eventuallyEq (h : HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasDerivAt f₁ f' x :=
  HasDerivAtFilter.congr_of_eventuallyEq h h₁ (mem_of_mem_nhds h₁ : _)
#align has_deriv_at.congr_of_eventually_eq HasDerivAt.congr_of_eventuallyEq

theorem Filter.EventuallyEq.derivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    derivWithin f₁ s x = derivWithin f s x := by
  unfold derivWithin
  rw [hs.lineDerivWithin_eq hx]
#align filter.eventually_eq.deriv_within_eq Filter.EventuallyEq.derivWithin_eq

theorem derivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) :
    derivWithin f₁ s x = derivWithin f s x := by
  unfold derivWithin
  rw [lineDerivWithin_congr hs hx]
#align deriv_within_congr derivWithin_congr

theorem Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝 x] f) : deriv f₁ x = deriv f x := by
  unfold deriv
  rwa [Filter.EventuallyEq.lineDeriv_eq]
#align filter.eventually_eq.deriv_eq Filter.EventuallyEq.deriv_eq

protected theorem Filter.EventuallyEq.deriv (h : f₁ =ᶠ[𝓝 x] f) : deriv f₁ =ᶠ[𝓝 x] deriv f :=
  h.eventuallyEq_nhds.mono fun _ h => h.deriv_eq
#align filter.eventually_eq.deriv Filter.EventuallyEq.deriv

end congr

section id

/-! ### Derivative of the identity -/

variable (s x L)

theorem hasDerivAtFilter_id : HasDerivAtFilter id 1 x L :=
  (hasLineDerivAtFilter_id x L).hasDerivAtFilter
#align has_deriv_at_filter_id hasDerivAtFilter_id

theorem hasDerivWithinAt_id : HasDerivWithinAt id 1 s x :=
  hasDerivAtFilter_id _ _
#align has_deriv_within_at_id hasDerivWithinAt_id

theorem hasDerivAt_id : HasDerivAt id 1 x :=
  hasDerivAtFilter_id _ _
#align has_deriv_at_id hasDerivAt_id

theorem hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x :=
  hasDerivAtFilter_id _ _
#align has_deriv_at_id' hasDerivAt_id'

theorem hasStrictDerivAt_id : HasStrictDerivAt id 1 x :=
  (hasStrictLineDerivAt_id x).hasStrictDerivAt
#align has_strict_deriv_at_id hasStrictDerivAt_id

theorem deriv_id : deriv id x = 1 :=
  HasDerivAt.deriv (hasDerivAt_id x)
#align deriv_id deriv_id

@[simp]
theorem deriv_id' : deriv (@id 𝕜) = fun _ => 1 :=
  funext deriv_id
#align deriv_id' deriv_id'

@[simp]
theorem deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1 :=
  deriv_id'
#align deriv_id'' deriv_id''

theorem derivWithin_id (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin id s x = 1 :=
  (hasDerivWithinAt_id x s).derivWithin hxs
#align deriv_within_id derivWithin_id

end id

section Const

/-! ### Derivative of constant functions -/

variable (c : F) (s x L)

theorem hasDerivAtFilter_const : HasDerivAtFilter (fun _ => c) 0 x L :=
  (hasLineDerivAtFilter_const c x L).hasDerivAtFilter
#align has_deriv_at_filter_const hasDerivAtFilter_const

theorem hasStrictDerivAt_const : HasStrictDerivAt (fun _ => c) 0 x :=
  (hasStrictLineDerivAt_const c x).hasStrictDerivAt
#align has_strict_deriv_at_const hasStrictDerivAt_const

theorem hasDerivWithinAt_const : HasDerivWithinAt (fun _ => c) 0 s x :=
  hasDerivAtFilter_const _ _ _
#align has_deriv_within_at_const hasDerivWithinAt_const

theorem hasDerivAt_const : HasDerivAt (fun _ => c) 0 x :=
  hasDerivAtFilter_const _ _ _
#align has_deriv_at_const hasDerivAt_const

theorem deriv_const : deriv (fun _ => c) x = 0 :=
  HasDerivAt.deriv (hasDerivAt_const x c)
#align deriv_const deriv_const

@[simp]
theorem deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0 :=
  funext fun x => deriv_const x c
#align deriv_const' deriv_const'

theorem derivWithin_const (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin (fun _ => c) s x = 0 :=
  (hasDerivWithinAt_const _ _ _).derivWithin hxs
#align deriv_within_const derivWithin_const

end Const

section Continuous

/-! ### Continuity of a function admitting a derivative -/

nonrec theorem HasDerivAtFilter.tendsto_nhds (hL : L ≤ 𝓝 x) (h : HasDerivAtFilter f f' x L) :
    Tendsto f L (𝓝 (f x)) :=
  h.tendsto_nhds hL
#align has_deriv_at_filter.tendsto_nhds HasDerivAtFilter.tendsto_nhds

theorem HasDerivWithinAt.continuousWithinAt (h : HasDerivWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasDerivAtFilter.tendsto_nhds inf_le_left h
#align has_deriv_within_at.continuous_within_at HasDerivWithinAt.continuousWithinAt

theorem HasDerivAt.continuousAt (h : HasDerivAt f f' x) : ContinuousAt f x :=
  HasDerivAtFilter.tendsto_nhds le_rfl h
#align has_deriv_at.continuous_at HasDerivAt.continuousAt

protected theorem HasDerivAt.continuousOn {f f' : 𝕜 → F} (hderiv : ∀ x ∈ s, HasDerivAt f (f' x) x) :
    ContinuousOn f s := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
#align has_deriv_at.continuous_on HasDerivAt.continuousOn

end Continuous
