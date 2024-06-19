/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.ENNReal

#align_import topology.semicontinuous from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Semicontinuous maps

A function `f` from a topological space `α` to an ordered space `β` is lower semicontinuous at a
point `x` if, for any `y < f x`, for any `x'` close enough to `x`, one has `f x' > y`. In other
words, `f` can jump up, but it can not jump down.

Upper semicontinuous functions are defined similarly.

This file introduces these notions, and a basic API around them mimicking the API for continuous
functions.

## Main definitions and results

We introduce 4 definitions related to lower semicontinuity:
* `LowerSemicontinuousWithinAt f s x`
* `LowerSemicontinuousAt f x`
* `LowerSemicontinuousOn f s`
* `LowerSemicontinuous f`

We build a basic API using dot notation around these notions, and we prove that
* constant functions are lower semicontinuous;
* `indicator s (fun _ ↦ y)` is lower semicontinuous when `s` is open and `0 ≤ y`,
  or when `s` is closed and `y ≤ 0`;
* continuous functions are lower semicontinuous;
* left composition with a continuous monotone functions maps lower semicontinuous functions to lower
  semicontinuous functions. If the function is anti-monotone, it instead maps lower semicontinuous
  functions to upper semicontinuous functions;
* right composition with continuous functions preserves lower and upper semicontinuity;
* a sum of two (or finitely many) lower semicontinuous functions is lower semicontinuous;
* a supremum of a family of lower semicontinuous functions is lower semicontinuous;
* An infinite sum of `ℝ≥0∞`-valued lower semicontinuous functions is lower semicontinuous.

Similar results are stated and proved for upper semicontinuity.

We also prove that a function is continuous if and only if it is both lower and upper
semicontinuous.

We have some equivalent definitions of lower- and upper-semicontinuity (under certain
restrictions on the order on the codomain):
* `lowerSemicontinuous_iff_isOpen_preimage` in a linear order;
* `lowerSemicontinuous_iff_isClosed_preimage` in a linear order;
* `lowerSemicontinuousAt_iff_le_liminf` in a dense complete linear order;
* `lowerSemicontinuous_iff_isClosed_epigraph` in a dense complete linear order with the order
  topology.

## Implementation details

All the nontrivial results for upper semicontinuous functions are deduced from the corresponding
ones for lower semicontinuous functions using `OrderDual`.

## References

* <https://en.wikipedia.org/wiki/Closed_convex_function>
* <https://en.wikipedia.org/wiki/Semi-continuity>

-/


open Topology ENNReal

open Set Function Filter

variable {α : Type*} [TopologicalSpace α] {β : Type*} [Preorder β] {f g : α → β} {x : α}
  {s t : Set α} {y z : β}

/-! ### Main definitions -/


/-- A real function `f` is lower semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in `s`, then `f x'` is at least `f x - ε`. We formulate this in a general
preordered space, using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuousWithinAt (f : α → β) (s : Set α) (x : α) :=
  ∀ y < f x, ∀ᶠ x' in 𝓝[s] x, y < f x'
#align lower_semicontinuous_within_at LowerSemicontinuousWithinAt

/-- A real function `f` is lower semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at least `f x - ε`. We formulate this in
a general preordered space, using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuousOn (f : α → β) (s : Set α) :=
  ∀ x ∈ s, LowerSemicontinuousWithinAt f s x
#align lower_semicontinuous_on LowerSemicontinuousOn

/-- A real function `f` is lower semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuousAt (f : α → β) (x : α) :=
  ∀ y < f x, ∀ᶠ x' in 𝓝 x, y < f x'
#align lower_semicontinuous_at LowerSemicontinuousAt

/-- A real function `f` is lower semicontinuous if, for any `ε > 0`, for any `x`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuous (f : α → β) :=
  ∀ x, LowerSemicontinuousAt f x
#align lower_semicontinuous LowerSemicontinuous

/-- A real function `f` is upper semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We formulate this in a general
preordered space, using an arbitrary `y > f x` instead of `f x + ε`. -/
def UpperSemicontinuousWithinAt (f : α → β) (s : Set α) (x : α) :=
  ∀ y, f x < y → ∀ᶠ x' in 𝓝[s] x, f x' < y
#align upper_semicontinuous_within_at UpperSemicontinuousWithinAt

/-- A real function `f` is upper semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We formulate this in a
general preordered space, using an arbitrary `y > f x` instead of `f x + ε`. -/
def UpperSemicontinuousOn (f : α → β) (s : Set α) :=
  ∀ x ∈ s, UpperSemicontinuousWithinAt f s x
#align upper_semicontinuous_on UpperSemicontinuousOn

/-- A real function `f` is upper semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered space,
using an arbitrary `y > f x` instead of `f x + ε`. -/
def UpperSemicontinuousAt (f : α → β) (x : α) :=
  ∀ y, f x < y → ∀ᶠ x' in 𝓝 x, f x' < y
#align upper_semicontinuous_at UpperSemicontinuousAt

/-- A real function `f` is upper semicontinuous if, for any `ε > 0`, for any `x`, for all `x'`
close enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered
space, using an arbitrary `y > f x` instead of `f x + ε`. -/
def UpperSemicontinuous (f : α → β) :=
  ∀ x, UpperSemicontinuousAt f x
#align upper_semicontinuous UpperSemicontinuous

/-!
### Lower semicontinuous functions
-/


/-! #### Basic dot notation interface for lower semicontinuity -/


theorem LowerSemicontinuousWithinAt.mono (h : LowerSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    LowerSemicontinuousWithinAt f t x := fun y hy =>
  Filter.Eventually.filter_mono (nhdsWithin_mono _ hst) (h y hy)
#align lower_semicontinuous_within_at.mono LowerSemicontinuousWithinAt.mono

theorem lowerSemicontinuousWithinAt_univ_iff :
    LowerSemicontinuousWithinAt f univ x ↔ LowerSemicontinuousAt f x := by
  simp [LowerSemicontinuousWithinAt, LowerSemicontinuousAt, nhdsWithin_univ]
#align lower_semicontinuous_within_at_univ_iff lowerSemicontinuousWithinAt_univ_iff

theorem LowerSemicontinuousAt.lowerSemicontinuousWithinAt (s : Set α)
    (h : LowerSemicontinuousAt f x) : LowerSemicontinuousWithinAt f s x := fun y hy =>
  Filter.Eventually.filter_mono nhdsWithin_le_nhds (h y hy)
#align lower_semicontinuous_at.lower_semicontinuous_within_at LowerSemicontinuousAt.lowerSemicontinuousWithinAt

theorem LowerSemicontinuousOn.lowerSemicontinuousWithinAt (h : LowerSemicontinuousOn f s)
    (hx : x ∈ s) : LowerSemicontinuousWithinAt f s x :=
  h x hx
#align lower_semicontinuous_on.lower_semicontinuous_within_at LowerSemicontinuousOn.lowerSemicontinuousWithinAt

theorem LowerSemicontinuousOn.mono (h : LowerSemicontinuousOn f s) (hst : t ⊆ s) :
    LowerSemicontinuousOn f t := fun x hx => (h x (hst hx)).mono hst
#align lower_semicontinuous_on.mono LowerSemicontinuousOn.mono

theorem lowerSemicontinuousOn_univ_iff : LowerSemicontinuousOn f univ ↔ LowerSemicontinuous f := by
  simp [LowerSemicontinuousOn, LowerSemicontinuous, lowerSemicontinuousWithinAt_univ_iff]
#align lower_semicontinuous_on_univ_iff lowerSemicontinuousOn_univ_iff

theorem LowerSemicontinuous.lowerSemicontinuousAt (h : LowerSemicontinuous f) (x : α) :
    LowerSemicontinuousAt f x :=
  h x
#align lower_semicontinuous.lower_semicontinuous_at LowerSemicontinuous.lowerSemicontinuousAt

theorem LowerSemicontinuous.lowerSemicontinuousWithinAt (h : LowerSemicontinuous f) (s : Set α)
    (x : α) : LowerSemicontinuousWithinAt f s x :=
  (h x).lowerSemicontinuousWithinAt s
#align lower_semicontinuous.lower_semicontinuous_within_at LowerSemicontinuous.lowerSemicontinuousWithinAt

theorem LowerSemicontinuous.lowerSemicontinuousOn (h : LowerSemicontinuous f) (s : Set α) :
    LowerSemicontinuousOn f s := fun x _hx => h.lowerSemicontinuousWithinAt s x
#align lower_semicontinuous.lower_semicontinuous_on LowerSemicontinuous.lowerSemicontinuousOn

/-! #### Constants -/


theorem lowerSemicontinuousWithinAt_const : LowerSemicontinuousWithinAt (fun _x => z) s x :=
  fun _y hy => Filter.eventually_of_forall fun _x => hy
#align lower_semicontinuous_within_at_const lowerSemicontinuousWithinAt_const

theorem lowerSemicontinuousAt_const : LowerSemicontinuousAt (fun _x => z) x := fun _y hy =>
  Filter.eventually_of_forall fun _x => hy
#align lower_semicontinuous_at_const lowerSemicontinuousAt_const

theorem lowerSemicontinuousOn_const : LowerSemicontinuousOn (fun _x => z) s := fun _x _hx =>
  lowerSemicontinuousWithinAt_const
#align lower_semicontinuous_on_const lowerSemicontinuousOn_const

theorem lowerSemicontinuous_const : LowerSemicontinuous fun _x : α => z := fun _x =>
  lowerSemicontinuousAt_const
#align lower_semicontinuous_const lowerSemicontinuous_const

/-! #### Indicators -/


section

variable [Zero β]

theorem IsOpen.lowerSemicontinuous_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuous (indicator s fun _x => y) := by
  intro x z hz
  by_cases h : x ∈ s <;> simp [h] at hz
  · filter_upwards [hs.mem_nhds h]
    simp (config := { contextual := true }) [hz]
  · refine Filter.eventually_of_forall fun x' => ?_
    by_cases h' : x' ∈ s <;> simp [h', hz.trans_le hy, hz]
#align is_open.lower_semicontinuous_indicator IsOpen.lowerSemicontinuous_indicator

theorem IsOpen.lowerSemicontinuousOn_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousOn t
#align is_open.lower_semicontinuous_on_indicator IsOpen.lowerSemicontinuousOn_indicator

theorem IsOpen.lowerSemicontinuousAt_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousAt x
#align is_open.lower_semicontinuous_at_indicator IsOpen.lowerSemicontinuousAt_indicator

theorem IsOpen.lowerSemicontinuousWithinAt_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousWithinAt t x
#align is_open.lower_semicontinuous_within_at_indicator IsOpen.lowerSemicontinuousWithinAt_indicator

theorem IsClosed.lowerSemicontinuous_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuous (indicator s fun _x => y) := by
  intro x z hz
  by_cases h : x ∈ s <;> simp [h] at hz
  · refine Filter.eventually_of_forall fun x' => ?_
    by_cases h' : x' ∈ s <;> simp [h', hz, hz.trans_le hy]
  · filter_upwards [hs.isOpen_compl.mem_nhds h]
    simp (config := { contextual := true }) [hz]
#align is_closed.lower_semicontinuous_indicator IsClosed.lowerSemicontinuous_indicator

theorem IsClosed.lowerSemicontinuousOn_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousOn t
#align is_closed.lower_semicontinuous_on_indicator IsClosed.lowerSemicontinuousOn_indicator

theorem IsClosed.lowerSemicontinuousAt_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousAt x
#align is_closed.lower_semicontinuous_at_indicator IsClosed.lowerSemicontinuousAt_indicator

theorem IsClosed.lowerSemicontinuousWithinAt_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousWithinAt t x
#align is_closed.lower_semicontinuous_within_at_indicator IsClosed.lowerSemicontinuousWithinAt_indicator

end

/-! #### Relationship with continuity -/


theorem lowerSemicontinuous_iff_isOpen_preimage :
    LowerSemicontinuous f ↔ ∀ y, IsOpen (f ⁻¹' Ioi y) :=
  ⟨fun H y => isOpen_iff_mem_nhds.2 fun x hx => H x y hx, fun H _x y y_lt =>
    IsOpen.mem_nhds (H y) y_lt⟩
#align lower_semicontinuous_iff_is_open_preimage lowerSemicontinuous_iff_isOpen_preimage

theorem LowerSemicontinuous.isOpen_preimage (hf : LowerSemicontinuous f) (y : β) :
    IsOpen (f ⁻¹' Ioi y) :=
  lowerSemicontinuous_iff_isOpen_preimage.1 hf y
#align lower_semicontinuous.is_open_preimage LowerSemicontinuous.isOpen_preimage

section

variable {γ : Type*} [LinearOrder γ]

theorem lowerSemicontinuous_iff_isClosed_preimage {f : α → γ} :
    LowerSemicontinuous f ↔ ∀ y, IsClosed (f ⁻¹' Iic y) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  simp only [← isOpen_compl_iff, ← preimage_compl, compl_Iic]
#align lower_semicontinuous_iff_is_closed_preimage lowerSemicontinuous_iff_isClosed_preimage

theorem LowerSemicontinuous.isClosed_preimage {f : α → γ} (hf : LowerSemicontinuous f) (y : γ) :
    IsClosed (f ⁻¹' Iic y) :=
  lowerSemicontinuous_iff_isClosed_preimage.1 hf y
#align lower_semicontinuous.is_closed_preimage LowerSemicontinuous.isClosed_preimage

variable [TopologicalSpace γ] [OrderTopology γ]

theorem ContinuousWithinAt.lowerSemicontinuousWithinAt {f : α → γ} (h : ContinuousWithinAt f s x) :
    LowerSemicontinuousWithinAt f s x := fun _y hy => h (Ioi_mem_nhds hy)
#align continuous_within_at.lower_semicontinuous_within_at ContinuousWithinAt.lowerSemicontinuousWithinAt

theorem ContinuousAt.lowerSemicontinuousAt {f : α → γ} (h : ContinuousAt f x) :
    LowerSemicontinuousAt f x := fun _y hy => h (Ioi_mem_nhds hy)
#align continuous_at.lower_semicontinuous_at ContinuousAt.lowerSemicontinuousAt

theorem ContinuousOn.lowerSemicontinuousOn {f : α → γ} (h : ContinuousOn f s) :
    LowerSemicontinuousOn f s := fun x hx => (h x hx).lowerSemicontinuousWithinAt
#align continuous_on.lower_semicontinuous_on ContinuousOn.lowerSemicontinuousOn

theorem Continuous.lowerSemicontinuous {f : α → γ} (h : Continuous f) : LowerSemicontinuous f :=
  fun _x => h.continuousAt.lowerSemicontinuousAt
#align continuous.lower_semicontinuous Continuous.lowerSemicontinuous

end

/-! #### Equivalent definitions -/

section

variable {γ : Type*} [CompleteLinearOrder γ] [DenselyOrdered γ]

theorem lowerSemicontinuousWithinAt_iff_le_liminf {f : α → γ} :
    LowerSemicontinuousWithinAt f s x ↔ f x ≤ liminf f (𝓝[s] x) := by
  constructor
  · intro hf; unfold LowerSemicontinuousWithinAt at hf
    contrapose! hf
    obtain ⟨y, lty, ylt⟩ := exists_between hf; use y
    exact ⟨ylt, fun h => lty.not_le
      (le_liminf_of_le (by isBoundedDefault) (h.mono fun _ hx => le_of_lt hx))⟩
  exact fun hf y ylt => eventually_lt_of_lt_liminf (ylt.trans_le hf)

alias ⟨LowerSemicontinuousWithinAt.le_liminf, _⟩ := lowerSemicontinuousWithinAt_iff_le_liminf

theorem lowerSemicontinuousAt_iff_le_liminf {f : α → γ} :
    LowerSemicontinuousAt f x ↔ f x ≤ liminf f (𝓝 x) := by
  rw [← lowerSemicontinuousWithinAt_univ_iff, lowerSemicontinuousWithinAt_iff_le_liminf,
    ← nhdsWithin_univ]

alias ⟨LowerSemicontinuousAt.le_liminf, _⟩ := lowerSemicontinuousAt_iff_le_liminf

theorem lowerSemicontinuous_iff_le_liminf {f : α → γ} :
    LowerSemicontinuous f ↔ ∀ x, f x ≤ liminf f (𝓝 x) := by
  simp only [← lowerSemicontinuousAt_iff_le_liminf, LowerSemicontinuous]

alias ⟨LowerSemicontinuous.le_liminf, _⟩ := lowerSemicontinuous_iff_le_liminf

theorem lowerSemicontinuousOn_iff_le_liminf {f : α → γ} :
    LowerSemicontinuousOn f s ↔ ∀ x ∈ s, f x ≤ liminf f (𝓝[s] x) := by
  simp only [← lowerSemicontinuousWithinAt_iff_le_liminf, LowerSemicontinuousOn]

alias ⟨LowerSemicontinuousOn.le_liminf, _⟩ := lowerSemicontinuousOn_iff_le_liminf

variable [TopologicalSpace γ] [OrderTopology γ]

theorem lowerSemicontinuous_iff_isClosed_epigraph {f : α → γ} :
    LowerSemicontinuous f ↔ IsClosed {p : α × γ | f p.1 ≤ p.2} := by
  constructor
  · rw [lowerSemicontinuous_iff_le_liminf, isClosed_iff_forall_filter]
    rintro hf ⟨x, y⟩ F F_ne h h'
    rw [nhds_prod_eq, le_prod] at h'
    calc f x ≤ liminf f (𝓝 x) := hf x
    _ ≤ liminf f (map Prod.fst F) := liminf_le_liminf_of_le h'.1
    _ = liminf (f ∘ Prod.fst) F := (Filter.liminf_comp _ _ _).symm
    _ ≤ liminf Prod.snd F := liminf_le_liminf <| by
          simpa using (eventually_principal.2 fun (_ : α × γ) ↦ id).filter_mono h
    _ = y := h'.2.liminf_eq
  · rw [lowerSemicontinuous_iff_isClosed_preimage]
    exact fun hf y ↦ hf.preimage (Continuous.Prod.mk_left y)

@[deprecated] -- 2024-03-02
alias lowerSemicontinuous_iff_IsClosed_epigraph := lowerSemicontinuous_iff_isClosed_epigraph

alias ⟨LowerSemicontinuous.isClosed_epigraph, _⟩ := lowerSemicontinuous_iff_isClosed_epigraph

@[deprecated] -- 2024-03-02
alias LowerSemicontinuous.IsClosed_epigraph := LowerSemicontinuous.isClosed_epigraph

end

/-! ### Composition -/


section

variable {γ : Type*} [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
variable {δ : Type*} [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]
variable {ι : Type*} [TopologicalSpace ι]

theorem ContinuousAt.comp_lowerSemicontinuousWithinAt {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousWithinAt f s x) (gmon : Monotone g) :
    LowerSemicontinuousWithinAt (g ∘ f) s x := by
  intro y hy
  by_cases h : ∃ l, l < f x
  · obtain ⟨z, zlt, hz⟩ : ∃ z < f x, Ioc z (f x) ⊆ g ⁻¹' Ioi y :=
      exists_Ioc_subset_of_mem_nhds (hg (Ioi_mem_nhds hy)) h
    filter_upwards [hf z zlt] with a ha
    calc
      y < g (min (f x) (f a)) := hz (by simp [zlt, ha, le_refl])
      _ ≤ g (f a) := gmon (min_le_right _ _)

  · simp only [not_exists, not_lt] at h
    exact Filter.eventually_of_forall fun a => hy.trans_le (gmon (h (f a)))
#align continuous_at.comp_lower_semicontinuous_within_at ContinuousAt.comp_lowerSemicontinuousWithinAt

theorem ContinuousAt.comp_lowerSemicontinuousAt {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : LowerSemicontinuousAt f x) (gmon : Monotone g) : LowerSemicontinuousAt (g ∘ f) x := by
  simp only [← lowerSemicontinuousWithinAt_univ_iff] at hf ⊢
  exact hg.comp_lowerSemicontinuousWithinAt hf gmon
#align continuous_at.comp_lower_semicontinuous_at ContinuousAt.comp_lowerSemicontinuousAt

theorem Continuous.comp_lowerSemicontinuousOn {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuousOn f s) (gmon : Monotone g) : LowerSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_lowerSemicontinuousWithinAt (hf x hx) gmon
#align continuous.comp_lower_semicontinuous_on Continuous.comp_lowerSemicontinuousOn

theorem Continuous.comp_lowerSemicontinuous {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuous f) (gmon : Monotone g) : LowerSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_lowerSemicontinuousAt (hf x) gmon
#align continuous.comp_lower_semicontinuous Continuous.comp_lowerSemicontinuous

theorem ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousWithinAt f s x) (gmon : Antitone g) :
    UpperSemicontinuousWithinAt (g ∘ f) s x :=
  @ContinuousAt.comp_lowerSemicontinuousWithinAt α _ x s γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon
#align continuous_at.comp_lower_semicontinuous_within_at_antitone ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone

theorem ContinuousAt.comp_lowerSemicontinuousAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousAt f x) (gmon : Antitone g) :
    UpperSemicontinuousAt (g ∘ f) x :=
  @ContinuousAt.comp_lowerSemicontinuousAt α _ x γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon
#align continuous_at.comp_lower_semicontinuous_at_antitone ContinuousAt.comp_lowerSemicontinuousAt_antitone

theorem Continuous.comp_lowerSemicontinuousOn_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuousOn f s) (gmon : Antitone g) : UpperSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_lowerSemicontinuousWithinAt_antitone (hf x hx) gmon
#align continuous.comp_lower_semicontinuous_on_antitone Continuous.comp_lowerSemicontinuousOn_antitone

theorem Continuous.comp_lowerSemicontinuous_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuous f) (gmon : Antitone g) : UpperSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_lowerSemicontinuousAt_antitone (hf x) gmon
#align continuous.comp_lower_semicontinuous_antitone Continuous.comp_lowerSemicontinuous_antitone

theorem LowerSemicontinuousAt.comp_continuousAt {f : α → β} {g : ι → α} {x : ι}
    (hf : LowerSemicontinuousAt f (g x)) (hg : ContinuousAt g x) :
    LowerSemicontinuousAt (fun x ↦ f (g x)) x :=
  fun _ lt ↦ hg.eventually (hf _ lt)

theorem LowerSemicontinuousAt.comp_continuousAt_of_eq {f : α → β} {g : ι → α} {y : α} {x : ι}
    (hf : LowerSemicontinuousAt f y) (hg : ContinuousAt g x) (hy : g x = y) :
    LowerSemicontinuousAt (fun x ↦ f (g x)) x := by
  rw [← hy] at hf
  exact comp_continuousAt hf hg

theorem LowerSemicontinuous.comp_continuous {f : α → β} {g : ι → α}
    (hf : LowerSemicontinuous f) (hg : Continuous g) : LowerSemicontinuous fun x ↦ f (g x) :=
  fun x ↦ (hf (g x)).comp_continuousAt hg.continuousAt

end

/-! #### Addition -/


section

variable {ι : Type*} {γ : Type*} [LinearOrderedAddCommMonoid γ] [TopologicalSpace γ]
  [OrderTopology γ]

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
theorem LowerSemicontinuousWithinAt.add' {f g : α → γ} (hf : LowerSemicontinuousWithinAt f s x)
    (hg : LowerSemicontinuousWithinAt g s x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousWithinAt (fun z => f z + g z) s x := by
  intro y hy
  obtain ⟨u, v, u_open, xu, v_open, xv, h⟩ :
    ∃ u v : Set γ,
      IsOpen u ∧ f x ∈ u ∧ IsOpen v ∧ g x ∈ v ∧ u ×ˢ v ⊆ { p : γ × γ | y < p.fst + p.snd } :=
    mem_nhds_prod_iff'.1 (hcont (isOpen_Ioi.mem_nhds hy))
  by_cases hx₁ : ∃ l, l < f x
  · obtain ⟨z₁, z₁lt, h₁⟩ : ∃ z₁ < f x, Ioc z₁ (f x) ⊆ u :=
      exists_Ioc_subset_of_mem_nhds (u_open.mem_nhds xu) hx₁
    by_cases hx₂ : ∃ l, l < g x
    · obtain ⟨z₂, z₂lt, h₂⟩ : ∃ z₂ < g x, Ioc z₂ (g x) ⊆ v :=
        exists_Ioc_subset_of_mem_nhds (v_open.mem_nhds xv) hx₂
      filter_upwards [hf z₁ z₁lt, hg z₂ z₂lt] with z h₁z h₂z
      have A1 : min (f z) (f x) ∈ u := by
        by_cases H : f z ≤ f x
        · simp [H]
          exact h₁ ⟨h₁z, H⟩
        · simp [le_of_not_le H]
          exact h₁ ⟨z₁lt, le_rfl⟩
      have A2 : min (g z) (g x) ∈ v := by
        by_cases H : g z ≤ g x
        · simp [H]
          exact h₂ ⟨h₂z, H⟩
        · simp [le_of_not_le H]
          exact h₂ ⟨z₂lt, le_rfl⟩
      have : (min (f z) (f x), min (g z) (g x)) ∈ u ×ˢ v := ⟨A1, A2⟩
      calc
        y < min (f z) (f x) + min (g z) (g x) := h this
        _ ≤ f z + g z := add_le_add (min_le_left _ _) (min_le_left _ _)

    · simp only [not_exists, not_lt] at hx₂
      filter_upwards [hf z₁ z₁lt] with z h₁z
      have A1 : min (f z) (f x) ∈ u := by
        by_cases H : f z ≤ f x
        · simp [H]
          exact h₁ ⟨h₁z, H⟩
        · simp [le_of_not_le H]
          exact h₁ ⟨z₁lt, le_rfl⟩
      have : (min (f z) (f x), g x) ∈ u ×ˢ v := ⟨A1, xv⟩
      calc
        y < min (f z) (f x) + g x := h this
        _ ≤ f z + g z := add_le_add (min_le_left _ _) (hx₂ (g z))

  · simp only [not_exists, not_lt] at hx₁
    by_cases hx₂ : ∃ l, l < g x
    · obtain ⟨z₂, z₂lt, h₂⟩ : ∃ z₂ < g x, Ioc z₂ (g x) ⊆ v :=
        exists_Ioc_subset_of_mem_nhds (v_open.mem_nhds xv) hx₂
      filter_upwards [hg z₂ z₂lt] with z h₂z
      have A2 : min (g z) (g x) ∈ v := by
        by_cases H : g z ≤ g x
        · simp [H]
          exact h₂ ⟨h₂z, H⟩
        · simp [le_of_not_le H]
          exact h₂ ⟨z₂lt, le_rfl⟩
      have : (f x, min (g z) (g x)) ∈ u ×ˢ v := ⟨xu, A2⟩
      calc
        y < f x + min (g z) (g x) := h this
        _ ≤ f z + g z := add_le_add (hx₁ (f z)) (min_le_left _ _)
    · simp only [not_exists, not_lt] at hx₁ hx₂
      apply Filter.eventually_of_forall
      intro z
      have : (f x, g x) ∈ u ×ˢ v := ⟨xu, xv⟩
      calc
        y < f x + g x := h this
        _ ≤ f z + g z := add_le_add (hx₁ (f z)) (hx₂ (g z))
#align lower_semicontinuous_within_at.add' LowerSemicontinuousWithinAt.add'

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
theorem LowerSemicontinuousAt.add' {f g : α → γ} (hf : LowerSemicontinuousAt f x)
    (hg : LowerSemicontinuousAt g x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousAt (fun z => f z + g z) x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.add' hg hcont
#align lower_semicontinuous_at.add' LowerSemicontinuousAt.add'

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
theorem LowerSemicontinuousOn.add' {f g : α → γ} (hf : LowerSemicontinuousOn f s)
    (hg : LowerSemicontinuousOn g s)
    (hcont : ∀ x ∈ s, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousOn (fun z => f z + g z) s := fun x hx =>
  (hf x hx).add' (hg x hx) (hcont x hx)
#align lower_semicontinuous_on.add' LowerSemicontinuousOn.add'

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
theorem LowerSemicontinuous.add' {f g : α → γ} (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g)
    (hcont : ∀ x, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuous fun z => f z + g z := fun x => (hf x).add' (hg x) (hcont x)
#align lower_semicontinuous.add' LowerSemicontinuous.add'

variable [ContinuousAdd γ]

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem LowerSemicontinuousWithinAt.add {f g : α → γ} (hf : LowerSemicontinuousWithinAt f s x)
    (hg : LowerSemicontinuousWithinAt g s x) :
    LowerSemicontinuousWithinAt (fun z => f z + g z) s x :=
  hf.add' hg continuous_add.continuousAt
#align lower_semicontinuous_within_at.add LowerSemicontinuousWithinAt.add

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem LowerSemicontinuousAt.add {f g : α → γ} (hf : LowerSemicontinuousAt f x)
    (hg : LowerSemicontinuousAt g x) : LowerSemicontinuousAt (fun z => f z + g z) x :=
  hf.add' hg continuous_add.continuousAt
#align lower_semicontinuous_at.add LowerSemicontinuousAt.add

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem LowerSemicontinuousOn.add {f g : α → γ} (hf : LowerSemicontinuousOn f s)
    (hg : LowerSemicontinuousOn g s) : LowerSemicontinuousOn (fun z => f z + g z) s :=
  hf.add' hg fun _x _hx => continuous_add.continuousAt
#align lower_semicontinuous_on.add LowerSemicontinuousOn.add

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem LowerSemicontinuous.add {f g : α → γ} (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g) : LowerSemicontinuous fun z => f z + g z :=
  hf.add' hg fun _x => continuous_add.continuousAt
#align lower_semicontinuous.add LowerSemicontinuous.add

theorem lowerSemicontinuousWithinAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun z => ∑ i ∈ a, f i z) s x := by
  classical
    induction' a using Finset.induction_on with i a ia IH
    · exact lowerSemicontinuousWithinAt_const
    · simp only [ia, Finset.sum_insert, not_false_iff]
      exact
        LowerSemicontinuousWithinAt.add (ha _ (Finset.mem_insert_self i a))
          (IH fun j ja => ha j (Finset.mem_insert_of_mem ja))
#align lower_semicontinuous_within_at_sum lowerSemicontinuousWithinAt_sum

theorem lowerSemicontinuousAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun z => ∑ i ∈ a, f i z) x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_sum ha
#align lower_semicontinuous_at_sum lowerSemicontinuousAt_sum

theorem lowerSemicontinuousOn_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun z => ∑ i ∈ a, f i z) s := fun x hx =>
  lowerSemicontinuousWithinAt_sum fun i hi => ha i hi x hx
#align lower_semicontinuous_on_sum lowerSemicontinuousOn_sum

theorem lowerSemicontinuous_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuous (f i)) : LowerSemicontinuous fun z => ∑ i ∈ a, f i z :=
  fun x => lowerSemicontinuousAt_sum fun i hi => ha i hi x
#align lower_semicontinuous_sum lowerSemicontinuous_sum

end

/-! #### Supremum -/


section

variable {ι : Sort*} {δ δ' : Type*} [CompleteLinearOrder δ] [ConditionallyCompleteLinearOrder δ']

theorem lowerSemicontinuousWithinAt_ciSup {f : ι → α → δ'}
    (bdd : ∀ᶠ y in 𝓝[s] x, BddAbove (range fun i => f i y))
    (h : ∀ i, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ i, f i x') s x := by
  cases isEmpty_or_nonempty ι
  · simpa only [iSup_of_empty'] using lowerSemicontinuousWithinAt_const
  · intro y hy
    rcases exists_lt_of_lt_ciSup hy with ⟨i, hi⟩
    filter_upwards [h i y hi, bdd] with y hy hy' using hy.trans_le (le_ciSup hy' i)
#align lower_semicontinuous_within_at_csupr lowerSemicontinuousWithinAt_ciSup

theorem lowerSemicontinuousWithinAt_iSup {f : ι → α → δ}
    (h : ∀ i, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ i, f i x') s x :=
  lowerSemicontinuousWithinAt_ciSup (by simp) h
#align lower_semicontinuous_within_at_supr lowerSemicontinuousWithinAt_iSup

theorem lowerSemicontinuousWithinAt_biSup {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, LowerSemicontinuousWithinAt (f i hi) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ (i) (hi), f i hi x') s x :=
  lowerSemicontinuousWithinAt_iSup fun i => lowerSemicontinuousWithinAt_iSup fun hi => h i hi
#align lower_semicontinuous_within_at_bsupr lowerSemicontinuousWithinAt_biSup

theorem lowerSemicontinuousAt_ciSup {f : ι → α → δ'}
    (bdd : ∀ᶠ y in 𝓝 x, BddAbove (range fun i => f i y)) (h : ∀ i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ⨆ i, f i x') x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  rw [← nhdsWithin_univ] at bdd
  exact lowerSemicontinuousWithinAt_ciSup bdd h
#align lower_semicontinuous_at_csupr lowerSemicontinuousAt_ciSup

theorem lowerSemicontinuousAt_iSup {f : ι → α → δ} (h : ∀ i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ⨆ i, f i x') x :=
  lowerSemicontinuousAt_ciSup (by simp) h
#align lower_semicontinuous_at_supr lowerSemicontinuousAt_iSup

theorem lowerSemicontinuousAt_biSup {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, LowerSemicontinuousAt (f i hi) x) :
    LowerSemicontinuousAt (fun x' => ⨆ (i) (hi), f i hi x') x :=
  lowerSemicontinuousAt_iSup fun i => lowerSemicontinuousAt_iSup fun hi => h i hi
#align lower_semicontinuous_at_bsupr lowerSemicontinuousAt_biSup

theorem lowerSemicontinuousOn_ciSup {f : ι → α → δ'}
    (bdd : ∀ x ∈ s, BddAbove (range fun i => f i x)) (h : ∀ i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ⨆ i, f i x') s := fun x hx =>
  lowerSemicontinuousWithinAt_ciSup (eventually_nhdsWithin_of_forall bdd) fun i => h i x hx
#align lower_semicontinuous_on_csupr lowerSemicontinuousOn_ciSup

theorem lowerSemicontinuousOn_iSup {f : ι → α → δ} (h : ∀ i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ⨆ i, f i x') s :=
  lowerSemicontinuousOn_ciSup (by simp) h
#align lower_semicontinuous_on_supr lowerSemicontinuousOn_iSup

theorem lowerSemicontinuousOn_biSup {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, LowerSemicontinuousOn (f i hi) s) :
    LowerSemicontinuousOn (fun x' => ⨆ (i) (hi), f i hi x') s :=
  lowerSemicontinuousOn_iSup fun i => lowerSemicontinuousOn_iSup fun hi => h i hi
#align lower_semicontinuous_on_bsupr lowerSemicontinuousOn_biSup

theorem lowerSemicontinuous_ciSup {f : ι → α → δ'} (bdd : ∀ x, BddAbove (range fun i => f i x))
    (h : ∀ i, LowerSemicontinuous (f i)) : LowerSemicontinuous fun x' => ⨆ i, f i x' := fun x =>
  lowerSemicontinuousAt_ciSup (eventually_of_forall bdd) fun i => h i x
#align lower_semicontinuous_csupr lowerSemicontinuous_ciSup

theorem lowerSemicontinuous_iSup {f : ι → α → δ} (h : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x' => ⨆ i, f i x' :=
  lowerSemicontinuous_ciSup (by simp) h
#align lower_semicontinuous_supr lowerSemicontinuous_iSup

theorem lowerSemicontinuous_biSup {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, LowerSemicontinuous (f i hi)) :
    LowerSemicontinuous fun x' => ⨆ (i) (hi), f i hi x' :=
  lowerSemicontinuous_iSup fun i => lowerSemicontinuous_iSup fun hi => h i hi
#align lower_semicontinuous_bsupr lowerSemicontinuous_biSup

end

/-! #### Infinite sums -/


section

variable {ι : Type*}

theorem lowerSemicontinuousWithinAt_tsum {f : ι → α → ℝ≥0∞}
    (h : ∀ i, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun x' => ∑' i, f i x') s x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  refine lowerSemicontinuousWithinAt_iSup fun b => ?_
  exact lowerSemicontinuousWithinAt_sum fun i _hi => h i
#align lower_semicontinuous_within_at_tsum lowerSemicontinuousWithinAt_tsum

theorem lowerSemicontinuousAt_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ∑' i, f i x') x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_tsum h
#align lower_semicontinuous_at_tsum lowerSemicontinuousAt_tsum

theorem lowerSemicontinuousOn_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ∑' i, f i x') s := fun x hx =>
  lowerSemicontinuousWithinAt_tsum fun i => h i x hx
#align lower_semicontinuous_on_tsum lowerSemicontinuousOn_tsum

theorem lowerSemicontinuous_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x' => ∑' i, f i x' := fun x => lowerSemicontinuousAt_tsum fun i => h i x
#align lower_semicontinuous_tsum lowerSemicontinuous_tsum

end

/-!
### Upper semicontinuous functions
-/


/-! #### Basic dot notation interface for upper semicontinuity -/


theorem UpperSemicontinuousWithinAt.mono (h : UpperSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    UpperSemicontinuousWithinAt f t x := fun y hy =>
  Filter.Eventually.filter_mono (nhdsWithin_mono _ hst) (h y hy)
#align upper_semicontinuous_within_at.mono UpperSemicontinuousWithinAt.mono

theorem upperSemicontinuousWithinAt_univ_iff :
    UpperSemicontinuousWithinAt f univ x ↔ UpperSemicontinuousAt f x := by
  simp [UpperSemicontinuousWithinAt, UpperSemicontinuousAt, nhdsWithin_univ]
#align upper_semicontinuous_within_at_univ_iff upperSemicontinuousWithinAt_univ_iff

theorem UpperSemicontinuousAt.upperSemicontinuousWithinAt (s : Set α)
    (h : UpperSemicontinuousAt f x) : UpperSemicontinuousWithinAt f s x := fun y hy =>
  Filter.Eventually.filter_mono nhdsWithin_le_nhds (h y hy)
#align upper_semicontinuous_at.upper_semicontinuous_within_at UpperSemicontinuousAt.upperSemicontinuousWithinAt

theorem UpperSemicontinuousOn.upperSemicontinuousWithinAt (h : UpperSemicontinuousOn f s)
    (hx : x ∈ s) : UpperSemicontinuousWithinAt f s x :=
  h x hx
#align upper_semicontinuous_on.upper_semicontinuous_within_at UpperSemicontinuousOn.upperSemicontinuousWithinAt

theorem UpperSemicontinuousOn.mono (h : UpperSemicontinuousOn f s) (hst : t ⊆ s) :
    UpperSemicontinuousOn f t := fun x hx => (h x (hst hx)).mono hst
#align upper_semicontinuous_on.mono UpperSemicontinuousOn.mono

theorem upperSemicontinuousOn_univ_iff : UpperSemicontinuousOn f univ ↔ UpperSemicontinuous f := by
  simp [UpperSemicontinuousOn, UpperSemicontinuous, upperSemicontinuousWithinAt_univ_iff]
#align upper_semicontinuous_on_univ_iff upperSemicontinuousOn_univ_iff

theorem UpperSemicontinuous.upperSemicontinuousAt (h : UpperSemicontinuous f) (x : α) :
    UpperSemicontinuousAt f x :=
  h x
#align upper_semicontinuous.upper_semicontinuous_at UpperSemicontinuous.upperSemicontinuousAt

theorem UpperSemicontinuous.upperSemicontinuousWithinAt (h : UpperSemicontinuous f) (s : Set α)
    (x : α) : UpperSemicontinuousWithinAt f s x :=
  (h x).upperSemicontinuousWithinAt s
#align upper_semicontinuous.upper_semicontinuous_within_at UpperSemicontinuous.upperSemicontinuousWithinAt

theorem UpperSemicontinuous.upperSemicontinuousOn (h : UpperSemicontinuous f) (s : Set α) :
    UpperSemicontinuousOn f s := fun x _hx => h.upperSemicontinuousWithinAt s x
#align upper_semicontinuous.upper_semicontinuous_on UpperSemicontinuous.upperSemicontinuousOn

/-! #### Constants -/


theorem upperSemicontinuousWithinAt_const : UpperSemicontinuousWithinAt (fun _x => z) s x :=
  fun _y hy => Filter.eventually_of_forall fun _x => hy
#align upper_semicontinuous_within_at_const upperSemicontinuousWithinAt_const

theorem upperSemicontinuousAt_const : UpperSemicontinuousAt (fun _x => z) x := fun _y hy =>
  Filter.eventually_of_forall fun _x => hy
#align upper_semicontinuous_at_const upperSemicontinuousAt_const

theorem upperSemicontinuousOn_const : UpperSemicontinuousOn (fun _x => z) s := fun _x _hx =>
  upperSemicontinuousWithinAt_const
#align upper_semicontinuous_on_const upperSemicontinuousOn_const

theorem upperSemicontinuous_const : UpperSemicontinuous fun _x : α => z := fun _x =>
  upperSemicontinuousAt_const
#align upper_semicontinuous_const upperSemicontinuous_const

/-! #### Indicators -/


section

variable [Zero β]

theorem IsOpen.upperSemicontinuous_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuous (indicator s fun _x => y) :=
  @IsOpen.lowerSemicontinuous_indicator α _ βᵒᵈ _ s y _ hs hy
#align is_open.upper_semicontinuous_indicator IsOpen.upperSemicontinuous_indicator

theorem IsOpen.upperSemicontinuousOn_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousOn t
#align is_open.upper_semicontinuous_on_indicator IsOpen.upperSemicontinuousOn_indicator

theorem IsOpen.upperSemicontinuousAt_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousAt x
#align is_open.upper_semicontinuous_at_indicator IsOpen.upperSemicontinuousAt_indicator

theorem IsOpen.upperSemicontinuousWithinAt_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousWithinAt t x
#align is_open.upper_semicontinuous_within_at_indicator IsOpen.upperSemicontinuousWithinAt_indicator

theorem IsClosed.upperSemicontinuous_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuous (indicator s fun _x => y) :=
  @IsClosed.lowerSemicontinuous_indicator α _ βᵒᵈ _ s y _ hs hy
#align is_closed.upper_semicontinuous_indicator IsClosed.upperSemicontinuous_indicator

theorem IsClosed.upperSemicontinuousOn_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousOn t
#align is_closed.upper_semicontinuous_on_indicator IsClosed.upperSemicontinuousOn_indicator

theorem IsClosed.upperSemicontinuousAt_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousAt x
#align is_closed.upper_semicontinuous_at_indicator IsClosed.upperSemicontinuousAt_indicator

theorem IsClosed.upperSemicontinuousWithinAt_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousWithinAt t x
#align is_closed.upper_semicontinuous_within_at_indicator IsClosed.upperSemicontinuousWithinAt_indicator

end

/-! #### Relationship with continuity -/


theorem upperSemicontinuous_iff_isOpen_preimage :
    UpperSemicontinuous f ↔ ∀ y, IsOpen (f ⁻¹' Iio y) :=
  ⟨fun H y => isOpen_iff_mem_nhds.2 fun x hx => H x y hx, fun H _x y y_lt =>
    IsOpen.mem_nhds (H y) y_lt⟩
#align upper_semicontinuous_iff_is_open_preimage upperSemicontinuous_iff_isOpen_preimage

theorem UpperSemicontinuous.isOpen_preimage (hf : UpperSemicontinuous f) (y : β) :
    IsOpen (f ⁻¹' Iio y) :=
  upperSemicontinuous_iff_isOpen_preimage.1 hf y
#align upper_semicontinuous.is_open_preimage UpperSemicontinuous.isOpen_preimage

section

variable {γ : Type*} [LinearOrder γ]

theorem upperSemicontinuous_iff_isClosed_preimage {f : α → γ} :
    UpperSemicontinuous f ↔ ∀ y, IsClosed (f ⁻¹' Ici y) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  simp only [← isOpen_compl_iff, ← preimage_compl, compl_Ici]
#align upper_semicontinuous_iff_is_closed_preimage upperSemicontinuous_iff_isClosed_preimage

theorem UpperSemicontinuous.isClosed_preimage {f : α → γ} (hf : UpperSemicontinuous f) (y : γ) :
    IsClosed (f ⁻¹' Ici y) :=
  upperSemicontinuous_iff_isClosed_preimage.1 hf y
#align upper_semicontinuous.is_closed_preimage UpperSemicontinuous.isClosed_preimage

variable [TopologicalSpace γ] [OrderTopology γ]

theorem ContinuousWithinAt.upperSemicontinuousWithinAt {f : α → γ} (h : ContinuousWithinAt f s x) :
    UpperSemicontinuousWithinAt f s x := fun _y hy => h (Iio_mem_nhds hy)
#align continuous_within_at.upper_semicontinuous_within_at ContinuousWithinAt.upperSemicontinuousWithinAt

theorem ContinuousAt.upperSemicontinuousAt {f : α → γ} (h : ContinuousAt f x) :
    UpperSemicontinuousAt f x := fun _y hy => h (Iio_mem_nhds hy)
#align continuous_at.upper_semicontinuous_at ContinuousAt.upperSemicontinuousAt

theorem ContinuousOn.upperSemicontinuousOn {f : α → γ} (h : ContinuousOn f s) :
    UpperSemicontinuousOn f s := fun x hx => (h x hx).upperSemicontinuousWithinAt
#align continuous_on.upper_semicontinuous_on ContinuousOn.upperSemicontinuousOn

theorem Continuous.upperSemicontinuous {f : α → γ} (h : Continuous f) : UpperSemicontinuous f :=
  fun _x => h.continuousAt.upperSemicontinuousAt
#align continuous.upper_semicontinuous Continuous.upperSemicontinuous

end

/-! #### Equivalent definitions -/

section

variable {γ : Type*} [CompleteLinearOrder γ] [DenselyOrdered γ]

theorem upperSemicontinuousWithinAt_iff_limsup_le {f : α → γ} :
    UpperSemicontinuousWithinAt f s x ↔ limsup f (𝓝[s] x) ≤ f x :=
  lowerSemicontinuousWithinAt_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuousWithinAt.limsup_le, _⟩ := upperSemicontinuousWithinAt_iff_limsup_le

theorem upperSemicontinuousAt_iff_limsup_le {f : α → γ} :
    UpperSemicontinuousAt f x ↔ limsup f (𝓝 x) ≤ f x :=
  lowerSemicontinuousAt_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuousAt.limsup_le, _⟩ := upperSemicontinuousAt_iff_limsup_le

theorem upperSemicontinuous_iff_limsup_le {f : α → γ} :
    UpperSemicontinuous f ↔ ∀ x, limsup f (𝓝 x) ≤ f x :=
  lowerSemicontinuous_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuous.limsup_le, _⟩ := upperSemicontinuous_iff_limsup_le

theorem upperSemicontinuousOn_iff_limsup_le {f : α → γ} :
    UpperSemicontinuousOn f s ↔ ∀ x ∈ s, limsup f (𝓝[s] x) ≤ f x :=
  lowerSemicontinuousOn_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuousOn.limsup_le, _⟩ := upperSemicontinuousOn_iff_limsup_le

variable [TopologicalSpace γ] [OrderTopology γ]

theorem upperSemicontinuous_iff_IsClosed_hypograph {f : α → γ} :
    UpperSemicontinuous f ↔ IsClosed {p : α × γ | p.2 ≤ f p.1} :=
  lowerSemicontinuous_iff_isClosed_epigraph (γ := γᵒᵈ)

alias ⟨UpperSemicontinuous.IsClosed_hypograph, _⟩ := upperSemicontinuous_iff_IsClosed_hypograph

end

/-! ### Composition -/

section

variable {γ : Type*} [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
variable {δ : Type*} [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]
variable {ι : Type*} [TopologicalSpace ι]

theorem ContinuousAt.comp_upperSemicontinuousWithinAt {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousWithinAt f s x) (gmon : Monotone g) :
    UpperSemicontinuousWithinAt (g ∘ f) s x :=
  @ContinuousAt.comp_lowerSemicontinuousWithinAt α _ x s γᵒᵈ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon.dual
#align continuous_at.comp_upper_semicontinuous_within_at ContinuousAt.comp_upperSemicontinuousWithinAt

theorem ContinuousAt.comp_upperSemicontinuousAt {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : UpperSemicontinuousAt f x) (gmon : Monotone g) : UpperSemicontinuousAt (g ∘ f) x :=
  @ContinuousAt.comp_lowerSemicontinuousAt α _ x γᵒᵈ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon.dual
#align continuous_at.comp_upper_semicontinuous_at ContinuousAt.comp_upperSemicontinuousAt

theorem Continuous.comp_upperSemicontinuousOn {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuousOn f s) (gmon : Monotone g) : UpperSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_upperSemicontinuousWithinAt (hf x hx) gmon
#align continuous.comp_upper_semicontinuous_on Continuous.comp_upperSemicontinuousOn

theorem Continuous.comp_upperSemicontinuous {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuous f) (gmon : Monotone g) : UpperSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_upperSemicontinuousAt (hf x) gmon
#align continuous.comp_upper_semicontinuous Continuous.comp_upperSemicontinuous

theorem ContinuousAt.comp_upperSemicontinuousWithinAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousWithinAt f s x) (gmon : Antitone g) :
    LowerSemicontinuousWithinAt (g ∘ f) s x :=
  @ContinuousAt.comp_upperSemicontinuousWithinAt α _ x s γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon
#align continuous_at.comp_upper_semicontinuous_within_at_antitone ContinuousAt.comp_upperSemicontinuousWithinAt_antitone

theorem ContinuousAt.comp_upperSemicontinuousAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousAt f x) (gmon : Antitone g) :
    LowerSemicontinuousAt (g ∘ f) x :=
  @ContinuousAt.comp_upperSemicontinuousAt α _ x γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon
#align continuous_at.comp_upper_semicontinuous_at_antitone ContinuousAt.comp_upperSemicontinuousAt_antitone

theorem Continuous.comp_upperSemicontinuousOn_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuousOn f s) (gmon : Antitone g) : LowerSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_upperSemicontinuousWithinAt_antitone (hf x hx) gmon
#align continuous.comp_upper_semicontinuous_on_antitone Continuous.comp_upperSemicontinuousOn_antitone

theorem Continuous.comp_upperSemicontinuous_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuous f) (gmon : Antitone g) : LowerSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_upperSemicontinuousAt_antitone (hf x) gmon
#align continuous.comp_upper_semicontinuous_antitone Continuous.comp_upperSemicontinuous_antitone

theorem UpperSemicontinuousAt.comp_continuousAt {f : α → β} {g : ι → α} {x : ι}
    (hf : UpperSemicontinuousAt f (g x)) (hg : ContinuousAt g x) :
    UpperSemicontinuousAt (fun x ↦ f (g x)) x :=
  fun _ lt ↦ hg.eventually (hf _ lt)

theorem UpperSemicontinuousAt.comp_continuousAt_of_eq {f : α → β} {g : ι → α} {y : α} {x : ι}
    (hf : UpperSemicontinuousAt f y) (hg : ContinuousAt g x) (hy : g x = y) :
    UpperSemicontinuousAt (fun x ↦ f (g x)) x := by
  rw [← hy] at hf
  exact comp_continuousAt hf hg

theorem UpperSemicontinuous.comp_continuous {f : α → β} {g : ι → α}
    (hf : UpperSemicontinuous f) (hg : Continuous g) : UpperSemicontinuous fun x ↦ f (g x) :=
  fun x ↦ (hf (g x)).comp_continuousAt hg.continuousAt

end

/-! #### Addition -/


section

variable {ι : Type*} {γ : Type*} [LinearOrderedAddCommMonoid γ] [TopologicalSpace γ]
  [OrderTopology γ]

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
theorem UpperSemicontinuousWithinAt.add' {f g : α → γ} (hf : UpperSemicontinuousWithinAt f s x)
    (hg : UpperSemicontinuousWithinAt g s x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousWithinAt (fun z => f z + g z) s x :=
  @LowerSemicontinuousWithinAt.add' α _ x s γᵒᵈ _ _ _ _ _ hf hg hcont
#align upper_semicontinuous_within_at.add' UpperSemicontinuousWithinAt.add'

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
theorem UpperSemicontinuousAt.add' {f g : α → γ} (hf : UpperSemicontinuousAt f x)
    (hg : UpperSemicontinuousAt g x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousAt (fun z => f z + g z) x := by
  simp_rw [← upperSemicontinuousWithinAt_univ_iff] at *
  exact hf.add' hg hcont
#align upper_semicontinuous_at.add' UpperSemicontinuousAt.add'

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
theorem UpperSemicontinuousOn.add' {f g : α → γ} (hf : UpperSemicontinuousOn f s)
    (hg : UpperSemicontinuousOn g s)
    (hcont : ∀ x ∈ s, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousOn (fun z => f z + g z) s := fun x hx =>
  (hf x hx).add' (hg x hx) (hcont x hx)
#align upper_semicontinuous_on.add' UpperSemicontinuousOn.add'

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
theorem UpperSemicontinuous.add' {f g : α → γ} (hf : UpperSemicontinuous f)
    (hg : UpperSemicontinuous g)
    (hcont : ∀ x, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuous fun z => f z + g z := fun x => (hf x).add' (hg x) (hcont x)
#align upper_semicontinuous.add' UpperSemicontinuous.add'

variable [ContinuousAdd γ]

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem UpperSemicontinuousWithinAt.add {f g : α → γ} (hf : UpperSemicontinuousWithinAt f s x)
    (hg : UpperSemicontinuousWithinAt g s x) :
    UpperSemicontinuousWithinAt (fun z => f z + g z) s x :=
  hf.add' hg continuous_add.continuousAt
#align upper_semicontinuous_within_at.add UpperSemicontinuousWithinAt.add

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem UpperSemicontinuousAt.add {f g : α → γ} (hf : UpperSemicontinuousAt f x)
    (hg : UpperSemicontinuousAt g x) : UpperSemicontinuousAt (fun z => f z + g z) x :=
  hf.add' hg continuous_add.continuousAt
#align upper_semicontinuous_at.add UpperSemicontinuousAt.add

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem UpperSemicontinuousOn.add {f g : α → γ} (hf : UpperSemicontinuousOn f s)
    (hg : UpperSemicontinuousOn g s) : UpperSemicontinuousOn (fun z => f z + g z) s :=
  hf.add' hg fun _x _hx => continuous_add.continuousAt
#align upper_semicontinuous_on.add UpperSemicontinuousOn.add

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem UpperSemicontinuous.add {f g : α → γ} (hf : UpperSemicontinuous f)
    (hg : UpperSemicontinuous g) : UpperSemicontinuous fun z => f z + g z :=
  hf.add' hg fun _x => continuous_add.continuousAt
#align upper_semicontinuous.add UpperSemicontinuous.add

theorem upperSemicontinuousWithinAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun z => ∑ i ∈ a, f i z) s x :=
  @lowerSemicontinuousWithinAt_sum α _ x s ι γᵒᵈ _ _ _ _ f a ha
#align upper_semicontinuous_within_at_sum upperSemicontinuousWithinAt_sum

theorem upperSemicontinuousAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun z => ∑ i ∈ a, f i z) x := by
  simp_rw [← upperSemicontinuousWithinAt_univ_iff] at *
  exact upperSemicontinuousWithinAt_sum ha
#align upper_semicontinuous_at_sum upperSemicontinuousAt_sum

theorem upperSemicontinuousOn_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun z => ∑ i ∈ a, f i z) s := fun x hx =>
  upperSemicontinuousWithinAt_sum fun i hi => ha i hi x hx
#align upper_semicontinuous_on_sum upperSemicontinuousOn_sum

theorem upperSemicontinuous_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuous (f i)) : UpperSemicontinuous fun z => ∑ i ∈ a, f i z :=
  fun x => upperSemicontinuousAt_sum fun i hi => ha i hi x
#align upper_semicontinuous_sum upperSemicontinuous_sum

end

/-! #### Infimum -/


section

variable {ι : Sort*} {δ δ' : Type*} [CompleteLinearOrder δ] [ConditionallyCompleteLinearOrder δ']

theorem upperSemicontinuousWithinAt_ciInf {f : ι → α → δ'}
    (bdd : ∀ᶠ y in 𝓝[s] x, BddBelow (range fun i => f i y))
    (h : ∀ i, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ i, f i x') s x :=
  @lowerSemicontinuousWithinAt_ciSup α _ x s ι δ'ᵒᵈ _ f bdd h
#align upper_semicontinuous_within_at_cinfi upperSemicontinuousWithinAt_ciInf

theorem upperSemicontinuousWithinAt_iInf {f : ι → α → δ}
    (h : ∀ i, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ i, f i x') s x :=
  @lowerSemicontinuousWithinAt_iSup α _ x s ι δᵒᵈ _ f h
#align upper_semicontinuous_within_at_infi upperSemicontinuousWithinAt_iInf

theorem upperSemicontinuousWithinAt_biInf {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, UpperSemicontinuousWithinAt (f i hi) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ (i) (hi), f i hi x') s x :=
  upperSemicontinuousWithinAt_iInf fun i => upperSemicontinuousWithinAt_iInf fun hi => h i hi
#align upper_semicontinuous_within_at_binfi upperSemicontinuousWithinAt_biInf

theorem upperSemicontinuousAt_ciInf {f : ι → α → δ'}
    (bdd : ∀ᶠ y in 𝓝 x, BddBelow (range fun i => f i y)) (h : ∀ i, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun x' => ⨅ i, f i x') x :=
  @lowerSemicontinuousAt_ciSup α _ x ι δ'ᵒᵈ _ f bdd h
#align upper_semicontinuous_at_cinfi upperSemicontinuousAt_ciInf

theorem upperSemicontinuousAt_iInf {f : ι → α → δ} (h : ∀ i, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun x' => ⨅ i, f i x') x :=
  @lowerSemicontinuousAt_iSup α _ x ι δᵒᵈ _ f h
#align upper_semicontinuous_at_infi upperSemicontinuousAt_iInf

theorem upperSemicontinuousAt_biInf {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, UpperSemicontinuousAt (f i hi) x) :
    UpperSemicontinuousAt (fun x' => ⨅ (i) (hi), f i hi x') x :=
  upperSemicontinuousAt_iInf fun i => upperSemicontinuousAt_iInf fun hi => h i hi
#align upper_semicontinuous_at_binfi upperSemicontinuousAt_biInf

theorem upperSemicontinuousOn_ciInf {f : ι → α → δ'}
    (bdd : ∀ x ∈ s, BddBelow (range fun i => f i x)) (h : ∀ i, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun x' => ⨅ i, f i x') s := fun x hx =>
  upperSemicontinuousWithinAt_ciInf (eventually_nhdsWithin_of_forall bdd) fun i => h i x hx
#align upper_semicontinuous_on_cinfi upperSemicontinuousOn_ciInf

theorem upperSemicontinuousOn_iInf {f : ι → α → δ} (h : ∀ i, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun x' => ⨅ i, f i x') s := fun x hx =>
  upperSemicontinuousWithinAt_iInf fun i => h i x hx
#align upper_semicontinuous_on_infi upperSemicontinuousOn_iInf

theorem upperSemicontinuousOn_biInf {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, UpperSemicontinuousOn (f i hi) s) :
    UpperSemicontinuousOn (fun x' => ⨅ (i) (hi), f i hi x') s :=
  upperSemicontinuousOn_iInf fun i => upperSemicontinuousOn_iInf fun hi => h i hi
#align upper_semicontinuous_on_binfi upperSemicontinuousOn_biInf

theorem upperSemicontinuous_ciInf {f : ι → α → δ'} (bdd : ∀ x, BddBelow (range fun i => f i x))
    (h : ∀ i, UpperSemicontinuous (f i)) : UpperSemicontinuous fun x' => ⨅ i, f i x' := fun x =>
  upperSemicontinuousAt_ciInf (eventually_of_forall bdd) fun i => h i x
#align upper_semicontinuous_cinfi upperSemicontinuous_ciInf

theorem upperSemicontinuous_iInf {f : ι → α → δ} (h : ∀ i, UpperSemicontinuous (f i)) :
    UpperSemicontinuous fun x' => ⨅ i, f i x' := fun x => upperSemicontinuousAt_iInf fun i => h i x
#align upper_semicontinuous_infi upperSemicontinuous_iInf

theorem upperSemicontinuous_biInf {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, UpperSemicontinuous (f i hi)) :
    UpperSemicontinuous fun x' => ⨅ (i) (hi), f i hi x' :=
  upperSemicontinuous_iInf fun i => upperSemicontinuous_iInf fun hi => h i hi
#align upper_semicontinuous_binfi upperSemicontinuous_biInf

end

section

variable {γ : Type*} [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]

theorem continuousWithinAt_iff_lower_upperSemicontinuousWithinAt {f : α → γ} :
    ContinuousWithinAt f s x ↔
      LowerSemicontinuousWithinAt f s x ∧ UpperSemicontinuousWithinAt f s x := by
  refine ⟨fun h => ⟨h.lowerSemicontinuousWithinAt, h.upperSemicontinuousWithinAt⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  intro v hv
  simp only [Filter.mem_map]
  by_cases Hl : ∃ l, l < f x
  · rcases exists_Ioc_subset_of_mem_nhds hv Hl with ⟨l, lfx, hl⟩
    by_cases Hu : ∃ u, f x < u
    · rcases exists_Ico_subset_of_mem_nhds hv Hu with ⟨u, fxu, hu⟩
      filter_upwards [h₁ l lfx, h₂ u fxu] with a lfa fau
      cases' le_or_gt (f a) (f x) with h h
      · exact hl ⟨lfa, h⟩
      · exact hu ⟨le_of_lt h, fau⟩
    · simp only [not_exists, not_lt] at Hu
      filter_upwards [h₁ l lfx] with a lfa using hl ⟨lfa, Hu (f a)⟩
  · simp only [not_exists, not_lt] at Hl
    by_cases Hu : ∃ u, f x < u
    · rcases exists_Ico_subset_of_mem_nhds hv Hu with ⟨u, fxu, hu⟩
      filter_upwards [h₂ u fxu] with a lfa
      apply hu
      exact ⟨Hl (f a), lfa⟩
    · simp only [not_exists, not_lt] at Hu
      apply Filter.eventually_of_forall
      intro a
      have : f a = f x := le_antisymm (Hu _) (Hl _)
      rw [this]
      exact mem_of_mem_nhds hv
#align continuous_within_at_iff_lower_upper_semicontinuous_within_at continuousWithinAt_iff_lower_upperSemicontinuousWithinAt

theorem continuousAt_iff_lower_upperSemicontinuousAt {f : α → γ} :
    ContinuousAt f x ↔ LowerSemicontinuousAt f x ∧ UpperSemicontinuousAt f x := by
  simp_rw [← continuousWithinAt_univ, ← lowerSemicontinuousWithinAt_univ_iff, ←
    upperSemicontinuousWithinAt_univ_iff, continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
#align continuous_at_iff_lower_upper_semicontinuous_at continuousAt_iff_lower_upperSemicontinuousAt

theorem continuousOn_iff_lower_upperSemicontinuousOn {f : α → γ} :
    ContinuousOn f s ↔ LowerSemicontinuousOn f s ∧ UpperSemicontinuousOn f s := by
  simp only [ContinuousOn, continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
  exact
    ⟨fun H => ⟨fun x hx => (H x hx).1, fun x hx => (H x hx).2⟩, fun H x hx => ⟨H.1 x hx, H.2 x hx⟩⟩
#align continuous_on_iff_lower_upper_semicontinuous_on continuousOn_iff_lower_upperSemicontinuousOn

theorem continuous_iff_lower_upperSemicontinuous {f : α → γ} :
    Continuous f ↔ LowerSemicontinuous f ∧ UpperSemicontinuous f := by
  simp_rw [continuous_iff_continuousOn_univ, continuousOn_iff_lower_upperSemicontinuousOn,
    lowerSemicontinuousOn_univ_iff, upperSemicontinuousOn_univ_iff]
#align continuous_iff_lower_upper_semicontinuous continuous_iff_lower_upperSemicontinuous

end
