/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Antoine Chambert-Loir, Anatole Dedecker
-/
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Semicontinuous maps

A function `f` from a topological space `α` to an ordered space `β` is lower semicontinuous at a
point `x` if, for any `y < f x`, for any `x'` close enough to `x`, one has `f x' > y`. In other
words, `f` can jump up, but it cannot jump down.

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
* `lowerSemicontinuousAt_iff_le_liminf` in a complete linear order;
* `lowerSemicontinuous_iff_isClosed_epigraph` in a linear order with the order
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

/-- A real function `f` is lower semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at least `f x - ε`. We formulate this in
a general preordered space, using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuousOn (f : α → β) (s : Set α) :=
  ∀ x ∈ s, LowerSemicontinuousWithinAt f s x

/-- A real function `f` is lower semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuousAt (f : α → β) (x : α) :=
  ∀ y < f x, ∀ᶠ x' in 𝓝 x, y < f x'

/-- A real function `f` is lower semicontinuous if, for any `ε > 0`, for any `x`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuous (f : α → β) :=
  ∀ x, LowerSemicontinuousAt f x

/-- A real function `f` is upper semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We formulate this in a general
preordered space, using an arbitrary `y > f x` instead of `f x + ε`. -/
def UpperSemicontinuousWithinAt (f : α → β) (s : Set α) (x : α) :=
  ∀ y, f x < y → ∀ᶠ x' in 𝓝[s] x, f x' < y

/-- A real function `f` is upper semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We formulate this in a
general preordered space, using an arbitrary `y > f x` instead of `f x + ε`. -/
def UpperSemicontinuousOn (f : α → β) (s : Set α) :=
  ∀ x ∈ s, UpperSemicontinuousWithinAt f s x

/-- A real function `f` is upper semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered space,
using an arbitrary `y > f x` instead of `f x + ε`. -/
def UpperSemicontinuousAt (f : α → β) (x : α) :=
  ∀ y, f x < y → ∀ᶠ x' in 𝓝 x, f x' < y

/-- A real function `f` is upper semicontinuous if, for any `ε > 0`, for any `x`, for all `x'`
close enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered
space, using an arbitrary `y > f x` instead of `f x + ε`. -/
def UpperSemicontinuous (f : α → β) :=
  ∀ x, UpperSemicontinuousAt f x

/-!
### Lower semicontinuous functions
-/


/-! #### Basic dot notation interface for lower semicontinuity -/


theorem LowerSemicontinuousWithinAt.mono (h : LowerSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    LowerSemicontinuousWithinAt f t x := fun y hy =>
  Filter.Eventually.filter_mono (nhdsWithin_mono _ hst) (h y hy)

theorem LowerSemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : LowerSemicontinuousWithinAt f s a)
    (has : a ∈ s) (hfg : ∀ᶠ x in nhdsWithin a s, f x = g x) :
    LowerSemicontinuousWithinAt g s a := by
  intro b hb
  rw [← Filter.EventuallyEq.eq_of_nhdsWithin hfg has] at hb
  exact EventuallyEq.rw hfg _ (h b hb)

theorem lowerSemicontinuousWithinAt_univ_iff :
    LowerSemicontinuousWithinAt f univ x ↔ LowerSemicontinuousAt f x := by
  simp [LowerSemicontinuousWithinAt, LowerSemicontinuousAt, nhdsWithin_univ]

theorem LowerSemicontinuousAt.lowerSemicontinuousWithinAt (s : Set α)
    (h : LowerSemicontinuousAt f x) : LowerSemicontinuousWithinAt f s x := fun y hy =>
  Filter.Eventually.filter_mono nhdsWithin_le_nhds (h y hy)

theorem LowerSemicontinuousOn.lowerSemicontinuousWithinAt (h : LowerSemicontinuousOn f s)
    (hx : x ∈ s) : LowerSemicontinuousWithinAt f s x :=
  h x hx

theorem LowerSemicontinuousOn.mono (h : LowerSemicontinuousOn f s) (hst : t ⊆ s) :
    LowerSemicontinuousOn f t := fun x hx => (h x (hst hx)).mono hst

theorem lowerSemicontinuousOn_univ_iff : LowerSemicontinuousOn f univ ↔ LowerSemicontinuous f := by
  simp [LowerSemicontinuousOn, LowerSemicontinuous, lowerSemicontinuousWithinAt_univ_iff]

@[simp] theorem lowerSemicontinuous_restrict_iff :
    LowerSemicontinuous (s.restrict f) ↔ LowerSemicontinuousOn f s := by
  rw [LowerSemicontinuousOn, LowerSemicontinuous, SetCoe.forall]
  refine forall₂_congr fun a ha ↦ forall₂_congr fun b _ ↦ ?_
  simp only [nhdsWithin_eq_map_subtype_coe ha, eventually_map, restrict]

theorem LowerSemicontinuous.lowerSemicontinuousAt (h : LowerSemicontinuous f) (x : α) :
    LowerSemicontinuousAt f x :=
  h x

theorem LowerSemicontinuous.lowerSemicontinuousWithinAt (h : LowerSemicontinuous f) (s : Set α)
    (x : α) : LowerSemicontinuousWithinAt f s x :=
  (h x).lowerSemicontinuousWithinAt s

theorem LowerSemicontinuous.lowerSemicontinuousOn (h : LowerSemicontinuous f) (s : Set α) :
    LowerSemicontinuousOn f s := fun x _hx => h.lowerSemicontinuousWithinAt s x

/-! #### Constants -/


theorem lowerSemicontinuousWithinAt_const : LowerSemicontinuousWithinAt (fun _x => z) s x :=
  fun _y hy => Filter.Eventually.of_forall fun _x => hy

theorem lowerSemicontinuousAt_const : LowerSemicontinuousAt (fun _x => z) x := fun _y hy =>
  Filter.Eventually.of_forall fun _x => hy

theorem lowerSemicontinuousOn_const : LowerSemicontinuousOn (fun _x => z) s := fun _x _hx =>
  lowerSemicontinuousWithinAt_const

theorem lowerSemicontinuous_const : LowerSemicontinuous fun _x : α => z := fun _x =>
  lowerSemicontinuousAt_const

/-! ### lower bounds -/

section

variable {α : Type*} [TopologicalSpace α] {β : Type*} [LinearOrder β] {f : α → β} {s : Set α}

/-- A lower semicontinuous function attains its lower bound on a nonempty compact set. -/
theorem LowerSemicontinuousOn.exists_isMinOn {s : Set α} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : LowerSemicontinuousOn f s) :
    ∃ a ∈ s, IsMinOn f s a := by
--  hf.exists_forall_le_of_isCompact ne_s hs
  simp only [isMinOn_iff]
  have _ : Nonempty α := Exists.nonempty ne_s
  have _ : Nonempty s := Nonempty.to_subtype ne_s
  let φ : β → Filter α := fun b ↦ 𝓟 (s ∩ f ⁻¹' Iic b)
  let ℱ : Filter α := ⨅ a : s, φ (f a)
  have : ℱ.NeBot := by
    apply iInf_neBot_of_directed _ _
    · change Directed GE.ge (fun x ↦ (φ ∘ (fun (a : s) ↦ f ↑a)) x)
      exact Directed.mono_comp GE.ge (fun x y hxy ↦
          principal_mono.mpr (inter_subset_inter_right _ (preimage_mono <| Iic_subset_Iic.mpr hxy))
        ) (IsTotal.directed _)
    · intro x
      have : (pure x : Filter α) ≤ φ (f x) := le_principal_iff.mpr ⟨x.2, le_refl (f x)⟩
      exact neBot_of_le this
  have hℱs : ℱ ≤ 𝓟 s :=
    iInf_le_of_le (Classical.choice inferInstance) (principal_mono.mpr <| inter_subset_left)
  have hℱ (x) (hx : x ∈ s) : ∀ᶠ y in ℱ, f y ≤ f x :=
    mem_iInf_of_mem ⟨x, hx⟩ (by apply inter_subset_right)
  obtain ⟨a, ha, h⟩ := hs hℱs
  refine ⟨a, ha, fun x hx ↦ le_of_not_gt fun hxa ↦ ?_⟩
  let _ : (𝓝 a ⊓ ℱ).NeBot := h
  suffices ∀ᶠ _ in 𝓝 a ⊓ ℱ, False by rwa [eventually_const] at this
  filter_upwards [(hf a ha (f x) hxa).filter_mono (inf_le_inf_left _ hℱs),
    (hℱ x hx).filter_mono (inf_le_right : 𝓝 a ⊓ ℱ ≤ ℱ)] using fun y h₁ h₂ ↦ not_le_of_gt h₁ h₂

/-- A lower semicontinuous function is bounded below on a compact set. -/
theorem LowerSemicontinuousOn.bddBelow_of_isCompact [Nonempty β] {s : Set α} (hs : IsCompact s)
    (hf : LowerSemicontinuousOn f s) : BddBelow (f '' s) := by
  cases s.eq_empty_or_nonempty with
  | inl h =>
      simp only [h, Set.image_empty]
      exact bddBelow_empty
  | inr h =>
      obtain ⟨a, _, has⟩ := LowerSemicontinuousOn.exists_isMinOn h hs hf
      exact has.bddBelow

end

/-! #### Indicators -/


section

variable [Zero β]

theorem IsOpen.lowerSemicontinuous_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuous (indicator s fun _x => y) := by
  intro x z hz
  by_cases h : x ∈ s <;> simp [h] at hz
  · filter_upwards [hs.mem_nhds h]
    simp +contextual [hz]
  · refine Filter.Eventually.of_forall fun x' => ?_
    by_cases h' : x' ∈ s <;> simp [h', hz.trans_le hy, hz]

theorem IsOpen.lowerSemicontinuousOn_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousOn t

theorem IsOpen.lowerSemicontinuousAt_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousAt x

theorem IsOpen.lowerSemicontinuousWithinAt_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousWithinAt t x

theorem IsClosed.lowerSemicontinuous_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuous (indicator s fun _x => y) := by
  intro x z hz
  by_cases h : x ∈ s <;> simp [h] at hz
  · refine Filter.Eventually.of_forall fun x' => ?_
    by_cases h' : x' ∈ s <;> simp [h', hz, hz.trans_le hy]
  · filter_upwards [hs.isOpen_compl.mem_nhds h]
    simp +contextual [hz]

theorem IsClosed.lowerSemicontinuousOn_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousOn t

theorem IsClosed.lowerSemicontinuousAt_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousAt x

theorem IsClosed.lowerSemicontinuousWithinAt_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousWithinAt t x

end

/-! #### Relationship with continuity -/


theorem lowerSemicontinuous_iff_isOpen_preimage :
    LowerSemicontinuous f ↔ ∀ y, IsOpen (f ⁻¹' Ioi y) :=
  ⟨fun H y => isOpen_iff_mem_nhds.2 fun x hx => H x y hx, fun H _x y y_lt =>
    IsOpen.mem_nhds (H y) y_lt⟩

theorem LowerSemicontinuous.isOpen_preimage (hf : LowerSemicontinuous f) (y : β) :
    IsOpen (f ⁻¹' Ioi y) :=
  lowerSemicontinuous_iff_isOpen_preimage.1 hf y

theorem lowerSemicontinuousOn_iff_preimage_Ioi :
    LowerSemicontinuousOn f s ↔ ∀ b, ∃ u, IsOpen u ∧ s ∩ f ⁻¹' Set.Ioi b = s ∩ u := by
  simp only [← lowerSemicontinuous_restrict_iff, restrict_eq,
    lowerSemicontinuous_iff_isOpen_preimage, preimage_comp, isOpen_induced_iff,
    Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

section

variable {γ : Type*} [LinearOrder γ]

theorem lowerSemicontinuous_iff_isClosed_preimage {f : α → γ} :
    LowerSemicontinuous f ↔ ∀ y, IsClosed (f ⁻¹' Iic y) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  simp only [← isOpen_compl_iff, ← preimage_compl, compl_Iic]

theorem LowerSemicontinuous.isClosed_preimage {f : α → γ} (hf : LowerSemicontinuous f) (y : γ) :
    IsClosed (f ⁻¹' Iic y) :=
  lowerSemicontinuous_iff_isClosed_preimage.1 hf y

theorem lowerSemicontinuousOn_iff_preimage_Iic {f : α → γ} :
    LowerSemicontinuousOn f s ↔ ∀ b, ∃ v, IsClosed v ∧ s ∩ f ⁻¹' Set.Iic b = s ∩ v := by
  simp only [← lowerSemicontinuous_restrict_iff, restrict_eq,
      lowerSemicontinuous_iff_isClosed_preimage, preimage_comp,
      isClosed_induced_iff, Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

variable [TopologicalSpace γ] [OrderTopology γ]

theorem ContinuousWithinAt.lowerSemicontinuousWithinAt {f : α → γ} (h : ContinuousWithinAt f s x) :
    LowerSemicontinuousWithinAt f s x := fun _y hy => h (Ioi_mem_nhds hy)

theorem ContinuousAt.lowerSemicontinuousAt {f : α → γ} (h : ContinuousAt f x) :
    LowerSemicontinuousAt f x := fun _y hy => h (Ioi_mem_nhds hy)

theorem ContinuousOn.lowerSemicontinuousOn {f : α → γ} (h : ContinuousOn f s) :
    LowerSemicontinuousOn f s := fun x hx => (h x hx).lowerSemicontinuousWithinAt

theorem Continuous.lowerSemicontinuous {f : α → γ} (h : Continuous f) : LowerSemicontinuous f :=
  fun _x => h.continuousAt.lowerSemicontinuousAt

end

/-! #### Equivalent definitions -/

section

variable {γ : Type*} [CompleteLinearOrder γ]

theorem lowerSemicontinuousWithinAt_iff_le_liminf {f : α → γ} :
    LowerSemicontinuousWithinAt f s x ↔ f x ≤ liminf f (𝓝[s] x) := by
  constructor
  · intro hf; unfold LowerSemicontinuousWithinAt at hf
    contrapose! hf
    obtain ⟨z, ltz, y, ylt, h₁⟩ := hf.exists_disjoint_Iio_Ioi; use y
    exact ⟨ylt, fun h => ltz.not_ge
      (le_liminf_of_le (by isBoundedDefault) (h.mono fun _ h₂ =>
        le_of_not_gt fun h₃ => (h₁ _ h₃ _ h₂).false))⟩
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

end

section

variable {γ : Type*} [LinearOrder γ] [TopologicalSpace γ] [ClosedIciTopology γ]

theorem lowerSemicontinuousOn_iff_isClosed_epigraph {f : α → γ} {s : Set α} (hs : IsClosed s) :
    LowerSemicontinuousOn f s ↔ IsClosed {p : α × γ | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  simp_rw [LowerSemicontinuousOn, LowerSemicontinuousWithinAt, eventually_nhdsWithin_iff,
    ← isOpen_compl_iff, compl_setOf, isOpen_iff_eventually, mem_setOf, not_and, not_le]
  constructor
  · intro hf ⟨x, y⟩ h
    by_cases hx : x ∈ s
    · have ⟨y', hy', z, hz, h₁⟩ := (h hx).exists_disjoint_Iio_Ioi
      filter_upwards [(hf x hx z hz).prodMk_nhds (eventually_lt_nhds hy')]
        with _ ⟨h₂, h₃⟩ h₄ using h₁ _ h₃ _ <| h₂ h₄
    · filter_upwards [(continuous_fst.tendsto _).eventually (hs.isOpen_compl.eventually_mem hx)]
        with _ h₁ h₂ using (h₁ h₂).elim
  · intro hf x _ y hy
    exact ((Continuous.prodMk_left y).tendsto x).eventually (hf (x, y) (fun _ => hy))

theorem lowerSemicontinuous_iff_isClosed_epigraph {f : α → γ} :
    LowerSemicontinuous f ↔ IsClosed {p : α × γ | f p.1 ≤ p.2} := by
  simp [← lowerSemicontinuousOn_univ_iff, lowerSemicontinuousOn_iff_isClosed_epigraph]

alias ⟨LowerSemicontinuous.isClosed_epigraph, _⟩ := lowerSemicontinuous_iff_isClosed_epigraph

end

/-! ### Composition -/

section

variable {α β : Type*} [Preorder β] {f g : α → β} {s : Set α} {a : α}

variable [TopologicalSpace α]

variable {γ : Type*} [TopologicalSpace γ] {g : γ → α} {x : γ} {t : Set γ}

theorem LowerSemicontinuousWithinAt.comp
    (hf : LowerSemicontinuousWithinAt f s (g x)) (hg : ContinuousWithinAt g t x)
    (hg' : MapsTo g t s) :
    LowerSemicontinuousWithinAt (f ∘ g) t x := fun b hb ↦
  (hg.tendsto_nhdsWithin hg').eventually (hf b hb)

theorem LowerSemicontinuousAt.comp
    (hf : LowerSemicontinuousAt f (g x)) (hg : ContinuousAt g x) :
    LowerSemicontinuousAt (f ∘ g) x := fun b hb ↦
  hg.eventually (hf b hb)

theorem LowerSemicontinuousOn.comp
    (hf : LowerSemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    LowerSemicontinuousOn (f ∘ g) t := fun x hx ↦
  (hf (g x) (hg' hx)).comp (hg x hx) hg'

theorem LowerSemicontinuous.comp
    (hf : LowerSemicontinuous f) (hg : Continuous g) : LowerSemicontinuous (f ∘ g) := fun x ↦
  (hf (g x)).comp hg.continuousAt

end

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
      y < g (min (f x) (f a)) := hz (by simp [zlt, ha])
      _ ≤ g (f a) := gmon (min_le_right _ _)
  · simp only [not_exists, not_lt] at h
    exact Filter.Eventually.of_forall fun a => hy.trans_le (gmon (h (f a)))

theorem ContinuousAt.comp_lowerSemicontinuousAt {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : LowerSemicontinuousAt f x) (gmon : Monotone g) : LowerSemicontinuousAt (g ∘ f) x := by
  simp only [← lowerSemicontinuousWithinAt_univ_iff] at hf ⊢
  exact hg.comp_lowerSemicontinuousWithinAt hf gmon

theorem Continuous.comp_lowerSemicontinuousOn {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuousOn f s) (gmon : Monotone g) : LowerSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_lowerSemicontinuousWithinAt (hf x hx) gmon

theorem Continuous.comp_lowerSemicontinuous {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuous f) (gmon : Monotone g) : LowerSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_lowerSemicontinuousAt (hf x) gmon

theorem ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousWithinAt f s x) (gmon : Antitone g) :
    UpperSemicontinuousWithinAt (g ∘ f) s x :=
  @ContinuousAt.comp_lowerSemicontinuousWithinAt α _ x s γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon

theorem ContinuousAt.comp_lowerSemicontinuousAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousAt f x) (gmon : Antitone g) :
    UpperSemicontinuousAt (g ∘ f) x :=
  @ContinuousAt.comp_lowerSemicontinuousAt α _ x γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon

theorem Continuous.comp_lowerSemicontinuousOn_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuousOn f s) (gmon : Antitone g) : UpperSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_lowerSemicontinuousWithinAt_antitone (hf x hx) gmon

theorem Continuous.comp_lowerSemicontinuous_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuous f) (gmon : Antitone g) : UpperSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_lowerSemicontinuousAt_antitone (hf x) gmon

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

variable {ι : Type*} {γ : Type*} [AddCommMonoid γ] [LinearOrder γ] [IsOrderedAddMonoid γ]
  [TopologicalSpace γ] [OrderTopology γ]

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
        · simpa [H] using h₁ ⟨h₁z, H⟩
        · simpa [le_of_not_ge H]
      have A2 : min (g z) (g x) ∈ v := by
        by_cases H : g z ≤ g x
        · simpa [H] using h₂ ⟨h₂z, H⟩
        · simpa [le_of_not_ge H]
      have : (min (f z) (f x), min (g z) (g x)) ∈ u ×ˢ v := ⟨A1, A2⟩
      calc
        y < min (f z) (f x) + min (g z) (g x) := h this
        _ ≤ f z + g z := add_le_add (min_le_left _ _) (min_le_left _ _)
    · simp only [not_exists, not_lt] at hx₂
      filter_upwards [hf z₁ z₁lt] with z h₁z
      have A1 : min (f z) (f x) ∈ u := by
        by_cases H : f z ≤ f x
        · simpa [H] using h₁ ⟨h₁z, H⟩
        · simpa [le_of_not_ge H]
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
        · simpa [H] using h₂ ⟨h₂z, H⟩
        · simpa [le_of_not_ge H] using h₂ ⟨z₂lt, le_rfl⟩
      have : (f x, min (g z) (g x)) ∈ u ×ˢ v := ⟨xu, A2⟩
      calc
        y < f x + min (g z) (g x) := h this
        _ ≤ f z + g z := add_le_add (hx₁ (f z)) (min_le_left _ _)
    · simp only [not_exists, not_lt] at hx₁ hx₂
      apply Filter.Eventually.of_forall
      intro z
      have : (f x, g x) ∈ u ×ˢ v := ⟨xu, xv⟩
      calc
        y < f x + g x := h this
        _ ≤ f z + g z := add_le_add (hx₁ (f z)) (hx₂ (g z))

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
theorem LowerSemicontinuousAt.add' {f g : α → γ} (hf : LowerSemicontinuousAt f x)
    (hg : LowerSemicontinuousAt g x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousAt (fun z => f z + g z) x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.add' hg hcont

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
theorem LowerSemicontinuousOn.add' {f g : α → γ} (hf : LowerSemicontinuousOn f s)
    (hg : LowerSemicontinuousOn g s)
    (hcont : ∀ x ∈ s, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousOn (fun z => f z + g z) s := fun x hx =>
  (hf x hx).add' (hg x hx) (hcont x hx)

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
theorem LowerSemicontinuous.add' {f g : α → γ} (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g)
    (hcont : ∀ x, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuous fun z => f z + g z := fun x => (hf x).add' (hg x) (hcont x)

variable [ContinuousAdd γ]

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem LowerSemicontinuousWithinAt.add {f g : α → γ} (hf : LowerSemicontinuousWithinAt f s x)
    (hg : LowerSemicontinuousWithinAt g s x) :
    LowerSemicontinuousWithinAt (fun z => f z + g z) s x :=
  hf.add' hg continuous_add.continuousAt

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem LowerSemicontinuousAt.add {f g : α → γ} (hf : LowerSemicontinuousAt f x)
    (hg : LowerSemicontinuousAt g x) : LowerSemicontinuousAt (fun z => f z + g z) x :=
  hf.add' hg continuous_add.continuousAt

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem LowerSemicontinuousOn.add {f g : α → γ} (hf : LowerSemicontinuousOn f s)
    (hg : LowerSemicontinuousOn g s) : LowerSemicontinuousOn (fun z => f z + g z) s :=
  hf.add' hg fun _x _hx => continuous_add.continuousAt

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem LowerSemicontinuous.add {f g : α → γ} (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g) : LowerSemicontinuous fun z => f z + g z :=
  hf.add' hg fun _x => continuous_add.continuousAt

theorem lowerSemicontinuousWithinAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun z => ∑ i ∈ a, f i z) s x := by
  classical
    induction a using Finset.induction_on with
    | empty => exact lowerSemicontinuousWithinAt_const
    | insert _ _ ia IH =>
      simp only [ia, Finset.sum_insert, not_false_iff]
      exact
        LowerSemicontinuousWithinAt.add (ha _ (Finset.mem_insert_self ..))
          (IH fun j ja => ha j (Finset.mem_insert_of_mem ja))

theorem lowerSemicontinuousAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun z => ∑ i ∈ a, f i z) x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_sum ha

theorem lowerSemicontinuousOn_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun z => ∑ i ∈ a, f i z) s := fun x hx =>
  lowerSemicontinuousWithinAt_sum fun i hi => ha i hi x hx

theorem lowerSemicontinuous_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuous (f i)) : LowerSemicontinuous fun z => ∑ i ∈ a, f i z :=
  fun x => lowerSemicontinuousAt_sum fun i hi => ha i hi x

end

/-! #### Supremum -/

section

variable {α : Type*} {β : Type*} [TopologicalSpace α] [LinearOrder β]
  {f g : α → β} {s : Set α} {a : α}

theorem LowerSemicontinuousWithinAt.sup
    (hf : LowerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) :
    LowerSemicontinuousWithinAt (fun x ↦ f x ⊔ g x) s a := by
  intro b hb
  simp only [lt_sup_iff] at hb ⊢
  rcases hb with hb | hb
  · filter_upwards [hf b hb] with x using Or.intro_left _
  · filter_upwards [hg b hb] with x using Or.intro_right _

theorem LowerSemicontinuousAt.sup
    (hf : LowerSemicontinuousAt f a) (hg : LowerSemicontinuousAt g a) :
    LowerSemicontinuousAt (fun x ↦ f x ⊔ g x) a := by
  rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.sup hg

theorem LowerSemicontinuousOn.sup
    (hf : LowerSemicontinuousOn f s) (hg : LowerSemicontinuousOn g s) :
    LowerSemicontinuousOn (fun x ↦ f x ⊔ g x) s := fun a ha ↦
  (hf a ha).sup (hg a ha)

theorem LowerSemicontinuous.sup
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
    LowerSemicontinuous fun x ↦ f x ⊔ g x := fun a ↦
  (hf a).sup (hg a)

theorem LowerSemicontinuousWithinAt.inf
    (hf : LowerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) :
    LowerSemicontinuousWithinAt (fun x ↦ f x ⊓ g x) s a := by
  intro b hb
  simp only [lt_inf_iff] at hb ⊢
  exact Eventually.and (hf b hb.1) (hg b hb.2)

theorem LowerSemicontinuousAt.inf
    (hf : LowerSemicontinuousAt f a) (hg : LowerSemicontinuousAt g a) :
    LowerSemicontinuousAt (fun x ↦ f x ⊓ g x) a := by
  rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.inf hg

theorem LowerSemicontinuousOn.inf
    (hf : LowerSemicontinuousOn f s) (hg : LowerSemicontinuousOn g s) :
    LowerSemicontinuousOn (fun x ↦ f x ⊓ g x) s := fun a ha ↦
  (hf a ha).inf (hg a ha)

theorem LowerSemicontinuous.inf (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g) :
    LowerSemicontinuous fun x ↦ f x ⊓ g x := fun a ↦
  (hf a).inf (hg a)

variable {ι : Type*} {f : ι → α → β} {a : α} {I : Set ι}

end

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

theorem lowerSemicontinuousWithinAt_iSup {f : ι → α → δ}
    (h : ∀ i, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ i, f i x') s x :=
  lowerSemicontinuousWithinAt_ciSup (by simp) h

theorem lowerSemicontinuousWithinAt_biSup {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, LowerSemicontinuousWithinAt (f i hi) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ (i) (hi), f i hi x') s x :=
  lowerSemicontinuousWithinAt_iSup fun i => lowerSemicontinuousWithinAt_iSup fun hi => h i hi

theorem lowerSemicontinuousAt_ciSup {f : ι → α → δ'}
    (bdd : ∀ᶠ y in 𝓝 x, BddAbove (range fun i => f i y)) (h : ∀ i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ⨆ i, f i x') x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  rw [← nhdsWithin_univ] at bdd
  exact lowerSemicontinuousWithinAt_ciSup bdd h

theorem lowerSemicontinuousAt_iSup {f : ι → α → δ} (h : ∀ i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ⨆ i, f i x') x :=
  lowerSemicontinuousAt_ciSup (by simp) h

theorem lowerSemicontinuousAt_biSup {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, LowerSemicontinuousAt (f i hi) x) :
    LowerSemicontinuousAt (fun x' => ⨆ (i) (hi), f i hi x') x :=
  lowerSemicontinuousAt_iSup fun i => lowerSemicontinuousAt_iSup fun hi => h i hi

theorem lowerSemicontinuousOn_ciSup {f : ι → α → δ'}
    (bdd : ∀ x ∈ s, BddAbove (range fun i => f i x)) (h : ∀ i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ⨆ i, f i x') s := fun x hx =>
  lowerSemicontinuousWithinAt_ciSup (eventually_nhdsWithin_of_forall bdd) fun i => h i x hx

theorem lowerSemicontinuousOn_iSup {f : ι → α → δ} (h : ∀ i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ⨆ i, f i x') s :=
  lowerSemicontinuousOn_ciSup (by simp) h

theorem lowerSemicontinuousOn_biSup {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, LowerSemicontinuousOn (f i hi) s) :
    LowerSemicontinuousOn (fun x' => ⨆ (i) (hi), f i hi x') s :=
  lowerSemicontinuousOn_iSup fun i => lowerSemicontinuousOn_iSup fun hi => h i hi

theorem lowerSemicontinuous_ciSup {f : ι → α → δ'} (bdd : ∀ x, BddAbove (range fun i => f i x))
    (h : ∀ i, LowerSemicontinuous (f i)) : LowerSemicontinuous fun x' => ⨆ i, f i x' := fun x =>
  lowerSemicontinuousAt_ciSup (Eventually.of_forall bdd) fun i => h i x

theorem lowerSemicontinuous_iSup {f : ι → α → δ} (h : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x' => ⨆ i, f i x' :=
  lowerSemicontinuous_ciSup (by simp) h

theorem lowerSemicontinuous_biSup {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, LowerSemicontinuous (f i hi)) :
    LowerSemicontinuous fun x' => ⨆ (i) (hi), f i hi x' :=
  lowerSemicontinuous_iSup fun i => lowerSemicontinuous_iSup fun hi => h i hi

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

theorem lowerSemicontinuousAt_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ∑' i, f i x') x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_tsum h

theorem lowerSemicontinuousOn_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ∑' i, f i x') s := fun x hx =>
  lowerSemicontinuousWithinAt_tsum fun i => h i x hx

theorem lowerSemicontinuous_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x' => ∑' i, f i x' := fun x => lowerSemicontinuousAt_tsum fun i => h i x

end

/-!
### Upper semicontinuous functions
-/


/-! #### Basic dot notation interface for upper semicontinuity -/


theorem UpperSemicontinuousWithinAt.mono (h : UpperSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    UpperSemicontinuousWithinAt f t x := fun y hy =>
  Filter.Eventually.filter_mono (nhdsWithin_mono _ hst) (h y hy)

theorem UpperSemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : UpperSemicontinuousWithinAt f s a)
    (has : a ∈ s) (hfg : ∀ᶠ x in nhdsWithin a s, f x = g x) :
    UpperSemicontinuousWithinAt g s a :=
  LowerSemicontinuousWithinAt.congr_of_eventuallyEq (β := βᵒᵈ) h has hfg

theorem upperSemicontinuousWithinAt_univ_iff :
    UpperSemicontinuousWithinAt f univ x ↔ UpperSemicontinuousAt f x := by
  simp [UpperSemicontinuousWithinAt, UpperSemicontinuousAt, nhdsWithin_univ]

theorem UpperSemicontinuousAt.upperSemicontinuousWithinAt (s : Set α)
    (h : UpperSemicontinuousAt f x) : UpperSemicontinuousWithinAt f s x := fun y hy =>
  Filter.Eventually.filter_mono nhdsWithin_le_nhds (h y hy)

theorem UpperSemicontinuousOn.upperSemicontinuousWithinAt (h : UpperSemicontinuousOn f s)
    (hx : x ∈ s) : UpperSemicontinuousWithinAt f s x :=
  h x hx

theorem UpperSemicontinuousOn.mono (h : UpperSemicontinuousOn f s) (hst : t ⊆ s) :
    UpperSemicontinuousOn f t := fun x hx => (h x (hst hx)).mono hst

theorem upperSemicontinuousOn_univ_iff : UpperSemicontinuousOn f univ ↔ UpperSemicontinuous f := by
  simp [UpperSemicontinuousOn, UpperSemicontinuous, upperSemicontinuousWithinAt_univ_iff]

theorem UpperSemicontinuous.upperSemicontinuousAt (h : UpperSemicontinuous f) (x : α) :
    UpperSemicontinuousAt f x :=
  h x

theorem UpperSemicontinuous.upperSemicontinuousWithinAt (h : UpperSemicontinuous f) (s : Set α)
    (x : α) : UpperSemicontinuousWithinAt f s x :=
  (h x).upperSemicontinuousWithinAt s

theorem UpperSemicontinuous.upperSemicontinuousOn (h : UpperSemicontinuous f) (s : Set α) :
    UpperSemicontinuousOn f s := fun x _hx => h.upperSemicontinuousWithinAt s x

/-! #### Constants -/


theorem upperSemicontinuousWithinAt_const : UpperSemicontinuousWithinAt (fun _x => z) s x :=
  fun _y hy => Filter.Eventually.of_forall fun _x => hy

theorem upperSemicontinuousAt_const : UpperSemicontinuousAt (fun _x => z) x := fun _y hy =>
  Filter.Eventually.of_forall fun _x => hy

theorem upperSemicontinuousOn_const : UpperSemicontinuousOn (fun _x => z) s := fun _x _hx =>
  upperSemicontinuousWithinAt_const

theorem upperSemicontinuous_const : UpperSemicontinuous fun _x : α => z := fun _x =>
  upperSemicontinuousAt_const

/-! ### upper bounds -/

section

variable {α : Type*} [TopologicalSpace α] {β : Type*} [LinearOrder β] {f : α → β} {s : Set α}

/-- An upper semicontinuous function attains its upper bound on a nonempty compact set. -/
theorem UpperSemicontinuousOn.exists_isMaxOn {s : Set α} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : UpperSemicontinuousOn f s) :
    ∃ a ∈ s, IsMaxOn f s a :=
  LowerSemicontinuousOn.exists_isMinOn (β := βᵒᵈ) ne_s hs hf

/-- An upper semicontinuous function is bounded above on a compact set. -/
theorem UpperSemicontinuousOn.bddAbove_of_isCompact [Nonempty β] {s : Set α}
    (hs : IsCompact s) (hf : UpperSemicontinuousOn f s) : BddAbove (f '' s) :=
  LowerSemicontinuousOn.bddBelow_of_isCompact (β := βᵒᵈ) hs hf

end

/-! #### Indicators -/


section

variable [Zero β]

theorem IsOpen.upperSemicontinuous_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuous (indicator s fun _x => y) :=
  @IsOpen.lowerSemicontinuous_indicator α _ βᵒᵈ _ s y _ hs hy

theorem IsOpen.upperSemicontinuousOn_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousOn t

theorem IsOpen.upperSemicontinuousAt_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousAt x

theorem IsOpen.upperSemicontinuousWithinAt_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousWithinAt t x

theorem IsClosed.upperSemicontinuous_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuous (indicator s fun _x => y) :=
  @IsClosed.lowerSemicontinuous_indicator α _ βᵒᵈ _ s y _ hs hy

theorem IsClosed.upperSemicontinuousOn_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousOn t

theorem IsClosed.upperSemicontinuousAt_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousAt x

theorem IsClosed.upperSemicontinuousWithinAt_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousWithinAt t x

end

/-! #### Relationship with continuity -/


theorem upperSemicontinuous_iff_isOpen_preimage :
    UpperSemicontinuous f ↔ ∀ y, IsOpen (f ⁻¹' Iio y) :=
  ⟨fun H y => isOpen_iff_mem_nhds.2 fun x hx => H x y hx, fun H _x y y_lt =>
    IsOpen.mem_nhds (H y) y_lt⟩

theorem UpperSemicontinuous.isOpen_preimage (hf : UpperSemicontinuous f) (y : β) :
    IsOpen (f ⁻¹' Iio y) :=
  upperSemicontinuous_iff_isOpen_preimage.1 hf y

section

variable {γ : Type*} [LinearOrder γ]

theorem upperSemicontinuous_iff_isClosed_preimage {f : α → γ} :
    UpperSemicontinuous f ↔ ∀ y, IsClosed (f ⁻¹' Ici y) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  simp only [← isOpen_compl_iff, ← preimage_compl, compl_Ici]

theorem UpperSemicontinuous.isClosed_preimage {f : α → γ} (hf : UpperSemicontinuous f) (y : γ) :
    IsClosed (f ⁻¹' Ici y) :=
  upperSemicontinuous_iff_isClosed_preimage.1 hf y

variable [TopologicalSpace γ] [OrderTopology γ]

theorem ContinuousWithinAt.upperSemicontinuousWithinAt {f : α → γ} (h : ContinuousWithinAt f s x) :
    UpperSemicontinuousWithinAt f s x := fun _y hy => h (Iio_mem_nhds hy)

theorem ContinuousAt.upperSemicontinuousAt {f : α → γ} (h : ContinuousAt f x) :
    UpperSemicontinuousAt f x := fun _y hy => h (Iio_mem_nhds hy)

theorem ContinuousOn.upperSemicontinuousOn {f : α → γ} (h : ContinuousOn f s) :
    UpperSemicontinuousOn f s := fun x hx => (h x hx).upperSemicontinuousWithinAt

theorem Continuous.upperSemicontinuous {f : α → γ} (h : Continuous f) : UpperSemicontinuous f :=
  fun _x => h.continuousAt.upperSemicontinuousAt

end

/-! #### Equivalent definitions -/

section

variable {γ : Type*} [CompleteLinearOrder γ]

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

end

section

variable {γ : Type*} [LinearOrder γ] [TopologicalSpace γ] [ClosedIicTopology γ]

theorem upperSemicontinuousOn_iff_isClosed_hypograph {f : α → γ} (hs : IsClosed s) :
    UpperSemicontinuousOn f s ↔ IsClosed {p : α × γ | p.1 ∈ s ∧ p.2 ≤ f p.1} :=
  lowerSemicontinuousOn_iff_isClosed_epigraph hs (γ := γᵒᵈ)

theorem upperSemicontinuous_iff_IsClosed_hypograph {f : α → γ} :
    UpperSemicontinuous f ↔ IsClosed {p : α × γ | p.2 ≤ f p.1} :=
  lowerSemicontinuous_iff_isClosed_epigraph (γ := γᵒᵈ)

alias ⟨UpperSemicontinuous.IsClosed_hypograph, _⟩ := upperSemicontinuous_iff_IsClosed_hypograph

end

/-! ### Composition -/

section

variable {α : Type*} [TopologicalSpace α]
variable {β : Type*} [LinearOrder β]
variable {γ : Type*} [TopologicalSpace γ]
variable {f : α → β} {g : γ → α} {s : Set α} {a : α} {c : γ} {t : Set γ}

theorem UpperSemicontinuousWithinAt.comp
    (hf : UpperSemicontinuousWithinAt f s (g c)) (hg : ContinuousWithinAt g t c)
    (hg' : MapsTo g t s) :
    UpperSemicontinuousWithinAt (f ∘ g) t c :=
  LowerSemicontinuousWithinAt.comp (β := βᵒᵈ) hf hg hg'

theorem UpperSemicontinuousAt.comp
    (hf : UpperSemicontinuousAt f (g c)) (hg : ContinuousAt g c) :
    UpperSemicontinuousAt (f ∘ g) c :=
  LowerSemicontinuousAt.comp (β := βᵒᵈ) hf hg

theorem UpperSemicontinuousOn.comp
    (hf : UpperSemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    UpperSemicontinuousOn (f ∘ g) t :=
  LowerSemicontinuousOn.comp (β := βᵒᵈ) hf hg hg'

theorem UpperSemicontinuous.comp
    (hf : UpperSemicontinuous f) (hg : Continuous g) : UpperSemicontinuous (f ∘ g) :=
  LowerSemicontinuous.comp (β := βᵒᵈ) hf hg

@[simp] theorem upperSemicontinuousOn_iff_restrict {s : Set α} :
    UpperSemicontinuous (s.restrict f) ↔ UpperSemicontinuousOn f s :=
  lowerSemicontinuous_restrict_iff (β := βᵒᵈ)

theorem upperSemicontinuousOn_iff_preimage_Iio :
    UpperSemicontinuousOn f s ↔ ∀ b, ∃ u : Set α, IsOpen u ∧ s ∩ f ⁻¹' Set.Iio b = s ∩ u :=
  lowerSemicontinuousOn_iff_preimage_Ioi (β := βᵒᵈ)

theorem upperSemicontinuousOn_iff_preimage_Ici :
    UpperSemicontinuousOn f s ↔ ∀ b, ∃ v : Set α, IsClosed v ∧ s ∩ f ⁻¹' Set.Ici b = s ∩ v :=
  lowerSemicontinuousOn_iff_preimage_Iic (γ := βᵒᵈ)

end

section

variable {γ : Type*} [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
variable {δ : Type*} [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]
variable {ι : Type*} [TopologicalSpace ι]

theorem ContinuousAt.comp_upperSemicontinuousWithinAt {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousWithinAt f s x) (gmon : Monotone g) :
    UpperSemicontinuousWithinAt (g ∘ f) s x :=
  @ContinuousAt.comp_lowerSemicontinuousWithinAt α _ x s γᵒᵈ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon.dual

theorem ContinuousAt.comp_upperSemicontinuousAt {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : UpperSemicontinuousAt f x) (gmon : Monotone g) : UpperSemicontinuousAt (g ∘ f) x :=
  @ContinuousAt.comp_lowerSemicontinuousAt α _ x γᵒᵈ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon.dual

theorem Continuous.comp_upperSemicontinuousOn {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuousOn f s) (gmon : Monotone g) : UpperSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_upperSemicontinuousWithinAt (hf x hx) gmon

theorem Continuous.comp_upperSemicontinuous {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuous f) (gmon : Monotone g) : UpperSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_upperSemicontinuousAt (hf x) gmon

theorem ContinuousAt.comp_upperSemicontinuousWithinAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousWithinAt f s x) (gmon : Antitone g) :
    LowerSemicontinuousWithinAt (g ∘ f) s x :=
  @ContinuousAt.comp_upperSemicontinuousWithinAt α _ x s γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon

theorem ContinuousAt.comp_upperSemicontinuousAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousAt f x) (gmon : Antitone g) :
    LowerSemicontinuousAt (g ∘ f) x :=
  @ContinuousAt.comp_upperSemicontinuousAt α _ x γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon

theorem Continuous.comp_upperSemicontinuousOn_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuousOn f s) (gmon : Antitone g) : LowerSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_upperSemicontinuousWithinAt_antitone (hf x hx) gmon

theorem Continuous.comp_upperSemicontinuous_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuous f) (gmon : Antitone g) : LowerSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_upperSemicontinuousAt_antitone (hf x) gmon

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

variable {ι : Type*} {γ : Type*} [AddCommMonoid γ] [LinearOrder γ] [IsOrderedAddMonoid γ]
  [TopologicalSpace γ] [OrderTopology γ]

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
theorem UpperSemicontinuousWithinAt.add' {f g : α → γ} (hf : UpperSemicontinuousWithinAt f s x)
    (hg : UpperSemicontinuousWithinAt g s x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousWithinAt (fun z => f z + g z) s x :=
  LowerSemicontinuousWithinAt.add' (γ := γᵒᵈ) hf hg hcont

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
theorem UpperSemicontinuousAt.add' {f g : α → γ} (hf : UpperSemicontinuousAt f x)
    (hg : UpperSemicontinuousAt g x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousAt (fun z => f z + g z) x := by
  simp_rw [← upperSemicontinuousWithinAt_univ_iff] at *
  exact hf.add' hg hcont

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
theorem UpperSemicontinuousOn.add' {f g : α → γ} (hf : UpperSemicontinuousOn f s)
    (hg : UpperSemicontinuousOn g s)
    (hcont : ∀ x ∈ s, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousOn (fun z => f z + g z) s := fun x hx =>
  (hf x hx).add' (hg x hx) (hcont x hx)

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
theorem UpperSemicontinuous.add' {f g : α → γ} (hf : UpperSemicontinuous f)
    (hg : UpperSemicontinuous g)
    (hcont : ∀ x, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuous fun z => f z + g z := fun x => (hf x).add' (hg x) (hcont x)

variable [ContinuousAdd γ]

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem UpperSemicontinuousWithinAt.add {f g : α → γ} (hf : UpperSemicontinuousWithinAt f s x)
    (hg : UpperSemicontinuousWithinAt g s x) :
    UpperSemicontinuousWithinAt (fun z => f z + g z) s x :=
  hf.add' hg continuous_add.continuousAt

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem UpperSemicontinuousAt.add {f g : α → γ} (hf : UpperSemicontinuousAt f x)
    (hg : UpperSemicontinuousAt g x) : UpperSemicontinuousAt (fun z => f z + g z) x :=
  hf.add' hg continuous_add.continuousAt

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem UpperSemicontinuousOn.add {f g : α → γ} (hf : UpperSemicontinuousOn f s)
    (hg : UpperSemicontinuousOn g s) : UpperSemicontinuousOn (fun z => f z + g z) s :=
  hf.add' hg fun _x _hx => continuous_add.continuousAt

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
theorem UpperSemicontinuous.add {f g : α → γ} (hf : UpperSemicontinuous f)
    (hg : UpperSemicontinuous g) : UpperSemicontinuous fun z => f z + g z :=
  hf.add' hg fun _x => continuous_add.continuousAt

theorem upperSemicontinuousWithinAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun z => ∑ i ∈ a, f i z) s x :=
  lowerSemicontinuousWithinAt_sum (γ := γᵒᵈ) ha

theorem upperSemicontinuousAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun z => ∑ i ∈ a, f i z) x := by
  simp_rw [← upperSemicontinuousWithinAt_univ_iff] at *
  exact upperSemicontinuousWithinAt_sum ha

theorem upperSemicontinuousOn_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun z => ∑ i ∈ a, f i z) s := fun x hx =>
  upperSemicontinuousWithinAt_sum fun i hi => ha i hi x hx

theorem upperSemicontinuous_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuous (f i)) : UpperSemicontinuous fun z => ∑ i ∈ a, f i z :=
  fun x => upperSemicontinuousAt_sum fun i hi => ha i hi x

end

/-! #### Infimum -/

section

variable {α : Type*} {β : Type*} [TopologicalSpace α] [LinearOrder β]
    {f g : α → β} {s : Set α} {a : α}

theorem UpperSemicontinuousWithinAt.inf
    (hf : UpperSemicontinuousWithinAt f s a) (hg : UpperSemicontinuousWithinAt g s a) :
    UpperSemicontinuousWithinAt (fun x ↦ f x ⊓ g x) s a :=
  LowerSemicontinuousWithinAt.sup (β := βᵒᵈ) hf hg

theorem UpperSemicontinuousAt.inf
    (hf : UpperSemicontinuousAt f a) (hg : UpperSemicontinuousAt g a) :
    UpperSemicontinuousAt (fun x ↦ f x ⊓ g x) a :=
  LowerSemicontinuousAt.sup (β := βᵒᵈ) hf hg

theorem UpperSemicontinuousOn.inf
    (hf : UpperSemicontinuousOn f s) (hg : UpperSemicontinuousOn g s) :
    UpperSemicontinuousOn (fun x ↦ f x ⊓ g x) s :=
  LowerSemicontinuousOn.sup (β := βᵒᵈ) hf hg

theorem UpperSemicontinuous.inf (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g) :
    UpperSemicontinuous (fun x ↦ f x ⊓ g x) :=
  LowerSemicontinuous.sup (β := βᵒᵈ) hf hg

theorem UpperSemicontinuousWithinAt.sup
    (hf : UpperSemicontinuousWithinAt f s a) (hg : UpperSemicontinuousWithinAt g s a) :
    UpperSemicontinuousWithinAt (fun x ↦ f x ⊔ g x) s a :=
  LowerSemicontinuousWithinAt.inf (β := βᵒᵈ) hf hg

theorem UpperSemicontinuousAt.sup
    (hf : UpperSemicontinuousAt f a) (hg : UpperSemicontinuousAt g a) :
    UpperSemicontinuousAt (fun x ↦ f x ⊔ g x) a :=
  LowerSemicontinuousAt.inf (β := βᵒᵈ) hf hg

theorem UpperSemicontinuousOn.sup
    (hf : UpperSemicontinuousOn f s) (hg : UpperSemicontinuousOn g s) :
    UpperSemicontinuousOn (fun x ↦ f x ⊔ g x) s :=
  LowerSemicontinuousOn.inf (β := βᵒᵈ) hf hg

theorem UpperSemicontinuous.sup (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g) :
    UpperSemicontinuous fun x ↦ f x ⊔ g x :=
  LowerSemicontinuous.inf (β := βᵒᵈ) hf hg


end

section

variable {ι : Sort*} {δ δ' : Type*} [CompleteLinearOrder δ] [ConditionallyCompleteLinearOrder δ']

theorem upperSemicontinuousWithinAt_ciInf {f : ι → α → δ'}
    (bdd : ∀ᶠ y in 𝓝[s] x, BddBelow (range fun i => f i y))
    (h : ∀ i, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ i, f i x') s x :=
  @lowerSemicontinuousWithinAt_ciSup α _ x s ι δ'ᵒᵈ _ f bdd h

theorem upperSemicontinuousWithinAt_iInf {f : ι → α → δ}
    (h : ∀ i, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ i, f i x') s x :=
  @lowerSemicontinuousWithinAt_iSup α _ x s ι δᵒᵈ _ f h

theorem upperSemicontinuousWithinAt_biInf {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, UpperSemicontinuousWithinAt (f i hi) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ (i) (hi), f i hi x') s x :=
  upperSemicontinuousWithinAt_iInf fun i => upperSemicontinuousWithinAt_iInf fun hi => h i hi

theorem upperSemicontinuousAt_ciInf {f : ι → α → δ'}
    (bdd : ∀ᶠ y in 𝓝 x, BddBelow (range fun i => f i y)) (h : ∀ i, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun x' => ⨅ i, f i x') x :=
  @lowerSemicontinuousAt_ciSup α _ x ι δ'ᵒᵈ _ f bdd h

theorem upperSemicontinuousAt_iInf {f : ι → α → δ} (h : ∀ i, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun x' => ⨅ i, f i x') x :=
  @lowerSemicontinuousAt_iSup α _ x ι δᵒᵈ _ f h

theorem upperSemicontinuousAt_biInf {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, UpperSemicontinuousAt (f i hi) x) :
    UpperSemicontinuousAt (fun x' => ⨅ (i) (hi), f i hi x') x :=
  upperSemicontinuousAt_iInf fun i => upperSemicontinuousAt_iInf fun hi => h i hi

theorem upperSemicontinuousOn_ciInf {f : ι → α → δ'}
    (bdd : ∀ x ∈ s, BddBelow (range fun i => f i x)) (h : ∀ i, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun x' => ⨅ i, f i x') s := fun x hx =>
  upperSemicontinuousWithinAt_ciInf (eventually_nhdsWithin_of_forall bdd) fun i => h i x hx

theorem upperSemicontinuousOn_iInf {f : ι → α → δ} (h : ∀ i, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun x' => ⨅ i, f i x') s := fun x hx =>
  upperSemicontinuousWithinAt_iInf fun i => h i x hx

theorem upperSemicontinuousOn_biInf {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, UpperSemicontinuousOn (f i hi) s) :
    UpperSemicontinuousOn (fun x' => ⨅ (i) (hi), f i hi x') s :=
  upperSemicontinuousOn_iInf fun i => upperSemicontinuousOn_iInf fun hi => h i hi

theorem upperSemicontinuous_ciInf {f : ι → α → δ'} (bdd : ∀ x, BddBelow (range fun i => f i x))
    (h : ∀ i, UpperSemicontinuous (f i)) : UpperSemicontinuous fun x' => ⨅ i, f i x' := fun x =>
  upperSemicontinuousAt_ciInf (Eventually.of_forall bdd) fun i => h i x

theorem upperSemicontinuous_iInf {f : ι → α → δ} (h : ∀ i, UpperSemicontinuous (f i)) :
    UpperSemicontinuous fun x' => ⨅ i, f i x' := fun x => upperSemicontinuousAt_iInf fun i => h i x

theorem upperSemicontinuous_biInf {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, UpperSemicontinuous (f i hi)) :
    UpperSemicontinuous fun x' => ⨅ (i) (hi), f i hi x' :=
  upperSemicontinuous_iInf fun i => upperSemicontinuous_iInf fun hi => h i hi

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
      rcases le_or_gt (f a) (f x) with h | h
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
      apply Filter.Eventually.of_forall
      intro a
      have : f a = f x := le_antisymm (Hu _) (Hl _)
      rw [this]
      exact mem_of_mem_nhds hv

theorem continuousAt_iff_lower_upperSemicontinuousAt {f : α → γ} :
    ContinuousAt f x ↔ LowerSemicontinuousAt f x ∧ UpperSemicontinuousAt f x := by
  simp_rw [← continuousWithinAt_univ, ← lowerSemicontinuousWithinAt_univ_iff, ←
    upperSemicontinuousWithinAt_univ_iff, continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]

theorem continuousOn_iff_lower_upperSemicontinuousOn {f : α → γ} :
    ContinuousOn f s ↔ LowerSemicontinuousOn f s ∧ UpperSemicontinuousOn f s := by
  simp only [ContinuousOn, continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
  exact
    ⟨fun H => ⟨fun x hx => (H x hx).1, fun x hx => (H x hx).2⟩, fun H x hx => ⟨H.1 x hx, H.2 x hx⟩⟩

theorem continuous_iff_lower_upperSemicontinuous {f : α → γ} :
    Continuous f ↔ LowerSemicontinuous f ∧ UpperSemicontinuous f := by
  simp_rw [← continuousOn_univ, continuousOn_iff_lower_upperSemicontinuousOn,
    lowerSemicontinuousOn_univ_iff, upperSemicontinuousOn_univ_iff]

end
