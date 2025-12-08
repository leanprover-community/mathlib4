/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Antoine Chambert-Loir, Anatole Dedecker, Jireh Loreaux
-/
module

public import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.ContinuousOn

/-!
# Semicontinuous maps

A function `f` from a topological space `α` to an ordered space `β` is *lower semicontinuous* at a
point `x` if, for any `y < f x`, for any `x'` close enough to `x`, one has `f x' > y`. In other
words, `f` can jump up, but it cannot jump down.

*Upper semicontinuous* functions are defined similarly. Upper and lower hemicontinuity (of
functions `f : α → Set β`) are often defined in terms of sequential characterizations, but
here we take an equivalent approach. `f : α → Set β` is *upper hemicontinuous* at `x` if for any
neighborhood of `f x`, `f x'` is included in this neighborhood for all `x'` close enough to `x`.

Of course, one can see a superficial similarity between upper semicontinuity and upper
hemicontinuity. In fact, we can unify all of upper and lower semicontinuity and also upper and
lower hemicontinuity under one umbrella, by considering a general relation `r : α → β → Prop` and
defining semicontinuity of this relation.

This file introduces these notions, and a basic API around them mimicking the API for continuous
functions.

## Main definitions and results

We introduce 4 generic definitions related to semicontinuity:
* `SemicontinuousWithinAt r s x`
* `SemicontinuousAt r x`
* `SemicontinuousOn r s`
* `Semicontinuous r`

We build a basic API using dot notation around these notions, and we prove that
* constant functions are semicontinuous;
* right composition with continuous functions preserves semicontinuity;

We also define lower and upper semicontinuity as abbreviations of these generic definitions
and transfer the generic results to these notions.

## References

* <https://en.wikipedia.org/wiki/Semi-continuity>
* <https://en.wikipedia.org/wiki/Hemicontinuity>

-/

@[expose] public section

open scoped Topology

open Set Function Filter

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace γ]

/-! ## Main definitions -/

section Semicontinuous

/-- A relation `r : α → β → Prop` is semicontinuous within `s` at `x : α`, if whenever `r x y`
is true, it is also true for all `x'` sufficiently close to `x` within `s`.

This notion generalizes lower and upper semicontinuity of functions, as well as
lower and upper hemicontinuity of set-valued correspondences. -/
def SemicontinuousWithinAt (r : α → β → Prop) (s : Set α) (x : α) :=
  ∀ y, r x y → ∀ᶠ x' in 𝓝[s] x, r x' y

/-- A relation `r : α → β → Prop` is semicontinuous on `s` if it is semicontinuous within `s` at
each `x ∈ s`. -/
def SemicontinuousOn (r : α → β → Prop) (s : Set α) :=
  ∀ x ∈ s, SemicontinuousWithinAt r s x

/-- A relation `r : α → β → Prop` is semicontinuous at `x : α`, if whenever `r x y`
is true, it is also true for all `x'` sufficiently close to `x`.

This notion generalizes lower and upper semicontinuity of functions, as well as
lower and upper hemicontinuity of set-valued correspondences. -/
def SemicontinuousAt (r : α → β → Prop) (x : α) : Prop :=
  ∀ y, r x y → ∀ᶠ x' in 𝓝 x, r x' y

/-- A relation `r : α → β → Prop` is semicontinuous if it is semicontinuous within `s` at each
`x : α`. -/
def Semicontinuous (r : α → β → Prop) : Prop :=
  ∀ x, SemicontinuousAt r x

variable {r r' : α → β → Prop} {x : α} {s t : Set α}

theorem SemicontinuousWithinAt.mono (h : SemicontinuousWithinAt r s x) (hst : t ⊆ s) :
    SemicontinuousWithinAt r t x := fun y hy =>
  Filter.Eventually.filter_mono (nhdsWithin_mono _ hst) (h y hy)

theorem SemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : SemicontinuousWithinAt r s a)
    (has : a ∈ s) (hfg : ∀ᶠ x in 𝓝[s] a, ∀ y, r x y ↔ r' x y) :
    SemicontinuousWithinAt r' s a := by
  intro b hb
  simp_rw [← propext_iff, ← funext_iff] at hfg
  rw [← Filter.EventuallyEq.eq_of_nhdsWithin hfg has] at hb
  filter_upwards [hfg, h b hb] with x hx hxb
  exact hx ▸ hxb

theorem semicontinuousWithinAt_univ_iff :
    SemicontinuousWithinAt r univ x ↔ SemicontinuousAt r x := by
  simp [SemicontinuousWithinAt, SemicontinuousAt, nhdsWithin_univ]

theorem SemicontinuousAt.semicontinuousWithinAt (s : Set α)
    (h : SemicontinuousAt r x) : SemicontinuousWithinAt r s x := fun y hy =>
  Filter.Eventually.filter_mono nhdsWithin_le_nhds (h y hy)

theorem SemicontinuousOn.semicontinuousWithinAt (h : SemicontinuousOn r s)
    (hx : x ∈ s) : SemicontinuousWithinAt r s x :=
  h x hx

theorem SemicontinuousOn.mono (h : SemicontinuousOn r s) (hst : t ⊆ s) :
    SemicontinuousOn r t := fun x hx => (h x (hst hx)).mono hst

theorem semicontinuousOn_univ_iff : SemicontinuousOn r univ ↔ Semicontinuous r := by
  simp [SemicontinuousOn, Semicontinuous, semicontinuousWithinAt_univ_iff]

@[simp] theorem semicontinuous_restrict_iff :
    Semicontinuous (s.restrict r) ↔ SemicontinuousOn r s := by
  rw [SemicontinuousOn, Semicontinuous, SetCoe.forall]
  refine forall₂_congr fun a ha ↦ forall₂_congr fun b _ ↦ ?_
  simp only [nhdsWithin_eq_map_subtype_coe ha, eventually_map, restrict]

theorem Semicontinuous.semicontinuousAt (h : Semicontinuous r) (x : α) :
    SemicontinuousAt r x :=
  h x

theorem Semicontinuous.semicontinuousWithinAt (h : Semicontinuous r) (s : Set α)
    (x : α) : SemicontinuousWithinAt r s x :=
  (h x).semicontinuousWithinAt s

theorem Semicontinuous.semicontinuousOn (h : Semicontinuous r) (s : Set α) :
    SemicontinuousOn r s := fun x _hx => h.semicontinuousWithinAt s x

/-! #### Constants -/

theorem SemicontinuousWithinAt.const {f : β → Prop} : SemicontinuousWithinAt (fun _x => f) s x :=
  fun _y hy => Filter.Eventually.of_forall fun _x => hy

theorem SemicontinuousAt.const {f : β → Prop} : SemicontinuousAt (fun _x => f) x := fun _y hy =>
  Filter.Eventually.of_forall fun _x => hy

theorem SemicontinuousOn.const {f : β → Prop} : SemicontinuousOn (fun _x => f) s := fun _x _hx =>
  SemicontinuousWithinAt.const

theorem Semicontinuous.const {f : β → Prop} : Semicontinuous fun _x : α => f := fun _x =>
  SemicontinuousAt.const

/-! ### Precomposition with a continuous map -/

variable {x : γ} {g : γ → α} {s : Set γ} {t : Set α}

lemma SemicontinuousWithinAt.comp (h : SemicontinuousWithinAt r t (g x))
    (hg : ContinuousWithinAt g s x) (hst : Set.MapsTo g s t) :
    SemicontinuousWithinAt (r ∘ g) s x :=
  (hg.tendsto_nhdsWithin hst <| h · ·)

lemma SemicontinuousOn.comp {r : α → β → Prop} {γ : Type*}
    [TopologicalSpace γ] {g : γ → α} {s : Set γ} {t : Set α}
    (h : SemicontinuousOn r t) (hg : ContinuousOn g s)
    (hst : Set.MapsTo g s t) :
    SemicontinuousOn (r ∘ g) s :=
  fun x hx ↦ h (g x) (hst hx) |>.comp (hg x hx) hst

lemma SemicontinuousAt.comp {r : α → β → Prop} {γ : Type*} [TopologicalSpace γ]
    {x : γ} {g : γ → α} (h : SemicontinuousAt r (g x)) (hg : ContinuousAt g x) :
    SemicontinuousAt (r ∘ g) x :=
  (hg <| h · ·)

lemma Semicontinuous.comp {r : α → β → Prop} {γ : Type*} [TopologicalSpace γ]
    {g : γ → α} (h : Semicontinuous r) (hg : Continuous g) :
    Semicontinuous (r ∘ g) :=
  fun _ ↦ (h.semicontinuousAt _).comp hg.continuousAt

end Semicontinuous

section Preorder

/-! ## Lower and Upper Semicontinuity -/

variable [Preorder β] {f g : α → β} {x : α} {s t : Set α} {y z : β}

section Definitions

/-- A real function `f` is lower semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in `s`, then `f x'` is at least `f x - ε`. We formulate this in a general
preordered space, using an arbitrary `y < f x` instead of `f x - ε`. -/
abbrev LowerSemicontinuousWithinAt (f : α → β) (s : Set α) (x : α) :=
  SemicontinuousWithinAt (f · > ·) s x

/-- A real function `f` is lower semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at least `f x - ε`. We formulate this in
a general preordered space, using an arbitrary `y < f x` instead of `f x - ε`. -/
abbrev LowerSemicontinuousOn (f : α → β) (s : Set α) :=
  SemicontinuousOn (f · > ·) s

/-- A real function `f` is lower semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
abbrev LowerSemicontinuousAt (f : α → β) (x : α) :=
  SemicontinuousAt (f · > ·) x

/-- A real function `f` is lower semicontinuous if, for any `ε > 0`, for any `x`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
abbrev LowerSemicontinuous (f : α → β) :=
  Semicontinuous (f · > ·)

/-- A real function `f` is upper semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We formulate this in a general
preordered space, using an arbitrary `y > f x` instead of `f x + ε`. -/
abbrev UpperSemicontinuousWithinAt (f : α → β) (s : Set α) (x : α) :=
  SemicontinuousWithinAt (f · < ·) s x

/-- A real function `f` is upper semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We formulate this in a
general preordered space, using an arbitrary `y > f x` instead of `f x + ε`. -/
abbrev UpperSemicontinuousOn (f : α → β) (s : Set α) :=
  SemicontinuousOn (f · < ·) s

/-- A real function `f` is upper semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered space,
using an arbitrary `y > f x` instead of `f x + ε`. -/
abbrev UpperSemicontinuousAt (f : α → β) (x : α) :=
  SemicontinuousAt (f · < ·) x

/-- A real function `f` is upper semicontinuous if, for any `ε > 0`, for any `x`, for all `x'`
close enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered
space, using an arbitrary `y > f x` instead of `f x + ε`. -/
abbrev UpperSemicontinuous (f : α → β) :=
  Semicontinuous (f · < ·)

lemma lowerSemicontinuousWithinAt_iff {f : α → β} {s : Set α} {x : α} :
    LowerSemicontinuousWithinAt f s x ↔ ∀ y, y < f x → ∀ᶠ x' in 𝓝[s] x, y < f x' :=
  Iff.rfl

lemma lowerSemicontinuousOn_iff {f : α → β} {s : Set α} :
    LowerSemicontinuousOn f s ↔ ∀ x ∈ s, LowerSemicontinuousWithinAt f s x :=
  Iff.rfl

lemma lowerSemicontinuousAt_iff {f : α → β} {x : α} :
    LowerSemicontinuousAt f x ↔ ∀ y, y < f x → ∀ᶠ x' in 𝓝 x, y < f x' :=
  Iff.rfl

lemma lowerSemicontinuous_iff {f : α → β} :
    LowerSemicontinuous f ↔ ∀ x, LowerSemicontinuousAt f x :=
  Iff.rfl

lemma upperSemicontinuousWithinAt_iff {f : α → β} {s : Set α} {x : α} :
    UpperSemicontinuousWithinAt f s x ↔ ∀ y, f x < y → ∀ᶠ x' in 𝓝[s] x, f x' < y :=
  Iff.rfl

lemma upperSemicontinuousOn_iff {f : α → β} {s : Set α} :
    UpperSemicontinuousOn f s ↔ ∀ x ∈ s, UpperSemicontinuousWithinAt f s x :=
  Iff.rfl

lemma upperSemicontinuousAt_iff {f : α → β} {x : α} :
    UpperSemicontinuousAt f x ↔ ∀ y, f x < y → ∀ᶠ x' in 𝓝 x, f x' < y :=
  Iff.rfl

lemma upperSemicontinuous_iff {f : α → β} :
    UpperSemicontinuous f ↔ ∀ x, UpperSemicontinuousAt f x :=
  Iff.rfl

end Definitions

/-!
### Lower semicontinuous functions
-/

/-! #### Basic dot notation interface for lower semicontinuity -/

theorem LowerSemicontinuousWithinAt.mono (h : LowerSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    LowerSemicontinuousWithinAt f t x :=
  SemicontinuousWithinAt.mono h hst

theorem LowerSemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : LowerSemicontinuousWithinAt f s a)
    (has : a ∈ s) (hfg : f =ᶠ[𝓝[s] a] g) :
    LowerSemicontinuousWithinAt g s a :=
  SemicontinuousWithinAt.congr_of_eventuallyEq h has <| by
    filter_upwards [hfg] with x hx
    simp [hx]

theorem lowerSemicontinuousWithinAt_univ_iff :
    LowerSemicontinuousWithinAt f univ x ↔ LowerSemicontinuousAt f x :=
  semicontinuousWithinAt_univ_iff

theorem LowerSemicontinuousAt.lowerSemicontinuousWithinAt (s : Set α)
    (h : LowerSemicontinuousAt f x) : LowerSemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt s

theorem LowerSemicontinuousOn.lowerSemicontinuousWithinAt (h : LowerSemicontinuousOn f s)
    (hx : x ∈ s) : LowerSemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt hx

theorem LowerSemicontinuousOn.mono (h : LowerSemicontinuousOn f s) (hst : t ⊆ s) :
    LowerSemicontinuousOn f t :=
  SemicontinuousOn.mono h hst

theorem lowerSemicontinuousOn_univ_iff : LowerSemicontinuousOn f univ ↔ LowerSemicontinuous f :=
  semicontinuousOn_univ_iff

@[simp] theorem lowerSemicontinuous_restrict_iff :
    LowerSemicontinuous (s.restrict f) ↔ LowerSemicontinuousOn f s :=
  semicontinuous_restrict_iff (r := (f · > ·))

theorem LowerSemicontinuous.lowerSemicontinuousAt (h : LowerSemicontinuous f) (x : α) :
    LowerSemicontinuousAt f x :=
  h x

theorem LowerSemicontinuous.lowerSemicontinuousWithinAt (h : LowerSemicontinuous f) (s : Set α)
    (x : α) : LowerSemicontinuousWithinAt f s x :=
  (h x).semicontinuousWithinAt s

theorem LowerSemicontinuous.lowerSemicontinuousOn (h : LowerSemicontinuous f) (s : Set α) :
    LowerSemicontinuousOn f s :=
  h.semicontinuousOn s

/-! #### Constants -/

theorem lowerSemicontinuousWithinAt_const : LowerSemicontinuousWithinAt (fun _x => z) s x :=
  SemicontinuousWithinAt.const

theorem lowerSemicontinuousAt_const : LowerSemicontinuousAt (fun _x => z) x :=
  SemicontinuousAt.const

theorem lowerSemicontinuousOn_const : LowerSemicontinuousOn (fun _x => z) s :=
  SemicontinuousOn.const

theorem lowerSemicontinuous_const : LowerSemicontinuous fun _x : α => z :=
  Semicontinuous.const

/-! #### Composition -/
section

variable {g : γ → α} {x : γ} {t : Set γ}

theorem LowerSemicontinuousWithinAt.comp
    (hf : LowerSemicontinuousWithinAt f s (g x)) (hg : ContinuousWithinAt g t x)
    (hg' : MapsTo g t s) :
    LowerSemicontinuousWithinAt (f ∘ g) t x :=
  SemicontinuousWithinAt.comp hf hg hg'

theorem LowerSemicontinuousAt.comp
    (hf : LowerSemicontinuousAt f (g x)) (hg : ContinuousAt g x) :
    LowerSemicontinuousAt (f ∘ g) x :=
  SemicontinuousAt.comp hf hg

theorem LowerSemicontinuousOn.comp
    (hf : LowerSemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    LowerSemicontinuousOn (f ∘ g) t :=
  SemicontinuousOn.comp hf hg hg'

theorem LowerSemicontinuous.comp
    (hf : LowerSemicontinuous f) (hg : Continuous g) : LowerSemicontinuous (f ∘ g) :=
  Semicontinuous.comp hf hg

end

/-!
### Upper semicontinuous functions
-/


/-! #### Basic dot notation interface for upper semicontinuity -/


theorem UpperSemicontinuousWithinAt.mono (h : UpperSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    UpperSemicontinuousWithinAt f t x :=
  SemicontinuousWithinAt.mono h hst

theorem UpperSemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : UpperSemicontinuousWithinAt f s a)
    (has : a ∈ s) (hfg : ∀ᶠ x in nhdsWithin a s, f x = g x) :
    UpperSemicontinuousWithinAt g s a :=
  LowerSemicontinuousWithinAt.congr_of_eventuallyEq (β := βᵒᵈ) h has hfg

theorem upperSemicontinuousWithinAt_univ_iff :
    UpperSemicontinuousWithinAt f univ x ↔ UpperSemicontinuousAt f x :=
  semicontinuousWithinAt_univ_iff

@[simp] theorem upperSemicontinuousOn_iff_restrict {s : Set α} :
    UpperSemicontinuous (s.restrict f) ↔ UpperSemicontinuousOn f s :=
  lowerSemicontinuous_restrict_iff (β := βᵒᵈ)

theorem UpperSemicontinuousAt.upperSemicontinuousWithinAt (s : Set α)
    (h : UpperSemicontinuousAt f x) : UpperSemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt s

theorem UpperSemicontinuousOn.upperSemicontinuousWithinAt (h : UpperSemicontinuousOn f s)
    (hx : x ∈ s) : UpperSemicontinuousWithinAt f s x :=
  h x hx

theorem UpperSemicontinuousOn.mono (h : UpperSemicontinuousOn f s) (hst : t ⊆ s) :
    UpperSemicontinuousOn f t :=
  SemicontinuousOn.mono h hst

theorem upperSemicontinuousOn_univ_iff : UpperSemicontinuousOn f univ ↔ UpperSemicontinuous f :=
  semicontinuousOn_univ_iff

theorem UpperSemicontinuous.upperSemicontinuousAt (h : UpperSemicontinuous f) (x : α) :
    UpperSemicontinuousAt f x :=
  h x

theorem UpperSemicontinuous.upperSemicontinuousWithinAt (h : UpperSemicontinuous f) (s : Set α)
    (x : α) : UpperSemicontinuousWithinAt f s x :=
  (h x).semicontinuousWithinAt s

theorem UpperSemicontinuous.upperSemicontinuousOn (h : UpperSemicontinuous f) (s : Set α) :
    UpperSemicontinuousOn f s :=
  h.semicontinuousOn s

/-! #### Constants -/

theorem upperSemicontinuousWithinAt_const : UpperSemicontinuousWithinAt (fun _x => z) s x :=
  SemicontinuousWithinAt.const

theorem upperSemicontinuousAt_const : UpperSemicontinuousAt (fun _x => z) x :=
  SemicontinuousAt.const

theorem upperSemicontinuousOn_const : UpperSemicontinuousOn (fun _x => z) s :=
  SemicontinuousOn.const

theorem upperSemicontinuous_const : UpperSemicontinuous fun _x : α => z :=
  Semicontinuous.const

/-! #### Composition -/

section

variable {g : γ → α} {c : γ} {t : Set γ}

theorem UpperSemicontinuousWithinAt.comp
    (hf : UpperSemicontinuousWithinAt f s (g c)) (hg : ContinuousWithinAt g t c)
    (hg' : MapsTo g t s) :
    UpperSemicontinuousWithinAt (f ∘ g) t c :=
  SemicontinuousWithinAt.comp (r := (f · < ·)) hf hg hg' -- the elaboration aid is necessary.

theorem UpperSemicontinuousAt.comp
    (hf : UpperSemicontinuousAt f (g c)) (hg : ContinuousAt g c) :
    UpperSemicontinuousAt (f ∘ g) c :=
  SemicontinuousAt.comp (r := (f · < ·)) hf hg

theorem UpperSemicontinuousOn.comp
    (hf : UpperSemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    UpperSemicontinuousOn (f ∘ g) t :=
  SemicontinuousOn.comp (r := (f · < ·)) hf hg hg'

theorem UpperSemicontinuous.comp
    (hf : UpperSemicontinuous f) (hg : Continuous g) : UpperSemicontinuous (f ∘ g) :=
  Semicontinuous.comp (r := (f · < ·)) hf hg

end

end Preorder

section Hemi

/-! ## Lower and Upper Semicontinuity -/

variable [TopologicalSpace β]

section Definitions

/-- A real function `f` is lower semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in `s`, then `f x'` is at least `f x - ε`. We formulate this in a general
preordered space, using an arbitrary `y < f x` instead of `f x - ε`. -/
abbrev LowerHemicontinuousWithinAt (f : α → Set β) (s : Set α) (x : α) :=
  SemicontinuousWithinAt (fun x s ↦ IsOpen s ∧ ((f x) ∩ s).Nonempty) s x

/-- A real function `f` is lower semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at least `f x - ε`. We formulate this in
a general preordered space, using an arbitrary `y < f x` instead of `f x - ε`. -/
abbrev LowerHemicontinuousOn (f : α → Set β) (s : Set α) :=
  SemicontinuousOn (fun x s ↦ IsOpen s ∧ ((f x) ∩ s).Nonempty) s

/-- A real function `f` is lower semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
abbrev LowerHemicontinuousAt (f : α → Set β) (x : α) :=
  SemicontinuousAt (fun x s ↦ IsOpen s ∧ ((f x) ∩ s).Nonempty) x

/-- A real function `f` is lower semicontinuous if, for any `ε > 0`, for any `x`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
abbrev LowerHemicontinuous (f : α → Set β) :=
  Semicontinuous (fun x s ↦ IsOpen s ∧ ((f x) ∩ s).Nonempty)

open scoped Topology

/-- A real function `f` is upper semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We formulate this in a general
preordered space, using an arbitrary `y > f x` instead of `f x + ε`. -/
abbrev UpperHemicontinuousWithinAt (f : α → Set β) (s : Set α) (x : α) :=
  SemicontinuousWithinAt (fun x s ↦ s ∈ 𝓝ˢ (f x)) s x

/-- A real function `f` is upper semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We formulate this in a
general preordered space, using an arbitrary `y > f x` instead of `f x + ε`. -/
abbrev UpperHemicontinuousOn (f : α → Set β) (s : Set α) :=
  SemicontinuousOn (fun x s ↦ s ∈ 𝓝ˢ (f x)) s

/-- A real function `f` is upper semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered space,
using an arbitrary `y > f x` instead of `f x + ε`. -/
abbrev UpperHemicontinuousAt (f : α → Set β) (x : α) :=
  SemicontinuousAt (fun x s ↦ s ∈ 𝓝ˢ (f x)) x

/-- A real function `f` is upper semicontinuous if, for any `ε > 0`, for any `x`, for all `x'`
close enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered
space, using an arbitrary `y > f x` instead of `f x + ε`. -/
abbrev UpperHemicontinuous (f : α → Set β) :=
  Semicontinuous (fun x s ↦ s ∈ 𝓝ˢ (f x))

lemma lowerHemicontinuousWithinAt_iff {f : α → Set β} {s : Set α} {x : α} :
    LowerHemicontinuousWithinAt f s x ↔
      ∀ u, IsOpen u → ((f x) ∩ u).Nonempty → ∀ᶠ x' in 𝓝[s] x, ((f x') ∩ u).Nonempty := by
  simp +contextual [SemicontinuousWithinAt]

lemma lowerHemicontinuousOn_iff {f : α → Set β} {s : Set α} :
    LowerHemicontinuousOn f s ↔ ∀ x ∈ s, LowerHemicontinuousWithinAt f s x :=
  Iff.rfl

lemma lowerHemicontinuousAt_iff {f : α → Set β} {x : α} :
    LowerHemicontinuousAt f x ↔
      ∀ u, IsOpen u → ((f x) ∩ u).Nonempty → ∀ᶠ x' in 𝓝 x, ((f x') ∩ u).Nonempty := by
  simp +contextual [SemicontinuousAt]

lemma lowerHemicontinuous_iff {f : α → Set β} :
    LowerHemicontinuous f ↔ ∀ x, LowerHemicontinuousAt f x :=
  Iff.rfl

lemma upperHemicontinuousWithinAt_iff {f : α → Set β} {s : Set α} {x : α} :
    UpperHemicontinuousWithinAt f s x ↔ ∀ t, t ∈ 𝓝ˢ (f x) → ∀ᶠ x' in 𝓝[s] x, t ∈ 𝓝ˢ (f x') :=
  Iff.rfl

lemma upperHemicontinuousOn_iff {f : α → Set β} {s : Set α} :
    UpperHemicontinuousOn f s ↔ ∀ x ∈ s, UpperHemicontinuousWithinAt f s x :=
  Iff.rfl

lemma upperHemicontinuousAt_iff {f : α → Set β} {x : α} :
    UpperHemicontinuousAt f x ↔ ∀ t, t ∈ 𝓝ˢ (f x) → ∀ᶠ x' in 𝓝 x, t ∈ 𝓝ˢ (f x') :=
  Iff.rfl

lemma upperHemicontinuous_iff {f : α → Set β} :
    UpperHemicontinuous f ↔ ∀ x, UpperHemicontinuousAt f x :=
  Iff.rfl

end Definitions

/-!
### Lower semicontinuous functions
-/

/-! #### Basic dot notation interface for lower semicontinuity -/

variable {f g : α → Set β} {x : α} {s t : Set α} {y z : Set β}

theorem LowerHemicontinuousWithinAt.mono (h : LowerHemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    LowerHemicontinuousWithinAt f t x :=
  SemicontinuousWithinAt.mono h hst

theorem LowerHemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : LowerHemicontinuousWithinAt f s a)
    (has : a ∈ s) (hfg : f =ᶠ[𝓝[s] a] g) :
    LowerHemicontinuousWithinAt g s a :=
  SemicontinuousWithinAt.congr_of_eventuallyEq h has <| by
    filter_upwards [hfg] with x hx
    simp [hx]

theorem lowerHemicontinuousWithinAt_univ_iff :
    LowerHemicontinuousWithinAt f univ x ↔ LowerHemicontinuousAt f x :=
  semicontinuousWithinAt_univ_iff

theorem LowerHemicontinuousAt.lowerHemicontinuousWithinAt (s : Set α)
    (h : LowerHemicontinuousAt f x) : LowerHemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt s

theorem LowerHemicontinuousOn.lowerHemicontinuousWithinAt (h : LowerHemicontinuousOn f s)
    (hx : x ∈ s) : LowerHemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt hx

theorem LowerHemicontinuousOn.mono (h : LowerHemicontinuousOn f s) (hst : t ⊆ s) :
    LowerHemicontinuousOn f t :=
  SemicontinuousOn.mono h hst

theorem lowerHemicontinuousOn_univ_iff : LowerHemicontinuousOn f univ ↔ LowerHemicontinuous f :=
  semicontinuousOn_univ_iff

@[simp] theorem lowerHemicontinuous_restrict_iff :
    LowerHemicontinuous (s.restrict f) ↔ LowerHemicontinuousOn f s :=
  semicontinuous_restrict_iff (r := (fun x t ↦ IsOpen t ∧ ((f x) ∩ t).Nonempty))

theorem LowerHemicontinuous.lowerHemicontinuousAt (h : LowerHemicontinuous f) (x : α) :
    LowerHemicontinuousAt f x :=
  h x

theorem LowerHemicontinuous.lowerHemicontinuousWithinAt (h : LowerHemicontinuous f) (s : Set α)
    (x : α) : LowerHemicontinuousWithinAt f s x :=
  (h x).semicontinuousWithinAt s

theorem LowerHemicontinuous.lowerHemicontinuousOn (h : LowerHemicontinuous f) (s : Set α) :
    LowerHemicontinuousOn f s :=
  h.semicontinuousOn s

/-! #### Constants -/

theorem LowerHemicontinuousWithinAt.const : LowerHemicontinuousWithinAt (fun _x => z) s x :=
  SemicontinuousWithinAt.const

theorem LowerHemicontinuousAt.const : LowerHemicontinuousAt (fun _x => z) x :=
  SemicontinuousAt.const

theorem LowerHemicontinuousOn.const : LowerHemicontinuousOn (fun _x => z) s :=
  SemicontinuousOn.const

theorem LowerHemicontinuous.const : LowerHemicontinuous fun _x : α => z :=
  Semicontinuous.const

/-! #### Composition -/
section

variable {g : γ → α} {x : γ} {t : Set γ}

theorem LowerHemicontinuousWithinAt.comp
    (hf : LowerHemicontinuousWithinAt f s (g x)) (hg : ContinuousWithinAt g t x)
    (hg' : MapsTo g t s) :
    LowerHemicontinuousWithinAt (f ∘ g) t x :=
  SemicontinuousWithinAt.comp hf hg hg'

theorem LowerHemicontinuousAt.comp
    (hf : LowerHemicontinuousAt f (g x)) (hg : ContinuousAt g x) :
    LowerHemicontinuousAt (f ∘ g) x :=
  SemicontinuousAt.comp hf hg

theorem LowerHemicontinuousOn.comp
    (hf : LowerHemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    LowerHemicontinuousOn (f ∘ g) t :=
  SemicontinuousOn.comp hf hg hg'

theorem LowerHemicontinuous.comp
    (hf : LowerHemicontinuous f) (hg : Continuous g) : LowerHemicontinuous (f ∘ g) :=
  Semicontinuous.comp hf hg

end

/-!
### Upper semicontinuous functions
-/


/-! #### Basic dot notation interface for upper semicontinuity -/


theorem UpperHemicontinuousWithinAt.mono (h : UpperHemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    UpperHemicontinuousWithinAt f t x :=
  SemicontinuousWithinAt.mono h hst

theorem UpperHemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : UpperHemicontinuousWithinAt f s a)
    (has : a ∈ s) (hfg : ∀ᶠ x in nhdsWithin a s, f x = g x) :
    UpperHemicontinuousWithinAt g s a :=
  SemicontinuousWithinAt.congr_of_eventuallyEq h has <| by
    filter_upwards [hfg] with x hx
    simp [hx]

theorem upperHemicontinuousWithinAt_univ_iff :
    UpperHemicontinuousWithinAt f univ x ↔ UpperHemicontinuousAt f x :=
  semicontinuousWithinAt_univ_iff

@[simp] theorem upperHemicontinuousOn_iff_restrict {s : Set α} :
    UpperHemicontinuous (s.restrict f) ↔ UpperHemicontinuousOn f s :=
  semicontinuous_restrict_iff (r := (fun x t ↦ t ∈ 𝓝ˢ (f x)))

theorem UpperHemicontinuousAt.upperHemicontinuousWithinAt (s : Set α)
    (h : UpperHemicontinuousAt f x) : UpperHemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt s

theorem UpperHemicontinuousOn.upperHemicontinuousWithinAt (h : UpperHemicontinuousOn f s)
    (hx : x ∈ s) : UpperHemicontinuousWithinAt f s x :=
  h x hx

theorem UpperHemicontinuousOn.mono (h : UpperHemicontinuousOn f s) (hst : t ⊆ s) :
    UpperHemicontinuousOn f t :=
  SemicontinuousOn.mono h hst

theorem upperHemicontinuousOn_univ_iff : UpperHemicontinuousOn f univ ↔ UpperHemicontinuous f :=
  semicontinuousOn_univ_iff

theorem UpperHemicontinuous.upperHemicontinuousAt (h : UpperHemicontinuous f) (x : α) :
    UpperHemicontinuousAt f x :=
  h x

theorem UpperHemicontinuous.upperHemicontinuousWithinAt (h : UpperHemicontinuous f) (s : Set α)
    (x : α) : UpperHemicontinuousWithinAt f s x :=
  (h x).semicontinuousWithinAt s

theorem UpperHemicontinuous.upperHemicontinuousOn (h : UpperHemicontinuous f) (s : Set α) :
    UpperHemicontinuousOn f s :=
  h.semicontinuousOn s

/-! #### Constants -/

theorem UpperHemicontinuousWithinAt.const : UpperHemicontinuousWithinAt (fun _x => z) s x :=
  SemicontinuousWithinAt.const

theorem UpperHemicontinuousAt.const : UpperHemicontinuousAt (fun _x => z) x :=
  SemicontinuousAt.const

theorem UpperHemicontinuousOn.const : UpperHemicontinuousOn (fun _x => z) s :=
  SemicontinuousOn.const

theorem UpperHemicontinuous.const : UpperHemicontinuous fun _x : α => z :=
  Semicontinuous.const

/-! #### Composition -/

section

variable {g : γ → α} {c : γ} {t : Set γ}

theorem UpperHemicontinuousWithinAt.comp
    (hf : UpperHemicontinuousWithinAt f s (g c)) (hg : ContinuousWithinAt g t c)
    (hg' : MapsTo g t s) :
    UpperHemicontinuousWithinAt (f ∘ g) t c :=
  -- the elaboration aid is necessary.
  SemicontinuousWithinAt.comp (r := (fun x t ↦ t ∈ 𝓝ˢ (f x))) hf hg hg'

theorem UpperHemicontinuousAt.comp
    (hf : UpperHemicontinuousAt f (g c)) (hg : ContinuousAt g c) :
    UpperHemicontinuousAt (f ∘ g) c :=
  SemicontinuousAt.comp (r := (fun x t ↦ t ∈ 𝓝ˢ (f x))) hf hg

theorem UpperHemicontinuousOn.comp
    (hf : UpperHemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    UpperHemicontinuousOn (f ∘ g) t :=
  SemicontinuousOn.comp (r := (fun x t ↦ t ∈ 𝓝ˢ (f x))) hf hg hg'

theorem UpperHemicontinuous.comp
    (hf : UpperHemicontinuous f) (hg : Continuous g) : UpperHemicontinuous (f ∘ g) :=
  Semicontinuous.comp (r := (fun x t ↦ t ∈ 𝓝ˢ (f x))) hf hg

end

end Hemi
