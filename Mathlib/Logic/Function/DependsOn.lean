/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Data.Set.Restrict

/-!
# Functions depending only on some variables

When dealing with a function `f : Π i, α i` depending on many variables, some operations
may get rid of the dependency on some variables (see `Function.updateFinset` or
`MeasureTheory.lmarginal` for example). However considering this new function
as having a different domain with fewer points is not comfortable in Lean, as it requires the use
of subtypes and can lead to tedious writing.

On the other hand one wants to be able for example to describe some function as constant
with respect to some variables, and be able to deduce this when applying transformations
mentioned above. This is why we introduce the predicate `DependsOn f s`, which states that
if `x` and `y` coincide over the set `s`, then `f x = f y`.
This is equivalent to `Function.FactorsThrough f s.restrict`.

## Main definition

* `DependsOn f s`: If `x` and `y` coincide over the set `s`, then `f x` equals `f y`.

## Main statement

* `dependsOn_iff_factorsThrough`: A function `f` depends on `s` if and only if it factors
  through `s.restrict`.

## Implementation notes

When we write `DependsOn f s`, i.e. `f` only depends on `s`, it should be interpreted as
"`f` _potentially_ depends only on variables in `s`". However it might be the case
that `f` does not depend at all on variables in `s`, for example if `f` is constant.
As a consequence, `DependsOn f univ` is always true, see `dependsOn_univ`.

The predicate `DependsOn f s` can also be interpreted as saying that `f` is independent of all
the variables which are not in `s`. Although this phrasing might seem more natural, we choose to go
with `DependsOn` because writing mathematically "independent of variables in `s`" would boil down to
`∀ x y, (∀ i ∉ s, x i = y i) → f x = f y`, which is the same as `DependsOn f sᶜ`.

## Tags

depends on
-/

open Function Set

variable {ι : Type*} {α : ι → Type*} {β : Type*}

/-- A function `f` depends on `s` if, whenever `x` and `y` coincide over `s`, `f x = f y`.

It should be interpreted as "`f` _potentially_ depends only on variables in `s`".
However it might be the case that `f` does not depend at all on variables in `s`,
for example if `f` is constant. As a consequence, `DependsOn f univ` is always true,
see `dependsOn_univ`. -/
def DependsOn (f : (Π i, α i) → β) (s : Set ι) : Prop :=
  ∀ ⦃x y⦄, (∀ i ∈ s, x i = y i) → f x = f y

lemma dependsOn_iff_factorsThrough {f : (Π i, α i) → β} {s : Set ι} :
    DependsOn f s ↔ FactorsThrough f s.restrict := by
  rw [DependsOn, FactorsThrough]
  simp [funext_iff]

lemma dependsOn_iff_exists_comp [Nonempty β] {f : (Π i, α i) → β} {s : Set ι} :
    DependsOn f s ↔ ∃ g : (Π i : s, α i) → β, f = g ∘ s.restrict := by
  rw [dependsOn_iff_factorsThrough, factorsThrough_iff]

lemma dependsOn_univ (f : (Π i, α i) → β) : DependsOn f univ :=
  fun _ _ h ↦ congrArg _ <| funext fun i ↦ h i trivial

variable {f : (Π i, α i) → β}

/-- A constant function does not depend on any variable. -/
lemma dependsOn_const (b : β) : DependsOn (fun _ : Π i, α i ↦ b) ∅ := by simp [DependsOn]

lemma DependsOn.mono {s t : Set ι} (hst : s ⊆ t) (hf : DependsOn f s) : DependsOn f t :=
  fun _ _ h ↦ hf fun i hi ↦ h i (hst hi)

/-- A function which depends on the empty set is constant. -/
lemma DependsOn.empty (hf : DependsOn f ∅) (x y : Π i, α i) : f x = f y := hf (by simp)

lemma Set.dependsOn_restrict (s : Set ι) : DependsOn (s.restrict (π := α)) s :=
  fun _ _ h ↦ funext fun i ↦ h i.1 i.2
