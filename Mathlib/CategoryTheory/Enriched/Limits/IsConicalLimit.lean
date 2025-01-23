/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Conical limits in enriched ordinary categories

A limit cone in the underlying category of an enriched ordinary category is a *conical limit* if
it is a limit cone in the underlying ordinary category and moreover this limit cone is preserved
by covariant enriched representable functors. These conditions are encoded in the structure
`IsConicalLimit`.

The universal property of a conical limit is enriched as follows: the canonical comparison map
defines an isomorphism in the enriching category:

`limitComparisonIso (h : IsConicalLimit V c) : (X ⟶[V] c.pt) ≅ (limit (F ⋙ eCoyoneda V X))`

Conversely, if the canonical maps define isomorphisms for all `X` then `c` is a conical limit cone:

`ofIsIsoLimitComparison [∀ X, IsIso (IsConicalLimit.limitComparison V c X)]`
`(hc : IsLimit c) : IsConicalLimit V c`

This file develops some general API for conical limits in enriched ordinary categories.

## References

* [Kelly G.M., *Basic concepts of enriched category theory*][kelly2005]

See section 3.8 for a similar treatment, although the content of this file is not directly
adapted from there.

## TODO

Dualize everything to define conical colimits.
-/

universe v₁ u₁ w v' v u u'

namespace CategoryTheory.Enriched

open Limits

variable {J : Type u₁} [Category.{v₁} J]
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable {F : J ⥤ C} (c : Cone F) (X : C)

/--
A limit cone `c` in a `V`-enriched ordinary category `C` is a *`V`-enriched limit*
(or *conical limit*) if for every `X : C`, the cone obtained by applying the coyoneda
functor `(X ⟶[V] -)` to `c` is a limit cone in `V`.
-/
structure IsConicalLimit where
  /-- A conical limit cone is a limit cone. -/
  isLimit : IsLimit c
  /--
  The cone obtained by applying the coyoneda functor `(X ⟶[V] -)` to `c` is a limit cone in `V`.
  -/
  isConicalLimit (X : C) : IsLimit <| (eCoyoneda V X).mapCone c

namespace IsConicalLimit

variable {c}

/-- If the enriched coyoneda functor preserves limits of `F` then
any limit cone is conical. -/
noncomputable
def ofLimit (hc : IsLimit c) [hp : ∀ Y, PreservesLimit F (eCoyoneda V Y)] : IsConicalLimit V c where
  isLimit := hc
  isConicalLimit (Y : C) := (Classical.choice <| (hp Y).preserves hc)

/-- If the enriched coyoneda preserves limits of `F` then limit cones are conical limit cones. -/
example [hp : ∀ Y, PreservesLimit F (eCoyoneda V Y)] :
    Nonempty (IsConicalLimit V c) ↔ Nonempty (IsLimit c) :=
  ⟨(⟨Classical.choice · |>.isLimit⟩), (⟨ofLimit V <| Classical.choice ·⟩)⟩

variable {V}

/-- Transport evidence that a cone is a `V`-enriched limit cone across an isomorphism of cones. -/
noncomputable def ofIso {r₁ r₂ : Cone F} (h : IsConicalLimit V r₁) (i : r₁ ≅ r₂) :
    IsConicalLimit V r₂ where
  isLimit := h.isLimit.ofIsoLimit i
  isConicalLimit X := h.isConicalLimit X |>.ofIsoLimit
    { hom := Functor.mapConeMorphism _ i.hom
      inv := Functor.mapConeMorphism _ i.inv
      hom_inv_id := by simp only [Functor.mapCone, Functor.mapConeMorphism, Iso.map_hom_inv_id]
      inv_hom_id := by simp only [Functor.mapCone, Functor.mapConeMorphism, Iso.map_inv_hom_id] }

/-!
## Characterization in terms of the comparison map.

There is a canonical comparison map with the limit in `V`, the following proves that a limit
cone in `C` is a `V`-enriched limit if and only if the comparison map is an isomorphism
for every `X : C`.
-/

variable [HasLimit (F ⋙ eCoyoneda V X)]

variable (V) (c) in

/-- The canonical comparison map with the limit in `V`. -/
noncomputable def limitComparison :
    (X ⟶[V] c.pt) ⟶ limit (F ⋙ eCoyoneda V X) :=
  limit.lift _ <| (eCoyoneda V X).mapCone c

lemma limitComparison_eq_conePointUniqueUpToIso (h : IsConicalLimit V c) :
    limitComparison V c X =
    ((h.isConicalLimit X).conePointUniqueUpToIso (limit.isLimit _)).hom := by
  apply limit.hom_ext
  simp [limitComparison]

/-- `IsConicalLimit.limitComparison` is an isomorphism. -/
lemma isIso_limitComparison (h : IsConicalLimit V c) : IsIso (limitComparison V c X) := by
  rw [limitComparison_eq_conePointUniqueUpToIso X (h := h)]
  infer_instance

/-- For all `X : C`, the canonical comparison map with the limit in `V` as isomorphism -/
noncomputable def limitComparisonIso (h : IsConicalLimit V c) :
    (X ⟶[V] c.pt) ≅ (limit (F ⋙ eCoyoneda V X)) := by
  have := isIso_limitComparison X h
  exact (asIso (limitComparison V c X))

variable [∀ Y, HasLimit (F ⋙ eCoyoneda V Y)]

variable (V) in

/-- Reverse direction: if the comparison map is an isomorphism, then `c` is a conical limit. -/
noncomputable def ofIsIsoLimitComparison [∀ Y, IsIso (IsConicalLimit.limitComparison V c Y)]
    (hc : IsLimit c) : IsConicalLimit V c where
  isLimit := hc
  isConicalLimit Y := by
    suffices PreservesLimit F (eCoyoneda V Y) from
      Classical.choice (this.preserves hc)
    have : HasLimit F := ⟨c, hc⟩
    apply (config := { allowSynthFailures := true }) preservesLimit_of_isIso_post
    have h : limit.post F (eCoyoneda V Y) =
      ((eCoyoneda V Y).map ((limit.isLimit F).conePointUniqueUpToIso hc).hom) ≫
        limitComparison V c Y := by
      apply limit.hom_ext
      intro j
      simp [limitComparison, ← eHomWhiskerLeft_comp]
    rw [h]
    infer_instance

/--
A limit cone in `C` is a `V`-enriched limit if and only if the comparison map is an isomorphism
for every `X : C`.
Note: it's easier to use the two directions `isIso_limitComparison` and
`ofIsIsoLimitComparison` directly.
-/
example (hc : IsLimit c) : Nonempty (IsConicalLimit V c) ↔
    ∀ X, IsIso (limitComparison V c X) := by
  constructor
  · intro ⟨h⟩ X
    exact isIso_limitComparison X h
  · intro h
    exact ⟨ofIsIsoLimitComparison V hc⟩

end IsConicalLimit

variable (F)

/-- `ConicalLimitCone V F` contains a cone over `F` together with the information that it is a
conical limit. -/
structure ConicalLimitCone where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the limit cone -/
  isConicalLimit : IsConicalLimit V cone

end CategoryTheory.Enriched
