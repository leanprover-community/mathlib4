/-
Copyright (c) 2026 Victor Boscaro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Boscaro
-/
module

public import Mathlib.CategoryTheory.Category.Basic

/-!
# The walking arrow

This file defines `CategoryTheory.Limits.WalkingArrow`, the small category with two
objects `zero` and `one` and a single non-identity morphism `zero ⟶ one`. It is the
universal shape of a morphism, sitting alongside `WalkingPair`, `WalkingParallelPair`,
`WalkingCospan`, and `WalkingSpan`: functors `WalkingArrow ⥤ C` correspond to the
data of a morphism in `C`, i.e. to objects of the arrow category `Arrow C`.

The object names `zero` and `one` are chosen to match `WalkingParallelPair`; the
single non-identity morphism is named `arrow : zero ⟶ one`.

## Main definitions

* `CategoryTheory.Limits.WalkingArrow` — the inductive type with constructors `zero`,
  `one`.
* `CategoryTheory.Limits.WalkingArrowHom` — the type family of morphisms, with
  constructors `id X` and `arrow : zero ⟶ one`.
* `CategoryTheory.Limits.walkingArrowHomCategory` — the `SmallCategory` instance.

## Main results

* `CategoryTheory.Limits.walkingArrowHom_id` rewrites the bundled identity
  constructor to the categorical identity.

## Future work

* The equivalence of categories `(WalkingArrow ⥤ C) ≌ Arrow C` identifying functors
  out of the walking arrow with objects of the arrow category, deferred to a
  follow-up PR.
* The opposite/symmetry functor `WalkingArrow ⥤ WalkingArrowᵒᵖ`.

## References

* Cf. `Mathlib.CategoryTheory.Limits.Shapes.Equalizers` for the parallel-pair
  analog (`WalkingParallelPair`) from which the object naming `zero`/`one` is
  taken.

## Tags

walking arrow, arrow category, shape, small category
-/

@[expose] public section

namespace CategoryTheory.Limits

/-- The type of objects for the diagram indexing a single morphism (the "walking
arrow"). -/
inductive WalkingArrow : Type
  | zero
  | one
  deriving DecidableEq, Inhabited

open WalkingArrow

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will
-- complain about.
set_option genSizeOfSpec false in
/-- The type family of morphisms for the walking arrow diagram: identities together
with a single non-identity arrow `arrow : zero ⟶ one`. -/
inductive WalkingArrowHom : WalkingArrow → WalkingArrow → Type
  | id (X : WalkingArrow) : WalkingArrowHom X X
  | arrow : WalkingArrowHom zero one
  deriving DecidableEq

/-- Satisfying the inhabited linter. -/
instance : Inhabited (WalkingArrowHom zero one) where
  default := WalkingArrowHom.arrow

open WalkingArrowHom

/-- Composition of morphisms in the walking arrow diagram. -/
def WalkingArrowHom.comp :
    ∀ {X Y Z : WalkingArrow} (_ : WalkingArrowHom X Y)
      (_ : WalkingArrowHom Y Z), WalkingArrowHom X Z
  | _, _, _, id _, h => h
  | _, _, _, arrow, id one => arrow

/-- Left identity for composition in the walking arrow diagram. -/
theorem WalkingArrowHom.id_comp
    {X Y : WalkingArrow} (g : WalkingArrowHom X Y) : comp (id X) g = g :=
  rfl

/-- Right identity for composition in the walking arrow diagram. -/
theorem WalkingArrowHom.comp_id
    {X Y : WalkingArrow} (f : WalkingArrowHom X Y) : comp f (id Y) = f := by
  cases f <;> rfl

/-- Associativity of composition in the walking arrow diagram. -/
theorem WalkingArrowHom.assoc {X Y Z W : WalkingArrow}
    (f : WalkingArrowHom X Y) (g : WalkingArrowHom Y Z)
    (h : WalkingArrowHom Z W) : comp (comp f g) h = comp f (comp g h) := by
  cases f <;> cases g <;> cases h <;> rfl

/-- The small category structure on `WalkingArrow`. -/
instance walkingArrowHomCategory : SmallCategory WalkingArrow where
  Hom := WalkingArrowHom
  id := id
  comp := comp
  comp_id := comp_id
  id_comp := id_comp
  assoc := assoc

/-- The bundled identity constructor agrees with the categorical identity. -/
@[simp]
theorem walkingArrowHom_id (X : WalkingArrow) : WalkingArrowHom.id X = 𝟙 X :=
  rfl

end CategoryTheory.Limits
