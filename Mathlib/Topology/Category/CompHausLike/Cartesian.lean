/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.Topology.Category.CompHausLike.Limits

/-!

# Cartesian monoidal structure on `CompHausLike`

If the predicate `P` is preserved under taking type-theoretic products and `PUnit` satisfies it,
then `CompHausLike P` is a cartesian monoidal category.
-/

universe u

open CategoryTheory Limits

namespace CompHausLike

variable {P : TopCat.{u} → Prop} (X Y : CompHausLike.{u} P) [HasProp P (X × Y)]

/--
Explicit binary fan in `CompHausLike P`, given that the predicate `P` is preserved under taking
type-theoretic products.
-/
def productCone : BinaryFan X Y :=
  BinaryFan.mk (P := CompHausLike.of P (X × Y))
    (TopCat.ofHom { toFun := Prod.fst }) (TopCat.ofHom { toFun := Prod.snd })

/--
When the predicate `P` is preserved under taking type-theoretic products, that product is a
category-theoretic product in `CompHausLike P`.
-/
noncomputable def productIsLimit : IsLimit (productCone X Y) where
  lift := fun S : BinaryFan X Y ↦ TopCat.ofHom {
    toFun := fun s ↦ (S.fst s, S.snd s)  }
  fac := by rintro S (_ | _) <;> {dsimp; ext; rfl}
  uniq := by
    intro S m h
    ext x
    refine Prod.ext ?_ ?_
    · specialize h ⟨WalkingPair.left⟩
      apply_fun fun e ↦ e x at h
      exact h
    · specialize h ⟨WalkingPair.right⟩
      apply_fun fun e ↦ e x at h
      exact h

/--
When the predicate `P` is preserved under taking type-theoretic products and `PUnit` satisfies it,
then `CompHausLike P` is a cartesian monoidal category.

This could be an instance but that causes some slowness issues with typeclass search, therefore we
keep it as a def and turn it on as an instance for the explicit examples of `CompHausLike` as
needed.
-/
noncomputable def cartesianMonoidalCategory [∀ (X Y : CompHausLike.{u} P), HasProp P (X × Y)]
    [HasProp P PUnit.{u + 1}] : CartesianMonoidalCategory (CompHausLike.{u} P) :=
  .ofChosenFiniteProducts
    ⟨_, CompHausLike.isTerminalPUnit⟩
    (fun X Y ↦ ⟨productCone X Y, productIsLimit X Y⟩)

end CompHausLike
