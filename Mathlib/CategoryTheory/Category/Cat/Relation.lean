/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Combinatorics.Quiver.ConnectedComponent

/-!
# Relation induced by a category

The hom-set of a category can be seen as a (proof relevant) relation on its objects :
Two objects are connected if there is an arrow between them.
This relation is not an equivalence but can be turned into one.

## Equivalence relation induced by a category

One can take the equivalence closure, under which two objects are connected
iif there is a zigzag of arrows between them.

As a relation, it is proof irrelavant, in the sense that it does not know by which specific zigzag
two elements are connected, only that they are.

## Implmentation notes

We rely on `Quiver.ConnectedComponent`

-/

namespace CategoryTheory.Cat

variable {C D : Cat}
variable {a b : C}
variable (F : C ⥤ D)

open Quiver

private abbrev zigzagSetoidC : Setoid C := zigzagSetoid C

/-- Transport of some x to its component -/
def toCC (x : C) := WeaklyConnectedComponent.mk x

/-- two connected objects have the same component -/
lemma cc_eq_of_connected (f : a ⟶ b) : toCC a = toCC b :=
  (.intro ∘ Hom.toPath ∘ Sum.inl) f |> .rel _ _ |> Quot.EqvGen_sound

/-- Functors transport zigzag in the domain category to zigzags in the codomain category -/
lemma transportZigzag (nep : zigzagSetoidC.r a b) : zigzagSetoidC.r (F.obj a) (F.obj b) :=
  nep.elim (fun p => p.rec (⟨Quiver.Path.nil⟩)
    (fun _ f pd' ↦ pd'.elim (fun pd ↦
      f.elim
        (fun f ↦ ⟨Quiver.Path.cons pd (.inl (F.map f))⟩)
        (fun f ↦ ⟨Quiver.Path.cons pd (.inr (F.map f))⟩))))

/-- A zigzag in the discrete category entails an equality of its extremities -/
lemma eq_of_zigzag (X) {a b : typeToCat.obj X }   (nep : zigzagSetoidC.r a b) : a.as = b.as :=
  nep.elim (fun p => p.rec rfl
    (fun _ bc abeq => abeq.trans (bc.elim (Discrete.eq_of_hom) (Eq.symm ∘ Discrete.eq_of_hom))))

/-- fmap transports a functor to a function beetwen CC -/
private def ccfmap : (WeaklyConnectedComponent C) → (WeaklyConnectedComponent D) :=
  Quotient.lift
    (s:= zigzagSetoidC)
    (Quotient.mk zigzagSetoidC ∘ F.obj)
    (fun _ _ ↦ Quot.sound ∘ transportZigzag F)

private abbrev liftedMk {α} (s : Setoid α) : Quotient s → Quotient s :=
  Quotient.lift (Quotient.mk s) (fun _ _ ↦ Quotient.sound)

/-- The connected components functor -/
def connectedComponents.{v,u} : Cat.{v, u} ⥤ Type u where
  obj C := WeaklyConnectedComponent C
  map F := ccfmap F
  map_id C := by calc
    ccfmap (𝟙 C) = liftedMk (zigzagSetoidC) := (rfl : ccfmap (𝟙 C) = liftedMk zigzagSetoidC)
    _ = id := funext fun x ↦ (Quotient.exists_rep x).elim (fun _ h ↦ by simp [h.symm])
    _ = 𝟙 (WeaklyConnectedComponent C)   := by rfl
  map_comp f g := funext (fun x ↦ (Quotient.exists_rep x).elim (fun _ h => by
  simp only [h.symm, types_comp_apply];rfl))

end CategoryTheory.Cat
