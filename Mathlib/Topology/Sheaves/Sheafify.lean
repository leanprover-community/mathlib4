/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Stalks

#align_import topology.sheaves.sheafify from "leanprover-community/mathlib"@"bb103f356534a9a7d3596a672097e375290a4c3a"

/-!
# Sheafification of `Type` valued presheaves

We construct the sheafification of a `Type` valued presheaf,
as the subsheaf of dependent functions into the stalks
consisting of functions which are locally germs.

We show that the stalks of the sheafification are isomorphic to the original stalks,
via `stalkToFiber` which evaluates a germ of a dependent function at a point.

We construct a morphism `toSheafify` from a presheaf to (the underlying presheaf of)
its sheafification, given by sending a section to its collection of germs.

## Future work
Show that the map induced on stalks by `toSheafify` is the inverse of `stalkToFiber`.

Show sheafification is a functor from presheaves to sheaves,
and that it is the left adjoint of the forgetful functor,
following <https://stacks.math.columbia.edu/tag/007X>.
-/


universe v

noncomputable section

open TopCat Opposite TopologicalSpace CategoryTheory

variable {X : TopCat.{v}} (F : Presheaf (Type v) X)

namespace TopCat.Presheaf
set_option linter.uppercaseLean3 false -- `Top`

namespace Sheafify

/--
The prelocal predicate on functions into the stalks, asserting that the function is equal to a germ.
-/
def isGerm : PrelocalPredicate fun x => F.stalk x where
  pred {U} f := ∃ g : F.obj (op U), ∀ x : U, f x = F.germ x g
  res := fun i _ ⟨g, p⟩ => ⟨F.map i.op g, fun x => (p (i x)).trans (F.germ_res_apply i x g).symm⟩
#align Top.presheaf.sheafify.is_germ TopCat.Presheaf.Sheafify.isGerm

/-- The local predicate on functions into the stalks,
asserting that the function is locally equal to a germ.
-/
def isLocallyGerm : LocalPredicate fun x => F.stalk x :=
  (isGerm F).sheafify
#align Top.presheaf.sheafify.is_locally_germ TopCat.Presheaf.Sheafify.isLocallyGerm

end Sheafify

/-- The sheafification of a `Type` valued presheaf, defined as the functions into the stalks which
are locally equal to germs.
-/
def sheafify : Sheaf (Type v) X :=
  subsheafToTypes (Sheafify.isLocallyGerm F)
#align Top.presheaf.sheafify TopCat.Presheaf.sheafify

/-- The morphism from a presheaf to its sheafification,
sending each section to its germs.
(This forms the unit of the adjunction.)
-/
def toSheafify : F ⟶ F.sheafify.1 where
  app U f := ⟨fun x => F.germ x f, PrelocalPredicate.sheafifyOf ⟨f, fun x => rfl⟩⟩
  naturality U U' f := by
    ext x
    apply Subtype.ext -- Porting note: Added `apply`
    ext ⟨u, m⟩
    exact germ_res_apply F f.unop ⟨u, m⟩ x
#align Top.presheaf.to_sheafify TopCat.Presheaf.toSheafify

/-- The natural morphism from the stalk of the sheafification to the original stalk.
In `sheafifyStalkIso` we show this is an isomorphism.
-/
def stalkToFiber (x : X) : F.sheafify.presheaf.stalk x ⟶ F.stalk x :=
  TopCat.stalkToFiber (Sheafify.isLocallyGerm F) x
#align Top.presheaf.stalk_to_fiber TopCat.Presheaf.stalkToFiber

theorem stalkToFiber_surjective (x : X) : Function.Surjective (F.stalkToFiber x) := by
  apply TopCat.stalkToFiber_surjective
  intro t
  obtain ⟨U, m, s, rfl⟩ := F.germ_exist _ t
  use ⟨U, m⟩
  fconstructor
  · exact fun y => F.germ y s
  · exact ⟨PrelocalPredicate.sheafifyOf ⟨s, fun _ => rfl⟩, rfl⟩
#align Top.presheaf.stalk_to_fiber_surjective TopCat.Presheaf.stalkToFiber_surjective

theorem stalkToFiber_injective (x : X) : Function.Injective (F.stalkToFiber x) := by
  apply TopCat.stalkToFiber_injective
  intro U V fU hU fV hV e
  rcases hU ⟨x, U.2⟩ with ⟨U', mU, iU, gU, wU⟩
  rcases hV ⟨x, V.2⟩ with ⟨V', mV, iV, gV, wV⟩
  have wUx := wU ⟨x, mU⟩
  dsimp at wUx; erw [wUx] at e; clear wUx
  have wVx := wV ⟨x, mV⟩
  dsimp at wVx; erw [wVx] at e; clear wVx
  rcases F.germ_eq x mU mV gU gV e with ⟨W, mW, iU', iV', (e' : F.map iU'.op gU = F.map iV'.op gV)⟩
  use ⟨W ⊓ (U' ⊓ V'), ⟨mW, mU, mV⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · change W ⊓ (U' ⊓ V') ⟶ U.obj
    exact Opens.infLERight _ _ ≫ Opens.infLELeft _ _ ≫ iU
  · change W ⊓ (U' ⊓ V') ⟶ V.obj
    exact Opens.infLERight _ _ ≫ Opens.infLERight _ _ ≫ iV
  · intro w
    specialize wU ⟨w.1, w.2.2.1⟩
    specialize wV ⟨w.1, w.2.2.2⟩
    dsimp at wU wV ⊢
    erw [wU, ← F.germ_res iU' ⟨w, w.2.1⟩, wV, ← F.germ_res iV' ⟨w, w.2.1⟩,
      CategoryTheory.types_comp_apply, CategoryTheory.types_comp_apply, e']
#align Top.presheaf.stalk_to_fiber_injective TopCat.Presheaf.stalkToFiber_injective

/-- The isomorphism between a stalk of the sheafification and the original stalk.
-/
def sheafifyStalkIso (x : X) : F.sheafify.presheaf.stalk x ≅ F.stalk x :=
  (Equiv.ofBijective _ ⟨stalkToFiber_injective _ _, stalkToFiber_surjective _ _⟩).toIso
#align Top.presheaf.sheafify_stalk_iso TopCat.Presheaf.sheafifyStalkIso

-- PROJECT functoriality, and that sheafification is the left adjoint of the forgetful functor.
end TopCat.Presheaf
