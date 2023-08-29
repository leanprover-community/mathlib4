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
    -- ⊢ (F.map f ≫ (fun U f => { val := fun x => germ F x f, property := (_ : Preloc …
    apply Subtype.ext -- Porting note: Added `apply`
    -- ⊢ ↑((F.map f ≫ (fun U f => { val := fun x => germ F x f, property := (_ : Prel …
    ext ⟨u, m⟩
    -- ⊢ ↑((F.map f ≫ (fun U f => { val := fun x => germ F x f, property := (_ : Prel …
    exact germ_res_apply F f.unop ⟨u, m⟩ x
    -- 🎉 no goals
#align Top.presheaf.to_sheafify TopCat.Presheaf.toSheafify

/-- The natural morphism from the stalk of the sheafification to the original stalk.
In `sheafifyStalkIso` we show this is an isomorphism.
-/
def stalkToFiber (x : X) : F.sheafify.presheaf.stalk x ⟶ F.stalk x :=
  TopCat.stalkToFiber (Sheafify.isLocallyGerm F) x
#align Top.presheaf.stalk_to_fiber TopCat.Presheaf.stalkToFiber

theorem stalkToFiber_surjective (x : X) : Function.Surjective (F.stalkToFiber x) := by
  apply TopCat.stalkToFiber_surjective
  -- ⊢ ∀ (t : stalk F x), ∃ U f x_1, f { val := x, property := (_ : x ∈ U.obj) } = t
  intro t
  -- ⊢ ∃ U f x_1, f { val := x, property := (_ : x ∈ U.obj) } = t
  obtain ⟨U, m, s, rfl⟩ := F.germ_exist _ t
  -- ⊢ ∃ U_1 f x_1, f { val := x, property := (_ : x ∈ U_1.obj) } = ↑(germ F { val  …
  · use ⟨U, m⟩
    -- ⊢ ∃ f x_1, f { val := x, property := (_ : x ∈ { obj := U, property := m }.obj) …
    fconstructor
    -- ⊢ (y : { x_1 // x_1 ∈ { obj := U, property := m }.obj }) → stalk F ↑y
    · exact fun y => F.germ y s
      -- 🎉 no goals
    · exact ⟨PrelocalPredicate.sheafifyOf ⟨s, fun _ => rfl⟩, rfl⟩
      -- 🎉 no goals
#align Top.presheaf.stalk_to_fiber_surjective TopCat.Presheaf.stalkToFiber_surjective

theorem stalkToFiber_injective (x : X) : Function.Injective (F.stalkToFiber x) := by
  apply TopCat.stalkToFiber_injective
  -- ⊢ ∀ (U V : OpenNhds x) (fU : (y : { x_1 // x_1 ∈ U.obj }) → stalk F ↑y), Prelo …
  intro U V fU hU fV hV e
  -- ⊢ ∃ W iU iV, ∀ (w : { x_1 // x_1 ∈ W.obj }), fU ((fun x_1 => { val := ↑x_1, pr …
  rcases hU ⟨x, U.2⟩ with ⟨U', mU, iU, gU, wU⟩
  -- ⊢ ∃ W iU iV, ∀ (w : { x_1 // x_1 ∈ W.obj }), fU ((fun x_1 => { val := ↑x_1, pr …
  rcases hV ⟨x, V.2⟩ with ⟨V', mV, iV, gV, wV⟩
  -- ⊢ ∃ W iU iV, ∀ (w : { x_1 // x_1 ∈ W.obj }), fU ((fun x_1 => { val := ↑x_1, pr …
  have wUx := wU ⟨x, mU⟩
  -- ⊢ ∃ W iU iV, ∀ (w : { x_1 // x_1 ∈ W.obj }), fU ((fun x_1 => { val := ↑x_1, pr …
  dsimp at wUx; erw [wUx] at e; clear wUx
  -- ⊢ ∃ W iU iV, ∀ (w : { x_1 // x_1 ∈ W.obj }), fU ((fun x_1 => { val := ↑x_1, pr …
                -- ⊢ ∃ W iU iV, ∀ (w : { x_1 // x_1 ∈ W.obj }), fU ((fun x_1 => { val := ↑x_1, pr …
                                -- ⊢ ∃ W iU iV, ∀ (w : { x_1 // x_1 ∈ W.obj }), fU ((fun x_1 => { val := ↑x_1, pr …
  have wVx := wV ⟨x, mV⟩
  -- ⊢ ∃ W iU iV, ∀ (w : { x_1 // x_1 ∈ W.obj }), fU ((fun x_1 => { val := ↑x_1, pr …
  dsimp at wVx; erw [wVx] at e; clear wVx
  -- ⊢ ∃ W iU iV, ∀ (w : { x_1 // x_1 ∈ W.obj }), fU ((fun x_1 => { val := ↑x_1, pr …
                -- ⊢ ∃ W iU iV, ∀ (w : { x_1 // x_1 ∈ W.obj }), fU ((fun x_1 => { val := ↑x_1, pr …
                                -- ⊢ ∃ W iU iV, ∀ (w : { x_1 // x_1 ∈ W.obj }), fU ((fun x_1 => { val := ↑x_1, pr …
  rcases F.germ_eq x mU mV gU gV e with ⟨W, mW, iU', iV', (e' : F.map iU'.op gU = F.map iV'.op gV)⟩
  -- ⊢ ∃ W iU iV, ∀ (w : { x_1 // x_1 ∈ W.obj }), fU ((fun x_1 => { val := ↑x_1, pr …
  use ⟨W ⊓ (U' ⊓ V'), ⟨mW, mU, mV⟩⟩
  -- ⊢ ∃ iU iV, ∀ (w : { x_1 // x_1 ∈ { obj := W ⊓ (U' ⊓ V'), property := (_ : x ∈  …
  refine' ⟨_, _, _⟩
  · change W ⊓ (U' ⊓ V') ⟶ U.obj
    -- ⊢ W ⊓ (U' ⊓ V') ⟶ U.obj
    exact Opens.infLERight _ _ ≫ Opens.infLELeft _ _ ≫ iU
    -- 🎉 no goals
  · change W ⊓ (U' ⊓ V') ⟶ V.obj
    -- ⊢ W ⊓ (U' ⊓ V') ⟶ V.obj
    exact Opens.infLERight _ _ ≫ Opens.infLERight _ _ ≫ iV
    -- 🎉 no goals
  · intro w
    -- ⊢ fU ((fun x_1 => { val := ↑x_1, property := (_ : ↑x_1 ∈ ↑U.obj) }) w) = fV (( …
    specialize wU ⟨w.1, w.2.2.1⟩
    -- ⊢ fU ((fun x_1 => { val := ↑x_1, property := (_ : ↑x_1 ∈ ↑U.obj) }) w) = fV (( …
    specialize wV ⟨w.1, w.2.2.2⟩
    -- ⊢ fU ((fun x_1 => { val := ↑x_1, property := (_ : ↑x_1 ∈ ↑U.obj) }) w) = fV (( …
    dsimp at wU wV ⊢
    -- ⊢ fU { val := ↑w, property := (_ : ↑w ∈ ↑U.obj) } = fV { val := ↑w, property : …
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
