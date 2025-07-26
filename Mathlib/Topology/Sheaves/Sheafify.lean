/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Stalks

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

assert_not_exists CommRingCat


universe u v

noncomputable section

open TopCat Opposite TopologicalSpace CategoryTheory

variable {X : TopCat.{u}} (F : Presheaf (Type v) X) [UnivLE.{u, v}]

namespace TopCat.Presheaf

namespace Sheafify

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
/--
The prelocal predicate on functions into the stalks, asserting that the function is equal to a germ.
-/
def isGerm : PrelocalPredicate fun x ↦ F.stalk x where
  pred {U} f := ∃ g : F.obj (op U), ∀ x : U, f x = germ F U x.1 x.2 g
  res := fun i _ ⟨g, p⟩ ↦ ⟨F.map i.op g, fun x ↦ (p (i x)).trans (germ_res_apply F i x x.2 g).symm⟩

/-- The local predicate on functions into the stalks,
asserting that the function is locally equal to a germ.
-/
def isLocallyGerm : LocalPredicate fun x ↦ F.stalk x :=
  (isGerm F).sheafify

attribute [local instance] Types.instFunLike Types.instConcreteCategory

theorem isStalkSurj_isGerm (x : X) : IsStalkSurj (isGerm F).pred x := fun t ↦ by
  obtain ⟨U, m, s, rfl⟩ := F.germ_exist x t
  exact ⟨⟨U, m⟩, fun y ↦ F.germ _ _ y.2 s, ⟨s, fun _ ↦ rfl⟩, rfl⟩

theorem isStalkInj_isGerm (x : X) : IsStalkInj (isGerm F).pred x := by
  intro U V sU sV ⟨gU, mU⟩ ⟨gV, mV⟩ e
  have := (mU _).symm.trans (e.trans (mV _))
  have ⟨W, mW, iU, iV, e⟩ := F.germ_eq x _ _ gU gV this
  refine ⟨⟨W, mW⟩, iU, iV, fun w ↦ (mU _).trans (.trans ?_ <| .symm <| mV _)⟩
  exact (congr_fun (F.germ_res iU w w.2) gU).symm.trans (congr_arg (F.germ W w w.2) e)
    |>.trans (congr_fun (F.germ_res iV w w.2) gV)

end Sheafify

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
/-- The adjunction between presheaves and prelocal predicates. -/
def adjunctionPrelocalPredicate (F : Presheaf (Type u) X) {G : X → Type u}
    (P : PrelocalPredicate G) :
    {f : Π x, F.stalk x → G x // (Sheafify.isGerm F).pred ≤ (P.pullback f).pred} ≃
    (F ⟶ subpresheafToTypes P) where
  toFun f := ⟨fun U s ↦ ⟨fun x ↦ f.1 _ (F.germ _ _ x.2 s), f.2 _ _ ⟨_, fun _ ↦ rfl⟩⟩,
    fun U V i ↦ funext fun s ↦ Subtype.ext <| funext fun x ↦ congr_arg _ (F.germ_res_apply ..)⟩
  invFun f := ⟨fun x ↦ stalkToFiber P x ∘ (stalkFunctor _ x).map f,
    fun U s' ⟨s, eq⟩ ↦ by
      simp_rw [PrelocalPredicate.pullback, Pullback, eq, Function.comp_apply]
      convert (f.app _ s).2
      exact (congr_arg _ (stalkFunctor_map_germ_apply _ _ _ f _)).trans (stalkToFiber_germ ..)⟩
  left_inv f := Subtype.ext <| funext fun x ↦ funext fun g ↦ by
    obtain ⟨U, hx, s, rfl⟩ := F.germ_exist x g
    exact (congr_arg _ (stalkFunctor_map_germ_apply (C := Type u) ..)).trans (stalkToFiber_germ ..)
  right_inv f := ext fun U ↦ funext fun s ↦ Subtype.ext <| funext fun x ↦
    (congr_arg _ (stalkFunctor_map_germ_apply (C := Type u) ..)).trans (stalkToFiber_germ ..)

/-- The sheafification of a `Type` valued presheaf, defined as the functions into the stalks which
are locally equal to germs.
-/
def sheafify : Sheaf (Type _) X :=
  subsheafToTypes (Sheafify.isLocallyGerm F)

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The morphism from a presheaf to its sheafification,
sending each section to its germs.
(This forms the unit of the adjunction.)
-/
def toSheafify (F : Presheaf (Type u) X) : F ⟶ F.sheafify.1 where
  app U f := ⟨fun x ↦ germ F _ x x.2 f,
    PrelocalPredicate.sheafifyOf ⟨f, fun x ↦ rfl⟩⟩
  naturality U U' f := by
    ext x
    apply Subtype.ext -- Porting note: Added `apply`
    ext ⟨u, m⟩
    exact germ_res_apply F f.unop u m x

/-- The natural morphism from the stalk of the sheafification to the original stalk.
In `sheafifyStalkIso` we show this is an isomorphism.
-/
def stalkToFiber (x : X) : F.sheafify.presheaf.stalk x → stalk F x :=
  TopCat.stalkToFiber (Sheafify.isLocallyGerm F).1 x

theorem stalkToFiber_surjective (x : X) : Function.Surjective (F.stalkToFiber x) :=
  TopCat.stalkToFiber_surjective _ _ (Sheafify.isStalkSurj_isGerm F x).sheafify

theorem stalkToFiber_injective (x : X) : Function.Injective (F.stalkToFiber x) :=
  TopCat.stalkToFiber_injective _ _ (Sheafify.isStalkInj_isGerm F x).sheafify

/-- The isomorphism between a stalk of the sheafification and the original stalk.
-/
def sheafifyStalkIso {X : TopCat.{u}} (F : Presheaf (Type max u v) X) (x : X) :
    F.sheafify.presheaf.stalk x ≅ F.stalk x :=
  (Equiv.ofBijective _ ⟨stalkToFiber_injective F x, stalkToFiber_surjective F x⟩).toIso

-- PROJECT functoriality, and that sheafification is the left adjoint of the forgetful functor.
end TopCat.Presheaf
