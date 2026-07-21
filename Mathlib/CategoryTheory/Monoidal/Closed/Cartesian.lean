/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers, Thomas Read. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers, Thomas Read
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Cartesian closed categories

A cartesian closed category is a category with `CartesianMonoidalCategory` and `MonoidalClosed`
instances. There used to be a separate definition `CartesianClosed`, with its own API, but over time
this ended up as a duplicate of the former. Now, `CartesianClosed` and the surrounding API has been
deprecated, and the API for `MonoidalClosed` should be used instead. This file now contains a few
basic constructions for cartesian closed categories.

-/

@[expose] public section

universe v v₂ u u₂

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {X X' Y Y' Z : C}

instance CartesianMonoidalCategory.isLeftAdjoint_prod_functor
    (A : C) [Closed A] :
    (prod.functor.obj A).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (CartesianMonoidalCategory.tensorLeftIsoProd A)

namespace CartesianClosed

-- Porting note: notation fails to elaborate with `quotPrecheck` on.
set_option quotPrecheck false in
/-- Morphisms obtained using an exponentiable object. -/
scoped notation:20 A " ⟹ " B:19 => (ihom A).obj B

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `Functor.obj` -/
@[app_delab Functor.obj]
meta def delabFunctorObjExp : Delab :=
    whenPPOption getPPNotation <| withOverApp 6 do
  let e ← getExpr
  guard <| e.isAppOfArity' ``Functor.obj 6
  let A ← withNaryArg 4 do
    let e ← getExpr
    guard <| e.isAppOfArity' ``ihom 5
    withNaryArg 3 delab
  let B ← withNaryArg 5 delab
  `($A ⟹ $B)

-- Porting note: notation fails to elaborate with `quotPrecheck` on.
set_option quotPrecheck false in
/-- Morphisms from an exponentiable object. -/
scoped notation:30 B " ^^ " A:30 => (ihom A).obj B

end CartesianClosed

open CartesianClosed

/-- The internal element which points at the given morphism. -/
def internalizeHom {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A Y : C} [Closed A]
    (f : A ⟶ Y) : 𝟙_ C ⟶ A ⟹ Y :=
  MonoidalClosed.curry (fst _ _ ≫ f)

variable {A B : C} [Closed A]

open MonoidalClosed

/-- If an initial object `I` exists in a CCC, then `A ⨯ I ≅ I`. -/
@[simps]
def zeroMul {I : C} (t : IsInitial I) : A ⊗ I ≅ I where
  hom := snd _ _
  inv := t.to _
  hom_inv_id := by
    have : snd A I = uncurry (t.to _) := by
      rw [← curry_eq_iff]
      apply t.hom_ext
    rw [this, ← uncurry_natural_right, ← eq_curry_iff]
    apply t.hom_ext
  inv_hom_id := t.hom_ext _ _

/-- If an initial object `0` exists in a CCC, then `0 ⨯ A ≅ 0`. -/
def mulZero [BraidedCategory C] {I : C} (t : IsInitial I) : I ⊗ A ≅ I :=
  β_ _ _ ≪≫ zeroMul t

/-- If an initial object `0` exists in a CCC then `0^B ≅ 1` for any `B`. -/
def powZero [BraidedCategory C] {I : C} (t : IsInitial I) [MonoidalClosed C] : I ⟹ B ≅ 𝟙_ C where
  hom := default
  inv := curry ((mulZero t).hom ≫ t.to _)
  hom_inv_id := by
    rw [← curry_natural_left, curry_eq_iff, ← cancel_epi (mulZero t).inv]
    apply t.hom_ext

/-- If an initial object `I` exists in a CCC then it is a strict initial object,
i.e. any morphism to `I` is an iso.
This actually shows a slightly stronger version: any morphism to an initial object from an
exponentiable object is an isomorphism.
-/
theorem strict_initial {I : C} (t : IsInitial I) (f : A ⟶ I) : IsIso f := by
  have : Mono f := by
    rw [← lift_snd (𝟙 A) f, ← zeroMul_hom t]
    exact mono_comp _ _
  have : IsSplitEpi f := IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩
  apply isIso_of_mono_of_isSplitEpi

instance to_initial_isIso [HasInitial C] (f : A ⟶ ⊥_ C) : IsIso f :=
  strict_initial initialIsInitial _

/-- If an initial object `0` exists in a CCC then every morphism from it is monic. -/
theorem initial_mono {I : C} (B : C) (t : IsInitial I) [MonoidalClosed C] : Mono (t.to B) :=
  ⟨fun g h _ => by
    have := strict_initial t g
    have := strict_initial t h
    exact eq_of_inv_eq_inv (t.hom_ext _ _)⟩

instance Initial.mono_to [HasInitial C] (B : C) [MonoidalClosed C] : Mono (initial.to B) :=
  initial_mono B initialIsInitial

variable {D : Type u₂} [Category.{v₂} D]

section Functor

variable [CartesianMonoidalCategory D]

/-- Transport the property of being Cartesian closed across an equivalence of categories.

Note we didn't require any coherence between the choice of finite products here, since we transport
along the `prodComparison` isomorphism.
-/
@[instance_reducible]
noncomputable def cartesianClosedOfEquiv (e : C ≌ D) [MonoidalClosed C] : MonoidalClosed D :=
  letI : e.inverse.Monoidal := .ofChosenFiniteProducts _
  MonoidalClosed.ofEquiv e.inverse e.symm.toAdjunction

end Functor

end CategoryTheory
