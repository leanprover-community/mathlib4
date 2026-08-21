/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers
-/
module

public import Mathlib.CategoryTheory.Sites.Sieves.Basic

/-!
# The presheaf associated to a sieve

A sieve `S` on an object `X` of a category `C` determines a presheaf whose value at `Y` is the type
of morphisms `Y ⟶ X` belonging to `S`. The closure condition for a sieve makes this construction
functorial, and the resulting presheaf is naturally a subfunctor of the Yoneda presheaf of `X`.

This file defines the associated presheaf `Sieve.functor`, its monomorphic natural transformation
`Sieve.functorInclusion` into `yoneda.obj X`, and natural transformations induced by inclusions of
sieves. It also reconstructs a sieve from a subfunctor of a representable presheaf. Parallel
constructions using `uliftYoneda` are provided for situations in which universe levels must be
adjusted.

## Tags

sieve, presheaf, Yoneda
-/

@[expose] public section


universe w v₁ u₁

namespace CategoryTheory

open Category

variable {C : Type u₁} [Category.{v₁} C] {X : C}

namespace Sieve

variable {S : Sieve X}

/-- A sieve induces a presheaf. -/
@[simps obj map]
def functor (S : Sieve X) : Cᵒᵖ ⥤ Type v₁ where
  obj Y := { g : Y.unop ⟶ X // S g }
  map f := ↾fun g ↦ ⟨f.unop ≫ g.1, downward_closed _ g.2 _⟩

/-- If a sieve S is contained in a sieve T, then we have a morphism of presheaves on their induced
presheaves.
-/
@[simps]
def natTransOfLe {S T : Sieve X} (h : S ≤ T) : S.functor ⟶ T.functor where
  app _ := ↾fun f ↦ ⟨f.1, h _ f.2⟩

/-- The natural inclusion from the functor induced by a sieve to the yoneda embedding. -/
@[simps]
def functorInclusion (S : Sieve X) : S.functor ⟶ yoneda.obj X where
  app _ := ↾fun f ↦ f.1

set_option backward.isDefEq.respectTransparency.types false in
/-- Any component `f : Y ⟶ X` of the sieve `S` induces a natural transformation from `yoneda.obj Y`
to the presheaf induced by `S`. -/
@[simps]
def toFunctor (S : Sieve X) {Y : C} (f : Y ⟶ X) (hf : S f) : yoneda.obj Y ⟶ S.functor where
  app Z := ↾fun g ↦ ⟨g ≫ f, S.downward_closed hf g⟩

theorem natTransOfLe_comm {S T : Sieve X} (h : S ≤ T) :
    natTransOfLe h ≫ functorInclusion _ = functorInclusion _ :=
  rfl

open ConcreteCategory

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The presheaf induced by a sieve is a subobject of the yoneda embedding. -/
instance functorInclusion_is_mono : Mono S.functorInclusion :=
  ⟨fun f g h => by
    ext Y y
    simpa [Subtype.ext_iff] using congr_hom (NatTrans.congr_app h Y) y⟩

-- TODO: Show that when `f` is mono, this is right inverse to `functorInclusion` up to isomorphism.
/-- A natural transformation to a representable functor induces a sieve. This is the left inverse of
`functorInclusion`, shown in `sieveOfSubfunctor_functorInclusion`.
-/
@[simps]
def sieveOfSubfunctor {R} (f : R ⟶ yoneda.obj X) : Sieve X where
  arrows Y g := ∃ t, f.app (Opposite.op Y) t = g
  downward_closed := by
    rintro Y Z _ ⟨t, rfl⟩ g
    refine ⟨R.map g.op t, ?_⟩
    simp

theorem sieveOfSubfunctor_functorInclusion : sieveOfSubfunctor S.functorInclusion = S := by
  ext
  simp only [functorInclusion_app, sieveOfSubfunctor_apply]
  constructor
  · rintro ⟨⟨f, hf⟩, rfl⟩
    exact hf
  · intro hf
    exact ⟨⟨_, hf⟩, rfl⟩

instance functorInclusion_top_isIso : IsIso (⊤ : Sieve X).functorInclusion :=
  ⟨⟨{ app := fun _ => ↾fun a => ⟨a, ⟨⟩⟩ }, rfl, rfl⟩⟩

/-- A variant of `Sieve.functor` with universe lifting. -/
abbrev uliftFunctor (S : Sieve X) : Cᵒᵖ ⥤ Type (max w v₁) :=
  S.functor ⋙ CategoryTheory.uliftFunctor

/-- A variant of `Sieve.natTransOfLe` with universe lifting. -/
@[simps]
def uliftNatTransOfLe {S T : Sieve X} (h : S ≤ T) :
    Sieve.uliftFunctor.{w} S ⟶ Sieve.uliftFunctor.{w} T where
  app _ := ↾fun f ↦ ⟨f.down.1, h _ f.down.2⟩

/-- A variant of `Sieve.functorInclusion` with universe lifting. -/
@[simps! app]
def uliftFunctorInclusion (S : Sieve X) :
    S.uliftFunctor ⟶ uliftYoneda.{w}.obj X :=
  Functor.whiskerRight S.functorInclusion CategoryTheory.uliftFunctor

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `Sieve.toFunctor` with universe lifting. -/
@[simps]
def toUliftFunctor (S : Sieve X) {Y : C} (f : Y ⟶ X) (hf : S f) :
    uliftYoneda.{w}.obj Y ⟶ Sieve.uliftFunctor.{w} S where
  app Z := ↾fun g ↦ ⟨g.down ≫ f, S.downward_closed hf g.down⟩

theorem uliftNatTransOfLe_comm {S T : Sieve X} (h : S ≤ T) :
    uliftNatTransOfLe.{w} h ≫ uliftFunctorInclusion.{w} _ = uliftFunctorInclusion.{w} _ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The presheaf induced by a sieve is a subobject of the yoneda embedding. -/
instance uliftFunctorInclusion_is_mono (S : Sieve X) :
    Mono (Sieve.uliftFunctorInclusion.{w} S) :=
  ⟨fun _ _ h => by
    ext Y y
    refine ULift.ext _ _ (Subtype.ext_iff.2 ?_)
    simpa using congr_hom (NatTrans.congr_app h Y) y⟩

/-- A variant of `Sieve.sieveOfSubfunctor` with universe lifting. -/
@[simps]
def sieveOfUliftSubfunctor {R : Cᵒᵖ ⥤ Type max w v₁} (f : R ⟶ uliftYoneda.{w}.obj X) :
    Sieve X where
  arrows Y g := ∃ t, f.app (Opposite.op Y) t = { down := g }
  downward_closed := by
    intro Y Z _ ⟨t, ht⟩ g
    refine ⟨R.map g.op t, ?_⟩
    simp [ht]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem sieveOfUliftSubfunctor_uliftFunctorInclusion {S : Sieve X} :
    Sieve.sieveOfUliftSubfunctor.{w} (S.uliftFunctorInclusion) = S := by
  cat_disch

instance uliftFunctorInclusion_top_isIso : IsIso (Sieve.uliftFunctorInclusion.{w} (⊤ : Sieve X)) :=
  ⟨⟨{ app := fun _ ↦ ↾fun a ↦ ⟨a.down, ⟨⟩⟩ }, rfl, rfl⟩⟩


end Sieve

end CategoryTheory
