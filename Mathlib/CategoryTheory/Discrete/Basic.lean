/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison, Floris van Doorn
-/
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.Data.ULift

/-!
# Discrete categories

We define `Discrete α` as a structure containing a term `a : α` for any type `α`,
and use this type alias to provide a `SmallCategory` instance
whose only morphisms are the identities.

There is an annoying technical difficulty that it has turned out to be inconvenient
to allow categories with morphisms living in `Prop`,
so instead of defining `X ⟶ Y` in `Discrete α` as `X = Y`,
one might define it as `PLift (X = Y)`.
In fact, to allow `Discrete α` to be a `SmallCategory`
(i.e. with morphisms in the same universe as the objects),
we actually define the hom type `X ⟶ Y` as `ULift (PLift (X = Y))`.

`Discrete.functor` promotes a function `f : I → C` (for any category `C`) to a functor
`Discrete.functor f : Discrete I ⥤ C`.

Similarly, `Discrete.natTrans` and `Discrete.natIso` promote `I`-indexed families of morphisms,
or `I`-indexed families of isomorphisms to natural transformations or natural isomorphism.

We show equivalences of types are the same as (categorical) equivalences of the corresponding
discrete categories.
-/

namespace CategoryTheory

-- morphism levels before object levels. See note [category theory universes].
universe v₁ v₂ v₃ u₁ u₁' u₂ u₃

-- This is intentionally a structure rather than a type synonym
-- to enforce using `DiscreteEquiv` (or `Discrete.mk` and `Discrete.as`) to move between
-- `Discrete α` and `α`. Otherwise there is too much API leakage.
/-- A wrapper for promoting any type to a category,
with the only morphisms being equalities.
-/
@[ext, aesop safe cases (rule_sets := [CategoryTheory])]
structure Discrete (α : Type u₁) where
  /-- A wrapper for promoting any type to a category,
  with the only morphisms being equalities. -/
  as : α

@[simp]
theorem Discrete.mk_as {α : Type u₁} (X : Discrete α) : Discrete.mk X.as = X :=
  rfl

/-- `Discrete α` is equivalent to the original type `α`. -/
@[simps]
def discreteEquiv {α : Type u₁} : Discrete α ≃ α where
  toFun := Discrete.as
  invFun := Discrete.mk
  left_inv := by cat_disch
  right_inv := by cat_disch

instance {α : Type u₁} [DecidableEq α] : DecidableEq (Discrete α) :=
  discreteEquiv.decidableEq

/-- The "Discrete" category on a type, whose morphisms are equalities.

Because we do not allow morphisms in `Prop` (only in `Type`),
somewhat annoyingly we have to define `X ⟶ Y` as `ULift (PLift (X = Y))`. -/
@[stacks 001A]
instance discreteCategory (α : Type u₁) : SmallCategory (Discrete α) where
  Hom X Y := ULift (PLift (X.as = Y.as))
  id _ := ULift.up (PLift.up rfl)
  comp {X Y Z} g f := by
    cases X
    cases Y
    cases Z
    rcases f with ⟨⟨⟨⟩⟩⟩
    exact g

namespace Discrete

variable {α : Type u₁}

instance [Inhabited α] : Inhabited (Discrete α) :=
  ⟨⟨default⟩⟩

instance [Subsingleton α] : Subsingleton (Discrete α) :=
  ⟨by cat_disch⟩

instance instSubsingletonDiscreteHom (X Y : Discrete α) : Subsingleton (X ⟶ Y) :=
  show Subsingleton (ULift (PLift _)) from inferInstance

/-- A simple tactic to run `cases` on any `Discrete α` hypotheses. -/
macro "discrete_cases" : tactic =>
  `(tactic| fail_if_no_progress casesm* Discrete _, (_ : Discrete _) ⟶ (_ : Discrete _), PLift _)

open Lean Elab Tactic in
/--
Use:
```
attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases
```
to locally gives `cat_disch` the ability to call `cases` on
`Discrete` and `(_ : Discrete _) ⟶ (_ : Discrete _)` hypotheses.
-/
def discreteCases : TacticM Unit := do
  evalTactic (← `(tactic| discrete_cases))

-- TODO: investigate turning on either
-- `attribute [aesop safe cases (rule_sets := [CategoryTheory])] Discrete`
-- or
-- `attribute [aesop safe tactic (rule_sets := [CategoryTheory])] discreteCases`
-- globally.

instance [Unique α] : Unique (Discrete α) :=
  Unique.mk' (Discrete α)

/-- Extract the equation from a morphism in a discrete category. -/
theorem eq_of_hom {X Y : Discrete α} (i : X ⟶ Y) : X.as = Y.as :=
  i.down.down

/-- Promote an equation between the wrapped terms in `X Y : Discrete α` to a morphism `X ⟶ Y`
in the discrete category. -/
protected abbrev eqToHom {X Y : Discrete α} (h : X.as = Y.as) : X ⟶ Y :=
  eqToHom (by cat_disch)

/-- Promote an equation between the wrapped terms in `X Y : Discrete α` to an isomorphism `X ≅ Y`
in the discrete category. -/
protected abbrev eqToIso {X Y : Discrete α} (h : X.as = Y.as) : X ≅ Y :=
  eqToIso (by cat_disch)

/-- A variant of `eqToHom` that lifts terms to the discrete category. -/
abbrev eqToHom' {a b : α} (h : a = b) : Discrete.mk a ⟶ Discrete.mk b :=
  Discrete.eqToHom h

/-- A variant of `eqToIso` that lifts terms to the discrete category. -/
abbrev eqToIso' {a b : α} (h : a = b) : Discrete.mk a ≅ Discrete.mk b :=
  Discrete.eqToIso h

@[simp]
theorem id_def (X : Discrete α) : ULift.up (PLift.up (Eq.refl X.as)) = 𝟙 X :=
  rfl

variable {C : Type u₂} [Category.{v₂} C]

instance {I : Type u₁} {i j : Discrete I} (f : i ⟶ j) : IsIso f :=
  ⟨⟨Discrete.eqToHom (eq_of_hom f).symm, by cat_disch⟩⟩

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

/-- Any function `I → C` gives a functor `Discrete I ⥤ C`. -/
def functor {I : Type u₁} (F : I → C) : Discrete I ⥤ C where
  obj := F ∘ Discrete.as
  map {X Y} f := by
    dsimp
    rcases f with ⟨⟨h⟩⟩
    exact eqToHom (congrArg _ h)

@[simp]
theorem functor_obj {I : Type u₁} (F : I → C) (i : I) :
    (Discrete.functor F).obj (Discrete.mk i) = F i :=
  rfl

theorem functor_map {I : Type u₁} (F : I → C) {i : Discrete I} (f : i ⟶ i) :
    (Discrete.functor F).map f = 𝟙 (F i.as) := by cat_disch

@[simp]
theorem functor_obj_eq_as {I : Type u₁} (F : I → C) (X : Discrete I) :
    (Discrete.functor F).obj X = F X.as :=
  rfl
/-- The discrete functor induced by a composition of maps can be written as a
composition of two discrete functors.
-/
@[simps!]
def functorComp {I : Type u₁} {J : Type u₁'} (f : J → C) (g : I → J) :
    Discrete.functor (f ∘ g) ≅ Discrete.functor (Discrete.mk ∘ g) ⋙ Discrete.functor f :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- For functors out of a discrete category,
a natural transformation is just a collection of maps,
as the naturality squares are trivial.
-/
@[simps]
def natTrans {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ⟶ G.obj i) :
    F ⟶ G where
  app := f
  naturality := fun {X Y} ⟨⟨g⟩⟩ => by
    discrete_cases
    rcases g
    change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
    simp

/-- For functors out of a discrete category,
a natural isomorphism is just a collection of isomorphisms,
as the naturality squares are trivial.
-/
@[simps!]
def natIso {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ≅ G.obj i) :
    F ≅ G :=
  NatIso.ofComponents f fun ⟨⟨g⟩⟩ => by
    discrete_cases
    rcases g
    change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
    simp

instance {I : Type*} {F G : Discrete I ⥤ C} (f : ∀ i, F.obj i ⟶ G.obj i) [∀ i, IsIso (f i)] :
    IsIso (Discrete.natTrans f) := by
  change IsIso (Discrete.natIso (fun i => asIso (f i))).hom
  infer_instance

@[simp]
theorem natIso_app {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ≅ G.obj i)
    (i : Discrete I) : (Discrete.natIso f).app i = f i := by cat_disch

/-- Every functor `F` from a discrete category is naturally isomorphic (actually, equal) to
  `Discrete.functor (F.obj)`. -/
@[simps!]
def natIsoFunctor {I : Type u₁} {F : Discrete I ⥤ C} : F ≅ Discrete.functor (F.obj ∘ Discrete.mk) :=
  natIso fun _ => Iso.refl _

/-- Composing `Discrete.functor F` with another functor `G` amounts to composing `F` with `G.obj` -/
@[simps!]
def compNatIsoDiscrete {I : Type u₁} {D : Type u₃} [Category.{v₃} D] (F : I → C) (G : C ⥤ D) :
    Discrete.functor F ⋙ G ≅ Discrete.functor (G.obj ∘ F) :=
  natIso fun _ => Iso.refl _

/-- We can promote a type-level `Equiv` to
an equivalence between the corresponding `discrete` categories.
-/
@[simps]
def equivalence {I : Type u₁} {J : Type u₂} (e : I ≃ J) : Discrete I ≌ Discrete J where
  functor := Discrete.functor (Discrete.mk ∘ (e : I → J))
  inverse := Discrete.functor (Discrete.mk ∘ (e.symm : J → I))
  unitIso :=
    Discrete.natIso fun i => eqToIso (by simp)
  counitIso :=
    Discrete.natIso fun j => eqToIso (by simp)

/-- We can convert an equivalence of `discrete` categories to a type-level `Equiv`. -/
@[simps]
def equivOfEquivalence {α : Type u₁} {β : Type u₂} (h : Discrete α ≌ Discrete β) : α ≃ β where
  toFun := Discrete.as ∘ h.functor.obj ∘ Discrete.mk
  invFun := Discrete.as ∘ h.inverse.obj ∘ Discrete.mk
  left_inv a := by simpa using eq_of_hom (h.unitIso.app (Discrete.mk a)).2
  right_inv a := by simpa using eq_of_hom (h.counitIso.app (Discrete.mk a)).1

end Discrete

namespace Discrete

variable {J : Type v₁}

open Opposite

/-- A discrete category is equivalent to its opposite category. -/
@[simps! functor_obj_as inverse_obj]
protected def opposite (α : Type u₁) : (Discrete α)ᵒᵖ ≌ Discrete α :=
  let F : Discrete α ⥤ (Discrete α)ᵒᵖ := Discrete.functor fun x => op (Discrete.mk x)
  { functor := F.leftOp
    inverse := F
    unitIso := NatIso.ofComponents fun ⟨_⟩ => Iso.refl _
    counitIso := Discrete.natIso fun ⟨_⟩ => Iso.refl _ }

variable {C : Type u₂} [Category.{v₂} C]

@[simp]
theorem functor_map_id (F : Discrete J ⥤ C) {j : Discrete J} (f : j ⟶ j) :
    F.map f = 𝟙 (F.obj j) := by
  have h : f = 𝟙 j := by cat_disch
  rw [h]
  simp

end Discrete

@[simp]
lemma Discrete.forall {α : Type*} {p : Discrete α → Prop} :
    (∀ (a : Discrete α), p a) ↔ ∀ (a' : α), p ⟨a'⟩ := by
  rw [iff_iff_eq, discreteEquiv.forall_congr_left]
  simp [discreteEquiv]

@[simp]
lemma Discrete.exists {α : Type*} {p : Discrete α → Prop} :
    (∃ (a : Discrete α), p a) ↔ ∃ (a' : α), p ⟨a'⟩ := by
  rw [iff_iff_eq, discreteEquiv.exists_congr_left]
  simp [discreteEquiv]

/-- The equivalence of categories `(J → C) ≌ (Discrete J ⥤ C)`. -/
@[simps]
def piEquivalenceFunctorDiscrete (J : Type u₂) (C : Type u₁) [Category.{v₁} C] :
    (J → C) ≌ (Discrete J ⥤ C) where
  functor :=
    { obj := fun F => Discrete.functor F
      map := fun f => Discrete.natTrans (fun j => f j.as) }
  inverse :=
    { obj := fun F j => F.obj ⟨j⟩
      map := fun f j => f.app ⟨j⟩ }
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents (fun F => (NatIso.ofComponents (fun _ => Iso.refl _)
    (by
      rintro ⟨x⟩ ⟨y⟩ f
      obtain rfl : x = y := Discrete.eq_of_hom f
      obtain rfl : f = 𝟙 _ := rfl
      simp))) (by cat_disch)

/-- A category is discrete when there is at most one morphism between two objects,
in which case they are equal. -/
class IsDiscrete (C : Type*) [Category C] : Prop where
  subsingleton (X Y : C) : Subsingleton (X ⟶ Y) := by infer_instance
  eq_of_hom {X Y : C} (f : X ⟶ Y) : X = Y

attribute [instance] IsDiscrete.subsingleton

instance Discrete.isDiscrete (C : Type*) : IsDiscrete (Discrete C) where
  eq_of_hom := by rintro ⟨_⟩ ⟨_⟩ ⟨⟨rfl⟩⟩; rfl

section

variable {C : Type*} [Category C] [IsDiscrete C]

lemma obj_ext_of_isDiscrete {X Y : C} (f : X ⟶ Y) : X = Y := IsDiscrete.eq_of_hom f

instance isIso_of_isDiscrete {X Y : C} (f : X ⟶ Y) : IsIso f :=
  ⟨eqToHom (IsDiscrete.eq_of_hom f).symm, by cat_disch⟩

instance : IsDiscrete Cᵒᵖ where
  eq_of_hom := by
    rintro ⟨_⟩ ⟨_⟩ ⟨f⟩
    obtain rfl := obj_ext_of_isDiscrete f
    rfl

end

end CategoryTheory
