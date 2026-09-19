/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.PEmpty
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Initial and terminal objects in a category.

In this file we define the predicates `IsTerminal` and `IsInitial` as well as the class
`InitialMonoClass`.

The classes `HasTerminal` and `HasInitial` and the associated notations for terminal and initial
objects are defined in `Terminal.lean`.

## References
* [Stacks: Initial and final objects](https://stacks.math.columbia.edu/tag/002B)
-/

@[expose] public section

assert_not_exists CategoryTheory.Limits.HasLimit

noncomputable section

universe w w' v v₁ v₂ u u₁ u₂

open CategoryTheory Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

/-- Construct a cone for the empty diagram given an object. -/
@[to_dual (attr := implicit_reducible, simps)
/-- Construct a cocone for the empty diagram given an object. -/]
def asEmptyCone (X : C) : Cone (Functor.empty.{0} C) :=
  { pt := X
    π :=
    { app := by cat_disch } }

/-- `X` is terminal if the cone it induces on the empty diagram is limiting. -/
@[to_dual
/-- `X` is initial if the cocone it induces on the empty diagram is colimiting. -/]
abbrev IsTerminal (X : C) :=
  IsLimit (asEmptyCone X)

/-- An object `Y` is terminal iff for every `X` there is a unique morphism `X ⟶ Y`. -/
@[to_dual
/-- An object `X` is initial iff for every `Y` there is a unique morphism `X ⟶ Y`. -/]
def isTerminalEquivUnique (F : Discrete.{0} PEmpty.{1} ⥤ C) (Y : C) :
    IsLimit (⟨Y, by cat_disch, by simp⟩ : Cone F) ≃ ∀ X : C, Unique (X ⟶ Y) where
  toFun t X :=
    { default := t.lift ⟨X, ⟨by cat_disch, by simp⟩⟩
      uniq := fun f => t.uniq ⟨X, ⟨by cat_disch, by simp⟩⟩ f (by simp) }
  invFun u :=
    { lift := fun s => (u s.pt).default
      uniq := fun s _ _ => (u s.pt).2 _ }
  left_inv := by dsimp [Function.LeftInverse]; intro x; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.RightInverse, Function.LeftInverse]
    subsingleton

/-- An object `X` is terminal if for every `Y` there is a unique morphism `Y ⟶ X`
(as an instance). -/
@[to_dual
/-- An object `X` is initial if for every `Y` there is a unique morphism `X ⟶ Y`
(as an instance). -/]
def IsTerminal.ofUnique (X : C) [h : ∀ Y : C, Unique (Y ⟶ X)] : IsTerminal X where
  lift s := (h s.pt).default
  fac := fun _ ⟨j⟩ => j.elim

/-- An object `X` is terminal if for every `Y` there is a unique morphism `Y ⟶ X`
(as explicit arguments). -/
@[to_dual
/-- An object `X` is initial if for every `Y` there is a unique morphism `X ⟶ Y`
(as explicit arguments). -/]
def IsTerminal.ofUniqueHom {X : C} (h : ∀ Y : C, Y ⟶ X) (uniq : ∀ (Y : C) (m : Y ⟶ X), m = h Y) :
    IsTerminal X :=
  have : ∀ Y : C, Unique (Y ⟶ X) := fun Y ↦ ⟨⟨h Y⟩, uniq Y⟩
  IsTerminal.ofUnique X

/-- If `α` is a preorder with top, then `⊤` is a terminal object. -/
@[to_dual /-- If `α` is a preorder with bot, then `⊥` is an initial object. -/]
def isTerminalTop {α : Type*} [Preorder α] [OrderTop α] : IsTerminal (⊤ : α) :=
  IsTerminal.ofUnique _

/-- Transport a term of type `IsTerminal` across an isomorphism. -/
@[to_dual /-- Transport a term of type `IsInitial` across an isomorphism. -/]
def IsTerminal.ofIso {Y Z : C} (hY : IsTerminal Y) (i : Y ≅ Z) : IsTerminal Z :=
  IsLimit.ofIsoLimit hY
    { hom := { hom := i.hom }
      inv := { hom := i.inv } }

/-- If `X` and `Y` are isomorphic, then `X` is terminal iff `Y` is. -/
@[to_dual /-- If `X` and `Y` are isomorphic, then `X` is initial iff `Y` is. -/]
def IsTerminal.equivOfIso {X Y : C} (e : X ≅ Y) :
    IsTerminal X ≃ IsTerminal Y where
  toFun h := IsTerminal.ofIso h e
  invFun h := IsTerminal.ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Give the morphism to a terminal object from any other. -/
@[to_dual «to» /-- Give the morphism from an initial object to any other. -/]
def IsTerminal.from {X : C} (t : IsTerminal X) (Y : C) : Y ⟶ X :=
  t.lift (asEmptyCone Y)

/-- Any two morphisms to a terminal object are equal. -/
@[to_dual /-- Any two morphisms from an initial object are equal. -/]
theorem IsTerminal.hom_ext {X Y : C} (t : IsTerminal X) (f g : Y ⟶ X) : f = g :=
  IsLimit.hom_ext t (by simp)

@[to_dual (attr := simp) to_comp]
theorem IsTerminal.comp_from {Z : C} (t : IsTerminal Z) {X Y : C} (f : X ⟶ Y) :
    f ≫ t.from Y = t.from X :=
  t.hom_ext _ _

@[to_dual (attr := simp) to_self]
theorem IsTerminal.from_self {X : C} (t : IsTerminal X) : t.from X = 𝟙 X :=
  t.hom_ext _ _

/-- Any morphism from a terminal object is split mono. -/
@[to_dual isSplitEpi_to
/-- Any morphism to an initial object is split epi. -/]
theorem IsTerminal.isSplitMono_from {X Y : C} (t : IsTerminal X) (f : X ⟶ Y) : IsSplitMono f :=
  IsSplitMono.mk' ⟨t.from _, t.hom_ext _ _⟩

/-- Any morphism from a terminal object is mono. -/
@[to_dual epi_to /-- Any morphism to an initial object is epi. -/]
theorem IsTerminal.mono_from {X Y : C} (t : IsTerminal X) (f : X ⟶ Y) : Mono f := by
  have := t.isSplitMono_from f; infer_instance

/-- If `T` and `T'` are terminal, they are isomorphic. -/
@[to_dual (attr := simps)
/-- If `I` and `I'` are initial, they are isomorphic. -/]
def IsTerminal.uniqueUpToIso {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') : T ≅ T' where
  hom := hT'.from _
  inv := hT.from _

variable (C)

section Univ

variable (X : C) {F₁ : Discrete.{w} PEmpty ⥤ C} {F₂ : Discrete.{w'} PEmpty ⥤ C}

/-- Being terminal is independent of the empty diagram, its universe, and the cone over it,
as long as the cone points are isomorphic. -/
@[to_dual
/-- Being initial is independent of the empty diagram, its universe, and the cocone over it,
as long as the cocone points are isomorphic. -/]
def isLimitChangeEmptyCone {c₁ : Cone F₁} (hl : IsLimit c₁) (c₂ : Cone F₂) (hi : c₁.pt ≅ c₂.pt) :
    IsLimit c₂ where
  lift c := hl.lift ⟨c.pt, by cat_disch, by simp⟩ ≫ hi.hom
  uniq c f _ := by
    dsimp
    rw [← hl.uniq _ (f ≫ hi.inv) _]
    · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · simp

/-- Replacing an empty cone in `IsLimit` by another with the same cone point
is an equivalence. -/
@[to_dual
/-- Replacing an empty cocone in `IsColimit` by another with the same cocone point
is an equivalence. -/]
def isLimitEmptyConeEquiv (c₁ : Cone F₁) (c₂ : Cone F₂) (h : c₁.pt ≅ c₂.pt) :
    IsLimit c₁ ≃ IsLimit c₂ where
  toFun hl := isLimitChangeEmptyCone C hl c₂ h
  invFun hl := isLimitChangeEmptyCone C hl c₁ h.symm
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.LeftInverse, Function.RightInverse]; intro
    simp only [eq_iff_true_of_subsingleton]

/-- If `F` is an empty diagram, then a cone over `F` is limiting iff the cone point is terminal. -/
@[to_dual
/-- If `F` is an empty diagram,
then a cocone over `F` is colimiting iff the cocone point is initial. -/]
def isLimitEquivIsTerminalOfIsEmpty {J : Type*} [Category* J] [IsEmpty J] {F : J ⥤ C} (c : Cone F) :
    IsLimit c ≃ IsTerminal c.pt :=
  (IsLimit.whiskerEquivalenceEquiv (equivalenceOfIsEmpty (Discrete PEmpty.{1}) _)).trans
    (isLimitEmptyConeEquiv _ _ _ (.refl _))

end Univ

section

variable {C}

/-- An initial object is terminal in the opposite category. -/
@[to_dual /-- A terminal object is initial in the opposite category. -/]
def terminalOpOfInitial {X : C} (t : IsInitial X) : IsTerminal (Opposite.op X) where
  lift s := (t.to s.pt.unop).op
  uniq _ _ _ := Quiver.Hom.unop_inj (t.hom_ext _ _)

/-- An initial object in the opposite category is terminal in the original category. -/
@[to_dual /-- A terminal object in the opposite category is initial in the original category. -/]
def terminalUnopOfInitial {X : Cᵒᵖ} (t : IsInitial X) : IsTerminal X.unop where
  lift s := (t.to (Opposite.op s.pt)).unop
  uniq _ _ _ := Quiver.Hom.op_inj (t.hom_ext _ _)

/-- A category is an `InitialMonoClass` if the canonical morphism of an initial object is a
monomorphism.  In practice, this is most useful when given an arbitrary morphism out of the chosen
initial object, see `initial.mono_from`.
Given a terminal object, this is equivalent to the assumption that the unique morphism from initial
to terminal is a monomorphism, which is the second of Freyd's axioms for an AT category.

TODO: This is a condition satisfied by categories with zero objects and morphisms.
-/
class InitialMonoClass (C : Type u₁) [Category.{v₁} C] : Prop where
  /-- The map from the (any as stated) initial object to any other object is a
    monomorphism -/
  isInitial_mono_from : ∀ {I} (X : C) (hI : IsInitial I), Mono (hI.to X)

theorem IsInitial.mono_from [InitialMonoClass C] {I} {X : C} (hI : IsInitial I) (f : I ⟶ X) :
    Mono f := by
  rw [hI.hom_ext f (hI.to X)]
  apply InitialMonoClass.isInitial_mono_from

/-- To show a category is an `InitialMonoClass` it suffices to give an initial object such that
every morphism out of it is a monomorphism. -/
theorem InitialMonoClass.of_isInitial {I : C} (hI : IsInitial I) (h : ∀ X, Mono (hI.to X)) :
    InitialMonoClass C where
  isInitial_mono_from {I'} X hI' := by
    rw [hI'.hom_ext (hI'.to X) ((hI'.uniqueUpToIso hI).hom ≫ hI.to X)]
    apply mono_comp

/-- To show a category is an `InitialMonoClass` it suffices to show the unique morphism from an
initial object to a terminal object is a monomorphism. -/
theorem InitialMonoClass.of_isTerminal {I T : C} (hI : IsInitial I) (hT : IsTerminal T)
    (_ : Mono (hI.to T)) : InitialMonoClass C :=
  InitialMonoClass.of_isInitial hI fun X => mono_of_mono_fac (hI.hom_ext (_ ≫ hT.from X) (hI.to T))

variable {J : Type u} [Category.{v} J]

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cone for `J`.
In `limitOfDiagramInitial` we show it is a limit cone. -/
@[to_dual (attr := implicit_reducible, simps)
/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cocone for `J`.
In `colimitOfDiagramTerminal` we show it is a colimit cocone. -/]
def coneOfDiagramInitial {X : J} (tX : IsInitial X) (F : J ⥤ C) : Cone F where
  pt := F.obj X
  π :=
    { app := fun j => F.map (tX.to j)
      naturality := fun j j' k => by
        dsimp
        rw [← F.map_comp, Category.id_comp, tX.hom_ext (tX.to j ≫ k) (tX.to j')] }

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, show the cone
`coneOfDiagramInitial` is a limit. -/
@[to_dual
/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, show the cocone
`coconeOfDiagramTerminal` is a colimit. -/]
def limitOfDiagramInitial {X : J} (tX : IsInitial X) (F : J ⥤ C) :
    IsLimit (coneOfDiagramInitial tX F) where
  lift s := s.π.app X
  uniq s m w := by
    simp_rw [← w X, coneOfDiagramInitial_π_app, tX.hom_ext (tX.to X) (𝟙 _)]
    simp

@[to_dual isIso_ι_app_of_isTerminal]
lemma IsLimit.isIso_π_app_of_isInitial {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
    (X : J) (hX : IsInitial X) :
    IsIso (c.π.app X) := by
  change IsIso (conePointUniqueUpToIso hc (limitOfDiagramInitial hX F)).hom
  infer_instance

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cone for `J`,
provided that the morphisms in the diagram are isomorphisms.
In `limitOfDiagramTerminal` we show it is a limit cone. -/
@[to_dual (attr := implicit_reducible, simps)
/-- From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cocone for `J`,
provided that the morphisms in the diagram are isomorphisms.
In `colimitOfDiagramInitial` we show it is a colimit cocone. -/]
def coneOfDiagramTerminal {X : J} (hX : IsTerminal X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : Cone F where
  pt := F.obj X
  π :=
    { app := fun _ => inv (F.map (hX.from _))
      naturality := by
        intro i j f
        dsimp
        simp only [IsIso.eq_inv_comp, IsIso.comp_inv_eq, Category.id_comp, ← F.map_comp,
          hX.hom_ext (hX.from i) (f ≫ hX.from j)] }

/-- From a functor `F : J ⥤ C`, given a terminal object of `J` and that the morphisms in the
diagram are isomorphisms, show the cone `coneOfDiagramTerminal` is a limit. -/
@[to_dual
/-- From a functor `F : J ⥤ C`, given an initial object of `J` and that the morphisms in the
diagram are isomorphisms, show the cone `coconeOfDiagramInitial` is a colimit. -/]
def limitOfDiagramTerminal {X : J} (hX : IsTerminal X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsLimit (coneOfDiagramTerminal hX F) where
  lift S := S.π.app _


/-- Any morphism between terminal objects is an isomorphism. -/
@[to_dual (reorder := hX hY) /-- Any morphism between initial objects is an isomorphism. -/]
lemma isIso_of_isTerminal {X Y : C} (hX : IsTerminal X) (hY : IsTerminal Y) (f : X ⟶ Y) :
    IsIso f := by
  refine ⟨⟨IsTerminal.from hX Y, ?_⟩⟩
  simp only [IsTerminal.comp_from, IsTerminal.from_self, true_and]
  apply IsTerminal.hom_ext hY

end

/-- An initial object is terminal in the opposite category. -/
@[to_dual /-- A terminal object is initial in the opposite category. -/]
def IsInitial.op {X : C} (hX : IsInitial X) : IsTerminal (op X) :=
  IsTerminal.ofUniqueHom (fun _ ↦ (hX.to _).op)
    (fun _ _ ↦ Quiver.Hom.unop_inj (hX.hom_ext _ _))

/-- An initial object in the opposite category is terminal in the original category. -/
@[to_dual /-- A terminal object in the opposite category is initial in the original category. -/]
def IsInitial.unop {X : Cᵒᵖ} (hX : IsInitial X) : IsTerminal X.unop :=
  IsTerminal.ofUniqueHom (fun _ ↦ (hX.to _).unop)
    (fun _ _ ↦ Quiver.Hom.op_inj (hX.hom_ext _ _))

end Limits

namespace Functor
open Limits
variable (C : Type*) [Category* C] {D : Type*} [Category* D]

/-- The constant functor returning a specific terminal object is indeed terminal. -/
@[to_dual /-- The constant functor returning a specific initial object is indeed initial. -/]
def isTerminalConst {X : D} (hX : IsTerminal X) :
    IsTerminal ((Functor.const C).obj X) :=
  .ofUniqueHom (fun Y => { app Z := hX.from (Y.obj Z) }) (by intros; ext; apply hX.hom_ext)

@[to_dual (attr := simp) isInitialConst_to_app]
lemma isTerminalConst_from_app {X : D} (hX : IsTerminal X)
    (F : C ⥤ D) (Y : C) : ((isTerminalConst C hX).from F).app Y = hX.from (F.obj Y) := rfl

end Functor

end CategoryTheory
