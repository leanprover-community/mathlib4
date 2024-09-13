/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.PEmpty
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Initial and terminal objects in a category.

## References
* [Stacks: Initial and final objects](https://stacks.math.columbia.edu/tag/002B)
-/


noncomputable section

universe w w' v v₁ v₂ u u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

/-- Construct a cone for the empty diagram given an object. -/
@[simps]
def asEmptyCone (X : C) : Cone (Functor.empty.{0} C) :=
  { pt := X
    π :=
    { app := by aesop_cat } }

/-- Construct a cocone for the empty diagram given an object. -/
@[simps]
def asEmptyCocone (X : C) : Cocone (Functor.empty.{0} C) :=
  { pt := X
    ι :=
    { app := by aesop_cat } }

/-- `X` is terminal if the cone it induces on the empty diagram is limiting. -/
abbrev IsTerminal (X : C) :=
  IsLimit (asEmptyCone X)

/-- `X` is initial if the cocone it induces on the empty diagram is colimiting. -/
abbrev IsInitial (X : C) :=
  IsColimit (asEmptyCocone X)

/-- An object `Y` is terminal iff for every `X` there is a unique morphism `X ⟶ Y`. -/
def isTerminalEquivUnique (F : Discrete.{0} PEmpty.{1} ⥤ C) (Y : C) :
    IsLimit (⟨Y, by aesop_cat, by aesop_cat⟩ : Cone F) ≃ ∀ X : C, Unique (X ⟶ Y) where
  toFun t X :=
    { default := t.lift ⟨X, ⟨by aesop_cat, by aesop_cat⟩⟩
      uniq := fun f =>
        t.uniq ⟨X, ⟨by aesop_cat, by aesop_cat⟩⟩ f (by aesop_cat) }
  invFun u :=
    { lift := fun s => (u s.pt).default
      uniq := fun s _ _ => (u s.pt).2 _ }
  left_inv := by dsimp [Function.LeftInverse]; intro x; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.RightInverse,Function.LeftInverse]
    intro u; funext X; simp only

/-- An object `Y` is terminal if for every `X` there is a unique morphism `X ⟶ Y`
    (as an instance). -/
def IsTerminal.ofUnique (Y : C) [h : ∀ X : C, Unique (X ⟶ Y)] : IsTerminal Y where
  lift s := (h s.pt).default
  fac := fun _ ⟨j⟩ => j.elim

/-- An object `Y` is terminal if for every `X` there is a unique morphism `X ⟶ Y`
    (as explicit arguments). -/
def IsTerminal.ofUniqueHom {Y : C} (h : ∀ X : C, X ⟶ Y) (uniq : ∀ (X : C) (m : X ⟶ Y), m = h X) :
    IsTerminal Y :=
  have : ∀ X : C, Unique (X ⟶ Y) := fun X ↦ ⟨⟨h X⟩, uniq X⟩
  IsTerminal.ofUnique Y

/-- If `α` is a preorder with top, then `⊤` is a terminal object. -/
def isTerminalTop {α : Type*} [Preorder α] [OrderTop α] : IsTerminal (⊤ : α) :=
  IsTerminal.ofUnique _

/-- Transport a term of type `IsTerminal` across an isomorphism. -/
def IsTerminal.ofIso {Y Z : C} (hY : IsTerminal Y) (i : Y ≅ Z) : IsTerminal Z :=
  IsLimit.ofIsoLimit hY
    { hom := { hom := i.hom }
      inv := { hom := i.inv } }

/-- If `X` and `Y` are isomorphic, then `X` is terminal iff `Y` is. -/
def IsTerminal.equivOfIso {X Y : C} (e : X ≅ Y) :
    IsTerminal X ≃ IsTerminal Y where
  toFun h := IsTerminal.ofIso h e
  invFun h := IsTerminal.ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- An object `X` is initial iff for every `Y` there is a unique morphism `X ⟶ Y`. -/
def isInitialEquivUnique (F : Discrete.{0} PEmpty.{1} ⥤ C) (X : C) :
    IsColimit (⟨X, ⟨by aesop_cat, by aesop_cat⟩⟩ : Cocone F) ≃ ∀ Y : C, Unique (X ⟶ Y) where
  toFun t X :=
    { default := t.desc ⟨X, ⟨by aesop_cat, by aesop_cat⟩⟩
      uniq := fun f => t.uniq ⟨X, ⟨by aesop_cat, by aesop_cat⟩⟩ f (by aesop_cat) }
  invFun u :=
    { desc := fun s => (u s.pt).default
      uniq := fun s _ _ => (u s.pt).2 _ }
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.RightInverse,Function.LeftInverse]
    intro; funext; simp only

/-- An object `X` is initial if for every `Y` there is a unique morphism `X ⟶ Y`
    (as an instance). -/
def IsInitial.ofUnique (X : C) [h : ∀ Y : C, Unique (X ⟶ Y)] : IsInitial X where
  desc s := (h s.pt).default
  fac := fun _ ⟨j⟩ => j.elim

/-- An object `X` is initial if for every `Y` there is a unique morphism `X ⟶ Y`
    (as explicit arguments). -/
def IsInitial.ofUniqueHom {X : C} (h : ∀ Y : C, X ⟶ Y) (uniq : ∀ (Y : C) (m : X ⟶ Y), m = h Y) :
    IsInitial X :=
  have : ∀ Y : C, Unique (X ⟶ Y) := fun Y ↦ ⟨⟨h Y⟩, uniq Y⟩
  IsInitial.ofUnique X

/-- If `α` is a preorder with bot, then `⊥` is an initial object. -/
def isInitialBot {α : Type*} [Preorder α] [OrderBot α] : IsInitial (⊥ : α) :=
  IsInitial.ofUnique _

/-- Transport a term of type `is_initial` across an isomorphism. -/
def IsInitial.ofIso {X Y : C} (hX : IsInitial X) (i : X ≅ Y) : IsInitial Y :=
  IsColimit.ofIsoColimit hX
    { hom := { hom := i.hom }
      inv := { hom := i.inv } }

/-- If `X` and `Y` are isomorphic, then `X` is initial iff `Y` is. -/
def IsInitial.equivOfIso {X Y : C} (e : X ≅ Y) :
    IsInitial X ≃ IsInitial Y where
  toFun h := IsInitial.ofIso h e
  invFun h := IsInitial.ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Give the morphism to a terminal object from any other. -/
def IsTerminal.from {X : C} (t : IsTerminal X) (Y : C) : Y ⟶ X :=
  t.lift (asEmptyCone Y)

/-- Any two morphisms to a terminal object are equal. -/
theorem IsTerminal.hom_ext {X Y : C} (t : IsTerminal X) (f g : Y ⟶ X) : f = g :=
  IsLimit.hom_ext t (by aesop_cat)

@[simp]
theorem IsTerminal.comp_from {Z : C} (t : IsTerminal Z) {X Y : C} (f : X ⟶ Y) :
    f ≫ t.from Y = t.from X :=
  t.hom_ext _ _

@[simp]
theorem IsTerminal.from_self {X : C} (t : IsTerminal X) : t.from X = 𝟙 X :=
  t.hom_ext _ _

/-- Give the morphism from an initial object to any other. -/
def IsInitial.to {X : C} (t : IsInitial X) (Y : C) : X ⟶ Y :=
  t.desc (asEmptyCocone Y)

/-- Any two morphisms from an initial object are equal. -/
theorem IsInitial.hom_ext {X Y : C} (t : IsInitial X) (f g : X ⟶ Y) : f = g :=
  IsColimit.hom_ext t (by aesop_cat)

@[simp]
theorem IsInitial.to_comp {X : C} (t : IsInitial X) {Y Z : C} (f : Y ⟶ Z) : t.to Y ≫ f = t.to Z :=
  t.hom_ext _ _

@[simp]
theorem IsInitial.to_self {X : C} (t : IsInitial X) : t.to X = 𝟙 X :=
  t.hom_ext _ _

/-- Any morphism from a terminal object is split mono. -/
theorem IsTerminal.isSplitMono_from {X Y : C} (t : IsTerminal X) (f : X ⟶ Y) : IsSplitMono f :=
  IsSplitMono.mk' ⟨t.from _, t.hom_ext _ _⟩

/-- Any morphism to an initial object is split epi. -/
theorem IsInitial.isSplitEpi_to {X Y : C} (t : IsInitial X) (f : Y ⟶ X) : IsSplitEpi f :=
  IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩

/-- Any morphism from a terminal object is mono. -/
theorem IsTerminal.mono_from {X Y : C} (t : IsTerminal X) (f : X ⟶ Y) : Mono f := by
  haveI := t.isSplitMono_from f; infer_instance

/-- Any morphism to an initial object is epi. -/
theorem IsInitial.epi_to {X Y : C} (t : IsInitial X) (f : Y ⟶ X) : Epi f := by
  haveI := t.isSplitEpi_to f; infer_instance

/-- If `T` and `T'` are terminal, they are isomorphic. -/
@[simps]
def IsTerminal.uniqueUpToIso {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') : T ≅ T' where
  hom := hT'.from _
  inv := hT.from _

/-- If `I` and `I'` are initial, they are isomorphic. -/
@[simps]
def IsInitial.uniqueUpToIso {I I' : C} (hI : IsInitial I) (hI' : IsInitial I') : I ≅ I' where
  hom := hI.to _
  inv := hI'.to _

variable (C)

/-- A category has a terminal object if it has a limit over the empty diagram.
Use `hasTerminal_of_unique` to construct instances.
-/
abbrev HasTerminal :=
  HasLimitsOfShape (Discrete.{0} PEmpty) C

/-- A category has an initial object if it has a colimit over the empty diagram.
Use `hasInitial_of_unique` to construct instances.
-/
abbrev HasInitial :=
  HasColimitsOfShape (Discrete.{0} PEmpty) C

section Univ

variable (X : C) {F₁ : Discrete.{w} PEmpty ⥤ C} {F₂ : Discrete.{w'} PEmpty ⥤ C}

/-- Being terminal is independent of the empty diagram, its universe, and the cone over it,
    as long as the cone points are isomorphic. -/
def isLimitChangeEmptyCone {c₁ : Cone F₁} (hl : IsLimit c₁) (c₂ : Cone F₂) (hi : c₁.pt ≅ c₂.pt) :
    IsLimit c₂ where
  lift c := hl.lift ⟨c.pt, by aesop_cat, by aesop_cat⟩ ≫ hi.hom
  uniq c f _ := by
    dsimp
    rw [← hl.uniq _ (f ≫ hi.inv) _]
    · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · aesop_cat

/-- Replacing an empty cone in `IsLimit` by another with the same cone point
    is an equivalence. -/
def isLimitEmptyConeEquiv (c₁ : Cone F₁) (c₂ : Cone F₂) (h : c₁.pt ≅ c₂.pt) :
    IsLimit c₁ ≃ IsLimit c₂ where
  toFun hl := isLimitChangeEmptyCone C hl c₂ h
  invFun hl := isLimitChangeEmptyCone C hl c₁ h.symm
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.LeftInverse,Function.RightInverse]; intro
    simp only [eq_iff_true_of_subsingleton]

theorem hasTerminalChangeDiagram (h : HasLimit F₁) : HasLimit F₂ :=
  ⟨⟨⟨⟨limit F₁, by aesop_cat, by aesop_cat⟩,
    isLimitChangeEmptyCone C (limit.isLimit F₁) _ (eqToIso rfl)⟩⟩⟩

theorem hasTerminalChangeUniverse [h : HasLimitsOfShape (Discrete.{w} PEmpty) C] :
    HasLimitsOfShape (Discrete.{w'} PEmpty) C where
  has_limit _ := hasTerminalChangeDiagram C (h.1 (Functor.empty C))

/-- Being initial is independent of the empty diagram, its universe, and the cocone over it,
    as long as the cocone points are isomorphic. -/
def isColimitChangeEmptyCocone {c₁ : Cocone F₁} (hl : IsColimit c₁) (c₂ : Cocone F₂)
    (hi : c₁.pt ≅ c₂.pt) : IsColimit c₂ where
  desc c := hi.inv ≫ hl.desc ⟨c.pt, by aesop_cat, by aesop_cat⟩
  uniq c f _ := by
    dsimp
    rw [← hl.uniq _ (hi.hom ≫ f) _]
    · simp only [Iso.inv_hom_id_assoc]
    · aesop_cat

/-- Replacing an empty cocone in `IsColimit` by another with the same cocone point
    is an equivalence. -/
def isColimitEmptyCoconeEquiv (c₁ : Cocone F₁) (c₂ : Cocone F₂) (h : c₁.pt ≅ c₂.pt) :
    IsColimit c₁ ≃ IsColimit c₂ where
  toFun hl := isColimitChangeEmptyCocone C hl c₂ h
  invFun hl := isColimitChangeEmptyCocone C hl c₁ h.symm
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.LeftInverse,Function.RightInverse]; intro
    simp only [eq_iff_true_of_subsingleton]

theorem hasInitialChangeDiagram (h : HasColimit F₁) : HasColimit F₂ :=
  ⟨⟨⟨⟨colimit F₁, by aesop_cat, by aesop_cat⟩,
    isColimitChangeEmptyCocone C (colimit.isColimit F₁) _ (eqToIso rfl)⟩⟩⟩

theorem hasInitialChangeUniverse [h : HasColimitsOfShape (Discrete.{w} PEmpty) C] :
    HasColimitsOfShape (Discrete.{w'} PEmpty) C where
  has_colimit _ := hasInitialChangeDiagram C (h.1 (Functor.empty C))

end Univ

/-- An arbitrary choice of terminal object, if one exists.
You can use the notation `⊤_ C`.
This object is characterized by having a unique morphism from any object.
-/
abbrev terminal [HasTerminal C] : C :=
  limit (Functor.empty.{0} C)

/-- An arbitrary choice of initial object, if one exists.
You can use the notation `⊥_ C`.
This object is characterized by having a unique morphism to any object.
-/
abbrev initial [HasInitial C] : C :=
  colimit (Functor.empty.{0} C)

/-- Notation for the terminal object in `C` -/
notation "⊤_ " C:20 => terminal C

/-- Notation for the initial object in `C` -/
notation "⊥_ " C:20 => initial C

section

variable {C}

/-- We can more explicitly show that a category has a terminal object by specifying the object,
and showing there is a unique morphism to it from any other object. -/
theorem hasTerminal_of_unique (X : C) [h : ∀ Y : C, Unique (Y ⟶ X)] : HasTerminal C :=
  { has_limit := fun F => HasLimit.mk ⟨_, (isTerminalEquivUnique F X).invFun h⟩ }

theorem IsTerminal.hasTerminal {X : C} (h : IsTerminal X) : HasTerminal C :=
  { has_limit := fun F => HasLimit.mk ⟨⟨X, by aesop_cat, by aesop_cat⟩,
    isLimitChangeEmptyCone _ h _ (Iso.refl _)⟩ }

/-- We can more explicitly show that a category has an initial object by specifying the object,
and showing there is a unique morphism from it to any other object. -/
theorem hasInitial_of_unique (X : C) [h : ∀ Y : C, Unique (X ⟶ Y)] : HasInitial C :=
  { has_colimit := fun F => HasColimit.mk ⟨_, (isInitialEquivUnique F X).invFun h⟩ }

theorem IsInitial.hasInitial {X : C} (h : IsInitial X) : HasInitial C where
  has_colimit F :=
    HasColimit.mk ⟨⟨X, by aesop_cat, by aesop_cat⟩, isColimitChangeEmptyCocone _ h _ (Iso.refl _)⟩

/-- The map from an object to the terminal object. -/
abbrev terminal.from [HasTerminal C] (P : C) : P ⟶ ⊤_ C :=
  limit.lift (Functor.empty C) (asEmptyCone P)

/-- The map to an object from the initial object. -/
abbrev initial.to [HasInitial C] (P : C) : ⊥_ C ⟶ P :=
  colimit.desc (Functor.empty C) (asEmptyCocone P)

/-- A terminal object is terminal. -/
def terminalIsTerminal [HasTerminal C] : IsTerminal (⊤_ C) where
  lift s := terminal.from _

/-- An initial object is initial. -/
def initialIsInitial [HasInitial C] : IsInitial (⊥_ C) where
  desc s := initial.to _

instance uniqueToTerminal [HasTerminal C] (P : C) : Unique (P ⟶ ⊤_ C) :=
  isTerminalEquivUnique _ (⊤_ C) terminalIsTerminal P

instance uniqueFromInitial [HasInitial C] (P : C) : Unique (⊥_ C ⟶ P) :=
  isInitialEquivUnique _ (⊥_ C) initialIsInitial P

@[ext] theorem terminal.hom_ext [HasTerminal C] {P : C} (f g : P ⟶ ⊤_ C) : f = g := by ext ⟨⟨⟩⟩

@[ext] theorem initial.hom_ext [HasInitial C] {P : C} (f g : ⊥_ C ⟶ P) : f = g := by ext ⟨⟨⟩⟩

@[simp]
theorem terminal.comp_from [HasTerminal C] {P Q : C} (f : P ⟶ Q) :
    f ≫ terminal.from Q = terminal.from P := by
  simp [eq_iff_true_of_subsingleton]

@[simp]
theorem initial.to_comp [HasInitial C] {P Q : C} (f : P ⟶ Q) : initial.to P ≫ f = initial.to Q := by
  simp [eq_iff_true_of_subsingleton]

/-- The (unique) isomorphism between the chosen initial object and any other initial object. -/
@[simp]
def initialIsoIsInitial [HasInitial C] {P : C} (t : IsInitial P) : ⊥_ C ≅ P :=
  initialIsInitial.uniqueUpToIso t

/-- The (unique) isomorphism between the chosen terminal object and any other terminal object. -/
@[simp]
def terminalIsoIsTerminal [HasTerminal C] {P : C} (t : IsTerminal P) : ⊤_ C ≅ P :=
  terminalIsTerminal.uniqueUpToIso t

/-- Any morphism from a terminal object is split mono. -/
instance terminal.isSplitMono_from {Y : C} [HasTerminal C] (f : ⊤_ C ⟶ Y) : IsSplitMono f :=
  IsTerminal.isSplitMono_from terminalIsTerminal _

/-- Any morphism to an initial object is split epi. -/
instance initial.isSplitEpi_to {Y : C} [HasInitial C] (f : Y ⟶ ⊥_ C) : IsSplitEpi f :=
  IsInitial.isSplitEpi_to initialIsInitial _

/-- An initial object is terminal in the opposite category. -/
def terminalOpOfInitial {X : C} (t : IsInitial X) : IsTerminal (Opposite.op X) where
  lift s := (t.to s.pt.unop).op
  uniq s m _ := Quiver.Hom.unop_inj (t.hom_ext _ _)

/-- An initial object in the opposite category is terminal in the original category. -/
def terminalUnopOfInitial {X : Cᵒᵖ} (t : IsInitial X) : IsTerminal X.unop where
  lift s := (t.to (Opposite.op s.pt)).unop
  uniq s m _ := Quiver.Hom.op_inj (t.hom_ext _ _)

/-- A terminal object is initial in the opposite category. -/
def initialOpOfTerminal {X : C} (t : IsTerminal X) : IsInitial (Opposite.op X) where
  desc s := (t.from s.pt.unop).op
  uniq s m _ := Quiver.Hom.unop_inj (t.hom_ext _ _)

/-- A terminal object in the opposite category is initial in the original category. -/
def initialUnopOfTerminal {X : Cᵒᵖ} (t : IsTerminal X) : IsInitial X.unop where
  desc s := (t.from (Opposite.op s.pt)).unop
  uniq s m _ := Quiver.Hom.op_inj (t.hom_ext _ _)

instance hasInitial_op_of_hasTerminal [HasTerminal C] : HasInitial Cᵒᵖ :=
  (initialOpOfTerminal terminalIsTerminal).hasInitial

instance hasTerminal_op_of_hasInitial [HasInitial C] : HasTerminal Cᵒᵖ :=
  (terminalOpOfInitial initialIsInitial).hasTerminal

theorem hasTerminal_of_hasInitial_op [HasInitial Cᵒᵖ] : HasTerminal C :=
  (terminalUnopOfInitial initialIsInitial).hasTerminal

theorem hasInitial_of_hasTerminal_op [HasTerminal Cᵒᵖ] : HasInitial C :=
  (initialUnopOfTerminal terminalIsTerminal).hasInitial

instance {J : Type*} [Category J] {C : Type*} [Category C] [HasTerminal C] :
    HasLimit ((CategoryTheory.Functor.const J).obj (⊤_ C)) :=
  HasLimit.mk
    { cone :=
        { pt := ⊤_ C
          π := { app := fun _ => terminal.from _ } }
      isLimit := { lift := fun s => terminal.from _ } }

/-- The limit of the constant `⊤_ C` functor is `⊤_ C`. -/
@[simps hom]
def limitConstTerminal {J : Type*} [Category J] {C : Type*} [Category C] [HasTerminal C] :
    limit ((CategoryTheory.Functor.const J).obj (⊤_ C)) ≅ ⊤_ C where
  hom := terminal.from _
  inv :=
    limit.lift ((CategoryTheory.Functor.const J).obj (⊤_ C))
      { pt := ⊤_ C
        π := { app := fun j => terminal.from _ } }

@[reassoc (attr := simp)]
theorem limitConstTerminal_inv_π {J : Type*} [Category J] {C : Type*} [Category C] [HasTerminal C]
    {j : J} :
    limitConstTerminal.inv ≫ limit.π ((CategoryTheory.Functor.const J).obj (⊤_ C)) j =
      terminal.from _ := by aesop_cat

instance {J : Type*} [Category J] {C : Type*} [Category C] [HasInitial C] :
    HasColimit ((CategoryTheory.Functor.const J).obj (⊥_ C)) :=
  HasColimit.mk
    { cocone :=
        { pt := ⊥_ C
          ι := { app := fun _ => initial.to _ } }
      isColimit := { desc := fun s => initial.to _ } }

/-- The colimit of the constant `⊥_ C` functor is `⊥_ C`. -/
@[simps inv]
def colimitConstInitial {J : Type*} [Category J] {C : Type*} [Category C] [HasInitial C] :
    colimit ((CategoryTheory.Functor.const J).obj (⊥_ C)) ≅ ⊥_ C where
  hom :=
    colimit.desc ((CategoryTheory.Functor.const J).obj (⊥_ C))
      { pt := ⊥_ C
        ι := { app := fun j => initial.to _ } }
  inv := initial.to _

@[reassoc (attr := simp)]
theorem ι_colimitConstInitial_hom {J : Type*} [Category J] {C : Type*} [Category C] [HasInitial C]
    {j : J} :
    colimit.ι ((CategoryTheory.Functor.const J).obj (⊥_ C)) j ≫ colimitConstInitial.hom =
      initial.to _ := by aesop_cat

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

instance (priority := 100) initial.mono_from [HasInitial C] [InitialMonoClass C] (X : C)
    (f : ⊥_ C ⟶ X) : Mono f :=
  initialIsInitial.mono_from f

/-- To show a category is an `InitialMonoClass` it suffices to give an initial object such that
every morphism out of it is a monomorphism. -/
theorem InitialMonoClass.of_isInitial {I : C} (hI : IsInitial I) (h : ∀ X, Mono (hI.to X)) :
    InitialMonoClass C where
  isInitial_mono_from {I'} X hI' := by
    rw [hI'.hom_ext (hI'.to X) ((hI'.uniqueUpToIso hI).hom ≫ hI.to X)]
    apply mono_comp

/-- To show a category is an `InitialMonoClass` it suffices to show every morphism out of the
initial object is a monomorphism. -/
theorem InitialMonoClass.of_initial [HasInitial C] (h : ∀ X : C, Mono (initial.to X)) :
    InitialMonoClass C :=
  InitialMonoClass.of_isInitial initialIsInitial h

/-- To show a category is an `InitialMonoClass` it suffices to show the unique morphism from an
initial object to a terminal object is a monomorphism. -/
theorem InitialMonoClass.of_isTerminal {I T : C} (hI : IsInitial I) (hT : IsTerminal T)
    (_ : Mono (hI.to T)) : InitialMonoClass C :=
  InitialMonoClass.of_isInitial hI fun X => mono_of_mono_fac (hI.hom_ext (_ ≫ hT.from X) (hI.to T))

/-- To show a category is an `InitialMonoClass` it suffices to show the unique morphism from the
initial object to a terminal object is a monomorphism. -/
theorem InitialMonoClass.of_terminal [HasInitial C] [HasTerminal C] (h : Mono (initial.to (⊤_ C))) :
    InitialMonoClass C :=
  InitialMonoClass.of_isTerminal initialIsInitial terminalIsTerminal h

section Comparison

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

/-- The comparison morphism from the image of a terminal object to the terminal object in the target
category.
This is an isomorphism iff `G` preserves terminal objects, see
`CategoryTheory.Limits.PreservesTerminal.ofIsoComparison`.
-/
def terminalComparison [HasTerminal C] [HasTerminal D] : G.obj (⊤_ C) ⟶ ⊤_ D :=
  terminal.from _

-- TODO: Show this is an isomorphism if and only if `G` preserves initial objects.
/--
The comparison morphism from the initial object in the target category to the image of the initial
object.
-/
def initialComparison [HasInitial C] [HasInitial D] : ⊥_ D ⟶ G.obj (⊥_ C) :=
  initial.to _

end Comparison

variable {J : Type u} [Category.{v} J]

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cone for `J`.
In `limitOfDiagramInitial` we show it is a limit cone. -/
@[simps]
def coneOfDiagramInitial {X : J} (tX : IsInitial X) (F : J ⥤ C) : Cone F where
  pt := F.obj X
  π :=
    { app := fun j => F.map (tX.to j)
      naturality := fun j j' k => by
        dsimp
        rw [← F.map_comp, Category.id_comp, tX.hom_ext (tX.to j ≫ k) (tX.to j')] }

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, show the cone
`coneOfDiagramInitial` is a limit. -/
def limitOfDiagramInitial {X : J} (tX : IsInitial X) (F : J ⥤ C) :
    IsLimit (coneOfDiagramInitial tX F) where
  lift s := s.π.app X
  uniq s m w := by
    conv_lhs => dsimp
    simp_rw [← w X, coneOfDiagramInitial_π_app, tX.hom_ext (tX.to X) (𝟙 _)]
    simp

instance hasLimit_of_domain_hasInitial [HasInitial J] {F : J ⥤ C} : HasLimit F :=
  HasLimit.mk { cone := _, isLimit := limitOfDiagramInitial (initialIsInitial) F }

-- See note [dsimp, simp]
-- This is reducible to allow usage of lemmas about `cone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has an initial object then the image of it is isomorphic
to the limit of `F`. -/
abbrev limitOfInitial (F : J ⥤ C) [HasInitial J] : limit F ≅ F.obj (⊥_ J) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramInitial initialIsInitial F)

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cone for `J`,
provided that the morphisms in the diagram are isomorphisms.
In `limitOfDiagramTerminal` we show it is a limit cone. -/
@[simps]
def coneOfDiagramTerminal {X : J} (hX : IsTerminal X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : Cone F where
  pt := F.obj X
  π :=
    { app := fun i => inv (F.map (hX.from _))
      naturality := by
        intro i j f
        dsimp
        simp only [IsIso.eq_inv_comp, IsIso.comp_inv_eq, Category.id_comp, ← F.map_comp,
          hX.hom_ext (hX.from i) (f ≫ hX.from j)] }

/-- From a functor `F : J ⥤ C`, given a terminal object of `J` and that the morphisms in the
diagram are isomorphisms, show the cone `coneOfDiagramTerminal` is a limit. -/
def limitOfDiagramTerminal {X : J} (hX : IsTerminal X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsLimit (coneOfDiagramTerminal hX F) where
  lift S := S.π.app _

instance hasLimit_of_domain_hasTerminal [HasTerminal J] {F : J ⥤ C}
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : HasLimit F :=
  HasLimit.mk { cone := _, isLimit := limitOfDiagramTerminal (terminalIsTerminal) F }

-- This is reducible to allow usage of lemmas about `cone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has a terminal object and all the morphisms in the diagram
are isomorphisms, then the image of the terminal object is isomorphic to the limit of `F`. -/
abbrev limitOfTerminal (F : J ⥤ C) [HasTerminal J] [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] :
    limit F ≅ F.obj (⊤_ J) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramTerminal terminalIsTerminal F)

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cocone for `J`.
In `colimitOfDiagramTerminal` we show it is a colimit cocone. -/
@[simps]
def coconeOfDiagramTerminal {X : J} (tX : IsTerminal X) (F : J ⥤ C) : Cocone F where
  pt := F.obj X
  ι :=
    { app := fun j => F.map (tX.from j)
      naturality := fun j j' k => by
        dsimp
        rw [← F.map_comp, Category.comp_id, tX.hom_ext (k ≫ tX.from j') (tX.from j)] }

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, show the cocone
`coconeOfDiagramTerminal` is a colimit. -/
def colimitOfDiagramTerminal {X : J} (tX : IsTerminal X) (F : J ⥤ C) :
    IsColimit (coconeOfDiagramTerminal tX F) where
  desc s := s.ι.app X
  uniq s m w := by
    conv_rhs => dsimp -- Porting note: why do I need this much firepower?
    rw [← w X, coconeOfDiagramTerminal_ι_app, tX.hom_ext (tX.from X) (𝟙 _)]
    simp

instance hasColimit_of_domain_hasTerminal [HasTerminal J] {F : J ⥤ C} : HasColimit F :=
  HasColimit.mk { cocone := _, isColimit := colimitOfDiagramTerminal (terminalIsTerminal) F }

lemma IsColimit.isIso_ι_app_of_isTerminal {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
    (X : J) (hX : IsTerminal X) :
    IsIso (c.ι.app X) := by
  change IsIso (coconePointUniqueUpToIso (colimitOfDiagramTerminal hX F) hc).hom
  infer_instance

-- This is reducible to allow usage of lemmas about `cocone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has a terminal object then the image of it is isomorphic
to the colimit of `F`. -/
abbrev colimitOfTerminal (F : J ⥤ C) [HasTerminal J] : colimit F ≅ F.obj (⊤_ J) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramTerminal terminalIsTerminal F)

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cocone for `J`,
provided that the morphisms in the diagram are isomorphisms.
In `colimitOfDiagramInitial` we show it is a colimit cocone. -/
@[simps]
def coconeOfDiagramInitial {X : J} (hX : IsInitial X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : Cocone F where
  pt := F.obj X
  ι :=
    { app := fun i => inv (F.map (hX.to _))
      naturality := by
        intro i j f
        dsimp
        simp only [IsIso.eq_inv_comp, IsIso.comp_inv_eq, Category.comp_id, ← F.map_comp,
          hX.hom_ext (hX.to i ≫ f) (hX.to j)] }

/-- From a functor `F : J ⥤ C`, given an initial object of `J` and that the morphisms in the
diagram are isomorphisms, show the cone `coconeOfDiagramInitial` is a colimit. -/
def colimitOfDiagramInitial {X : J} (hX : IsInitial X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsColimit (coconeOfDiagramInitial hX F) where
  desc S := S.ι.app _

instance hasColimit_of_domain_hasInitial [HasInitial J] {F : J ⥤ C}
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : HasColimit F :=
  HasColimit.mk { cocone := _, isColimit := colimitOfDiagramInitial (initialIsInitial) F }

lemma IsLimit.isIso_π_app_of_isInitial {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
    (X : J) (hX : IsInitial X) :
    IsIso (c.π.app X) := by
  change IsIso (conePointUniqueUpToIso hc (limitOfDiagramInitial hX F)).hom
  infer_instance

-- This is reducible to allow usage of lemmas about `cocone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has an initial object and all the morphisms in the diagram
are isomorphisms, then the image of the initial object is isomorphic to the colimit of `F`. -/
abbrev colimitOfInitial (F : J ⥤ C) [HasInitial J] [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] :
    colimit F ≅ F.obj (⊥_ J) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramInitial initialIsInitial _)

/-- If `j` is initial in the index category, then the map `limit.π F j` is an isomorphism.
-/
theorem isIso_π_of_isInitial {j : J} (I : IsInitial j) (F : J ⥤ C) [HasLimit F] :
    IsIso (limit.π F j) :=
  ⟨⟨limit.lift _ (coneOfDiagramInitial I F), ⟨by ext; simp, by simp⟩⟩⟩

instance isIso_π_initial [HasInitial J] (F : J ⥤ C) : IsIso (limit.π F (⊥_ J)) :=
  isIso_π_of_isInitial initialIsInitial F

theorem isIso_π_of_isTerminal {j : J} (I : IsTerminal j) (F : J ⥤ C) [HasLimit F]
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsIso (limit.π F j) :=
  ⟨⟨limit.lift _ (coneOfDiagramTerminal I F), by ext; simp, by simp⟩⟩

instance isIso_π_terminal [HasTerminal J] (F : J ⥤ C) [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] :
    IsIso (limit.π F (⊤_ J)) :=
  isIso_π_of_isTerminal terminalIsTerminal F

/-- If `j` is terminal in the index category, then the map `colimit.ι F j` is an isomorphism.
-/
theorem isIso_ι_of_isTerminal {j : J} (I : IsTerminal j) (F : J ⥤ C) [HasColimit F] :
    IsIso (colimit.ι F j) :=
  ⟨⟨colimit.desc _ (coconeOfDiagramTerminal I F), ⟨by simp, by ext; simp⟩⟩⟩

instance isIso_ι_terminal [HasTerminal J] (F : J ⥤ C) : IsIso (colimit.ι F (⊤_ J)) :=
  isIso_ι_of_isTerminal terminalIsTerminal F

theorem isIso_ι_of_isInitial {j : J} (I : IsInitial j) (F : J ⥤ C) [HasColimit F]
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsIso (colimit.ι F j) :=
  ⟨⟨colimit.desc _ (coconeOfDiagramInitial I F), by
    refine ⟨?_, by ext; simp⟩
    dsimp; simp only [colimit.ι_desc, coconeOfDiagramInitial_pt, coconeOfDiagramInitial_ι_app,
      Functor.const_obj_obj, IsInitial.to_self, Functor.map_id]
    dsimp [inv]; simp only [Category.id_comp, Category.comp_id, and_self]
    apply @Classical.choose_spec _ (fun x => x = 𝟙 F.obj j) _
  ⟩⟩

instance isIso_ι_initial [HasInitial J] (F : J ⥤ C) [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] :
    IsIso (colimit.ι F (⊥_ J)) :=
  isIso_ι_of_isInitial initialIsInitial F

/-- Any morphism between terminal objects is an isomorphism. -/
lemma isIso_of_isTerminal {X Y : C} (hX : IsTerminal X) (hY : IsTerminal Y) (f : X ⟶ Y) :
    IsIso f := by
  refine ⟨⟨IsTerminal.from hX Y, ?_⟩⟩
  simp only [IsTerminal.comp_from, IsTerminal.from_self, true_and]
  apply IsTerminal.hom_ext hY

/-- Any morphism between initial objects is an isomorphism. -/
lemma isIso_of_isInitial {X Y : C} (hX : IsInitial X) (hY : IsInitial Y) (f : X ⟶ Y) :
    IsIso f := by
  refine ⟨⟨IsInitial.to hY X, ?_⟩⟩
  simp only [IsInitial.to_comp, IsInitial.to_self, and_true]
  apply IsInitial.hom_ext hX

end

end CategoryTheory.Limits
