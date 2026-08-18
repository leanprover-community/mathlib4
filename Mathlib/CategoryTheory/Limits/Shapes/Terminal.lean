/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Initial and terminal objects in a category.

## References
* [Stacks: Initial and final objects](https://stacks.math.columbia.edu/tag/002B)
-/

@[expose] public section


noncomputable section

universe w w' v v₁ v₂ u u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable (C)

/-- A category has a terminal object if it has a limit over the empty diagram.
Use `hasTerminal_of_unique` to construct instances.
-/
@[to_dual
/-- A category has an initial object if it has a colimit over the empty diagram.
Use `hasInitial_of_unique` to construct instances.
-/]
abbrev HasTerminal :=
  HasLimitsOfShape (Discrete.{0} PEmpty) C

section Univ

variable {F₁ : Discrete.{w} PEmpty ⥤ C} {F₂ : Discrete.{w'} PEmpty ⥤ C}

@[to_dual]
theorem hasTerminalChangeDiagram (h : HasLimit F₁) : HasLimit F₂ :=
  ⟨⟨⟨⟨limit F₁, by cat_disch, by simp⟩,
    isLimitChangeEmptyCone C (limit.isLimit F₁) _ (eqToIso rfl)⟩⟩⟩

@[to_dual]
theorem hasTerminalChangeUniverse [h : HasLimitsOfShape (Discrete.{w} PEmpty) C] :
    HasLimitsOfShape (Discrete.{w'} PEmpty) C where
  has_limit _ := hasTerminalChangeDiagram C (h.1 (Functor.empty C))

end Univ

/-- An arbitrary choice of terminal object, if one exists.
You can use the notation `⊤_ C`.
This object is characterized by having a unique morphism from any object.
-/
@[to_dual
/-- An arbitrary choice of initial object, if one exists.
You can use the notation `⊥_ C`.
This object is characterized by having a unique morphism to any object.
-/]
abbrev terminal [HasTerminal C] : C :=
  limit (Functor.empty.{0} C)

/-- Notation for the terminal object in `C` -/
notation "⊤_ " C:20 => terminal C

/-- Notation for the initial object in `C` -/
notation "⊥_ " C:20 => initial C

section

variable {C}

/-- We can more explicitly show that a category has a terminal object by specifying the object,
and showing there is a unique morphism to it from any other object. -/
@[to_dual
/-- We can more explicitly show that a category has an initial object by specifying the object,
and showing there is a unique morphism from it to any other object. -/]
theorem hasTerminal_of_unique (X : C) [∀ Y, Nonempty (Y ⟶ X)] [∀ Y, Subsingleton (Y ⟶ X)] :
    HasTerminal C where
  has_limit F := .mk ⟨_, (isTerminalEquivUnique F X).invFun fun _ ↦
    ⟨Classical.inhabited_of_nonempty', (Subsingleton.elim · _)⟩⟩

@[to_dual]
theorem IsTerminal.hasTerminal {X : C} (h : IsTerminal X) : HasTerminal C :=
  { has_limit := fun F => HasLimit.mk ⟨⟨X, by cat_disch, by simp⟩,
    isLimitChangeEmptyCone _ h _ (Iso.refl _)⟩ }

/-- The map from an object to the terminal object. -/
@[to_dual «to» /-- The map to an object from the initial object. -/]
abbrev terminal.from [HasTerminal C] (P : C) : P ⟶ ⊤_ C :=
  limit.lift (Functor.empty C) (asEmptyCone P)

/-- A terminal object is terminal. -/
@[to_dual /-- An initial object is initial. -/]
def terminalIsTerminal [HasTerminal C] : IsTerminal (⊤_ C) where
  lift _ := terminal.from _

@[to_dual uniqueFromInitial]
instance uniqueToTerminal [HasTerminal C] (P : C) : Unique (P ⟶ ⊤_ C) :=
  isTerminalEquivUnique _ (⊤_ C) terminalIsTerminal P

@[to_dual (attr := ext)]
theorem terminal.hom_ext [HasTerminal C] {P : C} (f g : P ⟶ ⊤_ C) : f = g := by ext ⟨⟨⟩⟩

-- `initial.to_comp` does not need the `reassoc` attribute.
@[to_dual (attr := simp) to_comp, reassoc (attr := simp)]
theorem terminal.comp_from [HasTerminal C] {P Q : C} (f : P ⟶ Q) :
    f ≫ terminal.from Q = terminal.from P := by
  simp [eq_iff_true_of_subsingleton]

/-- The (unique) isomorphism between the chosen initial object and any other initial object. -/
@[to_dual (attr := simps!)
/-- The (unique) isomorphism between the chosen terminal object and any other terminal object. -/]
def initialIsoIsInitial [HasInitial C] {P : C} (t : IsInitial P) : ⊥_ C ≅ P :=
  initialIsInitial.uniqueUpToIso t

/-- Any morphism from a terminal object is split mono. -/
@[to_dual isSplitEpi_to /-- Any morphism to an initial object is split epi. -/]
instance terminal.isSplitMono_from {Y : C} [HasTerminal C] (f : ⊤_ C ⟶ Y) : IsSplitMono f :=
  IsTerminal.isSplitMono_from terminalIsTerminal _

@[to_dual]
instance hasInitial_op_of_hasTerminal [HasTerminal C] : HasInitial Cᵒᵖ :=
  (initialOpOfTerminal terminalIsTerminal).hasInitial

@[to_dual]
theorem hasTerminal_of_hasInitial_op [HasInitial Cᵒᵖ] : HasTerminal C :=
  (terminalUnopOfInitial initialIsInitial).hasTerminal

@[to_dual]
instance {J : Type*} [Category* J] {C : Type*} [Category* C] [HasTerminal C] :
    HasLimit ((CategoryTheory.Functor.const J).obj (⊤_ C)) :=
  HasLimit.mk
    { cone :=
        { pt := ⊤_ C
          π := { app := fun _ => terminal.from _ } }
      isLimit := { lift := fun _ => terminal.from _ } }

/-- The limit of the constant `⊤_ C` functor is `⊤_ C`. -/
@[simps hom]
def limitConstTerminal {J : Type*} [Category* J] {C : Type*} [Category* C] [HasTerminal C] :
    limit ((CategoryTheory.Functor.const J).obj (⊤_ C)) ≅ ⊤_ C where
  hom := terminal.from _
  inv :=
    limit.lift ((CategoryTheory.Functor.const J).obj (⊤_ C))
      { pt := ⊤_ C
        π := { app := fun _ => terminal.from _ } }

@[reassoc (attr := simp)]
theorem limitConstTerminal_inv_π {J : Type*} [Category* J] {C : Type*} [Category* C] [HasTerminal C]
    {j : J} :
    limitConstTerminal.inv ≫ limit.π ((CategoryTheory.Functor.const J).obj (⊤_ C)) j =
      terminal.from _ := by cat_disch

/-- The colimit of the constant `⊥_ C` functor is `⊥_ C`. -/
@[simps inv]
def colimitConstInitial {J : Type*} [Category* J] {C : Type*} [Category* C] [HasInitial C] :
    colimit ((CategoryTheory.Functor.const J).obj (⊥_ C)) ≅ ⊥_ C where
  hom :=
    colimit.desc ((CategoryTheory.Functor.const J).obj (⊥_ C))
      { pt := ⊥_ C
        ι := { app := fun _ => initial.to _ } }
  inv := initial.to _

@[reassoc (attr := simp)]
theorem ι_colimitConstInitial_hom {J : Type*} [Category* J] {C : Type*} [Category* C] [HasInitial C]
    {j : J} :
    colimit.ι ((CategoryTheory.Functor.const J).obj (⊥_ C)) j ≫ colimitConstInitial.hom =
      initial.to _ := by cat_disch

instance (priority := 100) initial.mono_from [HasInitial C] [InitialMonoClass C] (X : C)
    (f : ⊥_ C ⟶ X) : Mono f :=
  initialIsInitial.mono_from f

/-- To show a category is an `InitialMonoClass` it suffices to show every morphism out of the
initial object is a monomorphism. -/
theorem InitialMonoClass.of_initial [HasInitial C] (h : ∀ X : C, Mono (initial.to X)) :
    InitialMonoClass C :=
  InitialMonoClass.of_isInitial initialIsInitial h

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
@[to_dual
-- TODO: Show this is an isomorphism if and only if `G` preserves initial objects.
/--
The comparison morphism from the initial object in the target category to the image of the initial
object.
-/]
def terminalComparison [HasTerminal C] [HasTerminal D] : G.obj (⊤_ C) ⟶ ⊤_ D :=
  terminal.from _

end Comparison

variable {J : Type u} [Category.{v} J]

@[to_dual]
instance hasLimit_of_domain_hasInitial [HasInitial J] {F : J ⥤ C} : HasLimit F :=
  HasLimit.mk { cone := _, isLimit := limitOfDiagramInitial (initialIsInitial) F }

-- This is reducible to allow usage of lemmas about `conePointUniqueUpToIso`.
/-- For a functor `F : J ⥤ C`, if `J` has an initial object then the image of it is isomorphic
to the limit of `F`. -/
@[to_dual
/-- For a functor `F : J ⥤ C`, if `J` has a terminal object then the image of it is isomorphic
to the colimit of `F`. -/]
abbrev limitOfInitial (F : J ⥤ C) [HasInitial J] : limit F ≅ F.obj (⊥_ J) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramInitial initialIsInitial F)

@[to_dual]
instance hasLimit_of_domain_hasTerminal [HasTerminal J] {F : J ⥤ C}
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : HasLimit F :=
  HasLimit.mk { cone := _, isLimit := limitOfDiagramTerminal (terminalIsTerminal) F }

-- This is reducible to allow usage of lemmas about `conePointUniqueUpToIso`.
/-- For a functor `F : J ⥤ C`, if `J` has a terminal object and all the morphisms in the diagram
are isomorphisms, then the image of the terminal object is isomorphic to the limit of `F`. -/
@[to_dual
/-- For a functor `F : J ⥤ C`, if `J` has an initial object and all the morphisms in the diagram
are isomorphisms, then the image of the initial object is isomorphic to the colimit of `F`. -/]
abbrev limitOfTerminal (F : J ⥤ C) [HasTerminal J] [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] :
    limit F ≅ F.obj (⊤_ J) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramTerminal terminalIsTerminal F)

/-- If `j` is initial in the index category, then the map `limit.π F j` is an isomorphism. -/
@[to_dual isIso_ι_of_isTerminal
/-- If `j` is terminal in the index category, then the map `colimit.ι F j` is an isomorphism. -/]
theorem isIso_π_of_isInitial {j : J} (I : IsInitial j) (F : J ⥤ C) [HasLimit F] :
    IsIso (limit.π F j) :=
  ⟨⟨limit.lift _ (coneOfDiagramInitial I F), ⟨by ext; simp, by simp⟩⟩⟩

@[to_dual isIso_ι_terminal]
instance isIso_π_initial [HasInitial J] (F : J ⥤ C) : IsIso (limit.π F (⊥_ J)) :=
  isIso_π_of_isInitial initialIsInitial F

@[to_dual isIso_ι_of_isInitial]
theorem isIso_π_of_isTerminal {j : J} (I : IsTerminal j) (F : J ⥤ C) [HasLimit F]
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsIso (limit.π F j) :=
  ⟨⟨limit.lift _ (coneOfDiagramTerminal I F), by ext; simp, by simp⟩⟩

@[to_dual isIso_ι_initial]
instance isIso_π_terminal [HasTerminal J] (F : J ⥤ C) [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] :
    IsIso (limit.π F (⊤_ J)) :=
  isIso_π_of_isTerminal terminalIsTerminal F

end

end CategoryTheory.Limits
