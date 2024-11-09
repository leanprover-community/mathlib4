import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.MorphismProperty.Tactic

open CategoryTheory MorphismProperty

universe u v

variable {n : ℕ} {C} [Category C]

section setup

/-- A toy class to test `addMorphismPropertyInstances`. -/
class ContainsIdentities (W : MorphismProperty C) : Prop where
  /-- for all `X : C`, the identity of `X` satisfies the morphism property -/
  id_mem : ∀ (X : C), W (𝟙 X)

/-- A toy class to test `addMorphismPropertyInstances`. -/
class IsStableUnderComposition (P : MorphismProperty C) : Prop where
  comp_mem {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) : P f → P g → P (f ≫ g)

@[morphismPropertyInstance]
lemma of_isIso (P : MorphismProperty C) [ContainsIdentities P] [RespectsIso P] {X Y : C} (f : X ⟶ Y)
    [IsIso f] : P f :=
  Category.id_comp f ▸ RespectsIso.postcomp P f (𝟙 X) (ContainsIdentities.id_mem X)

@[morphismPropertyInstance]
lemma comp_mem (W : MorphismProperty C) [IsStableUnderComposition W]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g) : W (f ≫ g) :=
  IsStableUnderComposition.comp_mem f g hf hg

end setup

section basic

/-- A toy class to test `addMorphismPropertyInstances` -/
class Foo.Bar (n : ℕ) {X Y : PUnit} (f : X ⟶ Y) : Prop where

instance : IsStableUnderComposition (@Foo.Bar n) := ⟨fun _ _ _ _ ↦ ⟨⟩⟩
instance : ContainsIdentities (@Foo.Bar n) := ⟨fun _ ↦ ⟨⟩⟩

/- This should add the lemma `comp_mem`. -/
addMorphismPropertyInstances @Foo.Bar n

assert_exists Foo.Bar.comp_mem

example {X Y : PUnit.{v+1}} (f g : X ⟶ Y) [Foo.Bar 1 f] [Foo.Bar 1 g] : Foo.Bar 1 (f ≫ g) :=
  inferInstance

instance : RespectsIso (@Foo.Bar n) := @RespectsIso.mk _ _ _ (fun _ _ _ ↦ ⟨⟩) (fun _ _ _ ↦ ⟨⟩)

/- This should add the lemma `of_isIso`. -/
addMorphismPropertyInstances @Foo.Bar.{u} n

assert_exists Foo.Bar.of_isIso

example {X Y : PUnit.{v+1}} (f : X ⟶ Y) [IsIso f] : Foo.Bar 0 f :=
  inferInstance

end basic

section verbose

namespace Foo

/-- A toy class to test `addMorphismPropertyInstances`. -/
class Bar2 {X Y : PUnit} (f : X ⟶ Y) : Prop where

instance : IsStableUnderComposition @Foo.Bar2 := ⟨fun _ _ _ _ ↦ ⟨⟩⟩

/--
info: Successfully added 1 instances out of 2.

Added instance Foo.Bar2.comp_mem:
  ∀ {X Y Z : PUnit.{u_1 + 1}} (f : X ⟶ Y) (g : Y ⟶ Z) [hf : Bar2 f] [hg : Bar2 g], Bar2 (f ≫ g)

Failed to add instance for of_isIso:
Failed to synthesize ContainsIdentities @Bar2.
-/
#guard_msgs in
addMorphismPropertyInstances? @Bar2

/--
error: Failed to add any instances:

Failed to add instance for comp_mem:
(kernel) constant has already been declared 'Foo.Bar2.comp_mem'

Failed to add instance for of_isIso:
Failed to synthesize ContainsIdentities @Bar2.
-/
#guard_msgs in
addMorphismPropertyInstances @Bar2

end Foo

end verbose

section specificCategory

/-- A toy class to test `addMorphismPropertyInstances` -/
class Foo.Bar3 {X Y : C} (f : X ⟶ Y) : Prop where

instance : IsStableUnderComposition (@Foo.Bar3 C _) := ⟨fun _ _ _ _ ↦ ⟨⟩⟩
instance : ContainsIdentities (@Foo.Bar3 C _) := ⟨fun _ ↦ ⟨⟩⟩

@[morphismPropertyInstance]
lemma lemma1 (P : MorphismProperty PUnit.{1}) [ContainsIdentities P] : P (𝟙 default) :=
  ContainsIdentities.id_mem _

@[morphismPropertyInstance]
lemma lemma2 (P : MorphismProperty PUnit) [ContainsIdentities P] : P (𝟙 default) :=
  ContainsIdentities.id_mem _

/- This should unify the hole `?C` with `PUnit` to generate `lemma1` and `lemma2`,
and add `?C` as a free variable to generate `comp_mem`.  -/
addMorphismPropertyInstances @Foo.Bar3 _ _
assert_exists Foo.Bar3.lemma1
assert_exists Foo.Bar3.lemma2
assert_exists Foo.Bar3.comp_mem

end specificCategory

section universeVars

set_option linter.unusedVariables false in
/-- An arrow containing an extra universe variable to test `addMorphismPropertyInstances`. -/
def hom (T : Type*) : Unit.unit ⟶ Unit.unit := 𝟙 _

@[morphismPropertyInstance]
lemma lemma3 (P : MorphismProperty PUnit.{1}) [ContainsIdentities P] (T) : P (hom T) :=
  ContainsIdentities.id_mem _

addMorphismPropertyInstances @Foo.Bar3 _ _
assert_exists Foo.Bar3.lemma3

end universeVars
