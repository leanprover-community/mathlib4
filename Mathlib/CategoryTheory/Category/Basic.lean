/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton
-/
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Tactic.PPWithUniv
import Mathlib.Tactic.Common

#align_import category_theory.category.basic from "leanprover-community/mathlib"@"2efd2423f8d25fa57cf7a179f5d8652ab4d0df44"

/-!
# Categories

Defines a category, as a type class parametrised by the type of objects.

## Notations

Introduces notations in the `CategoryTheory` scope
* `X ⟶ Y` for the morphism spaces (type as `\hom`),
* `𝟙 X` for the identity morphism on `X` (type as `\b1`),
* `f ≫ g` for composition in the 'arrows' convention (type as `\gg`).

Users may like to add `g ⊚ f` for composition in the standard convention, using
```lean
local notation g ` ⊚ `:80 f:80 := category.comp f g    -- type as \oo
```

## Porting note
I am experimenting with using the `aesop` tactic as a replacement for `tidy`.
-/


library_note "CategoryTheory universes"
/--
The typeclass `Category C` describes morphisms associated to objects of type `C : Type u`.

The universe levels of the objects and morphisms are independent, and will often need to be
specified explicitly, as `Category.{v} C`.

Typically any concrete example will either be a `SmallCategory`, where `v = u`,
which can be introduced as
```
universe u
variable {C : Type u} [SmallCategory C]
```
or a `LargeCategory`, where `u = v+1`, which can be introduced as
```
universe u
variable {C : Type (u+1)} [LargeCategory C]
```

In order for the library to handle these cases uniformly,
we generally work with the unconstrained `Category.{v u}`,
for which objects live in `Type u` and morphisms live in `Type v`.

Because the universe parameter `u` for the objects can be inferred from `C`
when we write `Category C`, while the universe parameter `v` for the morphisms
can not be automatically inferred, through the category theory library
we introduce universe parameters with morphism levels listed first,
as in
```
universe v u
```
or
```
universe v₁ v₂ u₁ u₂
```
when multiple independent universes are needed.

This has the effect that we can simply write `Category.{v} C`
(that is, only specifying a single parameter) while `u` will be inferred.

Often, however, it's not even necessary to include the `.{v}`.
(Although it was in earlier versions of Lean.)
If it is omitted a "free" universe will be used.
-/

namespace Std.Tactic.Ext
open Lean Elab Tactic

/-- A wrapper for `ext` that we can pass to `aesop`. -/
def extCore' : TacticM Unit := do
  evalTactic (← `(tactic| ext))

end Std.Tactic.Ext

universe v u

namespace CategoryTheory

/-- A preliminary structure on the way to defining a category,
containing the data, but none of the axioms. -/
@[pp_with_univ]
class CategoryStruct (obj : Type u) extends Quiver.{v + 1} obj : Type max u (v + 1) where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g`. -/
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)
#align category_theory.category_struct CategoryTheory.CategoryStruct

initialize_simps_projections CategoryStruct (-toQuiver_Hom)

/-- Notation for the identity morphism in a category. -/
scoped notation "𝟙" => CategoryStruct.id  -- type as \b1

/-- Notation for composition of morphisms in a category. -/
scoped infixr:80 " ≫ " => CategoryStruct.comp -- type as \gg

/-- Close the main goal with `sorry` if its type contains `sorry`, and fail otherwise. -/
syntax (name := sorryIfSorry) "sorry_if_sorry" : tactic

open Lean Meta Elab.Tactic in
@[tactic sorryIfSorry, inherit_doc sorryIfSorry] def evalSorryIfSorry : Tactic := fun _ => do
  let goalType ← getMainTarget
  if goalType.hasSorry then
    closeMainGoal (← mkSorry goalType true)
  else
    throwError "The goal does not contain `sorry`"

/--
A thin wrapper for `aesop` which adds the `CategoryTheory` rule set and
allows `aesop` to look through semireducible definitions when calling `intros`.
It also turns on `zetaDelta` in the `simp` config, allowing `aesop_cat` to unfold any `let`s.
This tactic fails when it is unable to solve the goal, making it suitable for
use in auto-params.
-/
macro (name := aesop_cat) "aesop_cat" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  first | sorry_if_sorry |
  aesop $c* (config := { introsTransparency? := some .default, terminal := true })
            (simp_config := { decide := true, zetaDelta := true })
            (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))

/--
We also use `aesop_cat?` to pass along a `Try this` suggestion when using `aesop_cat`
-/
macro (name := aesop_cat?) "aesop_cat?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  first | sorry_if_sorry |
  aesop? $c* (config := { introsTransparency? := some .default, terminal := true })
             (simp_config := { decide := true, zetaDelta := true })
             (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))
/--
A variant of `aesop_cat` which does not fail when it is unable to solve the
goal. Use this only for exploration! Nonterminal `aesop` is even worse than
nonterminal `simp`.
-/
macro (name := aesop_cat_nonterminal) "aesop_cat_nonterminal" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c* (config := { introsTransparency? := some .default, warnOnNonterminal := false })
              (simp_config := { decide := true, zetaDelta := true })
              (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))


-- We turn on `ext` inside `aesop_cat`.
attribute [aesop safe tactic (rule_sets := [CategoryTheory])] Std.Tactic.Ext.extCore'

-- We turn on the mathlib version of `rfl` inside `aesop_cat`.
attribute [aesop safe tactic (rule_sets := [CategoryTheory])] Mathlib.Tactic.rflTac

-- Porting note:
-- Workaround for issue discussed at https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Failure.20of.20TC.20search.20in.20.60simp.60.20with.20.60etaExperiment.60.2E
-- now that etaExperiment is always on.
attribute [aesop safe (rule_sets := [CategoryTheory])] Subsingleton.elim

/-- The typeclass `Category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `Category.{v} C`. (See also `LargeCategory` and `SmallCategory`.)

See <https://stacks.math.columbia.edu/tag/0014>.
-/
@[pp_with_univ]
class Category (obj : Type u) extends CategoryStruct.{v} obj : Type max u (v + 1) where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f := by aesop_cat
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by aesop_cat
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    aesop_cat
#align category_theory.category CategoryTheory.Category
#align category_theory.category.assoc CategoryTheory.Category.assoc
#align category_theory.category.comp_id CategoryTheory.Category.comp_id
#align category_theory.category.id_comp CategoryTheory.Category.id_comp

attribute [simp] Category.id_comp Category.comp_id Category.assoc
attribute [trans] CategoryStruct.comp

example {C} [Category C] {X Y : C} (f : X ⟶ Y) : 𝟙 X ≫ f = f := by simp
example {C} [Category C] {X Y : C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by simp

/-- A `LargeCategory` has objects in one universe level higher than the universe level of
the morphisms. It is useful for examples such as the category of types, or the category
of groups, etc.
-/
abbrev LargeCategory (C : Type (u + 1)) : Type (u + 1) := Category.{u} C
#align category_theory.large_category CategoryTheory.LargeCategory

/-- A `SmallCategory` has objects and morphisms in the same universe level.
-/
abbrev SmallCategory (C : Type u) : Type (u + 1) := Category.{u} C
#align category_theory.small_category CategoryTheory.SmallCategory

section

variable {C : Type u} [Category.{v} C] {X Y Z : C}

initialize_simps_projections Category (-Hom)

/-- postcompose an equation between morphisms by another morphism -/
theorem eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z) : f ≫ h = g ≫ h := by rw [w]
#align category_theory.eq_whisker CategoryTheory.eq_whisker

/-- precompose an equation between morphisms by another morphism -/
theorem whisker_eq (f : X ⟶ Y) {g h : Y ⟶ Z} (w : g = h) : f ≫ g = f ≫ h := by rw [w]
#align category_theory.whisker_eq CategoryTheory.whisker_eq

/--
Notation for whiskering an equation by a morphism (on the right).
If `f g : X ⟶ Y` and `w : f = g` and `h : Y ⟶ Z`, then `w =≫ h : f ≫ h = g ≫ h`.
-/
scoped infixr:80 " =≫ " => eq_whisker

/--
Notation for whiskering an equation by a morphism (on the left).
If `g h : Y ⟶ Z` and `w : g = h` and `h : X ⟶ Y`, then `f ≫= w : f ≫ g = f ≫ h`.
-/
scoped infixr:80 " ≫= " => whisker_eq

theorem eq_of_comp_left_eq {f g : X ⟶ Y} (w : ∀ {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    f = g := by
  convert w (𝟙 Y) <;> simp
#align category_theory.eq_of_comp_left_eq CategoryTheory.eq_of_comp_left_eq

theorem eq_of_comp_right_eq {f g : Y ⟶ Z} (w : ∀ {X : C} (h : X ⟶ Y), h ≫ f = h ≫ g) :
    f = g := by
  convert w (𝟙 Y) <;> simp
#align category_theory.eq_of_comp_right_eq CategoryTheory.eq_of_comp_right_eq

theorem eq_of_comp_left_eq' (f g : X ⟶ Y)
    (w : (fun {Z} (h : Y ⟶ Z) => f ≫ h) = fun {Z} (h : Y ⟶ Z) => g ≫ h) : f = g :=
  eq_of_comp_left_eq @fun Z h => by convert congr_fun (congr_fun w Z) h
#align category_theory.eq_of_comp_left_eq' CategoryTheory.eq_of_comp_left_eq'

theorem eq_of_comp_right_eq' (f g : Y ⟶ Z)
    (w : (fun {X} (h : X ⟶ Y) => h ≫ f) = fun {X} (h : X ⟶ Y) => h ≫ g) : f = g :=
  eq_of_comp_right_eq @fun X h => by convert congr_fun (congr_fun w X) h
#align category_theory.eq_of_comp_right_eq' CategoryTheory.eq_of_comp_right_eq'

theorem id_of_comp_left_id (f : X ⟶ X) (w : ∀ {Y : C} (g : X ⟶ Y), f ≫ g = g) : f = 𝟙 X := by
  convert w (𝟙 X)
  simp
#align category_theory.id_of_comp_left_id CategoryTheory.id_of_comp_left_id

theorem id_of_comp_right_id (f : X ⟶ X) (w : ∀ {Y : C} (g : Y ⟶ X), g ≫ f = g) : f = 𝟙 X := by
  convert w (𝟙 X)
  simp
#align category_theory.id_of_comp_right_id CategoryTheory.id_of_comp_right_id

theorem comp_ite {P : Prop} [Decidable P] {X Y Z : C} (f : X ⟶ Y) (g g' : Y ⟶ Z) :
    (f ≫ if P then g else g') = if P then f ≫ g else f ≫ g' := by aesop
#align category_theory.comp_ite CategoryTheory.comp_ite

theorem ite_comp {P : Prop} [Decidable P] {X Y Z : C} (f f' : X ⟶ Y) (g : Y ⟶ Z) :
    (if P then f else f') ≫ g = if P then f ≫ g else f' ≫ g := by aesop
#align category_theory.ite_comp CategoryTheory.ite_comp

theorem comp_dite {P : Prop} [Decidable P]
    {X Y Z : C} (f : X ⟶ Y) (g : P → (Y ⟶ Z)) (g' : ¬P → (Y ⟶ Z)) :
    (f ≫ if h : P then g h else g' h) = if h : P then f ≫ g h else f ≫ g' h := by aesop
#align category_theory.comp_dite CategoryTheory.comp_dite

theorem dite_comp {P : Prop} [Decidable P]
    {X Y Z : C} (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y)) (g : Y ⟶ Z) :
    (if h : P then f h else f' h) ≫ g = if h : P then f h ≫ g else f' h ≫ g := by aesop
#align category_theory.dite_comp CategoryTheory.dite_comp

/-- A morphism `f` is an epimorphism if it can be cancelled when precomposed:
`f ≫ g = f ≫ h` implies `g = h`.

See <https://stacks.math.columbia.edu/tag/003B>.
-/
class Epi (f : X ⟶ Y) : Prop where
  /-- A morphism `f` is an epimorphism if it can be cancelled when precomposed. -/
  left_cancellation : ∀ {Z : C} (g h : Y ⟶ Z), f ≫ g = f ≫ h → g = h
#align category_theory.epi CategoryTheory.Epi

/-- A morphism `f` is a monomorphism if it can be cancelled when postcomposed:
`g ≫ f = h ≫ f` implies `g = h`.

See <https://stacks.math.columbia.edu/tag/003B>.
-/
class Mono (f : X ⟶ Y) : Prop where
  /-- A morphism `f` is a monomorphism if it can be cancelled when postcomposed. -/
  right_cancellation : ∀ {Z : C} (g h : Z ⟶ X), g ≫ f = h ≫ f → g = h
#align category_theory.mono CategoryTheory.Mono

instance (X : C) : Epi (𝟙 X) :=
  ⟨fun g h w => by aesop⟩

instance (X : C) : Mono (𝟙 X) :=
  ⟨fun g h w => by aesop⟩

theorem cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} : f ≫ g = f ≫ h ↔ g = h :=
  ⟨fun p => Epi.left_cancellation g h p, congr_arg _⟩
#align category_theory.cancel_epi CategoryTheory.cancel_epi

theorem cancel_mono (f : X ⟶ Y) [Mono f] {g h : Z ⟶ X} : g ≫ f = h ≫ f ↔ g = h :=
  -- Porting note: in Lean 3 we could just write `congr_arg _` here.
  ⟨fun p => Mono.right_cancellation g h p, congr_arg (fun k => k ≫ f)⟩
#align category_theory.cancel_mono CategoryTheory.cancel_mono

theorem cancel_epi_id (f : X ⟶ Y) [Epi f] {h : Y ⟶ Y} : f ≫ h = f ↔ h = 𝟙 Y := by
  convert cancel_epi f
  simp
#align category_theory.cancel_epi_id CategoryTheory.cancel_epi_id

theorem cancel_mono_id (f : X ⟶ Y) [Mono f] {g : X ⟶ X} : g ≫ f = f ↔ g = 𝟙 X := by
  convert cancel_mono f
  simp
#align category_theory.cancel_mono_id CategoryTheory.cancel_mono_id

theorem epi_comp {X Y Z : C} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) [Epi g] : Epi (f ≫ g) := by
  constructor
  intro Z a b w
  apply (cancel_epi g).1
  apply (cancel_epi f).1
  simpa using w
#align category_theory.epi_comp CategoryTheory.epi_comp

theorem mono_comp {X Y Z : C} (f : X ⟶ Y) [Mono f] (g : Y ⟶ Z) [Mono g] : Mono (f ≫ g) := by
  constructor
  intro Z a b w
  apply (cancel_mono f).1
  apply (cancel_mono g).1
  simpa using w
#align category_theory.mono_comp CategoryTheory.mono_comp

theorem mono_of_mono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono (f ≫ g)] : Mono f := by
  constructor
  intro Z a b w
  replace w := congr_arg (fun k => k ≫ g) w
  dsimp at w
  rw [Category.assoc, Category.assoc] at w
  exact (cancel_mono _).1 w
#align category_theory.mono_of_mono CategoryTheory.mono_of_mono

theorem mono_of_mono_fac {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [Mono h]
    (w : f ≫ g = h) : Mono f := by
  subst h
  exact mono_of_mono f g
#align category_theory.mono_of_mono_fac CategoryTheory.mono_of_mono_fac

theorem epi_of_epi {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ g)] : Epi g := by
  constructor
  intro Z a b w
  replace w := congr_arg (fun k => f ≫ k) w
  dsimp at w
  rw [← Category.assoc, ← Category.assoc] at w
  exact (cancel_epi _).1 w
#align category_theory.epi_of_epi CategoryTheory.epi_of_epi

theorem epi_of_epi_fac {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [Epi h]
    (w : f ≫ g = h) : Epi g := by
  subst h; exact epi_of_epi f g
#align category_theory.epi_of_epi_fac CategoryTheory.epi_of_epi_fac

end

section

variable (C : Type u)
variable [Category.{v} C]

universe u'

instance uliftCategory : Category.{v} (ULift.{u'} C) where
  Hom X Y := X.down ⟶ Y.down
  id X := 𝟙 X.down
  comp f g := f ≫ g
#align category_theory.ulift_category CategoryTheory.uliftCategory

-- We verify that this previous instance can lift small categories to large categories.
example (D : Type u) [SmallCategory D] : LargeCategory (ULift.{u + 1} D) := by infer_instance

end

end CategoryTheory

-- Porting note: We hope that this will become less necessary,
-- as in Lean4 `simp` will automatically enter "`dsimp` mode" when needed with dependent arguments.
-- Optimistically, we will eventually remove this library note.
library_note "dsimp, simp"
/-- Many proofs in the category theory library use the `dsimp, simp` pattern,
which typically isn't necessary elsewhere.

One would usually hope that the same effect could be achieved simply with `simp`.

The essential issue is that composition of morphisms involves dependent types.
When you have a chain of morphisms being composed, say `f : X ⟶ Y` and `g : Y ⟶ Z`,
then `simp` can operate successfully on the morphisms
(e.g. if `f` is the identity it can strip that off).

However if we have an equality of objects, say `Y = Y'`,
then `simp` can't operate because it would break the typing of the composition operations.
We rarely have interesting equalities of objects
(because that would be "evil" --- anything interesting should be expressed as an isomorphism
and tracked explicitly),
except of course that we have plenty of definitional equalities of objects.

`dsimp` can apply these safely, even inside a composition.

After `dsimp` has cleared up the object level, `simp` can resume work on the morphism level ---
but without the `dsimp` step, because `simp` looks at expressions syntactically,
the relevant lemmas might not fire.

There's no bound on how many times you potentially could have to switch back and forth,
if the `simp` introduced new objects we again need to `dsimp`.
In practice this does occur, but only rarely, because `simp` tends to shorten chains of compositions
(i.e. not introduce new objects at all).
-/
