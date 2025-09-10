/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison, Johannes Hölzl, Reid Barton
-/
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Tactic.PPWithUniv
import Mathlib.Tactic.Common
import Mathlib.Tactic.StacksAttribute
import Mathlib.Tactic.TryThis

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
local notation:80 g " ⊚ " f:80 => CategoryTheory.CategoryStruct.comp f g    -- type as \oo
```

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
cannot be automatically inferred, through the category theory library
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

universe v u

namespace CategoryTheory

/-- A preliminary structure on the way to defining a category,
containing the data, but none of the axioms. -/
@[pp_with_univ]
class CategoryStruct (obj : Type u) : Type max u (v + 1) extends Quiver.{v + 1} obj where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g`. -/
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

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
    closeMainGoal `sorry_if_sorry (← mkSorry goalType true)
  else
    throwError "The goal does not contain `sorry`"

/--
`rfl_cat` is a macro for `intros; rfl` which is attempted in `aesop_cat` before
doing the more expensive `aesop` tactic.

This gives a speedup because `simp` (called by `aesop`) can be very slow.
https://github.com/leanprover-community/mathlib4/pull/25475 contains measurements from June 2025.

Implementation notes:
* `refine id ?_`:
  In some cases it is important that the type of the proof matches the expected type exactly.
  e.g. if the goal is `2 = 1 + 1`, the `rfl` tactic will give a proof of type `2 = 2`.
  Starting a proof with `refine id ?_` is a trick to make sure that the proof has exactly
  the expected type, in this case `2 = 1 + 1`. See also
  https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/changing.20a.20proof.20can.20break.20a.20later.20proof
* `apply_rfl`:
  `rfl` is a macro that attempts both `eq_refl` and `apply_rfl`. Since `apply_rfl`
  subsumes `eq_refl`, we can use `apply_rfl` instead. This fails twice as fast as `rfl`.

-/
macro (name := rfl_cat) "rfl_cat" : tactic => do `(tactic| (refine id ?_; intros; apply_rfl))

/--
A thin wrapper for `aesop` which adds the `CategoryTheory` rule set and
allows `aesop` to look through semireducible definitions when calling `intros`.
This tactic fails when it is unable to solve the goal, making it suitable for
use in auto-params.
-/
macro (name := aesop_cat) "aesop_cat" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  first | sorry_if_sorry | rfl_cat |
  aesop $c* (config := { introsTransparency? := some .default, terminal := true })
            (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))

/--
We also use `aesop_cat?` to pass along a `Try this` suggestion when using `aesop_cat`
-/
macro (name := aesop_cat?) "aesop_cat?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  first | sorry_if_sorry | try_this rfl_cat |
  aesop? $c* (config := { introsTransparency? := some .default, terminal := true })
             (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))
/--
A variant of `aesop_cat` which does not fail when it is unable to solve the
goal. Use this only for exploration! Nonterminal `aesop` is even worse than
nonterminal `simp`.
-/
macro (name := aesop_cat_nonterminal) "aesop_cat_nonterminal" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c* (config := { introsTransparency? := some .default, warnOnNonterminal := false })
              (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))

attribute [aesop safe (rule_sets := [CategoryTheory])] Subsingleton.elim

open Lean Elab Tactic in
/-- A tactic for discharging easy category theory goals, widely used as an autoparameter.
Currently this defaults to the `aesop_cat` wrapper around `aesop`, but by setting
the option `mathlib.tactic.category.grind` to `true`, it will use the `grind` tactic instead.
-/
def categoryTheoryDischarger : TacticM Unit := do
  if ← getBoolOption `mathlib.tactic.category.grind then
    if ← getBoolOption `mathlib.tactic.category.log_grind then
      logInfo "Category theory discharger using `grind`."
    evalTacticSeq (← `(tacticSeq|
      intros; (try dsimp only) <;> ((try ext); grind (gen := 20) (ematch := 20))))
  else
    if ← getBoolOption `mathlib.tactic.category.log_aesop then
      logInfo "Category theory discharger using `aesop`."
    evalTactic (← `(tactic| aesop_cat))

@[inherit_doc categoryTheoryDischarger]
elab (name := cat_disch) "cat_disch" : tactic =>
  categoryTheoryDischarger

set_option mathlib.tactic.category.grind true

/-- The typeclass `Category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `Category.{v} C`. (See also `LargeCategory` and `SmallCategory`.) -/
@[pp_with_univ, stacks 0014]
class Category (obj : Type u) : Type max u (v + 1) extends CategoryStruct.{v} obj where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f := by cat_disch
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by cat_disch
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    cat_disch

attribute [simp] Category.id_comp Category.comp_id Category.assoc
attribute [trans] CategoryStruct.comp

attribute [grind =] Category.id_comp Category.comp_id
attribute [grind _=_] Category.assoc

example {C} [Category C] {X Y : C} (f : X ⟶ Y) : 𝟙 X ≫ f = f := by simp
example {C} [Category C] {X Y : C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by simp

/-- A `LargeCategory` has objects in one universe level higher than the universe level of
the morphisms. It is useful for examples such as the category of types, or the category
of groups, etc.
-/
abbrev LargeCategory (C : Type (u + 1)) : Type (u + 1) := Category.{u} C

/-- A `SmallCategory` has objects and morphisms in the same universe level.
-/
abbrev SmallCategory (C : Type u) : Type (u + 1) := Category.{u} C

section

variable {C : Type u} [Category.{v} C] {X Y Z : C}

initialize_simps_projections Category (-Hom)

/-- postcompose an equation between morphisms by another morphism -/
theorem eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z) : f ≫ h = g ≫ h := by rw [w]

/-- precompose an equation between morphisms by another morphism -/
theorem whisker_eq (f : X ⟶ Y) {g h : Y ⟶ Z} (w : g = h) : f ≫ g = f ≫ h := by rw [w]

/--
Notation for whiskering an equation by a morphism (on the right).
If `f g : X ⟶ Y` and `w : f = g` and `h : Y ⟶ Z`, then `w =≫ h : f ≫ h = g ≫ h`.
-/
scoped infixr:80 " =≫ " => eq_whisker

/--
Notation for whiskering an equation by a morphism (on the left).
If `g h : Y ⟶ Z` and `w : g = h` and `f : X ⟶ Y`, then `f ≫= w : f ≫ g = f ≫ h`.
-/
scoped infixr:80 " ≫= " => whisker_eq

theorem eq_of_comp_left_eq {f g : X ⟶ Y} (w : ∀ {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    f = g := by
  convert w (𝟙 Y) <;> simp

theorem eq_of_comp_right_eq {f g : Y ⟶ Z} (w : ∀ {X : C} (h : X ⟶ Y), h ≫ f = h ≫ g) :
    f = g := by
  convert w (𝟙 Y) <;> simp

theorem eq_of_comp_left_eq' (f g : X ⟶ Y)
    (w : (fun {Z} (h : Y ⟶ Z) => f ≫ h) = fun {Z} (h : Y ⟶ Z) => g ≫ h) : f = g :=
  eq_of_comp_left_eq @fun Z h => by convert congr_fun (congr_fun w Z) h

theorem eq_of_comp_right_eq' (f g : Y ⟶ Z)
    (w : (fun {X} (h : X ⟶ Y) => h ≫ f) = fun {X} (h : X ⟶ Y) => h ≫ g) : f = g :=
  eq_of_comp_right_eq @fun X h => by convert congr_fun (congr_fun w X) h

theorem id_of_comp_left_id (f : X ⟶ X) (w : ∀ {Y : C} (g : X ⟶ Y), f ≫ g = g) : f = 𝟙 X := by
  convert w (𝟙 X)
  simp

theorem id_of_comp_right_id (f : X ⟶ X) (w : ∀ {Y : C} (g : Y ⟶ X), g ≫ f = g) : f = 𝟙 X := by
  convert w (𝟙 X)
  simp

theorem comp_ite {P : Prop} [Decidable P] {X Y Z : C} (f : X ⟶ Y) (g g' : Y ⟶ Z) :
    (f ≫ if P then g else g') = if P then f ≫ g else f ≫ g' := by aesop

theorem ite_comp {P : Prop} [Decidable P] {X Y Z : C} (f f' : X ⟶ Y) (g : Y ⟶ Z) :
    (if P then f else f') ≫ g = if P then f ≫ g else f' ≫ g := by aesop

theorem comp_dite {P : Prop} [Decidable P]
    {X Y Z : C} (f : X ⟶ Y) (g : P → (Y ⟶ Z)) (g' : ¬P → (Y ⟶ Z)) :
    (f ≫ if h : P then g h else g' h) = if h : P then f ≫ g h else f ≫ g' h := by aesop

theorem dite_comp {P : Prop} [Decidable P]
    {X Y Z : C} (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y)) (g : Y ⟶ Z) :
    (if h : P then f h else f' h) ≫ g = if h : P then f h ≫ g else f' h ≫ g := by aesop

/-- A morphism `f` is an epimorphism if it can be cancelled when precomposed:
`f ≫ g = f ≫ h` implies `g = h`. -/
@[stacks 003B]
class Epi (f : X ⟶ Y) : Prop where
  /-- A morphism `f` is an epimorphism if it can be cancelled when precomposed. -/
  left_cancellation : ∀ {Z : C} (g h : Y ⟶ Z), f ≫ g = f ≫ h → g = h

/-- A morphism `f` is a monomorphism if it can be cancelled when postcomposed:
`g ≫ f = h ≫ f` implies `g = h`. -/
@[stacks 003B]
class Mono (f : X ⟶ Y) : Prop where
  /-- A morphism `f` is a monomorphism if it can be cancelled when postcomposed. -/
  right_cancellation : ∀ {Z : C} (g h : Z ⟶ X), g ≫ f = h ≫ f → g = h

instance (X : C) : Epi (𝟙 X) :=
  ⟨fun g h w => by aesop⟩

instance (X : C) : Mono (𝟙 X) :=
  ⟨fun g h w => by aesop⟩

theorem cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} : f ≫ g = f ≫ h ↔ g = h :=
  ⟨fun p => Epi.left_cancellation g h p, congr_arg _⟩

theorem cancel_epi_assoc_iff (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} {W : C} {k l : Z ⟶ W} :
    (f ≫ g) ≫ k = (f ≫ h) ≫ l ↔ g ≫ k = h ≫ l :=
  ⟨fun p => (cancel_epi f).1 <| by simpa using p, fun p => by simp only [Category.assoc, p]⟩

theorem cancel_mono (f : X ⟶ Y) [Mono f] {g h : Z ⟶ X} : g ≫ f = h ≫ f ↔ g = h :=
  -- Porting note: in Lean 3 we could just write `congr_arg _` here.
  ⟨fun p => Mono.right_cancellation g h p, congr_arg (fun k => k ≫ f)⟩

theorem cancel_mono_assoc_iff (f : X ⟶ Y) [Mono f] {g h : Z ⟶ X} {W : C} {k l : W ⟶ Z} :
    k ≫ (g ≫ f) = l ≫ (h ≫ f) ↔ k ≫ g = l ≫ h :=
  ⟨fun p => (cancel_mono f).1 <| by simpa using p, fun p => by simp only [← Category.assoc, p]⟩

theorem cancel_epi_id (f : X ⟶ Y) [Epi f] {h : Y ⟶ Y} : f ≫ h = f ↔ h = 𝟙 Y := by
  convert cancel_epi f
  simp

theorem cancel_mono_id (f : X ⟶ Y) [Mono f] {g : X ⟶ X} : g ≫ f = f ↔ g = 𝟙 X := by
  convert cancel_mono f
  simp

/-- The composition of epimorphisms is again an epimorphism. This version takes `Epi f` and `Epi g`
as typeclass arguments. For a version taking them as explicit arguments, see `epi_comp'`. -/
instance epi_comp {X Y Z : C} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) [Epi g] : Epi (f ≫ g) :=
  ⟨fun _ _ w => (cancel_epi g).1 <| (cancel_epi_assoc_iff f).1 w⟩

/-- The composition of epimorphisms is again an epimorphism. This version takes `Epi f` and `Epi g`
as explicit arguments. For a version taking them as typeclass arguments, see `epi_comp`. -/
theorem epi_comp' {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Epi f) (hg : Epi g) : Epi (f ≫ g) :=
  inferInstance

/-- The composition of monomorphisms is again a monomorphism. This version takes `Mono f` and
`Mono g` as typeclass arguments. For a version taking them as explicit arguments, see `mono_comp'`.
-/
instance mono_comp {X Y Z : C} (f : X ⟶ Y) [Mono f] (g : Y ⟶ Z) [Mono g] : Mono (f ≫ g) :=
  ⟨fun _ _ w => (cancel_mono f).1 <| (cancel_mono_assoc_iff g).1 w⟩

/-- The composition of monomorphisms is again a monomorphism. This version takes `Mono f` and
`Mono g` as explicit arguments. For a version taking them as typeclass arguments, see `mono_comp`.
-/
theorem mono_comp' {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Mono f) (hg : Mono g) :
    Mono (f ≫ g) :=
  inferInstance

theorem mono_of_mono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono (f ≫ g)] : Mono f :=
  ⟨fun _ _ w => (cancel_mono (f ≫ g)).1 <| by simp only [← Category.assoc, w]⟩

theorem mono_of_mono_fac {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [Mono h]
    (w : f ≫ g = h) : Mono f := by
  subst h; exact mono_of_mono f g

theorem epi_of_epi {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ g)] : Epi g :=
  ⟨fun _ _ w => (cancel_epi (f ≫ g)).1 <| by simp only [Category.assoc, w]⟩

theorem epi_of_epi_fac {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [Epi h]
    (w : f ≫ g = h) : Epi g := by
  subst h; exact epi_of_epi f g

/-- `f : X ⟶ Y` is a monomorphism iff for all `Z`, composition of morphisms `Z ⟶ X` with `f`
is injective. -/
lemma mono_iff_forall_injective {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ ∀ Z, (fun g : Z ⟶ X ↦ g ≫ f).Injective :=
  ⟨fun _ _ _ _ hg ↦ (cancel_mono f).1 hg, fun h ↦ ⟨fun _ _ hg ↦ h _ hg⟩⟩

/-- `f : X ⟶ Y` is an epimorphism iff for all `Z`, composition of morphisms `Y ⟶ Z` with `f`
is injective. -/
lemma epi_iff_forall_injective {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ ∀ Z, (fun g : Y ⟶ Z ↦ f ≫ g).Injective :=
  ⟨fun _ _ _ _ hg ↦ (cancel_epi f).1 hg, fun h ↦ ⟨fun _ _ hg ↦ h _ hg⟩⟩

section

variable [Quiver.IsThin C] (f : X ⟶ Y)

instance : Mono f where
  right_cancellation _ _ _ := Subsingleton.elim _ _

instance : Epi f where
  left_cancellation _ _ _ := Subsingleton.elim _ _

end

end

section

variable (C : Type u)
variable [Category.{v} C]

universe u'

/-- The category structure on `ULift C` that is induced from the category
structure on `C`. This is not made a global instance because of a diamond
when `C` is a preordered type. -/
def uliftCategory : Category.{v} (ULift.{u'} C) where
  Hom X Y := X.down ⟶ Y.down
  id X := 𝟙 X.down
  comp f g := f ≫ g

attribute [local instance] uliftCategory in
-- We verify that this previous instance can lift small categories to large categories.
example (D : Type u) [SmallCategory D] : LargeCategory (ULift.{u + 1} D) := by infer_instance

end

end CategoryTheory
