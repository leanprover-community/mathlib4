/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison, Johannes Hölzl, Reid Barton
-/
module

public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Tactic.PPWithUniv
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.DatabaseAttributes
public import Mathlib.Tactic.TryThis

/-!
# Categories

Defines a category, as a type class parametrised by the type of objects.

## Notation

Introduces notations in the `CategoryTheory` scope
* `X ⟶ Y` for the morphism spaces (type as `\hom`),
* `𝟙 X` for the identity morphism on `X` (type as `\b1`),
* `f ≫ g` for composition in the 'arrows' convention (type as `\gg`).

Users may like to add `g ⊚ f` for composition in the standard convention, using
```lean
local notation:80 g " ⊚ " f:80 => CategoryTheory.CategoryStruct.comp f g    -- type as \oo
```

-/

@[expose] public section


library_note «category theory universes»
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

library_note «universe output parameters and typeclass caching»
/--
Many classes in Mathlib have universe parameters that do not appear in their
input parameter types. For example:
* `Category.{v} (C : Type u)` — the morphism universe `v` is not determined by `C`
* `HasLimitsOfSize.{v₁, u₁} (C : Type u) [Category.{v} C]` — the shape universes `v₁, u₁`
  are not determined by `C`
* `Small.{w} (α : Type v)` — the target universe `w` is not determined by `α`
  (but `v` is determined by `α`, so `v` *is* an output)
* `Functor.IsContinuous.{t} (F) (J) (K)` — the sheaf type universe `t` is not determined
  by `F`, `J`, `K`
* `UnivLE.{u, v}` — has no input parameters at all

By default (since https://github.com/leanprover/lean4/pull/12286), Lean treats any universe
parameter not occurring in input types as an output parameter, and erases it from typeclass
resolution cache keys. This means that queries differing only in such a universe share a
cache entry — the first result found is reused.

This is correct when the universe truly is determined by the inputs (e.g., `v` in
`Small.{w} (α : Type v)`), but incorrect when the universe is part of the *question*
(e.g., `v` in `Category.{v} C`). Cache collisions cause "stuck at solving universe constraint"
errors or silent misresolution.

The `@[univ_out_params]` attribute
(from https://github.com/leanprover/lean4/pull/12423) overrides the default:
* `@[univ_out_params]` — no universe parameters are output (all kept in cache key)
* `@[univ_out_params v]` — only `v` is output

**Rule of thumb:** if the class is typically used with explicit universe annotations
(e.g., `HasLimitsOfSize.{v₁, u₁} C`) or is marked `@[pp_with_univ]`, its "extra" universe
parameters are likely inputs, not outputs, and the class should be annotated with
`@[univ_out_params]`.
-/

universe v u

namespace CategoryTheory

/-- A preliminary structure on the way to defining a category,
containing the data, but none of the axioms. -/
@[pp_with_univ]
class CategoryStruct (obj : Type u) : Type max u (v + 1) extends Quiver.{v} obj where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g`. -/
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

attribute [trans, to_dual self (reorder := X Z, 6 7)] CategoryStruct.comp
attribute [to_dual self (reorder := comp (X Z, 4 5))] CategoryStruct.mk

initialize_simps_projections CategoryStruct (-toQuiver_Hom, -Hom)

/-- Notation for the identity morphism in a category. -/
scoped notation "𝟙" => CategoryStruct.id  -- type as \b1

/-- Notation for composition of morphisms in a category. -/
scoped infixr:80 " ≫ " => CategoryStruct.comp -- type as \gg

/-- Close the main goal with `sorry` if its type contains `sorry`, and fail otherwise. -/
syntax (name := sorryIfSorry) "sorry_if_sorry" : tactic

open Lean Meta Elab.Tactic in
@[tactic sorryIfSorry, inherit_doc sorryIfSorry] meta def evalSorryIfSorry : Tactic := fun _ => do
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
meta def categoryTheoryDischarger : TacticM Unit := do
  if ← getBoolOption `mathlib.tactic.category.grind then
    if ← getBoolOption `mathlib.tactic.category.log_grind then
      logInfo "Category theory discharger using `grind`."
    evalTacticSeq (← `(tacticSeq|
      intros; (try dsimp only) <;> ((try ext) <;> grind (gen := 20) (ematch := 20))))
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
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the morphism universe `v` would default to
-- being a universe output parameter.
-- See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ, stacks 0014]
class Category (obj : Type u) : Type max u (v + 1) extends CategoryStruct.{v} obj where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f := by cat_disch
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by cat_disch
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    cat_disch

attribute [to_dual existing (attr := simp, grind =) id_comp] Category.comp_id
attribute [simp, grind _=_] Category.assoc

initialize_simps_projections Category (-Hom)

/-- `Category.mk'` is the dual of `Category.mk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing mk]
abbrev Category.mk' {obj : Type u} [CategoryStruct.{v} obj]
    (id_comp : ∀ {X Y : obj} (f : Y ⟶ X), f ≫ 𝟙 X = f)
    (comp_id : ∀ {X Y : obj} (f : Y ⟶ X), 𝟙 Y ≫ f = f)
    (assoc : ∀ {W X Y Z : obj} (f : X ⟶ W) (g : Y ⟶ X) (h : Z ⟶ Y), h ≫ g ≫ f = (h ≫ g) ≫ f) :
    Category.{v, u} obj where

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

@[to_dual existing assoc]
lemma Category.assoc' {W X Y Z : C} (f : X ⟶ W) (g : Y ⟶ X) (h : Z ⟶ Y) :
    h ≫ g ≫ f = (h ≫ g) ≫ f := (Category.assoc h g f).symm

/-- Postcompose an equation between morphisms by another morphism -/
@[to_dual (reorder := w h) whisker_eq
/-- Precompose an equation between morphisms by another morphism -/]
theorem eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z) : f ≫ h = g ≫ h := by rw [w]

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

@[to_dual eq_of_comp_right_eq]
theorem eq_of_comp_left_eq {f g : X ⟶ Y} (w : ∀ {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    f = g := by
  convert w (𝟙 Y) <;> simp

@[to_dual eq_of_comp_right_eq']
theorem eq_of_comp_left_eq' (f g : X ⟶ Y)
    (w : (fun {Z} (h : Y ⟶ Z) => f ≫ h) = fun {Z} (h : Y ⟶ Z) => g ≫ h) : f = g :=
  eq_of_comp_left_eq @fun Z h => by convert congr_fun (congr_fun w Z) h

@[to_dual id_of_comp_right_id]
theorem id_of_comp_left_id (f : X ⟶ X) (w : ∀ {Y : C} (g : X ⟶ Y), f ≫ g = g) : f = 𝟙 X := by
  convert w (𝟙 X)
  simp

@[to_dual (reorder := f g' g) ite_comp]
theorem comp_ite {P : Prop} [Decidable P] {X Y Z : C} (f : X ⟶ Y) (g g' : Y ⟶ Z) :
    (f ≫ if P then g else g') = if P then f ≫ g else f ≫ g' := by aesop

@[to_dual (reorder := f g' g) dite_comp]
theorem comp_dite {P : Prop} [Decidable P]
    {X Y Z : C} (f : X ⟶ Y) (g : P → (Y ⟶ Z)) (g' : ¬P → (Y ⟶ Z)) :
    (f ≫ if h : P then g h else g' h) = if h : P then f ≫ g h else f ≫ g' h := by aesop

/-- A morphism `f` is an epimorphism if it can be cancelled when precomposed:
`f ≫ g = f ≫ h` implies `g = h`. -/
class Epi (f : X ⟶ Y) : Prop where
  /-- A morphism `f` is an epimorphism if it can be cancelled when precomposed. -/
  left_cancellation : ∀ {Z : C} (g h : Y ⟶ Z), f ≫ g = f ≫ h → g = h

/-- A morphism `f` is a monomorphism if it can be cancelled when postcomposed:
`g ≫ f = h ≫ f` implies `g = h`. -/
@[to_dual (attr := stacks 003B) Epi]
class Mono (f : X ⟶ Y) : Prop where
  /-- A morphism `f` is a monomorphism if it can be cancelled when postcomposed. -/
  right_cancellation : ∀ {Z : C} (g h : Z ⟶ X), g ≫ f = h ≫ f → g = h

@[to_dual]
instance (X : C) : Epi (𝟙 X) :=
  ⟨fun g h w => by aesop⟩

@[to_dual]
theorem cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} : f ≫ g = f ≫ h ↔ g = h :=
  ⟨fun p => Epi.left_cancellation g h p, congr_arg _⟩

@[to_dual]
theorem cancel_epi_assoc_iff (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} {W : C} {k l : Z ⟶ W} :
    (f ≫ g) ≫ k = (f ≫ h) ≫ l ↔ g ≫ k = h ≫ l :=
  ⟨fun p => (cancel_epi f).1 <| by simpa using p, fun p => by simp only [Category.assoc, p]⟩

@[to_dual]
theorem cancel_epi_id (f : X ⟶ Y) [Epi f] {h : Y ⟶ Y} : f ≫ h = f ↔ h = 𝟙 Y := by
  convert cancel_epi f
  simp

/-- The composition of epimorphisms is again an epimorphism. This version takes `Epi f` and `Epi g`
as typeclass arguments. For a version taking them as explicit arguments, see `epi_comp'`. -/
@[to_dual (reorder := f g, 7 9)
/-- The composition of monomorphisms is again a monomorphism. This version takes `Mono f` and
`Mono g` as typeclass arguments. For a version taking them as explicit arguments, see `mono_comp'`.
-/]
instance epi_comp (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) [Epi g] : Epi (f ≫ g) :=
  ⟨fun _ _ w => (cancel_epi g).1 <| (cancel_epi_assoc_iff f).1 w⟩

/-- The composition of epimorphisms is again an epimorphism. This version takes `Epi f` and `Epi g`
as explicit arguments. For a version taking them as typeclass arguments, see `epi_comp`. -/
@[to_dual (reorder := hf hg)
/-- The composition of monomorphisms is again a monomorphism. This version takes `Mono f` and
`Mono g` as explicit arguments. For a version taking them as typeclass arguments, see `mono_comp`.
-/]
theorem epi_comp' {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Epi f) (hg : Epi g) : Epi (f ≫ g) :=
  inferInstance

@[to_dual (reorder := f g)]
theorem epi_of_epi (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ g)] : Epi g :=
  ⟨fun _ _ w => (cancel_epi (f ≫ g)).1 <| by simp only [Category.assoc, w]⟩

@[to_dual]
theorem epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g := by
  subst h; exact epi_of_epi f g

/-- `f : X ⟶ Y` is an epimorphism iff for all `Z`, composition of morphisms `Y ⟶ Z` with `f`
is injective. -/
@[to_dual
/-- `f : X ⟶ Y` is a monomorphism iff for all `Z`, composition of morphisms `Z ⟶ X` with `f`
is injective. -/]
lemma epi_iff_forall_injective (f : X ⟶ Y) : Epi f ↔ ∀ Z, (fun g : Y ⟶ Z ↦ f ≫ g).Injective :=
  ⟨fun _ _ _ _ hg ↦ (cancel_epi f).1 hg, fun h ↦ ⟨fun _ _ hg ↦ h _ hg⟩⟩

@[to_dual]
instance [Quiver.IsThin C] (f : X ⟶ Y) : Epi f where
  left_cancellation _ _ _ := Subsingleton.elim _ _

end

section

variable (C : Type u)
variable [Category.{v} C]

universe u'

/-- The category structure on `ULift C` that is induced from the category
structure on `C`. This is not made a global instance because of a diamond
when `C` is a preordered type. -/
@[instance_reducible]
def uliftCategory : Category.{v} (ULift.{u'} C) where
  Hom X Y := X.down ⟶ Y.down
  id X := 𝟙 X.down
  comp f g := f ≫ g

attribute [local instance] uliftCategory in
-- We verify that this previous instance can lift small categories to large categories.
example (D : Type u) [SmallCategory D] : LargeCategory (ULift.{u + 1} D) := by infer_instance

end

end CategoryTheory
