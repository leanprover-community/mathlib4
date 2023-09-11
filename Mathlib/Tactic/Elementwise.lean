/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Kyle Miller
-/

import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Util.AddRelatedDecl

/-!
# Tools to reformulate category-theoretic lemmas in concrete categories

## The `elementwise` attribute

The `elementwise` attribute generates lemmas for concrete categories from lemmas
that equate morphisms in a category.

A sort of inverse to this for the `Type _` category is the `@[higher_order]` attribute.

For more details, see the documentation attached to the `syntax` declaration.

## Main definitions

- The `@[elementwise]` attribute.

- The ``elementwise_of% h` term elaborator.

## Implementation

This closely follows the implementation of the `@[reassoc]` attribute, due to Simon Hudon and
reimplemented by Scott Morrison in Lean 4.
-/

open Lean Meta Elab Tactic
open Mathlib.Tactic

namespace Tactic.Elementwise
open CategoryTheory

section theorems

theorem forget_hom_Type (α β : Type u) (f : α ⟶ β) : (forget (Type u)).map f = f := rfl

theorem forall_congr_forget_Type (α : Type u) (p : α → Prop) :
  (∀ (x : ConcreteCategory.Forget.obj α), p x) ↔ ∀ (x : α), p x := Iff.rfl

attribute [local instance] ConcreteCategory.hasCoeToFun ConcreteCategory.hasCoeToSort

theorem hom_elementwise [Category C] [ConcreteCategory C]
    {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x := by rw [h]

end theorems

/-- List of simp lemmas to apply to the elementwise theorem. -/
def elementwiseThms : List Name :=
  [``CategoryTheory.coe_id, ``CategoryTheory.coe_comp, ``CategoryTheory.comp_apply,
    ``CategoryTheory.id_apply,
    -- further simplifications if the category is `Type`
    ``forget_hom_Type, ``forall_congr_forget_Type]

/--
Given an equation `f = g` between morphisms `X ⟶ Y` in a category `C`
(possibly after a `∀` binder), produce the equation `∀ (x : X), f x = g x` or
`∀ [ConcreteCategory C] (x : X), f x = g x` as needed (after the `∀` binder), but
with compositions fully right associated and identities removed.

Returns the proof of the new theorem along with (optionally) a new level metavariable
for the first universe parameter to `ConcreteCategory`.
-/
def elementwiseExpr (type pf : Expr) : MetaM (Expr × Option Level) := do
  let type := (← instantiateMVars type).cleanupAnnotations
  forallTelescope type fun fvars type' => do
    mkHomElementwise type' (mkAppN pf fvars) fun eqPf instConcr? => do
      let eqPf' ← simpType (simpOnlyNames elementwiseThms) eqPf
      if let some (w, instConcr) := instConcr? then
        return (← Meta.mkLambdaFVars (fvars.push instConcr) eqPf', w)
      else
        return (← Meta.mkLambdaFVars fvars eqPf', none)
where
  /-- Given an equality, extract a `Category` instance from it or raise an error.
  Returns the name of the category and its instance. -/
  extractCatInstance (eqTy : Expr) : MetaM (Expr × Expr) := do
    let some (α, _, _) := eqTy.cleanupAnnotations.eq? | failure
    let (``Quiver.Hom, #[_, instQuiv, _, _]) := α.getAppFnArgs | failure
    let (``CategoryTheory.CategoryStruct.toQuiver, #[_, instCS]) := instQuiv.getAppFnArgs | failure
    let (``CategoryTheory.Category.toCategoryStruct, #[C, instC]) := instCS.getAppFnArgs | failure
    return (C, instC)
  mkHomElementwise {α} (eqTy eqPf : Expr) (k : Expr → Option (Level × Expr) → MetaM α) :
      MetaM α := do
    let (C, instC) ← try extractCatInstance eqTy catch _ =>
      throwError "elementwise expects equality of morphisms in a category"
    try
      -- First try being optimistic that there is already a ConcreteCategory instance.
      let eqPf' ← mkAppM ``hom_elementwise #[eqPf]
      k eqPf' none
    catch _ =>
      -- That failed, so we need to introduce the instance, which takes creating
      -- a fresh universe level for `ConcreteCategory`'s forgetful functor.
      let .app (.const ``Category [v, u]) _ ← inferType instC
        | throwError "internal error in elementwise"
      let w ← mkFreshLevelMVar
      let cty : Expr := mkApp2 (.const ``ConcreteCategory [w, v, u]) C instC
      withLocalDecl `inst .instImplicit cty fun cfvar => do
        let eqPf' ← mkAppM ``hom_elementwise #[eqPf]
        k eqPf' (some (w, cfvar))

/-- Gives a name based on `baseName` that's not already in the list. -/
private partial def mkUnusedName (names : List Name) (baseName : Name) : Name :=
  if not (names.contains baseName) then
    baseName
  else
    let rec loop (i : Nat := 0) : Name :=
      let w := Name.appendIndexAfter baseName i
      if names.contains w then
        loop (i + 1)
      else
        w
    loop 1

/-- The `elementwise` attribute can be added to a lemma proving an equation of morphisms, and it
creates a new lemma for a `ConcreteCategory` giving an equation with those morphisms applied
to some value.

For example:

```lean
@[elementwise]
lemma some_lemma {C : Type _} [Category C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : ...) : f ≫ g = h := ...
```

produces

```lean
lemma some_lemma_apply {C : Type _} [Category C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : ...)
    [ConcreteCategory C] (x : X) : g (f x) = h x := ...
```

Here `X` is being coerced to a type via `CategoryTheory.ConcreteCategory.hasCoeToSort` and
`f`, `g`, and `h` are being coerced to functions via `CategoryTheory.ConcreteCategory.hasCoeToFun`.
Further, we simplify the type using `CategoryTheory.coe_id : ((𝟙 X) : X → X) x = x` and
`CategoryTheory.coe_comp : (f ≫ g) x = g (f x)`,
replacing morphism composition with function composition.

The `[ConcreteCategory C]` argument will be omitted if it is possible to synthesize an instance.

The name of the produced lemma can be specified with `@[elementwise other_lemma_name]`.
If `simp` is added first, the generated lemma will also have the `simp` attribute.
 -/
syntax (name := elementwise) "elementwise" ("(" &"attr" ":=" Parser.Term.attrInstance,* ")")? : attr

initialize registerBuiltinAttribute {
  name := `elementwise
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| elementwise $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`elementwise` can only be used as a global attribute"
    addRelatedDecl src "_apply" ref `elementwise stx? fun type value levels => do
      let (newValue, level?) ← elementwiseExpr type value
      let newLevels ← if let some level := level? then do
        let w := mkUnusedName levels `w
        unless ← isLevelDefEq level (mkLevelParam w) do
          throwError "Could not create level parameter for ConcreteCategory instance"
        pure <| w :: levels
      else
        pure levels
      pure (newValue, newLevels)
  | _ => throwUnsupportedSyntax }

/--
`elementwise_of% h`, where `h` is a proof of an equation `f = g` between
morphisms `X ⟶ Y` in a concrete category (possibly after a `∀` binder),
produces a proof of equation `∀ (x : X), f x = g x`, but with compositions fully
right associated and identities removed.

A typical example is using `elementwise_of%` to dynamically generate rewrite lemmas:
```lean
example (M N K : Mon) (f : M ⟶ N) (g : N ⟶ K) (h : M ⟶ K) (w : f ≫ g = h) (m : M) :
    g (f m) = h m := by rw [elementwise_of% w]
```
In this case, `elementwise_of% w` generates the lemma `∀ (x : M), f (g x) = h x`.

Like the `@[elementwise]` attribute, `elementwise_of%` inserts a `ConcreteCategory`
instance argument if it can't synthesize a relevant `ConcreteCategory` instance.
(Technical note: The forgetful functor's universe variable is instantiated with a
fresh level metavariable in this case.)
-/
elab "elementwise_of% " t:term : term => do
  let e ← Term.elabTerm t none
  let (pf, _) ← elementwiseExpr (← inferType e) e
  return pf

end Tactic.Elementwise
