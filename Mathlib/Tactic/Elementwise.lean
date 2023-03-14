/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Kyle Miller
-/

import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Tactic.Reassoc

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
    let tgt := match src with
      | Name.str n s => Name.mkStr n $ s ++ "_apply"
      | x => x
    if (kind != AttributeKind.global) then
      throwError "`elementwise` can only be used as a global attribute"
    addDeclarationRanges tgt
      { range := ← getDeclarationRange (← getRef)
        selectionRange := ← getDeclarationRange ref }
    let info ← getConstInfo src
    let (newValue, level?) ← elementwiseExpr info.type info.value!
    let mut levels := info.levelParams
    if let some level := level? then
      let w := mkUnusedName levels `w
      unless ← isLevelDefEq level (mkLevelParam w) do
        throwError "Could not create level parameter for ConcreteCategory instance"
      levels := w :: levels
    let newValue ← instantiateMVars newValue
    let newType ← instantiateMVars (← inferType newValue)
    match info with
    | ConstantInfo.thmInfo info =>
      addAndCompile <| .thmDecl
        { info with levelParams := levels, type := newType, name := tgt, value := newValue }
    | ConstantInfo.defnInfo info =>
      -- It looks a bit weird that we use `.thmDecl` here too,
      -- but apparently structure fields are created using `def`
      -- even with they are propositional. If `elementwise` worked, it was a `Prop` anyway.
      addAndCompile <| .thmDecl
        { info with levelParams := levels, type := newType, name := tgt, value := newValue }
    | _ => throwError "Constant {src} is not a theorem or definition."
    if isProtected (← getEnv) src then
      setEnv $ addProtected (← getEnv) tgt
    let stx := match stx? with | some stx => stx | none => #[]
    _ ← Term.TermElabM.run' <| ToAdditive.applyAttributes ref stx `elementwise src tgt
  | _ => throwUnsupportedSyntax }

/--
`elementwise_of% h`, where `h` is
an equation `f = g` between morphisms `X ⟶ Y` in a category (possibly after a `∀` binder),
produces the equation `∀ (x : X), f x = g x`, but with compositions fully right associated and
identities removed. The category must already have a `ConcreteCategory` instance.

The type and proof of `%elementwise_of h` is generated by `Tactic.Elementwise.elementwiseExpr`
which makes `%elementwise_of` meta-programming adjacent. It is not called as a tactic but as
an expression. The goal is to avoid creating assumptions that are dismissed after one use:
```lean
example (M N K : Mon) (f : M ⟶ N) (g : N ⟶ K) (h : M ⟶ K) (w : f ≫ g = h) (m : M) :
    g (f m) = h m := by rw [%elementwise_of w]
```
-/
elab "elementwise_of% " t:term : term => do
  let e ← Term.elabTerm t none
  let (pf, none) ← elementwiseExpr (← inferType e) e
    | throwError "Could not synthesize a `ConcreteCategory` instance associated to the equality"
  return pf

end Tactic.Elementwise
