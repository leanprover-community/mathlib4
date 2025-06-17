/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Kyle Miller
-/

import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Util.AddRelatedDecl
import Batteries.Tactic.Lint

/-!
# Tools to reformulate category-theoretic lemmas in concrete categories

## The `elementwise` attribute

The `elementwise` attribute generates lemmas for concrete categories from lemmas
that equate morphisms in a category.

A sort of inverse to this for the `Type*` category is the `@[higher_order]` attribute.

For more details, see the documentation attached to the `syntax` declaration.

## Main definitions

- The `@[elementwise]` attribute.

- The ``elementwise_of% h` term elaborator.

## Implementation

This closely follows the implementation of the `@[reassoc]` attribute, due to Simon Hudon and
reimplemented by Kim Morrison in Lean 4.
-/

open Lean Meta Elab Tactic
open Mathlib.Tactic

namespace Tactic.Elementwise
open CategoryTheory

section theorems

universe u

theorem forall_congr_forget_Type (α : Type u) (p : α → Prop) :
    (∀ (x : (forget (Type u)).obj α), p x) ↔ ∀ (x : α), p x := Iff.rfl

attribute [local instance] HasForget.instFunLike HasForget.hasCoeToSort

theorem forget_hom_Type (α β : Type u) (f : α ⟶ β) : DFunLike.coe f = f := rfl

theorem hom_elementwise {C : Type*} [Category C] [HasForget C]
    {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x := by rw [h]

end theorems

/-- List of simp lemmas to apply to the elementwise theorem. -/
def elementwiseThms : List Name :=
  [ -- HasForget lemmas
    ``CategoryTheory.coe_id, ``CategoryTheory.coe_comp, ``CategoryTheory.comp_apply,
    ``CategoryTheory.id_apply,
    -- ConcreteCategory lemmas
    ``CategoryTheory.hom_id, ``CategoryTheory.hom_comp, ``id_eq, ``Function.comp_apply,
    -- further simplifications if the category is `Type`
    ``forget_hom_Type, ``forall_congr_forget_Type, ``types_comp_apply, ``types_id_apply,
    -- further simplifications to turn `HasForget` definitions into `ConcreteCategory` ones
    -- (if available)
    ``forget_obj, ``ConcreteCategory.forget_map_eq_coe, ``coe_toHasForget_instFunLike,
    -- simp can itself simplify trivial equalities into `true`. Adding this lemma makes it
    -- easier to detect when this has occurred.
    ``implies_true]

/--
Given an equation `f = g` between morphisms `X ⟶ Y` in a category `C`
(possibly after a `∀` binder), produce the equation `∀ (x : X), f x = g x` or
`∀ [HasForget C] (x : X), f x = g x` as needed (after the `∀` binder), but
with compositions fully right associated and identities removed.

Returns the proof of the new theorem along with (optionally) a new level metavariable
for the first universe parameter to `HasForget`.

The `simpSides` option controls whether to simplify both sides of the equality, for simpNF
purposes.
-/
def elementwiseExpr (src : Name) (type pf : Expr) (simpSides := true) :
    MetaM (Expr × Option (Level × Level)) := do
  let type := (← instantiateMVars type).cleanupAnnotations
  forallTelescope type fun fvars type' => do
    mkHomElementwise type' (← mkExpectedTypeHint (mkAppN pf fvars) type') fun eqPf instConcr? => do
      -- First simplify using elementwise-specific lemmas
      let mut eqPf' ← simpType (simpOnlyNames elementwiseThms (config := { decide := false })) eqPf
      if (← inferType eqPf') == .const ``True [] then
        throwError "elementwise lemma for {src} is trivial after applying HasForget \
          lemmas, which can be caused by how applications are unfolded. \
          Using elementwise is unnecessary."
      if simpSides then
        let ctx ← Simp.Context.mkDefault
        let (ty', eqPf'') ← simpEq (fun e => return (← simp e ctx).1) (← inferType eqPf') eqPf'
        -- check that it's not a simp-trivial equality:
        forallTelescope ty' fun _ ty' => do
          if let some (_, lhs, rhs) := ty'.eq? then
            if ← Batteries.Tactic.Lint.isSimpEq lhs rhs then
              throwError "applying simp to both sides reduces elementwise lemma for {src} \
                to the trivial equality {ty'}. \
                Either add `nosimp` or remove the `elementwise` attribute."
        eqPf' ← mkExpectedTypeHint eqPf'' ty'
      if let some (w, uF, insts) := instConcr? then
        return (← Meta.mkLambdaFVars (fvars.append insts) eqPf', (w, uF))
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
  mkHomElementwise {α} [Inhabited α] (eqTy eqPf : Expr)
      (k : Expr → Option (Level × Level × Array Expr) → MetaM α) :
      MetaM α := do
    let (C, instC) ← try extractCatInstance eqTy catch _ =>
      throwError "elementwise expects equality of morphisms in a category"
    -- First try being optimistic that there is already a HasForget instance.
    if let some eqPf' ← observing? (mkAppM ``hom_elementwise #[eqPf]) then
      k eqPf' none
    else
      -- That failed, so we need to introduce the instance, which takes creating
      -- a fresh universe level for `ConcreteCategory`'s forgetful functor.
      let .app (.const ``Category [v, u]) _ ← inferType instC
        | throwError "internal error in elementwise: {← inferType instC}"
      let w ← mkFreshLevelMVar
      let uF ← mkFreshLevelMVar
      -- Give a type to the `FunLike` instance on `F`
      let fty (F carrier : Expr) : Expr :=
        -- I *think* this is right, but it certainly doesn't feel like I'm doing it right.
        .forallE `X C (.forallE `Y C (mkApp3
          (.const ``FunLike [.succ uF, .succ w, .succ w])
          (mkApp2 F (.bvar 1) (.bvar 0))
          (mkApp carrier (.bvar 1)) (mkApp carrier (.bvar 0))) default) default
      -- Give a type to the `ConcreteCategory` instance on `C`
      let cty (F carrier instFunLike : Expr) : Expr :=
        mkApp5 (.const ``ConcreteCategory [w, v, u, uF]) C instC F carrier instFunLike
      withLocalDecls
        #[(`F, .implicit, fun _ => pure <| .forallE `X C (.forallE `Y C
            (.sort (.succ uF)) default) default),
          (`carrier, .implicit, fun _ => pure <| .forallE `X C (.sort (.succ w)) default),
          (`instFunLike, .implicit, fun decls => pure <| fty decls[0]! decls[1]!),
          (`inst, .instImplicit, fun decls => pure <| cty decls[0]! decls[1]! decls[2]!)]
        fun cfvars => do
          let eqPf' ← mkAppM ``hom_elementwise #[eqPf]
          k eqPf' (some (w, uF, cfvars))

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
creates a new lemma for a `HasForget` giving an equation with those morphisms applied
to some value.

Syntax examples:
- `@[elementwise]`
- `@[elementwise nosimp]` to not use `simp` on both sides of the generated lemma
- `@[elementwise (attr := simp)]` to apply the `simp` attribute to both the generated lemma and
  the original lemma.

Example application of `elementwise`:

```lean
@[elementwise]
lemma some_lemma {C : Type*} [Category C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : ...) : f ≫ g = h := ...
```

produces

```lean
lemma some_lemma_apply {C : Type*} [Category C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : ...)
    [HasForget C] (x : X) : g (f x) = h x := ...
```

Here `X` is being coerced to a type via `CategoryTheory.HasForget.hasCoeToSort` and
`f`, `g`, and `h` are being coerced to functions via `CategoryTheory.HasForget.hasCoeToFun`.
Further, we simplify the type using `CategoryTheory.coe_id : ((𝟙 X) : X → X) x = x` and
`CategoryTheory.coe_comp : (f ≫ g) x = g (f x)`,
replacing morphism composition with function composition.

The `[HasForget C]` argument will be omitted if it is possible to synthesize an instance.

The name of the produced lemma can be specified with `@[elementwise other_lemma_name]`.
If `simp` is added first, the generated lemma will also have the `simp` attribute.
-/
syntax (name := elementwise) "elementwise"
  " nosimp"? (" (" &"attr" " := " Parser.Term.attrInstance,* ")")? : attr

initialize registerBuiltinAttribute {
  name := `elementwise
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| elementwise $[nosimp%$nosimp?]? $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`elementwise` can only be used as a global attribute"
    addRelatedDecl src "_apply" ref stx? fun type value levels => do
      let (newValue, level?) ← elementwiseExpr src type value (simpSides := nosimp?.isNone)
      let newLevels ← if let some (levelW, levelUF) := level? then do
        let w := mkUnusedName levels `w
        let uF := mkUnusedName levels `uF
        unless ← isLevelDefEq levelW (mkLevelParam w) do
          throwError "Could not create level parameter `w` for ConcreteCategory instance"
        unless ← isLevelDefEq levelUF (mkLevelParam uF) do
          throwError "Could not create level parameter `uF` for ConcreteCategory instance"
        pure <| uF :: w :: levels
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
example (M N K : MonCat) (f : M ⟶ N) (g : N ⟶ K) (h : M ⟶ K) (w : f ≫ g = h) (m : M) :
    g (f m) = h m := by rw [elementwise_of% w]
```
In this case, `elementwise_of% w` generates the lemma `∀ (x : M), f (g x) = h x`.

Like the `@[elementwise]` attribute, `elementwise_of%` inserts a `HasForget`
instance argument if it can't synthesize a relevant `HasForget` instance.
(Technical note: The forgetful functor's universe variable is instantiated with a
fresh level metavariable in this case.)

One difference between `elementwise_of%` and `@[elementwise]` is that `@[elementwise]` by
default applies `simp` to both sides of the generated lemma to get something that is in simp
normal form. `elementwise_of%` does not do this.
-/
elab "elementwise_of% " t:term : term => do
  let e ← Term.elabTerm t none
  let (pf, _) ← elementwiseExpr .anonymous (← inferType e) e (simpSides := false)
  return pf

-- TODO: elementwise tactic
syntax "elementwise" (ppSpace colGt ident)* : tactic
syntax "elementwise!" (ppSpace colGt ident)* : tactic

end Tactic.Elementwise
