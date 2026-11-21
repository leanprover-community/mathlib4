/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Tactic.Translate.Util

/-!
# Omitting arguments in a translation

This module defines omissions, which can be specified with `to_mdifferentiable (omit := ...)` or
`to_additive (omit := ...)`, to deal with definitions and theorems that need to have some
argument(s) omitted during translation.

An omission is specified with a single number: for example, `1 2` will omit the 1st and 2nd
argument of the declaration during translation.

Instead of using numbers to refer to argument, you can also refer to them by name. For example
`a b` will omit the arguments named `a` and `b`. This is implemented in `elabArgStx`.

## Examples

- `to_differentiable` needs to omit the regularity arguments during translation, such as
  `ContDiff 𝕜 n f` ↦ `Differentiable 𝕜 f`

- TODO(Michael): are there examples of a lemma with a hypothesis `hn : n ≠ 0` or similar
  which should have their argument omitted upon translation?
  existing lemmas like `ContDiff.differentiable` seem to not be examples

- TODO(Michael): examples like translating a `ContMDiffVectorBundle ... n` hypothesis to
  `ContMDiffVectorBundle ... 1`, as in
  `Bundle.Trivialization.contMDiffAt_section_iff` (over a C^n bundle) ↦
  `Bundle.Trivialization.mdifferentiableAt_section_iff` (which requires a `C¹` bundle)

## Implementation details

-/

public meta section

namespace Mathlib.Tactic.Translate
open Lean Meta Elab

/-- `ArgOmit` represents a list of arguments to be omitted during translation. -/
structure ArgOmit where
  /-- The list of argument indices which are omitted: we assume these are sorted
  in ascending order. -/
  args : List Nat := []
  /-- The recursive omission for omitting arguments of arguments.
  For the purpose of checking equality between omissions, this should be sorted. -/
  argOmissions : Array (Nat × ArgOmit) := #[]
  deriving Inhabited

namespace ArgOmit

/-- Return `true` if the omissions doesn't do anything. -/
def isEmpty (r : ArgOmit) : Bool := r matches ⟨[], #[]⟩

/- only for internal testing anyway; this is not the actually executed code
/-- Modify an array of arguments by omitting all elements of given indices. -/
private def _root_.test {α} [Inhabited α] (c : List Nat) : Array α → Array α := fun arr ↦
  -- Sort `c` into ascending order, and remove from the highest indices.
  c.mergeSort.reverse.foldl (α := Array α) (fun a i ↦ a.eraseIdxIfInBounds i) arr

#guard test [2] #["a", "b", "c"] == #["a", "b"]
#guard test [1] #["a", "b", "c"] == #["a", "c"]
#guard test [0, 2] #["a", "b", "c"] == #["b"]
#guard test [0, 2, 4] #["a", "b", "c", "d", "e"] == #["b", "d"]

#guard test [0, 2] #["a", "b", "c", "d", "e"] == #["b", "d", "e"]
#guard test [2, 0] #["a", "b", "c", "d", "e"] == #["b", "d", "e"]
-/

/-- Remove a collection of arguments from a given an array of arguments. -/
def omit! {α} [Inhabited α] (r : ArgOmit) : Array α → Array α :=
  -- We assume `r.args` has indices in ascending order: remove from the end
  -- as otherwise we invalidate indices.
  r.args.mergeSort.reverse.foldl (α := Array α) (fun a i ↦ a.eraseIdxIfInBounds i)

/-- Return the minimum size of an array on which the given omissions configuration is valid. -/
def range (r : ArgOmit) : Nat :=
  r.argOmissions.foldl (max · <| ·.1 + 1) <|
    r.args.iter.map (· + 1) |>.fold max 0

/-- Two omissions are considered equal if all arguments are the same. -/
partial def beq (r₁ r₂ : ArgOmit) : Bool :=
  r₁.args.beq r₂.args &&
    have : BEq ArgOmit := ⟨beq⟩
    r₁.argOmissions == r₂.argOmissions

instance : BEq ArgOmit := ⟨beq⟩

/-- Print an `ArgOmit`, representing the arguments by their index. -/
def toString (r : ArgOmit) : String :=
  let args : List String := r.args.map ToString.toString
  let argOmissions := r.argOmissions.map (fun x ↦ s!"{x.1 + 1} ({x.2.toString})")
  s!"{", ".intercalate (args ++ argOmissions.toList)}"
decreasing_by
  cases r; grind [→ Array.sizeOf_lt_of_mem]

instance : ToString ArgOmit := ⟨fun x ↦ x.toString⟩

end ArgOmit

/-- `Omission` represents a list of arguments for translating a given constant. -/
structure Omission where
  /-- The omissions of arguments. -/
  omission : ArgOmit := {}

/-! ### Omitting arguments in an expression -/

/-- Apply the given binder infos to the binders in expression `e`. -/
private def fixBinderInfos (bis : List BinderInfo) (e : Expr) : Expr :=
  match bis, e with
  | bi :: bis, .forallE n d b _ => .forallE n d (fixBinderInfos bis b) bi
  | bi :: bis, .lam n d b _ => .lam n d (fixBinderInfos bis b) bi
  | _, _ => e

/-
In the implementation of `reorderForall` and `reorderLambda` we use metavariables.
To reorder the arguments in one, we assign it to a reordered new metavariable.
This trick lets us avoid traversing the expression manually when handling recursive reorderings.
Instead, we implicitly rely on `instantiateMVars`.
-/
mutual

/-- Omit the given metavariables using the given `ArgOmit`. -/
private partial def reorderMVars (mvars : Array Expr) (omissions : ArgOmit) :
    MetaM (Array Expr) := do
  let mut mvars := mvars
  for (arg, argOmission) in omissions.argOmissions do
    let mvarId := mvars[arg]!.mvarId!
    let decl ← mvarId.getDecl
    let mvarId' ← mkFreshExprMVar (← omitForall argOmission decl.type) (userName := decl.userName)
    -- Note: we assign `mvarId` in terms of `mvarId'`, and to do this we need to reorder `mvarId'`
    -- with the reverse reorder of `argReorder`.
    -- TODO(Michael): does this comment apply here? If so, how to fix it?
    -- We cannot invert omitting arguments...
    mvarId.assign (← omitLambda argOmission mvarId')
    mvars := mvars.set! arg mvarId'
  return omissions.omit! mvars

/-- Reorder the arguments of a function type using the given `ArgOmit`. -/
partial def omitForall (omission : ArgOmit) (e : Expr) : MetaM Expr := do
  let (mvars, bis, e) ← forallMetaBoundedTelescope e omission.range
  unless mvars.size = omission.range do
    throwError "the omissions configuration `(omit := {omission})` is out of bounds, \
      the type{indentExpr e}\nhas only {mvars.size} arguments"
  let bis := omission.omit! bis |>.toList
  -- Note that `mkForallFVars` also works with mvars.
  fixBinderInfos bis <$> mkForallFVars (← reorderMVars mvars omission) e

/-- Reorder the arguments of a function using the given `ArgOmit`. -/
partial def omitLambda (omission : ArgOmit) (e : Expr) : MetaM Expr := do
  let (mvars, bis, _) ← forallMetaBoundedTelescope (← inferType e) omission.range
  unless mvars.size = omission.range do
    throwError "the omissions configuration (reorder := {omission}) is out of bounds, \
      the function{indentExpr e}\nhas only {mvars.size} arguments"
  let bis := omission.omit! bis |>.toList
  -- Note that `mkLambdaFVars` also works with mvars.
  fixBinderInfos bis <$> mkLambdaFVars (← reorderMVars mvars omission) (e.beta mvars)

end

-- /-! ### Guessing the reorder given the reordered expression -/

-- /-- Decompose the permutation `map` into its disjoint cycle representation. -/
-- private def decomposePerm {n} (map : Vector (Option (Fin n)) n) : Permutation := Id.run do
--   let mut map := map
--   let mut perm := []
--   for h : i in *...n do
--     let mut some j := map[i] | continue
--     if i = j then continue
--     let mut cycle := ⟨[i, j], by grind⟩
--     repeat do
--       let some j' := map[j] | return [] -- If the permutation is malformed, return `[]`.
--       -- To avoid computing the same cycle multiple times, and to avoid infinite loops,
--       -- we erase visited elements from `map`.
--       map := map.set! j none
--       if j' = i then break
--       j := j'
--       cycle := ⟨cycle.1 ++ [j.val], by grind⟩
--     perm := cycle :: perm
--   return perm

-- /-- Return the permutation that sends `src` to `tgt`, if it exists. -/
-- def getPermutation {α : Type*} [BEq α] (src : Array α) (tgt : Array α) : Option Permutation := do
--   let n := src.size
--   if h : n = tgt.size then
--     have src : Vector α n := src.toVector
--     have tgt : Vector α n := h ▸ tgt.toVector
--     return decomposePerm (← src.mapM (some <$> tgt.finIdxOf? ·))
--   else
--     none

-- /-- Determine how many forall binders should be introduced to get a non-dependent conclusion. -/
-- private def depForallDepth : Expr → Nat
--   | .forallE _ _ b _ =>
--     let d := depForallDepth b
--     if d == 0 && !b.hasLooseBVar 0 then 0 else d + 1
--   | _ => 0

-- /-- Try to determine the value of the `(reorder := ...)` option that would be needed to translate
-- type `e₁` to type `e₂`. If there is no good guess, default to `[]`.
-- The heuristic that we use is to compare the conclusions of `e₁` and `e₂`,
-- and to observe which variables are swapped.
-- We also apply this heuristic recursively in hypotheses. -/
-- partial def guessReorder (src tgt : Expr) : MetaM ArgOmit := withReducible do
--   let src ← whnf src; let tgt ← whnf tgt
--   let depth := depForallDepth src
--   unless depth == depForallDepth tgt do return {}
--   forallBoundedTelescope src depth fun srcVars src ↦ do
--   forallBoundedTelescope tgt depth fun tgtVars tgt ↦ do
--   let srcMap : Std.HashMap FVarId Nat := .ofArray <| srcVars.mapIdx fun i x => (x.fvarId!, i)
--   let tgtMap : Std.HashMap FVarId Nat := .ofArray <| tgtVars.mapIdx fun i x => (x.fvarId!, i)
--   let perm := (← visit src tgt (.replicate depth none) |>.run (srcMap, tgtMap) |>.run' {} |>.run)
--     |>.elim [] decomposePerm
--   -- Recursively guess the reorder in the hypotheses
--   let mut argReorders := #[]
--   for i in *...depth do
--     let r ← guessReorder (← inferType srcVars[i]!) (← inferType tgtVars[i]!)
--     unless r.isEmpty do
--       argReorders := argReorders.push (i, r)
--   let mut src := src; let mut tgt := tgt
--   let mut n := depth
--   while src.isForall && tgt.isForall do
--     let r ← guessReorder src.bindingDomain! tgt.bindingDomain!
--     unless r.isEmpty do
--       argReorders := argReorders.push (n, r)
--     -- This won't create loose bound variables, because we already introduced all dependent foralls.
--     src := src.bindingBody!
--     tgt := tgt.bindingBody!
--     n := n + 1
--   return { perm, argReorders }
-- where
--   /-- Determine for each `i : Fin n` to what `j : Fin n` it should get translated. -/
--   visit (src tgt : Expr) {n : Nat} (map : Vector (Option (Fin n)) n) :
--       ReaderT (Std.HashMap FVarId Nat × Std.HashMap FVarId Nat)
--       StateRefT (Std.HashSet (Expr × Expr)) (OptionT BaseIO) (Vector (Option (Fin n)) n) := do
--     if (← get).contains (src, tgt) then return map
--     let map ← match src, tgt with
--       | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => visit d₁ d₂ map >>= visit b₁ b₂
--       | .lam _ d₁ b₁ _    , .lam _ d₂ b₂ _     => visit d₁ d₂ map >>= visit b₁ b₂
--       | .mdata _ e₁       , .mdata _ e₂        => visit e₁ e₂ map
--       | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => visit t₁ t₂ map >>= visit v₁ v₂ >>= visit b₁ b₂
--       | .app f₁ a₁        , .app f₂ a₂         => visit f₁ f₂ map >>= visit a₁ a₂
--       | .proj _ _ e₁      , .proj _ _ e₂       => visit e₁ e₂ map
--       | .fvar fvarId₁  , .fvar fvarId₂  =>
--         let some i₁ := (← read).1[fvarId₁]? | pure map
--         let some i₂ := (← read).2[fvarId₂]? | pure map
--         if h : i₂ < n then
--           if let some i₂' := map[i₁]! then
--             guard (i₂ == i₂') -- If `i₂ ≠ i₂'`, it's not clear what `i₁` should be translated to.
--             pure map
--           else
--             pure <| map.set! i₁ (some ⟨i₂, h⟩)
--         else
--           panic! s!"index {i₂} is out of bounds ({n})"
--       /- To avoid false positives, we do a sanity check to make sure that the two expressions are
--       indeed of the same shape. Note that we cannot check for `e₁ == e₁`, because the universes
--       in `e₁` and `e₂` might be different (because we decide only later whether to swap them). -/
--       | .lit _, .lit _ | .bvar _, .bvar _ | .sort _, .sort _ | .const .., .const .. => pure map
--       | _, _ => failure
--     modify (·.insert (src, tgt))
--     return map

/-! ### Syntax for specifying an omission -/

-- Note: We have to use `declare_syntax_cat` because the omissions syntax is recursive.
/-- The syntax category for the omission syntax. -/
declare_syntax_cat translateOmission

syntax omissionPart := (ident <|> num)+ (" (" translateOmission ")")?
attribute [nolint docBlame] omissionPart

/--
`(omit := ...)` omits the arguments/hypotheses in the generated declaration.
This is used in `to_differentiable` to omit the regularity argument when translating from
`ContDiff` to `Differentiable`, `ContMDiff` to `MDifferentiable` etc.
It uses a space-separated list of 1-based argument indices. For omitting arguments of an argument
`a`, it uses the notation `a (...)` where `...` can be any omission.

For example:
- `(omit := 5 6)` omits the fifth and the sixth argument.
- `(omit := H (2 3))` will omit the second and third arguments that appear in the hypothesis `H`.
-/
syntax (name := «omit») omissionPart,* : translateOmission

/-- Elaborate the argument of an `(omit := ...)` option. -/
partial def elabOmit (stx : TSyntax `translateOmission) (argNames : Array Name)
    (args : Array Expr) (head : MessageData) : MetaM ArgOmit :=
  match stx with
  | `(«omit»| $[$parts],*) => withRef stx do
    let mut omitArgs := []
    let mut omitArgOmissions := #[]
    for part in parts do
      let `(omissionPart| $[$idxStx]* $[($argOmit?)]?) := part | throwUnsupportedSyntax
      let indices ← idxStx.toList.mapM (elabArgStx · argNames args head)
      omitArgs := indices ++ omitArgs
      if let some argOmit := argOmit? then
        for arg in indices do
        let omission ←
          -- Use a reducing telescope to see through `autoParam`.
          withReducible <| forallTelescopeReducing (← inferType args[arg]!) fun xs _ ↦ do
            let argNames ← xs.mapM (·.fvarId!.getUserName)
            -- Recursively elaborate the nested omission syntax.
            elabOmit argOmit argNames xs m!"{args[arg]!}"
        omitArgOmissions := omitArgOmissions.push (arg, omission)
    omitArgOmissions := omitArgOmissions.qsort (·.1 < ·.1)
    -- check that the `argOmissions` aren't duplicated.
    for h : i in *...(omitArgOmissions.size - 1) do
      let arg₀ := omitArgOmissions[i]; let arg₁ := omitArgOmissions[i + 1]
      if arg₀.1 == arg₁.1 then
        throwError "The omission within argument {arg₀.1 + 1} has been set to both \
          `{arg₀.2.toString}` and `{arg₁.2.toString}`. Please specify it only once."
    return { args := omitArgs, argOmissions := omitArgOmissions }
  | _ => throwUnsupportedSyntax

end Mathlib.Tactic.Translate
