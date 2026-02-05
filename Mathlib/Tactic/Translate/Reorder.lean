/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public meta import Mathlib.Data.Array.Defs

/-!
# Reordering arguments

This module defines reorders, which are used by `to_dual (reorder := ...)` in order to deal with
definitions and theorems that need to have their arguments reordered.
-/

public meta section

namespace Mathlib.Tactic.Translate
open Lean Meta Elab

/-- `Reorder` represents a permutation of arguments in a translation. -/
structure Reorder where
  perm : List {l : List Nat // 2 ≤ l.length} := []
  /-- It is assumed to be sorted. -/
  argReorders : Array (Nat × Reorder) := #[]
  deriving Inhabited

/-- Permute a list of either universe levels or universe parameters.
The current heuristic is to swap the first two universes if the first argument is permuted. -/
def Reorder.permuteUniv {α} (r : Reorder) (us : List α) : List α :=
  if r.perm.any (·.1.contains 0) then
    if let x :: y :: l := us then
      y :: x :: l
    else us
  else us

/-- Return true if the reorder doesn't do anything. -/
def Reorder.isEmpty (r : Reorder) : Bool := r matches {}

/-- Return the nested reorder for argument `arg`. -/
def Reorder.argReorder? (r : Reorder) (arg : Nat) : Option Reorder :=
  r.argReorders.binSearch (arg, default) (·.1 < ·.1) |>.map (·.2)

/-- Permute an array of arguments using the given reorder. -/
def Reorder.permute! {α} [Inhabited α] (r : Reorder) : Array α → Array α :=
  r.perm.foldl (·.cyclicPermute! ·.1)

/-- Compute where the `n`-th element in an array is sent to by `Reorder.permute!`. -/
def Reorder.permuteSingle (r : Reorder) (n : Nat) : Nat :=
  r.perm.findSome? (fun cycle ↦ getNext (cycle.1.head (by grind)) cycle.1) |>.getD n
where
  getNext (head : Nat) : List Nat → Option Nat
    | [] => none
    | b :: bs => if b = n then bs.head?.getD head else getNext head bs

/-- Return the reorder that reverses the action of the given reorder. -/
def Reorder.reverse (r : Reorder) : Reorder := {
  perm := r.perm.map ( ⟨·.1.reverse, by grind⟩)
  argReorders := r.argReorders.map fun x ↦ (permuteSingle r x.1, x.2.reverse)
}
decreasing_by
  cases r; grind [→ Array.sizeOf_lt_of_mem]

/-- Return the minimum size of an array on which `Reorder.permute!` can run. -/
def Reorder.size (r : Reorder) : Nat :=
  if r.isEmpty then 0 else
  1 + r.argReorders.foldl (max · ·.1) (r.perm.iter.flatMap (·.1.iter) |>.fold max 0)

/-- Check whether the permutations are equal by running both on `(0...=max).toArray`. -/
partial def Reorder.beq (r₁ r₂ : Reorder) : Bool :=
  r₁.size == r₂.size &&
    r₁.permute! (0...r₁.size).toArray == r₂.permute! (0...r₁.size).toArray &&
      have : BEq Reorder := ⟨Reorder.beq⟩
      r₁.argReorders == r₂.argReorders

instance : BEq Reorder := ⟨Reorder.beq⟩

protected def Reorder.toString (r : Reorder) : String :=
  let perm := r.perm.map (" ".intercalate <| ·.1.map (toString <| · + 1))
  let argReorders := r.argReorders.map (fun x ↦ s!"{x.1 + 1} ({x.2.toString})")
  s!"{", ".intercalate (perm ++ argReorders.toList)}"
decreasing_by
  cases r; grind [→ Array.sizeOf_lt_of_mem]

/-- Reorder pi-binders. See doc of `reorderAttr` for the interpretation of the argument -/
partial def reorderForall (reorder : Reorder) (src : Expr) : MetaM Expr := do
  forallBoundedTelescope src reorder.size fun xs e => do
  unless xs.size = reorder.size do
    throwError "the permutation\n{reorder.perm}\nprovided by the `(reorder := ...)` option is \
      out of bounds, the type{indentExpr src}\nhas only {xs.size} arguments"
  let mut lctx ← getLCtx
  for (arg, reorder) in reorder.argReorders do
    let x := xs[arg]!.fvarId!
    let type ← x.getType
    let type ← reorderForall reorder type
    lctx := lctx.modifyLocalDecl x (·.setType type)
  return lctx.mkForall (reorder.permute! xs) e

/-- Reorder lambda-binders. See doc of `reorderAttr` for the interpretation of the argument -/
partial def reorderLambda (reorder : Reorder) (src : Expr) : MetaM Expr := do
  let (xs, _, e) ← lambdaMetaTelescope src reorder.size
  let (ys, _, _) ← forallMetaBoundedTelescope (← inferType e) (reorder.size - xs.size)
  let e := mkAppN e ys
  let mut xs := xs ++ ys
  unless xs.size = reorder.size do
    throwError "the permutation\n{reorder.perm}\nis out of bounds, \
      the function{indentExpr src}\nhas only {xs.size} arguments"
  for (n, reorder) in reorder.argReorders do
    let mvarId := xs[n]!.mvarId!
    let newMVarId ← mkFreshExprMVar (← reorderForall reorder (← mvarId.getType))
    mvarId.assign (← reorderLambda reorder.reverse newMVarId)
    xs := xs.set! n newMVarId
  mkLambdaFVars (reorder.permute! xs) e

/-- Try to determine the value of the `(reorder := ...)` option that would be needed to translate
type `e₁` to type `e₂`. If there is no good guess, default to `[]`.
The heuristic that we use is to compare the conclusions of `e₁` and `e₂`,
and to observe which variables are swapped. -/
partial def guessReorder (src tgt : Expr) (srcMap tgtMap : Std.HashMap FVarId Nat := {}) :
    MetaM Reorder := withReducible do
  let src ← whnf src; let tgt ← whnf tgt
  if isDepForall src && isDepForall tgt then
    forallBoundedTelescope src (some 1) fun xsrc src ↦ do
    forallBoundedTelescope tgt (some 1) fun xtgt tgt ↦ do
    let srcMap := srcMap.insert xsrc[0]!.fvarId! srcMap.size
    let tgtMap := tgtMap.insert xtgt[0]!.fvarId! tgtMap.size
    guessReorder src tgt srcMap tgtMap
  else
  let mut n := srcMap.size
  let perm := (go src tgt (.replicate n none)).elim [] decomposePerm
  let mut src := src; let mut tgt := tgt
  let mut argReorders := #[]
  while src.isForall && tgt.isForall do
    let r ← guessReorder src.bindingDomain! tgt.bindingDomain!
    unless r.isEmpty do
      argReorders := argReorders.push (n, r)
    src := src.bindingBody!
    tgt := tgt.bindingBody!
    n := n + 1
  return { perm, argReorders }
  -- Compute the list of cycles representing the permutation `map`.
where
  /-- Decompose the permutation `map` into its disjoint cycle representation. -/
  decomposePerm {n} (map : Vector (Option (Fin n)) n) := Id.run do
    let mut map := map
    let mut perm := []
    for h : i in 0...n do
      let mut some j := map[i] | continue
      if i = j then continue
      let mut cycle := ⟨[i, j], by grind⟩
      repeat do
        let some j' := map[j] | return [] -- If the permutation is malformed, return `[]`.
        -- To avoid computing the same cycle multiple times, and to avoid infinite loops,
        -- we erase visited elements from `map`.
        map := map.set! j none
        if j' = i then break
        j := j'
        cycle := ⟨cycle.1 ++ [↑j], by grind⟩
      perm := cycle :: perm
    return perm
  /-- Determine whether the given expression is a forall with a dependency.
  If it has no dependency, then we can treat it as the conclusion. -/
  isDepForall : Expr → Bool
    | .forallE _ _ b _ => b.hasLooseBVar 0 || isDepForall b
    | _ => false
  /-- Determine for each `i : Fin n` to what `j : Fin n` it should get translated. -/
  go (src tgt : Expr) {n : Nat} (map : Vector (Option (Fin n)) n) :
      Option (Vector (Option (Fin n)) n) := do
    match src, tgt with
    | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => go d₁ d₂ map >>= go b₁ b₂
    | .lam _ d₁ b₁ _    , .lam _ d₂ b₂ _     => go d₁ d₂ map >>= go b₁ b₂
    | .mdata _ e₁       , .mdata _ e₂        => go e₁ e₂ map
    | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => go t₁ t₂ map >>= go v₁ v₂ >>= go b₁ b₂
    | .app f₁ a₁        , .app f₂ a₂         => go f₁ f₂ map >>= go a₁ a₂
    | .proj _ _ e₁      , .proj _ _ e₂       => go e₁ e₂ map
    | .fvar fvarId₁  , .fvar fvarId₂  =>
      let some i₁ := srcMap[fvarId₁]? | some map
      let some i₂ := tgtMap[fvarId₂]? | some map
      if h : i₂ < n then
        if let some i₂' := map[i₁]! then
          guard (i₂ == i₂') -- If `i₂ ≠ i₂'`, it's not clear what `i₁` should be translated to.
          some map
        else
          some <| map.set! i₁ (some ⟨i₂, h⟩)
      else
        panic! s!"index {i₂} is out of bounds ({n})"
    /- To avoid false positives, we do a sanity check to make sure that the two expressions are
    indeed of the same shape. Note that we cannot check for `e₁ == e₁`, because the universes
    in `e₁` and `e₂` might be different (because we decide only later whether to swap them). -/
    | .lit _, .lit _ | .bvar _, .bvar _ | .sort _, .sort _ | .const .., .const .. => some map
    | _, _ => none

/-- Elaborate syntax that refers to an argument of the declaration.
This is either a 1-indexed number, or a name from `argNames`.
`fvars` is only used to add hover information to `stx`,
and `head` is only used for the error message. -/
def elabArgStx (head : MessageData) (argNames : Array Name) (fvars : Array Expr)
    (stx : TSyntax [`ident, `num]) : MetaM Nat := do
  let n ← match stx with
    | `($name:ident) => match argNames.idxOf? name.getId with
      | some n => pure n
      | none => throwErrorAt stx
        "invalid argument '{stx}', it is not an argument of '{head}'."
    | `($n:num) =>
      if n.getNat = 0 then
        throwErrorAt stx "invalid index `{stx}`, arguments are counted starting from 1."
      if n.getNat > fvars.size then
        throwErrorAt stx "index `{stx}` is out of bounds, there are only `{fvars.size}` arguments"
      pure (n.getNat - 1)
    | _ => throwUnsupportedSyntax
  Elab.Term.addTermInfo' stx fvars[n]! |>.run'
  return n

declare_syntax_cat translateReorder

syntax (name := reorder) ((ident <|> num)+ (" (" translateReorder ")")?),* : translateReorder

partial def elabReorder (stx : TSyntax `translateReorder)
    (head : MessageData) (argNames : Array Name) (args : Array Expr) : MetaM Reorder :=
  match stx with
  | `(reorder| $[$[$permStx]* $[($argReordersStx)]?],*) => do
    let mut perm := []
    let mut argReorders := #[]
    for cycleStx in permStx, argReorder? in argReordersStx do
      if h : cycleStx.size = 0 then throwUnsupportedSyntax else
      let cycle ← cycleStx.toList.mapM (elabArgStx head argNames args)
      if h : 2 ≤ cycle.length then
        perm := ⟨cycle, h⟩ :: perm
      else
        if argReorder?.isNone then
        throwErrorAt cycleStx[0].raw "\
          invalid cycle `{cycleStx[0]}`, a cycle must have at least 2 elements.\n\
          `(reorder := ...)` uses cycle notation to specify a permutation.\n\
          For example `(reorder := 1 2, 5 6)` swaps the first two arguments with each other \
          and the fifth and the sixth argument and `(reorder := 3 4 5)` will move \
          the fifth argument before the third argument."
      if let some argReorder := argReorder? then
        for arg in cycle do
          let reorder ←
            withReducible <| forallTelescopeReducing (← inferType args[arg]!) fun xs _ ↦ do
            let argNames ← xs.mapM (·.fvarId!.getUserName)
            elabReorder argReorder m!"{args[arg]!}" argNames xs
          argReorders := argReorders.push (arg, reorder)
    return { perm, argReorders := argReorders.qsort (·.1 < ·.1) }
  | _ => throwUnsupportedSyntax

end Mathlib.Tactic.Translate
