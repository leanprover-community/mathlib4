/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Init

/-!
# Reordering arguments in a translation

This module defines reorders, which are used by `to_dual (reorder := ...)` and
`to_additive (reorder := ...)` to deal with definitions and theorems that need to have their
arguments reordered.

A reordering is specified using disjoint cycle notation. For example, `1 2 3, 4 5` will
move the 1st argument to the 2nd, move the 2nd to the 3rd, and the 3rd to the 1st, and it will
swap the 4th and 5th arguments.

Instead of using numbers to refer to argument, you can also refer to them by name. For example
`a b` will swap the arguments named `a` and `b`. This is implemented in `elabArgStx`.

To specify reordering arguments of arguments, the syntax is recursive. For example,
`4 (1 2)` will reorder the first two arguments of the fourth argument.

## Examples

- `to_dual` needs to swap the arguments of some definitions to translate them,
  such as `a ≤ b` ↦ `b ≤ a` and `a ⇨ b` ↦ `b \ a`.
  In these cases, we reorder the 3rd and 4th arguments, which can be specified using
  `@[to_dual (reorder := 3 4)]`.

- `to_additive` needs to swap the arguments when translating `a ^ n` ↦ `n • a`.

- Some theorems are dual to themselves only after reordering some arguments.
  For example, `le_total : ∀ a b : α, a ≤ b ∨ b ≤ a` is dual to itself after swapping `a` and `b`.
  Thanks to the heuristic in `guessReorder`, this reordering can often be found automatically,
  so it suffices to write `@[to_dual self]`.

## TODO

We need better support for reordering of universes for `to_dual` in category theory,
for example to dualize `CategoryTheory.Comma` to itself.

-/

public meta section

namespace Mathlib.Tactic.Translate
open Lean Meta Elab

abbrev Perm := List {l : List Nat // 2 ≤ l.length}

/-- `ArgReorder` represents a permutation of arguments in a translation. -/
structure ArgReorder where
  /-- The list of disjoint cycles that represents the permutation. -/
  perm : Perm := []
  /-- The recursive reorders for reordering arguments of arguments.
  For the purpose of checking equality between reorders, this should be sorted. -/
  argReorders : Array (Nat × ArgReorder) := #[]
  deriving Inhabited

/-- `Reorder` represents a permutation of arguments and universe levels for translating
a given constant. -/
structure Reorder where
  /-- The reordering of universe levels. -/
  univReorder : Perm := []
  /-- The reordering of arguments. -/
  reorder : ArgReorder := {}

/-- Return `true` if the reorder doesn't do anything. -/
def ArgReorder.isEmpty (r : ArgReorder) : Bool := r matches {}

/-- Permute an array of arguments using the given reorder. -/
def Perm.permute! {α} [Inhabited α] (c : Perm) : Array α → Array α :=
  c.foldl (cyclicPermute! · ·.1)
where
  /-- Permute the array using a sequence of indices defining a cyclic permutation.
  If the list of indices `l = [i₁, i₂, ..., iₙ]` are all distinct then
  `(cyclicPermute! a l)[iₖ₊₁] = a[iₖ]` and `(cyclicPermute! a l)[i₀] = a[iₙ]` -/
  cyclicPermute! [Inhabited α] : Array α → List Nat → Array α
    | a, [] => a
    | a, i :: is => cyclicPermuteAux a is a[i]! i
  cyclicPermuteAux : Array α → List Nat → α → Nat → Array α
    | a, [], x, i0 => a.set! i0 x
    | a, i :: is, x, i0 =>
      let (y, a) := a.swapAt! i x
      cyclicPermuteAux a is y i0

/-- Permute a list of either universe levels or universe parameters. -/
def Perm.permuteList! {α} [Inhabited α] (p : Perm) (us : List α) : List α :=
  if p.isEmpty then us else (p.permute! us.toArray).toList

/-- Permute an array of arguments using the given reorder. -/
def ArgReorder.permute! {α} [Inhabited α] (r : ArgReorder) : Array α → Array α :=
  r.perm.permute!

/-- Return the inverse permutation. -/
def Perm.reverse (c : Perm) : Perm :=
  c.map (⟨·.1.reverse, by grind⟩)

/-- Return the reorder that reverses the action of the given reorder. -/
def ArgReorder.reverse (r : ArgReorder) : ArgReorder := {
  perm := r.perm.reverse
  argReorders := r.argReorders.map fun x ↦ (permuteSingle r x.1, x.2.reverse)
}
decreasing_by
  cases r; grind [→ Array.sizeOf_lt_of_mem]
where
  /-- Compute where `Reorder.permute!` sends the `n`-th element in an array. -/
  permuteSingle (r : ArgReorder) (n : Nat) : Nat :=
    r.perm.findSome? (fun cycle ↦ getCycleSuccessor n (cycle.1.head (by grind)) cycle.1) |>.getD n
  /-- Return the successor of `n` in a cycle, where `head` is the head of the cycle list. -/
  getCycleSuccessor (n head : Nat) : List Nat → Option Nat
    | [] => none
    | b :: bs => if b = n then bs.head?.getD head else getCycleSuccessor n head bs

/-- Return the reorder that reverses the action of the given reorder. -/
def Reorder.reverse (r : Reorder) : Reorder where
  univReorder := r.univReorder.reverse
  reorder := r.reorder.reverse

def Perm.range (p : Perm) : Nat :=
  p.iter.flatMap (·.1.iter) |>.fold max 0

/-- Return the minimum size of an array on which the given reorder is valid. -/
def ArgReorder.range (r : ArgReorder) : Nat :=
  if r.isEmpty then 0 else
  1 + r.argReorders.foldl (max · ·.1) r.perm.range

/-- Two permutations are considered equal if they permute in the same way. -/
def Perm.beq (p₁ p₂ : Perm) : Bool :=
  p₁.range == p₂.range &&
    let rangeArr := (0...p₁.range).toArray;
    p₁.permute! rangeArr == p₂.permute! rangeArr

/-- Two reorders are considered equal if all permutations are the same. -/
partial def ArgReorder.beq (r₁ r₂ : ArgReorder) : Bool :=
  r₁.perm.beq r₂.perm &&
    have : BEq ArgReorder := ⟨ArgReorder.beq⟩
    r₁.argReorders == r₂.argReorders

instance : BEq ArgReorder := ⟨ArgReorder.beq⟩

/-- Print a `ArgReorder`, representing the arguments by their index. -/
def ArgReorder.toString (r : ArgReorder) : String :=
  let perm := r.perm.map (" ".intercalate <| ·.1.map (s!"{· + 1}"))
  let argReorders := r.argReorders.map (fun x ↦ s!"{x.1 + 1} ({x.2.toString})")
  s!"{", ".intercalate (perm ++ argReorders.toList)}"
decreasing_by
  cases r; grind [→ Array.sizeOf_lt_of_mem]

instance : ToString ArgReorder := ⟨fun x ↦ x.toString⟩
instance : ToMessageData ArgReorder := ⟨fun x ↦ x.toString⟩

/-! ### Reordering an expression -/

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

/-- Reorder the given metavariables using the given `ArgReorder`. -/
private partial def reorderMVars (mvars : Array Expr) (reorder : ArgReorder) :
    MetaM (Array Expr) := do
  let mut mvars := mvars
  for (arg, argReorder) in reorder.argReorders do
    let mvarId := mvars[arg]!.mvarId!
    let decl ← mvarId.getDecl
    let mvarId' ← mkFreshExprMVar (← reorderForall argReorder decl.type) (userName := decl.userName)
    -- Note: we assign `mvarId` in terms of `mvarId'`, and to do this we need to reorder `mvarId'`
    -- with the reverse reorder of `argReorder`.
    mvarId.assign (← reorderLambda argReorder.reverse mvarId')
    mvars := mvars.set! arg mvarId'
  return reorder.permute! mvars

/-- Reorder the arguments of a function type using the given `ArgReorder`. -/
partial def reorderForall (reorder : ArgReorder) (e : Expr) : MetaM Expr := do
  let (mvars, bis, e) ← forallMetaBoundedTelescope e reorder.range
  unless mvars.size = reorder.range do
    throwError "the permutation (reorder := {reorder}) is out of bounds, \
      the type{indentExpr e}\nhas only {mvars.size} arguments"
  let bis := reorder.permute! bis |>.toList
  -- Note that `mkForallFVars` also works with mvars.
  fixBinderInfos bis <$> mkForallFVars (← reorderMVars mvars reorder) e

/-- Reorder the arguments of a function using the given `ArgReorder`. -/
partial def reorderLambda (reorder : ArgReorder) (e : Expr) : MetaM Expr := do
  let (mvars, bis, e) ← lambdaMetaTelescope e reorder.range
  let (mvars', bis', _) ← forallMetaBoundedTelescope (← inferType e) (reorder.range - mvars.size)
  let mut mvars := mvars ++ mvars'
  unless mvars.size = reorder.range do
    throwError "the permutation (reorder := {reorder}) is out of bounds, \
      the function{indentExpr e}\nhas only {mvars.size} arguments"
  let bis := reorder.permute! (bis ++ bis') |>.toList
  -- Note that `mkLambdaFVars` also works with mvars.
  fixBinderInfos bis <$> mkLambdaFVars (← reorderMVars mvars reorder) (mkAppN e mvars')

end

/-! ### Guessing the reorder given the reordered expression -/

/-- Decompose the permutation `map` into its disjoint cycle representation. -/
 private def decomposePerm {n} (map : Vector (Option (Fin n)) n) : Perm := Id.run do
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

/-- Determine the universe level reorder from the argument reorder. -/
def guessUnivReorder (reorder : ArgReorder) (src : Expr) (params : List Name) : Perm := Id.run do
  let mut map := .replicate params.length none
  for ⟨cycle, _⟩ in show List _ from reorder.perm do
    for i in cycle, i' in cycle.tail ++ [cycle.head (by grind)] do
      for u in getUnivs (getNthHyp i src), u' in getUnivs (getNthHyp i' src) do
        let some p := getParam? u | pure ()
        let some p' := getParam? u' | pure ()
        if p != p' then
          let some n := params.finIdxOf? p | pure ()
          let some n' := params.finIdxOf? p' | pure ()
          map := map.set n n'
  return decomposePerm map
where
  getNthHyp : Nat → Expr → Expr
    | 0, e => e.bindingDomain!
    | n + 1, e => getNthHyp n e.bindingBody!
  getUnivs (e : Expr) : List Level :=
    match e.getAppFn with
    | .const _ us => us
    | .sort u => [u]
    | _ => []
  getParam? : Level → Option Name
    | .param p => some p
    | .succ u => getParam? u
    | _ => none

/-- Determine how many forall binders should be introduced to get a non-dependent conclusion. -/
private def depForallDepth : Expr → Nat
  | .forallE _ _ b _ =>
    let d := depForallDepth b
    if d == 0 && !b.hasLooseBVar 0 then 0 else d + 1
  | _ => 0

/-- Try to determine the value of the `(reorder := ...)` option that would be needed to translate
type `e₁` to type `e₂`. If there is no good guess, default to `[]`.
The heuristic that we use is to compare the conclusions of `e₁` and `e₂`,
and to observe which variables are swapped.
We also apply this heuristic recursively in hypotheses. -/
partial def guessReorder (src tgt : Expr) : MetaM ArgReorder := withReducible do
  let src ← whnf src; let tgt ← whnf tgt
  let depth := depForallDepth src
  unless depth == depForallDepth tgt do return {}
  forallBoundedTelescope src depth fun srcVars src ↦ do
  forallBoundedTelescope tgt depth fun tgtVars tgt ↦ do
  let srcMap : Std.HashMap FVarId Nat := .ofArray <| srcVars.mapIdx fun i x => (x.fvarId!, i)
  let tgtMap : Std.HashMap FVarId Nat := .ofArray <| tgtVars.mapIdx fun i x => (x.fvarId!, i)
  let perm := (visit src tgt (.replicate depth none) (srcMap, tgtMap)).elim [] decomposePerm
  -- Recursively guess the reorder in the hypotheses
  let mut argReorders := #[]
  for i in *...depth do
    let r ← guessReorder (← inferType srcVars[i]!) (← inferType tgtVars[i]!)
    unless r.isEmpty do
      argReorders := argReorders.push (i, r)
  let mut src := src; let mut tgt := tgt
  let mut n := depth
  while src.isForall && tgt.isForall do
    let r ← guessReorder src.bindingDomain! tgt.bindingDomain!
    unless r.isEmpty do
      argReorders := argReorders.push (n, r)
    -- This won't create loose bound variables, because we already introduced all dependent foralls.
    src := src.bindingBody!
    tgt := tgt.bindingBody!
    n := n + 1
  return { perm, argReorders }
where
  /-- Determine for each `i : Fin n` to what `j : Fin n` it should get translated. -/
  visit (src tgt : Expr) {n : Nat} (map : Vector (Option (Fin n)) n) :
      ReaderT (Std.HashMap FVarId Nat × Std.HashMap FVarId Nat)
      Option (Vector (Option (Fin n)) n) := do
    match src, tgt with
    | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => visit d₁ d₂ map >>= visit b₁ b₂
    | .lam _ d₁ b₁ _    , .lam _ d₂ b₂ _     => visit d₁ d₂ map >>= visit b₁ b₂
    | .mdata _ e₁       , .mdata _ e₂        => visit e₁ e₂ map
    | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => visit t₁ t₂ map >>= visit v₁ v₂ >>= visit b₁ b₂
    | .app f₁ a₁        , .app f₂ a₂         => visit f₁ f₂ map >>= visit a₁ a₂
    | .proj _ _ e₁      , .proj _ _ e₂       => visit e₁ e₂ map
    | .fvar fvarId₁  , .fvar fvarId₂  =>
      let some i₁ := (← read).1[fvarId₁]? | some map
      let some i₂ := (← read).2[fvarId₂]? | some map
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

/-! ### Syntax for specifying a reorder -/

-- Note: We have to use `declare_syntax_cat` because the reorder syntax is recursive.
/-- The syntax category for the reorder syntax. -/
declare_syntax_cat translateReorder

syntax reorderPart := (ident <|> num)+ (" (" translateReorder ")")?
attribute [nolint docBlame] reorderPart

/--
`(reorder := ...)` reorders the arguments/hypotheses in the generated declaration.
This is used in `to_dual` to swap the arguments in `≤`, `<` and `⟶`,
and it is used in `to_additive` to translate from `a ^ n` to `n • a`.
It uses disjoint cycle notation for the permutation. For reordering arguments of an argument `a`,
it uses the notation `a (...)` where `...` can be any reorder.

For example:
- `(reorder := α β, 5 6)` swaps the arguments `α` and `β` with each other and the fifth and
  the sixth argument.
- `(reorder := 3 4 5)` will move the fifth argument before the third argument.
- `(reorder := H (x y))` will swap the arguments `x` and `y` that appear in the hypothesis `H`.

If the translated declaration already exists (i.e. when using `existing` or `self`), the reorder
argument is automatically inferred using the function `guessReorder`. -/
syntax (name := reorder) reorderPart,* : translateReorder

/-- Elaborate syntax that refers to an argument of a declaration or hypothesis.
This is either a 1-indexed number, or a name from `argNames`.
- `fvars` is only used to add hover information to `stx`
- `head` is only used for the error message. -/
def elabArgStx (stx : TSyntax [`ident, `num]) (argNames : Array Name) (fvars : Array Expr)
    (head : MessageData) : MetaM Nat := do
  let n ← match stx with
    | `($name:ident) => match argNames.idxOf? name.getId with
      | some n => pure n
      | none => throwErrorAt stx
        "invalid argument `{stx}`, it is not an argument of `{head}`."
    | `($n:num) =>
      if n.getNat = 0 then
        throwErrorAt stx "invalid index `{stx}`, arguments are counted starting from 1."
      if n.getNat > fvars.size then
        throwErrorAt stx "index `{stx}` is out of bounds, there are only `{fvars.size}` arguments"
      pure (n.getNat - 1)
    | _ => throwUnsupportedSyntax
  Elab.Term.addTermInfo' stx fvars[n]! |>.run'
  return n

/-- Elaborate the argument of a `(reorder := ...)` option. -/
partial def elabReorder (stx : TSyntax `translateReorder) (argNames : Array Name)
    (args : Array Expr) (head : MessageData) : MetaM ArgReorder :=
  match stx with
  | `(reorder| $[$parts],*) => withRef stx do
    let mut perm := []
    let mut argReorders := #[]
    for part in parts do
      let `(reorderPart| $[$cycleStx]* $[($argReorder?)]?) := part | throwUnsupportedSyntax
      let cycle ← cycleStx.toList.mapM (elabArgStx · argNames args head)
      if h : 2 ≤ cycle.length then
        perm := ⟨cycle, h⟩ :: perm
      else if argReorder?.isNone then
        throwErrorAt part "\
          Invalid cycle `{part}`, a cycle must have at least 2 elements.\n\
            See the docstring of `reorder` for how to specify reorders."
      if let some argReorder := argReorder? then
        for arg in cycle do
        let reorder ←
          -- Use a reducing telescope to see through `autoParam`.
          withReducible <| forallTelescopeReducing (← inferType args[arg]!) fun xs _ ↦ do
            let argNames ← xs.mapM (·.fvarId!.getUserName)
            -- Recursively elaborate the nested reorder syntax.
            elabReorder argReorder argNames xs m!"{args[arg]!}"
        argReorders := argReorders.push (arg, reorder)
    -- Check that the cycles are disjoint
    _ ← perm.iter.flatMap (·.1.iter) |>.foldM (init := ({} : Std.HashSet Nat)) fun s n ↦ do
      let (contains, s) := s.containsThenInsert n
      if contains then throwError
        "Please remove the duplicate entries from the disjoint cycle representation.\n\
        See the docstring of `reorder` for how to specify reorders."
      return s
    argReorders := argReorders.qsort (·.1 < ·.1)
    -- check that the `argReorders` aren't duplicated.
    for h : i in *...(argReorders.size - 1) do
      let arg₀ := argReorders[i]; let arg₁ := argReorders[i + 1]
      if arg₀.1 == arg₁.1 then
        throwError "The reorder within argument {arg₀.1 + 1} has been set to both \
          `{arg₀.2.toString}` and `{arg₁.2.toString}`. Please specify it only once."
    return { perm, argReorders }
  | _ => throwUnsupportedSyntax

end Mathlib.Tactic.Translate
