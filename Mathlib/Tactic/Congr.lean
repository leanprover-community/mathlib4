import Lean.Meta
import Mathlib.Mathport.Syntax
import Mathlib.Tactic.Ext

namespace Mathlib.Tactic.Congr
open Lean Meta Elab

/-- try to close goal using reflexivity and subsingletons -/
def tryCloseGoal (mvar: MVarId) : MetaM Bool := do
  let u ← mkFreshLevelMVar
  try
    let res ←  Meta.apply mvar (mkConst ``Eq.refl [u])
    unless res.isEmpty do
      throwError "failed to close goal"
    pure true
  catch _ =>
  try
    let res ←  Meta.apply mvar (mkConst ``Subsingleton.intro [u])
    unless res.isEmpty do
      throwError "failed to close goal"
    pure true
  catch _ =>
    pure false

/-- apply `congr` after trying to close goal, optionally return result if successful -/
def congrStep? (mvar: MVarId) : MetaM (Option (List MVarId)) := do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let closed  ← tryCloseGoal mvar
  if !closed then
    try
      let res ←  Meta.apply mvar (mkConst ``congr [u, v])
      return some res
    catch e =>
      pure none
  else
    pure none

/-- recursively apply congr and try to close goals, not an error if tactics fail -/
partial def recCongr(maxDepth? : Option Nat)(mvar: MVarId) : MetaM (List MVarId) := do
  let closeOnly : Bool := (maxDepth?.map (fun n => decide (n ≤  1))).getD false
  if closeOnly then
    let  chk ← tryCloseGoal mvar
    if chk then return [] else return [mvar]
  let res ← congrStep? mvar
  match res with
  | some [] => return []
  | some xs => do
    let depth? := maxDepth?.map (fun n => n - 1)
    let groups ← xs.mapM (recCongr depth?)
    return groups.bind id
  | none => return [mvar]

/-- apply `congr` and then continue recursively; error if first application fails -/
def Meta.congr(maxDepth? : Option Nat)(mvar : MVarId) : MetaM (List MVarId) := do
  try
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let xs ← Meta.apply mvar (mkConst ``congr [u, v])
    let groups ← xs.mapM (recCongr maxDepth?)
    return groups.bind id
  catch e =>
    throwTacticEx `congr mvar e.toMessageData

open Lean.Elab.Tactic

syntax (name := congrBase) "congr_base" (ppSpace (colGt num))? : tactic

/--
The `congr` tactic attempts to identify both sides of an equality goal `A = B`, leaving as new goals the subterms of `A` and `B` which are not definitionally equal. Example: suppose the goal is `x * f y = g w * f z`. Then congr will produce two goals: `x = g w` and `y = z`.

If `x y : t`, and an instance subsingleton t is in scope, then any goals of the form `x = y` are solved automatically.

The `congr` tactic, but takes an optional argument which gives
the depth of recursive applications.
* This is useful when `congr` without a depth bound is too aggressive in breaking down the goal.
* For example, given `⊢ f (g (x + y)) = f (g (y + x))`, `congr'` produces the goals `⊢ x = y`
  and `⊢ y = x`, while `congr' 2` produces the intended `⊢ x + y = y + x`.
* If, at any point, a subgoal matches a hypothesis then the subgoal will be closed.
-/
@[tactic congrBase] def congrTacticImpl : Tactic := fun stx =>
match stx with
| `(tactic|congr_base $(x?)?) =>
  withMainContext do
    let x? := x?.map <| fun card => (Syntax.isNatLit? card).get!
    liftMetaTactic (Meta.congr x?)
| _ => throwIllFormedSyntax

-- TODO: use `ext` not `ext1`
macro_rules
| `(tactic| congr $(x?)?) => do
    `(tactic|congr_base $(x?)?)
| `(tactic| congr $(x?)? with $xs) => do
    `(tactic| focus (congr_base $(x?)?; ext1 $xs))

example (x y w: Nat)(f g: Nat → Nat): x * f y = g w * f z := by
  congr
  have : x = g w := sorry
  assumption
  have : y = z := sorry
  assumption

example (x y : Nat)(f g: Nat → Nat): f (g (x + y)) = f (g (y + x)) := by
  congr 2
  have : x + y = y + x := sorry
  assumption
