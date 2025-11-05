/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Batteries.Lean.HashMap
import Mathlib.Tactic.Linarith.Datatypes

/-!
# The Fourier-Motzkin elimination procedure

The Fourier-Motzkin procedure is a variable elimination method for linear inequalities.
<https://en.wikipedia.org/wiki/Fourier%E2%80%93Motzkin_elimination>

Given a set of linear inequalities `comps = {tᵢ Rᵢ 0}`,
we aim to eliminate a single variable `a` from the set.
We partition `comps` into `comps_pos`, `comps_neg`, and `comps_zero`,
where `comps_pos` contains the comparisons `tᵢ Rᵢ 0` in which
the coefficient of `a` in `tᵢ` is positive, and similar.

For each pair of comparisons `tᵢ Rᵢ 0 ∈ comps_pos`, `tⱼ Rⱼ 0 ∈ comps_neg`,
we compute coefficients `vᵢ, vⱼ ∈ ℕ` such that `vᵢ*tᵢ + vⱼ*tⱼ` cancels out `a`.
We collect these sums `vᵢ*tᵢ + vⱼ*tⱼ R' 0` in a set `S` and set `comps' = S ∪ comps_zero`,
a new set of comparisons in which `a` has been eliminated.

Theorem: `comps` and `comps'` are equisatisfiable.

We recursively eliminate all variables from the system. If we derive an empty clause `0 < 0`,
we conclude that the original system was unsatisfiable.
-/

open Batteries
open Std (format ToFormat TreeSet)

namespace Std.TreeSet

variable {α : Type*} {cmp}

/--
`O(n₂ * log (n₁ + n₂))`. Merges the maps `t₁` and `t₂`.
If equal keys exist in both, the key from `t₂` is preferred.
-/
def union (t₁ t₂ : TreeSet α cmp) : TreeSet α cmp :=
  t₂.foldl .insert t₁

instance : Union (TreeSet α cmp) := ⟨TreeSet.union⟩

/--
`O(n₁ * (log n₁ + log n₂))`. Constructs the set of all elements of `t₁` that are not in `t₂`.
-/
def sdiff (t₁ t₂ : TreeSet α cmp) : TreeSet α cmp := t₁.filter (!t₂.contains ·)

instance : SDiff (TreeSet α cmp) := ⟨TreeSet.sdiff⟩

end Std.TreeSet

namespace Mathlib.Tactic.Linarith

/-!
### Datatypes

The `CompSource` and `PComp` datatypes are specific to the FM elimination routine;
they are not shared with other components of `linarith`.
-/

/--
`CompSource` tracks the source of a comparison.
The atomic source of a comparison is an assumption, indexed by a natural number.
Two comparisons can be added to produce a new comparison,
and one comparison can be scaled by a natural number to produce a new comparison.
-/
inductive CompSource : Type
  | assump : Nat → CompSource
  | add : CompSource → CompSource → CompSource
  | scale : Nat → CompSource → CompSource
deriving Inhabited

/--
Given a `CompSource` `cs`, `cs.flatten` maps an assumption index
to the number of copies of that assumption that appear in the history of `cs`.

For example, suppose `cs` is produced by scaling assumption 2 by 5,
and adding to that the sum of assumptions 1 and 2.
`cs.flatten` maps `1 ↦ 1, 2 ↦ 6`.
-/
def CompSource.flatten : CompSource → Std.HashMap Nat Nat
  | (CompSource.assump n) => (∅ : Std.HashMap Nat Nat).insert n 1
  | (CompSource.add c1 c2) =>
      (CompSource.flatten c1).mergeWith (fun _ b b' => b + b') (CompSource.flatten c2)
  | (CompSource.scale n c) => (CompSource.flatten c).map (fun _ v => v * n)

/-- Formats a `CompSource` for printing. -/
def CompSource.toString : CompSource → String
  | (CompSource.assump e) => ToString.toString e
  | (CompSource.add c1 c2) => CompSource.toString c1 ++ " + " ++ CompSource.toString c2
  | (CompSource.scale n c) => ToString.toString n ++ " * " ++ CompSource.toString c

instance : ToFormat CompSource :=
  ⟨fun a => CompSource.toString a⟩

/--
A `PComp` stores a linear comparison `Σ cᵢ*xᵢ R 0`,
along with information about how this comparison was derived.
The original expressions fed into `linarith` are each assigned a unique natural number label.
The *historical set* `PComp.history` stores the labels of expressions
that were used in deriving the current `PComp`.
Variables are also indexed by natural numbers. The sets `PComp.effective`, `PComp.implicit`,
and `PComp.vars` contain variable indices.
* `PComp.vars` contains the variables that appear in any inequality in the historical set.
* `PComp.effective` contains the variables that have been effectively eliminated from `PComp`.
  A variable `n` is said to be *effectively eliminated* in `p : PComp` if the elimination of `n`
  produced at least one of the ancestors of `p` (or `p` itself).
* `PComp.implicit` contains the variables that have been implicitly eliminated from `PComp`.
  A variable `n` is said to be *implicitly eliminated* in `p` if it satisfies the following
  properties:
  - `n` appears in some inequality in the historical set (i.e. in `p.vars`).
  - `n` does not appear in `p.c.vars` (i.e. it has been eliminated).
  - `n` was not effectively eliminated.

We track these sets in order to compute whether the history of a `PComp` is *minimal*.
Checking this directly is expensive, but effective approximations can be defined in terms of these
sets. During the variable elimination process, a `PComp` with non-minimal history can be discarded.
-/
structure PComp : Type where
  /-- The comparison `Σ cᵢ*xᵢ R 0`. -/
  c : Comp
  /-- We track how the comparison was constructed by adding and scaling previous comparisons,
  back to the original assumptions. -/
  src : CompSource
  /-- The set of original assumptions which have been used in constructing this comparison. -/
  history : TreeSet ℕ Ord.compare
  /-- The variables which have been *effectively eliminated*,
  i.e. by running the elimination algorithm on that variable. -/
  effective : TreeSet ℕ Ord.compare
  /-- The variables which have been *implicitly eliminated*.
  These are variables that appear in the historical set,
  do not appear in `c` itself, and are not in `effective. -/
  implicit : TreeSet ℕ Ord.compare
  /-- The union of all variables appearing in those original assumptions
  which appear in the `history` set. -/
  vars : TreeSet ℕ Ord.compare

/--
Any comparison whose history is not minimal is redundant,
and need not be included in the new set of comparisons.
`elimedGE : ℕ` is a natural number such that all variables with index ≥ `elimedGE` have been
removed from the system.

This test is an overapproximation to minimality. It gives necessary but not sufficient conditions.
If the history of `c` is minimal, then `c.maybeMinimal` is true,
but `c.maybeMinimal` may also be true for some `c` with non-minimal history.
Thus, if `c.maybeMinimal` is false, `c` is known not to be minimal and must be redundant.
See https://doi.org/10.1016/B978-0-444-88771-9.50019-2 (Theorem 13).
The condition described there considers only implicitly eliminated variables that have been
officially eliminated from the system. This is not the case for every implicitly eliminated
variable. Consider eliminating `z` from `{x + y + z < 0, x - y - z < 0}`. The result is the set
`{2*x < 0}`; `y` is implicitly but not officially eliminated.

This implementation of Fourier-Motzkin elimination processes variables in decreasing order of
indices. Immediately after a step that eliminates variable `k`, variable `k'` has been eliminated
iff `k' ≥ k`. Thus we can compute the intersection of officially and implicitly eliminated variables
by taking the set of implicitly eliminated variables with indices ≥ `elimedGE`.
-/
def PComp.maybeMinimal (c : PComp) (elimedGE : ℕ) : Bool :=
  c.history.size ≤ 1 + ((c.implicit.filter (· ≥ elimedGE)).union c.effective).size

/--
The `src : CompSource` field is ignored when comparing `PComp`s. Two `PComp`s proving the same
comparison, with different sources, are considered equivalent.
-/
def PComp.cmp (p1 p2 : PComp) : Ordering := p1.c.cmp p2.c

/-- `PComp.scale c n` scales the coefficients of `c` by `n` and notes this in the `CompSource`. -/
def PComp.scale (c : PComp) (n : ℕ) : PComp :=
  { c with c := c.c.scale n, src := c.src.scale n }

/--
`PComp.add c1 c2 elimVar` creates the result of summing the linear comparisons `c1` and `c2`,
during the process of eliminating the variable `elimVar`.
The computation assumes, but does not enforce, that `elimVar` appears in both `c1` and `c2`
and does not appear in the sum.
Computing the sum of the two comparisons is easy; the complicated details lie in tracking the
additional fields of `PComp`.
* The historical set `pcomp.history` of `c1 + c2` is the union of the two historical sets.
* `vars` is the union of `c1.vars` and `c2.vars`.
* The effectively eliminated variables of `c1 + c2` are the union of the two effective sets,
  with `elim_var` inserted.
* The implicitly eliminated variables of `c1 + c2` are those that appear in
  `vars` but not `c.vars` or `effective`.
(Note that the description of the implicitly eliminated variables of `c1 + c2` in the algorithm
described in Section 6 of https://doi.org/10.1016/B978-0-444-88771-9.50019-2 seems to be wrong:
that says it should be `(c1.implicit.union c2.implicit).sdiff explicit`.
Since the implicitly eliminated sets start off empty for the assumption,
this formula would leave them always empty.)
-/
def PComp.add (c1 c2 : PComp) (elimVar : ℕ) : PComp :=
  let c := c1.c.add c2.c
  let src := c1.src.add c2.src
  let history := c1.history.union c2.history
  let vars := c1.vars.union c2.vars
  let effective := (c1.effective.union c2.effective).insert elimVar
  let implicit := (vars.sdiff (.ofList c.vars _)).sdiff effective
  ⟨c, src, history, effective, implicit, vars⟩

/--
`PComp.assump c n` creates a `PComp` whose comparison is `c` and whose source is
`CompSource.assump n`, that is, `c` is derived from the `n`th hypothesis.
The history is the singleton set `{n}`.
No variables have been eliminated (effectively or implicitly).
-/
def PComp.assump (c : Comp) (n : ℕ) : PComp where
  c := c
  src := CompSource.assump n
  history := {n}
  effective := .empty
  implicit := .empty
  vars := .ofList c.vars _

instance : ToFormat PComp :=
  ⟨fun p => format p.c.coeffs ++ toString p.c.str ++ "0"⟩

instance : ToString PComp :=
  ⟨fun p => toString p.c.coeffs ++ toString p.c.str ++ "0"⟩

/-- A collection of comparisons. -/
abbrev PCompSet := TreeSet PComp PComp.cmp

/-! ### Elimination procedure -/

/-- If `c1` and `c2` both contain variable `a` with opposite coefficients,
produces `v1` and `v2` such that `a` has been cancelled in `v1*c1 + v2*c2`. -/
def elimVar (c1 c2 : Comp) (a : ℕ) : Option (ℕ × ℕ) :=
  let v1 := c1.coeffOf a
  let v2 := c2.coeffOf a
  if v1 * v2 < 0 then
    let vlcm := Nat.lcm v1.natAbs v2.natAbs
    some ⟨vlcm / v1.natAbs, vlcm / v2.natAbs⟩
  else none

/--
`pelimVar p1 p2` calls `elimVar` on the `Comp` components of `p1` and `p2`.
If this returns `v1` and `v2`, it creates a new `PComp` equal to `v1*p1 + v2*p2`,
and tracks this in the `CompSource`.
-/
def pelimVar (p1 p2 : PComp) (a : ℕ) : Option PComp := do
  let (n1, n2) ← elimVar p1.c p2.c a
  return (p1.scale n1).add (p2.scale n2) a

/--
A `PComp` represents a contradiction if its `Comp` field represents a contradiction.
-/
def PComp.isContr (p : PComp) : Bool := p.c.isContr

/--
`elimWithSet a p comps` collects the result of calling `pelimVar p p' a`
for every `p' ∈ comps`.
-/
def elimWithSet (a : ℕ) (p : PComp) (comps : PCompSet) : PCompSet :=
  comps.foldl (fun s pc =>
  match pelimVar p pc a with
  | some pc => if pc.maybeMinimal a then s.insert pc else s
  | none => s) TreeSet.empty

/--
The state for the elimination monad.
* `maxVar`: the largest variable index that has not been eliminated.
* `comps`: a set of comparisons

The elimination procedure proceeds by eliminating variable `v` from `comps` progressively
in decreasing order.
-/
structure LinarithData : Type where
  /-- The largest variable index that has not been (officially) eliminated. -/
  maxVar : ℕ
  /-- The set of comparisons. -/
  comps : PCompSet

/--
The linarith monad extends an exceptional monad with a `LinarithData` state.
An exception produces a contradictory `PComp`.
-/
abbrev LinarithM : Type → Type :=
  StateT LinarithData (ExceptT PComp Lean.Core.CoreM)

/-- Returns the current max variable. -/
def getMaxVar : LinarithM ℕ :=
  LinarithData.maxVar <$> get

/-- Return the current comparison set. -/
def getPCompSet : LinarithM PCompSet :=
  LinarithData.comps <$> get

/-- Throws an exception if a contradictory `PComp` is contained in the current state. -/
def validate : LinarithM Unit := do
  match (← getPCompSet).toList.find? (fun p : PComp => p.isContr) with
  | none => return ()
  | some c => throwThe _ c

/--
Updates the current state with a new max variable and comparisons,
and calls `validate` to check for a contradiction.
-/
def update (maxVar : ℕ) (comps : PCompSet) : LinarithM Unit := do
  StateT.set ⟨maxVar, comps⟩
  validate

/--
`splitSetByVarSign a comps` partitions the set `comps` into three parts.
* `pos` contains the elements of `comps` in which `a` has a positive coefficient.
* `neg` contains the elements of `comps` in which `a` has a negative coefficient.
* `notPresent` contains the elements of `comps` in which `a` has coefficient 0.

Returns `(pos, neg, notPresent)`.
-/
def splitSetByVarSign (a : ℕ) (comps : PCompSet) : PCompSet × PCompSet × PCompSet :=
  comps.foldl (fun ⟨pos, neg, notPresent⟩ pc =>
    let n := pc.c.coeffOf a
    if n > 0 then ⟨pos.insert pc, neg, notPresent⟩
    else if n < 0 then ⟨pos, neg.insert pc, notPresent⟩
    else ⟨pos, neg, notPresent.insert pc⟩)
    ⟨TreeSet.empty, TreeSet.empty, TreeSet.empty⟩

/--
`elimVarM a` performs one round of Fourier-Motzkin elimination, eliminating the variable `a`
from the `linarith` state.
-/
def elimVarM (a : ℕ) : LinarithM Unit := do
  let vs ← getMaxVar
  if (a ≤ vs) then
    Lean.Core.checkSystem decl_name%.toString
    let ⟨pos, neg, notPresent⟩ := splitSetByVarSign a (← getPCompSet)
    update (vs - 1) (← pos.foldlM (fun s p => do
      Lean.Core.checkSystem decl_name%.toString
      pure (s.union (elimWithSet a p neg))) notPresent)
  else
    pure ()

/--
`elimAllVarsM` eliminates all variables from the linarith state, leaving it with a set of
ground comparisons. If this succeeds without exception, the original `linarith` state is consistent.
-/
def elimAllVarsM : LinarithM Unit := do
  for i in (List.range ((← getMaxVar) + 1)).reverse do
    elimVarM i

/--
`mkLinarithData hyps vars` takes a list of hypotheses and the largest variable present in
those hypotheses. It produces an initial state for the elimination monad.
-/
def mkLinarithData (hyps : List Comp) (maxVar : ℕ) : LinarithData :=
  ⟨maxVar, .ofList (hyps.mapIdx fun n cmp => PComp.assump cmp n) _⟩

/-- An oracle that uses Fourier-Motzkin elimination. -/
def CertificateOracle.fourierMotzkin : CertificateOracle where
  produceCertificate hyps maxVar := do
    let linarithData := mkLinarithData hyps maxVar
    let result ←
      (ExceptT.run (StateT.run (do validate; elimAllVarsM : LinarithM Unit) linarithData) :)
    match result with
    | (Except.ok _) => failure
    | (Except.error contr) => return contr.src.flatten

end Mathlib.Tactic.Linarith
