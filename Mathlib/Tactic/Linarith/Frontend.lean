/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Control.Basic
import Mathlib.Tactic.Linarith.Verification
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm
import Mathlib.Tactic.Ring.Basic

/-!
# `linarith`: solving linear arithmetic goals

`linarith` is a tactic for solving goals with linear arithmetic.

Suppose we have a set of hypotheses in `n` variables
`S = {a₁x₁ + a₂x₂ + ... + aₙxₙ R b₁x₁ + b₂x₂ + ... + bₙxₙ}`,
where `R ∈ {<, ≤, =, ≥, >}`.
Our goal is to determine if the inequalities in `S` are jointly satisfiable, that is, if there is
an assignment of values to `x₁, ..., xₙ` such that every inequality in `S` is true.

Specifically, we aim to show that they are *not* satisfiable. This amounts to proving a
contradiction. If our goal is also a linear inequality, we negate it and move it to a hypothesis
before trying to prove `False`.

When the inequalities are over a dense linear order, `linarith` is a decision procedure: it will
prove `False` if and only if the inequalities are unsatisfiable. `linarith` will also run on some
types like `ℤ` that are not dense orders, but it will fail to prove `False` on some unsatisfiable
problems. It will run over concrete types like `ℕ`, `ℚ`, and `ℝ`, as well as abstract types that
are instances of `CommRing`, `LinearOrder` and `IsStrictOrderedRing`.

## Algorithm sketch

First, the inequalities in the set `S` are rearranged into the form `tᵢ Rᵢ 0`, where
`Rᵢ ∈ {<, ≤, =}` and each `tᵢ` is of the form `∑ cⱼxⱼ`.

`linarith` uses an untrusted oracle to search for a certificate of unsatisfiability.
The oracle searches for a list of natural number coefficients `kᵢ` such that `∑ kᵢtᵢ = 0`, where for
at least one `i`, `kᵢ > 0` and `Rᵢ = <`.

Given a list of such coefficients, `linarith` verifies that `∑ kᵢtᵢ = 0` using a normalization
tactic such as `ring`. It proves that `∑ kᵢtᵢ < 0` by transitivity, since each component of the sum
is either equal to, less than or equal to, or less than zero by hypothesis. This produces a
contradiction.

## Preprocessing

`linarith` does some basic preprocessing before running. Most relevantly, inequalities over natural
numbers are cast into inequalities about integers, and rational division by numerals is canceled
into multiplication. We do this so that we can guarantee the coefficients in the certificate are
natural numbers, which allows the tactic to solve goals over types that are not fields.

Preprocessors are allowed to branch, that is, to case split on disjunctions. `linarith` will succeed
overall if it succeeds in all cases. This leads to exponential blowup in the number of `linarith`
calls, and should be used sparingly. The default preprocessor set does not include case splits.

## Oracles

There are two oracles that can be used in `linarith` so far.

1. **Fourier-Motzkin elimination.**
  This technique transforms a set of inequalities in `n` variables to an equisatisfiable set in
  `n - 1` variables. Once all variables have been eliminated, we conclude that the original set was
  unsatisfiable iff the comparison `0 < 0` is in the resulting set.
  While performing this elimination, we track the history of each derived comparison. This allows us
  to represent any comparison at any step as a positive combination of comparisons from the original
  set. In particular, if we derive `0 < 0`, we can find our desired list of coefficients
  by counting how many copies of each original comparison appear in the history.
  This oracle was historically implemented earlier, and is sometimes faster on small states, but it
  has [bugs](https://github.com/leanprover-community/mathlib4/issues/2717) and cannot handle
  large problems. You can use it with `linarith (oracle := .fourierMotzkin)`.

2. **Simplex Algorithm (default).**
  This oracle reduces the search for a unsatisfiability certificate to some Linear Programming
  problem. The problem is then solved by a standard Simplex Algorithm. We use
  [Bland's pivot rule](https://en.wikipedia.org/wiki/Bland%27s_rule) to guarantee that the algorithm
  terminates.
  The default version of the algorithm operates with sparse matrices as it is usually faster. You
  can invoke the dense version by `linarith (oracle := .simplexAlgorithmDense)`.

## Implementation details

`linarith` homogenizes numerical constants: the expression `1` is treated as a variable `t₀`.

Often `linarith` is called on goals that have comparison hypotheses over multiple types. This
creates multiple `linarith` problems, each of which is handled separately; the goal is solved as
soon as one problem is found to be contradictory.

Disequality hypotheses `t ≠ 0` do not fit in this pattern. `linarith` will attempt to prove equality
goals by splitting them into two weak inequalities and running twice. But it does not split
disequality hypotheses, since this would lead to a number of runs exponential in the number of
disequalities in the context.

The oracle is very modular. It can easily be replaced with another function of type
`List Comp → ℕ → MetaM ((Std.HashMap ℕ ℕ))`,
which takes a list of comparisons and the largest variable
index appearing in those comparisons, and returns a map from comparison indices to coefficients.
An alternate oracle can be specified in the `LinarithConfig` object.

A variant, `nlinarith`, adds an extra preprocessing step to handle some basic nonlinear goals.
There is a hook in the `LinarithConfig` configuration object to add custom preprocessing routines.

The certificate checking step is *not* by reflection. `linarith` converts the certificate into a
proof term of type `False`.

Some of the behavior of `linarith` can be inspected with the option
`set_option trace.linarith true`.
However, both oracles mainly runs outside the tactic monad, so we cannot trace intermediate
steps there.

## File structure

The components of `linarith` are spread between a number of files for the sake of organization.

* `Lemmas.lean` contains proofs of some arithmetic lemmas that are used in preprocessing and in
  verification.
* `Datatypes.lean` contains data structures that are used across multiple files, along with some
  useful auxiliary functions.
* `Preprocessing.lean` contains functions used at the beginning of the tactic to transform
  hypotheses into a shape suitable for the main routine.
* `Parsing.lean` contains functions used to compute the linear structure of an expression.
* The `Oracle` folder contains files implementing the oracles that can be used to produce a
  certificate of unsatisfiability.
* `Verification.lean` contains the certificate checking functions that produce a proof of `False`.
* `Frontend.lean` contains the control methods and user-facing components of the tactic.

## Tags

linarith, nlinarith, lra, nra, Fourier-Motzkin, linear arithmetic, linear programming
-/

open Lean Elab Parser Tactic Meta
open Batteries


namespace Mathlib.Tactic.Linarith

/-! ### Config objects

The config object is defined in the frontend, instead of in `Datatypes.lean`, since the oracles must
be in context to choose a default.

-/

section

/-- A configuration object for `linarith`. -/
structure LinarithConfig : Type where
  /-- Discharger to prove that a candidate linear combination of hypothesis is zero. -/
  -- TODO There should be a def for this, rather than calling `evalTactic`?
  discharger : TacticM Unit := do evalTactic (← `(tactic| ring1))
  -- We can't actually store a `Type` here,
  -- as we want `LinarithConfig : Type` rather than ` : Type 1`,
  -- so that we can define `elabLinarithConfig : Lean.Syntax → Lean.Elab.TermElabM LinarithConfig`.
  -- For now, we simply don't support restricting the type.
  -- (restrict_type : Option Type := none)
  /-- Prove goals which are not linear comparisons by first calling `exfalso`. -/
  exfalso : Bool := true
  /-- Transparency mode for identifying atomic expressions in comparisons. -/
  transparency : TransparencyMode := .reducible
  /-- Split conjunctions in hypotheses. -/
  splitHypotheses : Bool := true
  /-- Split `≠` in hypotheses, by branching in cases `<` and `>`. -/
  splitNe : Bool := false
  /-- If true, `linarith?` attempts to greedily remove unused hypotheses from its
  suggestion. -/
  minimize : Bool := true
  /-- Override the list of preprocessors. -/
  preprocessors : List GlobalBranchingPreprocessor := defaultPreprocessors
  /-- Specify an oracle for identifying candidate contradictions.
  `.simplexAlgorithmSparse`, `.simplexAlgorithmSparse`, and `.fourierMotzkin` are available. -/
  oracle : CertificateOracle := .simplexAlgorithmSparse

/--
`cfg.updateReducibility reduce_default` will change the transparency setting of `cfg` to
`default` if `reduce_default` is true. In this case, it also sets the discharger to `ring!`,
since this is typically needed when using stronger unification.
-/
def LinarithConfig.updateReducibility (cfg : LinarithConfig) (reduce_default : Bool) :
    LinarithConfig :=
  if reduce_default then
    { cfg with transparency := .default, discharger := do evalTactic (← `(tactic| ring1!)) }
  else cfg

end

/-! ### Control -/

/--
If `e` is a comparison `a R b` or the negation of a comparison `¬ a R b`, found in the target,
`getContrLemma e` returns the name of a lemma that will change the goal to an
implication, along with the type of `a` and `b`.

For example, if `e` is `(a : ℕ) < b`, returns ``(`lt_of_not_ge, ℕ)``.
-/
def getContrLemma (e : Expr) : MetaM (Name × Expr) := do
  match ← e.ineqOrNotIneq? with
  | (true, Ineq.lt, t, _) => pure (``lt_of_not_ge, t)
  | (true, Ineq.le, t, _) => pure (``le_of_not_gt, t)
  | (true, Ineq.eq, t, _) => pure (``eq_of_not_lt_of_not_gt, t)
  | (false, _, t, _) => pure (``Not.intro, t)

/--
`applyContrLemma` inspects the target to see if it can be moved to a hypothesis by negation.
For example, a goal `⊢ a ≤ b` can become `b < a ⊢ false`.
If this is the case, it applies the appropriate lemma and introduces the new hypothesis.
It returns the type of the terms in the comparison (e.g. the type of `a` and `b` above) and the
newly introduced local constant.
Otherwise returns `none`.
-/
def applyContrLemma (g : MVarId) : MetaM (Option (Expr × Expr) × MVarId) := do
  try
    let (nm, tp) ← getContrLemma (← withReducible g.getType')
    let [g] ← g.apply (← mkConst' nm) | failure
    let (f, g) ← g.intro1P
    return (some (tp, .fvar f), g)
  catch _ => return (none, g)

/-- A map of keys to values, where the keys are `Expr` up to defeq and one key can be
associated to multiple values. -/
abbrev ExprMultiMap α := Array (Expr × List α)

/-- Retrieves the list of values at a key, as well as the index of the key for later modification.
(If the key is not in the map it returns `self.size` as the index.) -/
def ExprMultiMap.find {α : Type} (self : ExprMultiMap α) (k : Expr) : MetaM (Nat × List α) := do
  for h : i in [:self.size] do
    let (k', vs) := self[i]
    if ← isDefEq k' k then
      return (i, vs)
  return (self.size, [])

/-- Insert a new value into the map at key `k`. This does a defeq check with all other keys
in the map. -/
def ExprMultiMap.insert {α : Type} (self : ExprMultiMap α) (k : Expr) (v : α) :
    MetaM (ExprMultiMap α) := do
  for h : i in [:self.size] do
    if ← isDefEq self[i].1 k then
      return self.modify i fun (k, vs) => (k, v::vs)
  return self.push (k, [v])

/--
`partitionByTypeIdx l` takes a list `l` of pairs `(h, i)` where `h` is a proof of a
comparison and `i` records the original position of `h`. The proofs are grouped by the
type of the variables appearing in the comparison, e.g. `(a : ℚ) < 1` and
`(b : ℤ) > c` will be separated. The resulting map associates each type with the
list of `(h, i)` pairs over that type.
-/
def partitionByTypeIdx (l : List (Expr × Nat)) : MetaM (ExprMultiMap (Expr × Nat)) :=
  l.foldlM (fun m ⟨h, i⟩ => do m.insert (← typeOfIneqProof h) (h, i)) #[]

/--
Given a list `ls` of pairs `(α, L)` where each `L` is a list of indexed proofs of
comparisons over the type `α`, `findLinarithContradiction cfg g ls` tries each list in
succession, invoking `linarith` until one produces a contradiction. It returns the
resulting proof of `False` together with the indices of the hypotheses that had
nonzero coefficients in the final certificate.
-/
def findLinarithContradiction (cfg : LinarithConfig) (g : MVarId)
    (ls : List (Expr × List (Expr × Nat))) : MetaM (Expr × List Nat) :=
  try
    ls.firstM (fun ⟨α, L⟩ =>
      withTraceNode `linarith (return m!"{exceptEmoji ·} running on type {α}") do
        let (pf, idxs) ←
          proveFalseByLinarith cfg.transparency cfg.oracle cfg.discharger g (L.map Prod.fst)
        let idxs := idxs.map fun i => L[i]!.2
        return (pf, idxs))
  catch e => throwError "linarith failed to find a contradiction\n{g}\n{e.toMessageData}"

/--
Given a list `hyps` of proofs of comparisons, `runLinarith cfg prefType g hyps` preprocesses
`hyps` according to the list of preprocessors in `cfg`. This results in a list of branches
(typically only one), each of which must succeed in order to close the goal.

In each branch, the hypotheses are partitioned by type and `linarith` is run on each class in
turn; one of these must succeed in order for `linarith` to succeed on the branch. If `prefType`
is provided, the corresponding class is tried first.

On success, the metavariable `g` is assigned and the function returns the indices of the
original hypotheses that were used with nonzero coefficient in the final proof.
-/
-- If it succeeds, the passed metavariable should have been assigned.
def runLinarith (cfg : LinarithConfig) (prefType : Option Expr) (g : MVarId)
    (hyps : List Expr) : MetaM (List Nat) := do
  let singleProcess (g : MVarId) (hyps : List (Expr × Nat)) : MetaM (Expr × List Nat) :=
    g.withContext do
      linarithTraceProofs
        s!"after preprocessing, linarith has {hyps.length} facts:" (hyps.map Prod.fst)
      let mut hyp_set ← partitionByTypeIdx hyps
      trace[linarith] "hypotheses appear in {hyp_set.size} different types"
      -- If we have a preferred type, strip it from `hyp_set` and prepare a handler with a custom
      -- trace message
      let pref : MetaM _ ← do
        if let some t := prefType then
          let (i, vs) ← hyp_set.find t
          hyp_set := hyp_set.eraseIdxIfInBounds i
          pure <|
            withTraceNode `linarith (return m!"{exceptEmoji ·} running on preferred type {t}") do
              let (pf, idxs) ←
                proveFalseByLinarith cfg.transparency cfg.oracle cfg.discharger g (vs.map Prod.fst)
              let idxs := idxs.map fun j => vs[j]!.2
              return (pf, idxs)
        else
          pure failure
      pref <|> findLinarithContradiction cfg g hyp_set.toList
  let mut preprocessors := cfg.preprocessors
  if cfg.splitNe then
    preprocessors := Linarith.removeNe :: preprocessors
  if cfg.splitHypotheses then
    preprocessors := Linarith.splitConjunctions.globalize.branching :: preprocessors
  let branches ← preprocess preprocessors g hyps
  let mut used : List Nat := []
  for (g, es) in branches do
    let esIdx := es.zipIdx
    let (r, idxs) ← singleProcess g esIdx
    g.assign r
    used := idxs ++ used
  -- Verify that we closed the goal. Failure here should only result from a bad `Preprocessor`.
  (Expr.mvar g).ensureHasNoMVars
  return used.eraseDups

-- /--
-- `filterHyps restr_type hyps` takes a list of proofs of comparisons `hyps`, and filters it
-- to only those that are comparisons over the type `restr_type`.
-- -/
-- def filterHyps (restr_type : Expr) (hyps : List Expr) : MetaM (List Expr) :=
--   hyps.filterM (fun h => do
--     let ht ← inferType h
--     match getContrLemma ht with
--     | some (_, htype) => isDefEq htype restr_type
--     | none => return false)

/--
`linarithUsedHyps only_on hyps cfg g` runs `linarith` with the supplied hypotheses. It
fails if the goal cannot be closed. When successful, it returns the subset of `hyps` that
were actually used (i.e. had a nonzero coefficient) in the final certificate.

* `hyps` is a list of proofs of comparisons to include in the search.
* If `only_on` is true, the search will be restricted to `hyps`. Otherwise it will use all
  comparisons in the local context.
* If `cfg.transparency := semireducible`,
  it will unfold semireducible definitions when trying to match atomic expressions.
-/
partial def linarithUsedHyps (only_on : Bool) (hyps : List Expr)
    (cfg : LinarithConfig := {}) (g : MVarId) : MetaM (List Expr) := g.withContext do
  -- if the target is an equality, we run `linarith` twice, to prove ≤ and ≥.
  if (← whnfR (← instantiateMVars (← g.getType))).isEq then
    trace[linarith] "target is an equality: splitting"
    if let some [g₁, g₂] ← try? (g.apply (← mkConst' ``eq_of_not_lt_of_not_gt)) then
      let h₁ ← withTraceNode `linarith (return m!"{exceptEmoji ·} proving ≥") <|
        linarithUsedHyps only_on hyps cfg g₁
      let h₂ ← withTraceNode `linarith (return m!"{exceptEmoji ·} proving ≤") <|
        linarithUsedHyps only_on hyps cfg g₂
      return h₁ ++ h₂

  /- If we are proving a comparison goal (and not just `False`), we consider the type of the
    elements in the comparison to be the "preferred" type. That is, if we find comparison
    hypotheses in multiple types, we will run `linarith` on the goal type first.
    In this case we also receive a new variable from moving the goal to a hypothesis.
    Otherwise, there is no preferred type and no new variable; we simply change the goal to `False`.
  -/

  let (g, target_type, new_var) ← match ← applyContrLemma g with
  | (none, g) =>
    if cfg.exfalso then
      trace[linarith] "using exfalso"
      pure (← g.exfalso, none, none)
    else
      pure (g, none, none)
  | (some (t, v), g) => pure (g, some t, some v)

  g.withContext do
    -- set up the list of hypotheses, considering the `only_on` and `restrict_type` options
    let hyps ←
      (if only_on then return new_var.toList ++ hyps
        else return (← getLocalHyps).toList ++ hyps)

    -- TODO in mathlib3 we could specify a restriction to a single type.
    -- I haven't done that here because I don't know how to store a `Type` in `LinarithConfig`.
    -- There's only one use of the `restrict_type` configuration option in mathlib3,
    -- and it can be avoided just by using `linarith only`.

    linarithTraceProofs "linarith is running on the following hypotheses:" hyps
    let usedIdxs ← runLinarith cfg target_type g hyps
    let used := usedIdxs.filterMap (hyps[·]?)
    let used := match new_var with
      | some nv => used.filter (fun h => !(h == nv))
      | none => used
    return used

/--
Run the core `linarith` procedure on the goal `g` using the hypotheses `hyps`.
If `only_on` is true, the search is restricted to `hyps`; otherwise all suitable
local hypotheses are considered. This is the workhorse behind the user-facing
`linarith` tactic.
-/
partial def linarith (only_on : Bool) (hyps : List Expr) (cfg : LinarithConfig := {})
    (g : MVarId) : MetaM Unit := do
  discard <| linarithUsedHyps only_on hyps cfg g

end Linarith

/-! ### User facing functions -/

open Syntax

/-- Syntax for the arguments of `linarith`, after the optional `!`. -/
syntax linarithArgsRest := optConfig (&" only")? (" [" term,* "]")?

/--
`linarith` attempts to find a contradiction between hypotheses that are linear (in)equalities.
Equivalently, it can prove a linear inequality by assuming its negation and proving `False`.

In theory, `linarith` should prove any goal that is true in the theory of linear arithmetic over
the rationals. While there is some special handling for non-dense orders like `Nat` and `Int`,
this tactic is not complete for these theories and will not prove every true goal. It will solve
goals over arbitrary types that instantiate `CommRing`, `LinearOrder` and `IsStrictOrderedRing`.

An example:
```lean
example (x y z : ℚ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0) : False := by
  linarith
```

`linarith` will use all appropriate hypotheses and the negation of the goal, if applicable.
Disequality hypotheses require case splitting and are not normally considered
(see the `splitNe` option below).

`linarith [t1, t2, t3]` will additionally use proof terms `t1, t2, t3`.

`linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
`h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.

`linarith!` will use a stronger reducibility setting to try to identify atoms. For example,
```lean
example (x : ℚ) : id x ≥ x := by
  linarith
```
will fail, because `linarith` will not identify `x` and `id x`. `linarith!` will.
This can sometimes be expensive.

`linarith (config := { .. })` takes a config object with five
optional arguments:
* `discharger` specifies a tactic to be used for reducing an algebraic equation in the
  proof stage. The default is `ring`. Other options include `simp` for basic
  problems.
* `transparency` controls how hard `linarith` will try to match atoms to each other. By default
  it will only unfold `reducible` definitions.
* If `splitHypotheses` is true, `linarith` will split conjunctions in the context into separate
  hypotheses.
* If `splitNe` is `true`, `linarith` will case split on disequality hypotheses.
  For a given `x ≠ y` hypothesis, `linarith` is run with both `x < y` and `x > y`,
  and so this runs linarith exponentially many times with respect to the number of
  disequality hypotheses. (`false` by default.)
* If `exfalso` is `false`, `linarith` will fail when the goal is neither an inequality nor `False`.
  (`true` by default.)
* If `minimize` is `false`, `linarith?` will report all hypotheses appearing in its initial
  proof without attempting to drop redundancies. (`true` by default.)
* `restrict_type` (not yet implemented in mathlib4)
  will only use hypotheses that are inequalities over `tp`. This is useful
  if you have e.g. both integer- and rational-valued inequalities in the local context, which can
  sometimes confuse the tactic.

A variant, `nlinarith`, does some basic preprocessing to handle some nonlinear goals.

The option `set_option trace.linarith true` will trace certain intermediate stages of the `linarith`
routine.
-/
syntax (name := linarith) "linarith" "!"? linarithArgsRest : tactic

/--
`linarith?` behaves like `linarith` but, on success, it prints a suggestion of
the form `linarith only [...]` listing a minimized set of hypotheses used in the
final proof.  Use `linarith?!` for the higher-reducibility variant and set the
`minimize` flag in the configuration to control whether greedy minimization is
performed.
-/
syntax (name := linarith?) "linarith?" "!"? linarithArgsRest : tactic

@[inherit_doc linarith] macro "linarith!" rest:linarithArgsRest : tactic =>
  `(tactic| linarith ! $rest:linarithArgsRest)
@[inherit_doc linarith?] macro "linarith?!" rest:linarithArgsRest : tactic =>
  `(tactic| linarith? ! $rest:linarithArgsRest)

/--
An extension of `linarith` with some preprocessing to allow it to solve some nonlinear arithmetic
problems. (Based on Coq's `nra` tactic.) See `linarith` for the available syntax of options,
which are inherited by `nlinarith`; that is, `nlinarith!` and `nlinarith only [h1, h2]` all work as
in `linarith`. The preprocessing is as follows:

* For every subterm `a ^ 2` or `a * a` in a hypothesis or the goal,
  the assumption `0 ≤ a ^ 2` or `0 ≤ a * a` is added to the context.
* For every pair of hypotheses `a1 R1 b1`, `a2 R2 b2` in the context, `R1, R2 ∈ {<, ≤, =}`,
  the assumption `0 R' (b1 - a1) * (b2 - a2)` is added to the context (non-recursively),
  where `R ∈ {<, ≤, =}` is the appropriate comparison derived from `R1, R2`.
-/
syntax (name := nlinarith) "nlinarith" "!"? linarithArgsRest : tactic
@[inherit_doc nlinarith] macro "nlinarith!" rest:linarithArgsRest : tactic =>
  `(tactic| nlinarith ! $rest:linarithArgsRest)

/-- Elaborate `t` in a way that is suitable for linarith. -/
def elabLinarithArg (tactic : Name) (t : Term) : TacticM Expr := Term.withoutErrToSorry do
  let (e, mvars) ← elabTermWithHoles t none tactic
  unless mvars.isEmpty do
    throwErrorAt t "Argument passed to {tactic} has metavariables:{indentD e}"
  return e

/--
Allow elaboration of `LinarithConfig` arguments to tactics.
-/
declare_config_elab elabLinarithConfig Linarith.LinarithConfig

elab_rules : tactic
  | `(tactic| linarith $[!%$bang]? $cfg:optConfig $[only%$o]? $[[$args,*]]?) => withMainContext do
    let args ← ((args.map (TSepArray.getElems)).getD {}).mapM (elabLinarithArg `linarith)
    let cfg := (← elabLinarithConfig cfg).updateReducibility bang.isSome
    commitIfNoEx do liftMetaFinishingTactic <| Linarith.linarith o.isSome args.toList cfg

elab_rules : tactic
  | `(tactic| linarith?%$tk $[!%$bang]? $cfg:optConfig $[only%$o]? $[[$args,*]]?) =>
      withMainContext do
        let args ← ((args.map (TSepArray.getElems)).getD {}).mapM (elabLinarithArg `linarith)
        let cfg := (← elabLinarithConfig cfg).updateReducibility bang.isSome
        let g ← getMainGoal
        let st ← saveState
        try
          let used₀ ← Linarith.linarithUsedHyps o.isSome args.toList cfg g
          -- Check that all used hypotheses are fvars (not arbitrary terms)
          if used₀.any (fun e => e.fvarId?.isNone) then
            throwError "linarith? currently only supports named hypothesis, not terms"
          let used ←
            if cfg.minimize then
              let rec minimize (hs : List Expr) (i : Nat) : TacticM (List Expr) := do
                if _h : i < hs.length then
                  let rest := hs.eraseIdx i
                  st.restore
                  try
                    let _ ← Linarith.linarith true rest cfg g
                    minimize rest i
                  catch _ => minimize hs (i+1)
                else
                  return hs
              minimize used₀ 0
            else
              pure used₀
          st.restore
          discard <| Linarith.linarith true used cfg g
          replaceMainGoal []
          -- TODO: we should check for, and deal with, shadowed names here.
          let idsList ← used.mapM fun e => do
            pure (Lean.mkIdent (← e.fvarId!.getUserName))
          let sugg ← `(tactic| linarith only [$(idsList.toArray),*])
          Lean.Meta.Tactic.TryThis.addSuggestion tk sugg
        catch e =>
          discard <| st.restore
          throw e

-- TODO restore this when `add_tactic_doc` is ported
-- add_tactic_doc
-- { name       := "linarith",
--   category   := doc_category.tactic,
--   decl_names := [`tactic.interactive.linarith],
--   tags       := ["arithmetic", "decision procedure", "finishing"] }

open Linarith

elab_rules : tactic
  | `(tactic| nlinarith $[!%$bang]? $cfg:optConfig $[only%$o]? $[[$args,*]]?) => withMainContext do
    let args ← ((args.map (TSepArray.getElems)).getD {}).mapM (elabLinarithArg `nlinarith)
    let cfg := (← elabLinarithConfig cfg).updateReducibility bang.isSome
    let cfg := { cfg with
      preprocessors := cfg.preprocessors.concat nlinarithExtras }
    commitIfNoEx do liftMetaFinishingTactic <| Linarith.linarith o.isSome args.toList cfg

-- TODO restore this when `add_tactic_doc` is ported
-- add_tactic_doc
-- { name       := "nlinarith",
--   category   := doc_category.tactic,
--   decl_names := [`tactic.interactive.nlinarith],
--   tags       := ["arithmetic", "decision procedure", "finishing"] }

end Mathlib.Tactic
