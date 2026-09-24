/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Core

/-!
# The `inclusion` tactic

The primary function of the inclusion tactic is as follows: given an expression `e` (for example
the type of a goal), compute an inclusion expression for `e`:

(In `Inclusion/Core/Types`)

```lean
structure ExprInclusion where
  inclusion : Expr
  proof : Expr
```

where `inclusion` is some expression that is built up of some kernel-computation-friendly
expressions in some kernel-computation-friendly type, and `proof` is a proof of `e ∈ inclusion`.

Since `inclusion` itself is meant to live in some kernel-computation-friendly type, we need a way
to interpret `inclusion` as a set in the type of `e`. That is the idea behind the following class:

(In `Inclusion/Core/ToSet`)

```lean
class ToSet (Iα : Type*) (α : outParam Type*) where
  toSet : Iα → Set α
```

Examples can be things like "intervals with dyadic endpoints" to sets of `ℝ`, "vectors of
intervals of dyadic endpoints" to sets of `ℝⁿ`, "balls with a dyadic complex center and dyadic
radius" to sets of `ℂ`, etc.

The most important example, however, is `IntervalBool` to `Prop`:

```lean
def IntervalBool.toPropSet : IntervalBool → Set Prop
  | true => {True}
  | false => {False}
  | undetermined => {True, False}

instance : ToSet IntervalBool Prop := ⟨IntervalBool.toPropSet⟩
```

Using this, the tactic can generate an inclusion expression for a goal like `x ^ 2 + 1 < 5`, and
then the proof of the goal is `proof` that `(x ^ 2 + 1 < 5) ∈ inclusion` along with a proof by
reflection that `inclusion = IntervalBool.true`.

## Constructing `ExprInclusion`s

`ExprInclusion`s are constructed in two phases which take place inside two different monads. The
first phase takes place in the `InclusionM` monad and is to construct an inclusion body:

(In `Inclusion/Core/Types`)

```lean
structure ExprInclusionBody where
  inclusionBody : Expr
  proofBody : Expr
```

which is the same as `ExprInclusion` except that `inclusionBody` is allowed to have "free `IVar`s
(inclusion variables)" (see the structure `IVar` in `Inclusion/Core/Types`) which represent "atomic"
variables whose initial value will be determined by hypotheses in the local context (in the next
phase). As an example, if we are applying the `inclusion` tactic to the goal
`(x : ℝ) + 1 ≤ 5` then (depending on which extensions we have enabled) we might have that `x` is
made into an `IVar`, which contains the expression of a placeholder variable `I` (which could be of
type `Interval Dyadic` for example) and a placeholder hypothesis `x ∈ I`. For technical reasons
these variables are synthetic opaque metavariables rather than free variables.

Remark: The technical reason that `IVar`s use synthetic opaque metavariables is that metavariables
are stored in the state of `MetaM` and are mutable. Free variables are stored in the local context
and are not mutable. Since the tactic constructs `IVar`s during the `InclusionM` phase and doesn't
know how many `IVars` there are or what they will be, it makes it difficult to use free variables.

The `InclusionM` phase uses inclusion extensions:

(In `Inclusion/Core/Extensions`)

```lean
structure InclusionExt where
  declName : Name := by exact decl_name%
  family : Name
  userName : Name := declName
  derive (e : Expr) : InclusionM ExprInclusionBody
  priority : Nat := eval_prio default
```

which belong to families (for example `interval_dyadic_real` containing extensions involving
computations as intervals of dyadics as inclusions for operations on the reals) and are registered
under discrimination tree keys which determine which expressions they match on (and thus can
possibly apply to).

The main driver of this phase is the function `mkExprInclusionBody`
(in `Inclusion/Core/Inclusion`) which collects all the extensions (from enabled families) that match
the current expression `e`, sorts them in order of priority, and then tries applying their `derive`
to `e` until one succeeds in producing an `ExprInclusionBody`. The expectation is that if
`derive e` succeeds it should produce a valid `ExprInclusionBody` for `e` and the metadata in the
`InclusionM` monad should be up to date. Many `derive`s will recursively call
`mkExprInclusionBody`; for example, you would expect that the extension which matches
`e := e1 ≤ e2` will call `mkExprInclusionBody` on `e1` and `e2` and then combine the results to
produce the `ExprInclusionBody` for `e`.

The second phase takes place in the `HypothesisM` monad. In this phase, initial inclusion
expressions for each `IVar` appearing in the `ExprInclusionBody` (constructed in the previous phase)
are derived from hypotheses in the local context. Then these hypotheses are used to "close" the
body and construct the final `ExprInclusion`. If an `IVar` has an enabled `cover` it is used to
"divide" the inclusion computation into checks on each of the smaller pieces, effectively creating
a refined inclusion function.

This phase uses hypothesis extensions:

(In `Inclusion/Core/Extensions`)

```lean
structure HypothesisExt where
  declName : Name := by exact decl_name%
  family : Name
  userName : Name := declName
  derive (h : Expr) : HypothesisM Unit
  priority : Nat := eval_prio default
```

which also belong to families and are registered under discrimination tree keys just like
`InclusionExt`s. Here, though, `derive h` generates inclusion hypotheses from a local hypothesis `h`
and puts them into the state of `HypothesisM`. The main driver for this phase is `collectHyps`
(in `Inclusion/Core/Inclusion`) which loops over all local declarations `h`, finds all hypothesis
extensions matching the type of `h`, and then tries each of their `derive` functions. The changes
made by a failed extension are rolled back, while every successful extension is allowed to add one
or more inclusion hypotheses.

## Params

It is convenient to allow `InclusionExt`s and `HypothesisExt`s to depend on shared parameters
which can be set by the user:

(In `Inclusion/Core/Extensions`)

```lean
structure InclusionParamDecl where
  name : Name
  type : Expr
  defaultValue? : Option Expr := none
```

The two examples in the current PR are:

* `prec`: which sets the dyadic precision (in bits) that each extension should use.
* `binSplit`: which sets the depth of binary interval splitting for each `IVar`.

These can be set by the user when calling the tactic like:

`inclusion [core, interval_dyadic_real, prec := 20, binSplit := 3]`

Two additional features which are not present in the current PR (and will require a bit of
refactoring) which will be added later are:

1. The ability to set "local" params. An important example being you may only want to set
   binary splitting on one specific variable (since doing it on each grows the number of cases
   exponentially).

2. The ability for `inclusion?` to "search" for optimal parameters using a compiled `ExprInclusion`
   function. To be maximally efficient these will have to be restricted to specific types (maybe
   just Nats) so that the function can be compiled once and used repeatedly.

## Writing Extensions

One can directly write inclusion and hypothesis extensions like:

```lean
@[inclusion_ext (_ : ℝ)]
meta def mkRealIVar : InclusionExt :=
  mkNDIVarExt `interval_dyadic_real
    ⟨q(ℝ), q(Interval Dyadic), q(instToSetIntervalDyadicReal)⟩ mkBinarySplitCover
```

```lean
@[hypothesis_ext _ ∧ _]
meta def andHyp : HypothesisExt where
  family := `core
  derive h := do
    let (``And, #[_, _]) := (← instantiateMVars (← inferType h)).getAppFnArgs | failure
    runHypothesisExts (← mkAppM ``And.left #[h])
    runHypothesisExts (← mkAppM ``And.right #[h])
```

where each expression supplied to `inclusion_ext` or `hypothesis_ext` is elaborated and then
converted into a `DiscrTree` key that the extension matches on.

However it is up to the extender to make sure both that the extension is deriving the right
inclusion body or hypotheses and is correctly maintaining the state of the current monad. This
approach to writing extensions gives significant flexibility but also could be highly error-prone.
Just like `MetaM` has both lots of low-level functions that are capable of breaking things and
should usually be avoided, as well as higher-level functions that are meant to be safer for tactic
writers to use, `Inclusion/ExtensionAPI` is meant to provide functions that extenders can use which
maintain the invariants expected by the `InclusionM` or `HypothesisM` monad. Most of these are
currently in `Inclusion/ExtensionAPI/Basic`. I expect many more to be added as the tactic develops.

The rules for `InclusionM` are:

* When an `InclusionExt` succeeds on an expression `e`, it must return an `ExprInclusionBody` whose
  `proofBody` proves `e ∈ inclusionBody` using a `ToSet` instance.
* Every inclusion-variable placeholder in the returned body must belong to an `IVar` registered in
  `InclusionM.State`. Its `setVar` must have the registered set type, and its `hypVar` must prove
  that its associated expression belongs to `setVar` using the registered `ToSet` instance.
* Every registered `IVar` must be well-formed in the initial local context. If it has a cover, the
  cover expression must have the corresponding `Cover` type.
* The returned body must not depend on untracked metavariables or temporary free variables
  introduced while running the extension.

The rules for `HypothesisM` are:

* Every inclusion hypothesis added by a `HypothesisExt` must be associated with an existing `IVar`.
* Each added `ExprInclusionBody` must have the same element type, set type, and `ToSet` instance as
  that `IVar`. Its `proofBody` must prove that the associated expression belongs to its
  `inclusionBody`.
* An added `inclusionBody` must not contain unresolved inclusion-variable placeholders.

But for certain `InclusionExt`s or `HypothesisExt`s that fit a (very specific) mold, there is an
API for defining extensions that doesn't even require metaprogramming. Instead you add an attribute
to a theorem which must be formatted in a specific way. We give these a special name
`InclusionOp`s and `HypothesisOp`s. Here are some examples:

```lean
@[inclusion_op interval_dyadic_real]
theorem add_mem {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J) :
    x + y ∈ I.add J :=
  Interval.add_mem Dyadic.toRealAddMonoidHom hx hy
```

```lean
@[hypothesis_op interval_dyadic_real]
theorem Iic_mem_of_le {x y : ℝ} {I : Interval Dyadic} (hxy : x ≤ y) (hy : y ∈ I) :
    x ∈ Interval.Iic I.ub :=
  Interval.mem_Iic_of_le hxy hy
```

The rules for `InclusionOp`s are:

* The theorem must conclude with an inclusion `e ∈ I` using a `ToSet` instance. The expression
  `e` becomes the discrimination-tree pattern, while `I` becomes the resulting inclusion body.
* Every hypothesis of the form `x ∈ X` using a `ToSet` instance is treated as a recursive input.
  Both `x` and `X` must be theorem variables, and `x` must occur in `e`. The generated extension
  recursively constructs an inclusion body for `x`, then substitutes its inclusion and proof for
  `X` and the hypothesis.
* To use a registered inclusion parameter, the theorem must have an argument with the same name and
  type as that parameter. The generated extension supplies its current value. The parameter may
  occur in `I`, but it may not occur in `e`.
* All remaining theorem arguments must be determined by matching the theorem or by typeclass
  synthesis.

The rules for `HypothesisOp`s are:

* The theorem must conclude with an inclusion `e ∈ I` using a `ToSet` instance.
* The theorem must have exactly one explicit proposition hypothesis which is not itself an
  inclusion. This hypothesis is the source hypothesis, and its type becomes the discrimination-tree
  pattern. Its proof may not occur in `e` or `I`.
* Every hypothesis of the form `x ∈ X` using a `ToSet` instance is treated as a recursive input.
  Both `x` and `X` must be theorem variables, and `x` must occur in the source hypothesis. The
  generated extension recursively constructs a closed inclusion body for `x`, then substitutes its
  inclusion and proof for `X` and the hypothesis.
* When the generated extension runs, `e` must be the expression associated with an existing `IVar`.
  The extension adds `I` as an inclusion hypothesis for that `IVar`.
* To use a registered inclusion parameter, the theorem must have an argument with the same name and
  type as that parameter. The generated extension supplies its current value. The parameter may
  occur in `I`, but it may not occur in the source hypothesis or `e`.
* All remaining theorem arguments must be determined by matching the theorem or by typeclass
  synthesis.

-/

public meta section

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

namespace Inclusion

/-- Configuration elaborator for the `inclusion` tactic. -/
declare_config_elab elabInclusionConfig InclusionConfig where
  omit paramSettings, families

/-- Families and parameters for the `inclusion` tactic -/
syntax inclusionArg := ident (" := " term)?

/-- Collect the enabled inclusion families and user-set parameter values. -/
def collectInclusionArgs (argStxs : Array Syntax) : TacticM InclusionConfig := do
  let mut paramSettings : NameMap Expr := {}
  let mut families := #[]
  let params := inclusionParamExt.getState (← getEnv)
  for argStx in argStxs do
    match argStx with
    | `(inclusionArg| $familyStx:ident) =>
      let family := familyStx.getId.eraseMacroScopes
      unless families.contains family do
        unless (← getInclusionFamily? family).isSome do
          throwError "Unknown inclusion family `{family}`"
        families := families.push family
    | `(inclusionArg| $nameStx:ident := $valueStx:term) =>
      let name := nameStx.getId
      let some decl := params.find? name
        | throwError "Unknown inclusion parameter `{name}`"
      if paramSettings.contains name then
        throwError "Inclusion parameter `{name}` was specified more than once"
      let value ← elabTerm valueStx decl.type
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      paramSettings := paramSettings.insert name value
    | _ => throwUnsupportedSyntax
  if families.isEmpty then
    throwError "At least one inclusion family must be specified"
  return { paramSettings, families }

/-- `inclusion [fam₁, fam₂, ...]` is a low-level tactic for proving the main goal by reasoning
about the set inclusion operator `∈` using the *inclusion families* `fam₁`, `fam₂`, ...
The goal `⊢ P` is first transformed into `⊢ P ∈ {True}` and then each family defines forward-
and backward reasoning rules to replace the goal with a form suitable for checking by computation
in the kernel, in other words, something that can be solved `by decide`.

`inclusion` is very flexible and intended as a building block for other tactics with a more
specific ambition, for example `dyadic_interval`.

An inclusion family is declared using `registerInclusionFamily` and can be extended using the
`inclusion_op` and `hypothesis_op` attributes.
The `core` family provides reasoning about logical operators `∧`, `∨`, `¬` and `=`. This family
is recommented to be included by default.


* `inclusion [fam₁, x := e]` sets the parameter named `x` to the value of the term `e`.
  All the families in an `inclusion` call can access this parameter.
* `inclusion (config := cfg) [fam₁, ...]` uses `cfg : InclusionConfig` as configuration options.
  In particular:
  * `inclusion +native [fam₁, ...]` only uses evaluation, rather than kernel computation, to perform
    the final proof check. Warning: this adds the Lean compiler to the trusted codebase.
  * `inclusion +kernel [fam₁, ...]` only uses the kernel to perform the final proof check and skips
    the (usually faster) evaluation-based check beforehand.
-/
elab (name := inclusion) "inclusion" cfg:optConfig " [" args:inclusionArg,* "]" : tactic => do
  let options ← elabInclusionConfig cfg
  let config ← collectInclusionArgs args.getElems
  let config := { config with kernel := options.kernel, native := options.native }
  closeMainGoalUsing `inclusion fun goal _ => inclusionCore goal config

/-- `inclusion? [fam₁, ...]` is a proof writing aid that quickly checks if
`inclusion [fam₁, ...]` would close the goal, without doing the expensive kernel computation that
actually closes the goal. -/
elab (name := inclusion?) "inclusion?" " [" args:inclusionArg,* "]" : tactic => do
  let config ← collectInclusionArgs args.getElems
  withoutModifyingStateWithInfoAndMessages <| withMainContext do
    try
      discard <| inclusionCore (← getMainTarget) config
      logInfo "The inclusion check succeeded."
    catch err =>
      logError m!"The inclusion check failed:\n{err.toMessageData}"

end Inclusion
