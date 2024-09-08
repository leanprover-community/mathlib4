/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Lean.Meta.RefinedDiscrTree.Lookup
import Mathlib.Lean.Meta.RefinedDiscrTree.Initialize

/-!
A discrimination tree for the purpose of unifying local expressions with library results.

This data structure is based on `Lean.Meta.DiscrTree` and `Lean.Meta.LazyDiscrTree`,
and includes many more features.
Comparing performance with `Lean.Meta.DiscrTree`, this version is a bit slower.
However in practice this does not matter, because a lookup in a discrimination tree is always
combined with `isDefEq` unification and these unifications are significantly more expensive,
so the extra lookup cost is neglegible, while better discrimination tree indexing, and thus
less potential matches can save a significant amount of computation.

## New features

- The keys `Key.lam`, `Key.forall` and `Key.bvar` have been introduced in order to allow for
  matching under lambda and forall binders. `Key.lam` has arity 1 and indexes the body.
  `Key.forall` has arity 2 and indexes the domain and the body. The reason for not indexing the
  domain of a lambda expression is that it is usually already determined, for example in
  `∃ a : α, p`, which is `@Exists α fun a : α => p`, we don't want to index the domain `α` twice.
  In a forall expression we should index the domain, because in an implication `p → q`
  we need to index both `p` and `q`. `Key.bvar` works the same as `Key.fvar`, but stores the
  De Bruijn index to identify it.

  For example, this allows for more specific matching with the left hand side of
  `∑ i in range n, i = n * (n - 1) / 2`, which is indexed by
  `[⟨Finset.sum, 5⟩, ⟨Nat, 0⟩, ⟨Nat, 0⟩, *0, ⟨Finset.Range, 1⟩, *1, λ, ⟨#0, 0⟩]`.

- The key `Key.star` takes a `Nat` identifier as an argument. For example,
  the library pattern `?a + ?a` is encoded as `@HAdd.hAdd *0 *0 *1 *2 *3 *3`.
  `*0` corresponds to the type of `a`, `*1` to the outParam of `HAdd.hAdd`,
  `*2` to the `HAdd` instance, and `*3` to `a`. This means that it will only match an expression
  `x + y` if `x` is definitionally equal to `y`. The matching algorithm requires
  that the same stars from the discrimination tree match with the same patterns
  in the lookup expression, and similarly requires that the same metavariables
  form the lookup expression match with the same pattern in the discrimination tree.

- We evaluate the matching score of a unification.
  This score represents the number of keys that had to be the same for the unification to succeed.
  For example, matching `(1 + 2) + 3` with `add_comm` gives a score of 2,
  since the pattern of commutativity is `@HAdd.hAdd *0 *0 *0 *1 *2 *3`: matching `HAdd.hAdd`
  gives 1 point, and matching `*0` again after its first appearence gives another point.
  Similarly, matching it with `add_assoc` gives a score of 5.

- Patterns that have the potential to be η-reduced are put into the `RefinedDiscrTree` under all
  possible reduced key sequences. This is for terms of the form `fun x => f (?m x₁ .. xₙ)`, where
  `?m` is a metavariable, and one of `x₁, .., xₙ` is `x`.
  For example, the pattern `Continuous fun y => Real.exp (f y)])` is indexed by
  both `@Continuous *0 ℝ *1 *2 (λ, Real.exp *3)`
  and  `@Continuous *0 ℝ *1 *2 Real.exp`
  so that it also comes up if you search with `Continuous Real.exp`.

- For sub-expressions not at the root of the original expression we have some additional reductions:
  - Any combination of `ofNat`, `Nat.zero`, `Nat.succ` and number literals
    is stored as just a number literal.
    This behaviour should be updated once the lean4 issue #2867 has been resolved.
  - The expression `fun a : α => a` is stored as `@id α`.
    - This makes lemmas such as `continuous_id'` redundant, which is the same as `continuous_id`,
      with `id` replaced by `fun x => x`.
  - Lambdas in front of number literals are removed. This is because usually `n : α → β` is
    defined to be `fun _ : α => n` for a number literal `n`. So instead of `λ, n` we store `n`.
  - Any expression with head constant `+`, `*`, `-`, `/`, `⁻¹`, `+ᵥ`, `•` or `^` is normalized to
    not have a lambda in front and to always have the default amount of arguments.
    e.g. `(f + g) a` is stored as `f a + g a` and `fun x => f x + g x` is stored as `f + g`.
    - This makes lemmas such as `MeasureTheory.integral_integral_add'` redundant, which is the
      same as `MeasureTheory.integral_integral_add`, with `f a + g a` replaced by `(f + g) a`
    - it also means that a lemma like `Continuous.mul` can be stated as talking about `f * g`
      instead of `fun x => f x * g x`.
    - When trying to find `Continuous.add` with the expression `Continuous fun x => 1 + x`,
      this is possible, because we first revert the eta-reduction that happens by default,
      and then distribute the lambda. Thus this is indexed as `Continuous (1 + id)`,
      which matches with `Continuous (f + g)` from `Continuous.add`.

- The key `Key.opaque` only matches with a `Key.star` key.
  Using the `WhnfCoreConfig` argument, we can disable β-reduction and ζ-reduction.
  As a result, we may get a lambda expression applied to an argument or a let-expression.
  Since there is no other support for indexing these, they will be indexed by `Key.opaque`.


## Lazy computation

We encode an `Expr` as an `Array Key`. This is implemented with a lazy computation:
we start with a `LazyEntry α`, which comes with a step function of type
`LazyEntry α → MetaM (Array (Key × LazyEntry α) ⊕ α)`.

-/

namespace Lean.Meta.RefinedDiscrTree

variable {α β : Type}

/-- Creates the core context used for initializing a tree using the current context. -/
private def treeCtx (ctx : Core.Context) : Core.Context := {
    fileName := ctx.fileName
    fileMap := ctx.fileMap
    options := ctx.options
    maxRecDepth := ctx.maxRecDepth
    maxHeartbeats := 0
    ref := ctx.ref
    diag := getDiag ctx.options
  }

/-- Returns candidates from all imported modules that match the expression. -/
def findImportMatches
    (ext : EnvExtension (IO.Ref (Option (RefinedDiscrTree α))))
    (addEntry : Name → ConstantInfo → MetaM (List (Key × LazyEntry α))) (ty : Expr)
    (constantsPerTask : Nat := 1000) (capacityPerTask : Nat := 128)
    (config : WhnfCoreConfig := {}) : MetaM (MatchResult α) := do
  let cctx ← (read : CoreM Core.Context)
  let ngen ← getNGen
  let (cNGen, ngen) := ngen.mkChild
  setNGen ngen
  let dummy : IO.Ref (Option (RefinedDiscrTree α)) ← IO.mkRef none
  let ref := @EnvExtension.getState _ ⟨dummy⟩ ext (← getEnv)
  let importTree ← (← ref.get).getDM do
    profileitM Exception  "lazy discriminator import initialization" (← getOptions) <|
      createImportedDiscrTree
        (treeCtx cctx) cNGen (← getEnv) addEntry constantsPerTask capacityPerTask config
  let (importCandidates, importTree) ← getMatch importTree ty false false
  ref.set (some importTree)
  return importCandidates

/--
Returns candidates from this module in this module that match the expression.

* `moduleRef` is a references to a lazy discriminator tree only containing
this module's definitions.
-/
def findModuleMatches (moduleRef : ModuleDiscrTreeRef α) (ty : Expr) : MetaM (MatchResult α) := do
  profileitM Exception  "lazy discriminator local search" (← getOptions) do
    let discrTree ← moduleRef.ref.get
    let (localCandidates, localTree) ← getMatch discrTree ty false false
    moduleRef.ref.set localTree
    return localCandidates

/--
`findMatchesExt` searches for entries in a lazily initialized discriminator tree.

It provides some additional capabilities beyond `findMatches` to adjust results
based on priority and cache module declarations

* `modulesTreeRef` points to the discriminator tree for local environment.
  Used for caching and created by `createLocalTree`.
* `ext` should be an environment extension with an IO.Ref for caching the import lazy
   discriminator tree.
* `addEntry` is the function for creating discriminator tree entries from constants.
* `droppedKeys` contains keys we do not want to consider when searching for matches.
  It is used for dropping very general keys.
* `constantsPerTask` stores number of constants in imported modules used to
  decide when to create new task.
* `ty` is the expression type.
-/
def findMatchesExt
    (moduleTreeRef : ModuleDiscrTreeRef α)
    (ext : EnvExtension (IO.Ref (Option (RefinedDiscrTree α))))
    (addEntry : Name → ConstantInfo → MetaM (List (Key × LazyEntry α)))
    (ty : Expr) (constantsPerTask : Nat := 1000) (capacityPerTask : Nat := 128)
    (config : WhnfCoreConfig := {}) : MetaM (MatchResult α × MatchResult α) := do
  let moduleMatches ← findModuleMatches moduleTreeRef ty
  let importMatches ← findImportMatches ext addEntry ty constantsPerTask capacityPerTask config
  return (moduleMatches, importMatches)

/--
`findMatches` searches for entries in a lazily initialized discriminator tree.

* `ext` should be an environment extension with an IO.Ref for caching the import lazy
   discriminator tree.
* `addEntry` is the function for creating discriminator tree entries from constants.
* `droppedKeys` contains keys we do not want to consider when searching for matches.
  It is used for dropping very general keys.
* `constantsPerTask` stores number of constants in imported modules used to
  decide when to create new task.
* `ty` is the expression type.
-/
def findMatches (ext : EnvExtension (IO.Ref (Option (RefinedDiscrTree α))))
    (addEntry : Name → ConstantInfo → MetaM (List (Key × LazyEntry α)))
    (ty : Expr) (constantsPerTask : Nat := 1000) (capacityPerTask : Nat := 128)
    (config : WhnfCoreConfig := {}) : MetaM (MatchResult α × MatchResult α) := do
  let moduleTreeRef ← createModuleTreeRef addEntry
  findMatchesExt moduleTreeRef ext addEntry ty constantsPerTask capacityPerTask config

end Lean.Meta.RefinedDiscrTree
