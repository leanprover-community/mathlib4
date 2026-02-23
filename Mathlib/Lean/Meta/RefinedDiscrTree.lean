/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Lean.Meta.RefinedDiscrTree.Lookup
public import Mathlib.Lean.Meta.RefinedDiscrTree.Initialize

/-!
A discrimination tree for the purpose of unifying local expressions with library results.

This data structure is based on `Lean.Meta.DiscrTree` and `Lean.Meta.LazyDiscrTree`,
and includes many more features.

## New features

- The keys `Key.lam`, `Key.forall` and `Key.bvar` have been introduced in order to allow for
  matching under lambda and forall binders. `Key.lam` has arity 1 and indexes the body.
  `Key.forall` has arity 2 and indexes the domain and the body. The reason for not indexing the
  domain of a lambda expression is that it is usually already determined, for example in
  `∃ a : α, p`, which is `@Exists α fun a : α => p`, we don't want to index the domain `α` twice.
  In a forall expression we should index the domain, because in an implication `p → q`
  we need to index both `p` and `q`. `Key.bvar` works the same as `Key.fvar`, but stores the
  De Bruijn index to identify the variable.

  For example, this allows for more specific matching with the left-hand side of
  `∑ i ∈ Finset.range n, i = n * (n - 1) / 2`, which is indexed by
  `[⟨Finset.sum, 5⟩, ⟨Nat, 0⟩, ⟨Nat, 0⟩, *0, ⟨Finset.Range, 1⟩, *1, λ, ⟨#0, 0⟩]`.

- The key `Key.star` takes a `Nat` identifier as an argument. For example,
  the library pattern `?a + ?a` is encoded as `@HAdd.hAdd *0 *0 *1 *2 *3 *3`.
  `*0` corresponds to the type of `?a`, `*1` to the outParam of `HAdd.hAdd`,
  `*2` to the `HAdd` instance, and `*3` to `a`. This means that it will only match an expression
  `x + y` if `x` is indexed the same as `y`. The matching algorithm ensures that both
  instances of `*3` match with the same pattern in the lookup expression.

- We evaluate the matching score of a unification.
  This score represents the number of keys that had to be the same for the unification to succeed.
  For example, matching `(1 + 2) + 3` with `add_comm` gives a score of 2,
  since the pattern of `add_comm` is `@HAdd.hAdd *0 *0 *0 *1 *2 *3`: matching `HAdd.hAdd`
  gives 1 point, and matching `*0` again after its first appearance gives another point.
  Similarly, matching it with `Nat.add_comm` gives a score of 3, and `add_assoc` gives a score of 5.

- Patterns that have the potential to be η-reduced are put into the `RefinedDiscrTree` under all
  possible reduced key sequences. This is for terms of the form `fun x => f (?m x₁ .. xₙ)`, where
  `?m` is a metavariable, one of `x₁, .., xₙ` is `x`, and `f` is not a metavariable.
  For example, the pattern `Continuous fun y => Real.exp (f y)])` is indexed by
  both `@Continuous *0 ℝ *1 *2 (λ, Real.exp *3)`
  and `@Continuous *0 ℝ *1 *2 Real.exp`,
  so that it also comes up if you look up `Continuous Real.exp`.

- How to deal with number literals is waiting for this issue to be resolved:
  https://github.com/leanprover/lean4/issues/2867

- The key `Key.opaque` only matches with a `Key.star` key.
  Depending on the configuration, β-reduction and ζ-reduction may be disabled, so the resulting
  applied lambda expressions or let-expressions are indexed by `Key.opaque`.

## Lazy computation

To encode an `Expr` as a sequence of `Key`s, we start with a `LazyEntry` and
we have an incremental evaluation function of type
`LazyEntry → MetaM (Option (List (Key × LazyEntry)))`, which computes the next keys
and lazy entries, or returns `none` if the last key has been reached already.

The `RefinedDiscrTree` then stores these `LazyEntries` at its leafs, and evaluates them
only if the lookup algorithm reaches this leaf.

## Alternative optimizations

`RefinedDiscrTree` is a non-persistent lazy data-structure. Therefore, when using it, you should
try to use it linearly (i.e. having reference count 1). This is ideal for library search purposes,
which build the discrimination tree once, and store a reference to the tree.

However, for tactics like `simp` and `fun_prop` this is less ideal, because they can't use the
data-structure linearly, since copies of the data structure must regularly be stored in the
environment. For `fun_prop` this is not a serious problem since it doesn't have that many
different lemmas anyways.

#### Future work:

Make a version of `RefinedDiscrTree` that is optimal for tactics like `simp` and
`fun_prop`. This would mean using a persistent data structure, and possibly a non-lazy structure.

## Matching vs Unification

A discrimination tree can be used in two ways: either with (unification) or without (matching)
allowing metavariables in the target expression to be instantiated.
Most applications use matching, and the only common use case where unification is used is
type class search. Since the intended applications of the `RefinedDiscrTree` currently use
matching, the lookup algorithm is most optimized for matching.

#### Future work:

Improve the unification lookup.

-/

public section

namespace Lean.Meta.RefinedDiscrTree

variable {α : Type}

/-- Creates the core context used for initializing a tree using the current context. -/
private def withTreeCtx (ctx : Core.Context) : Core.Context :=
  { ctx with maxHeartbeats := 0, diag := getDiag ctx.options }

/-- Returns candidates from all imported modules that match the expression. -/
def findImportMatches
    (ext : EnvExtension (IO.Ref (Option (RefinedDiscrTree α))))
    (addEntry : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry)))) (ty : Expr)
    (constantsPerTask : Nat := 1000) (capacityPerTask : Nat := 128) : MetaM (MatchResult α) := do
  let ngen ← getNGen
  let (cNGen, ngen) := ngen.mkChild
  setNGen ngen
  let _ : Inhabited (IO.Ref (Option (RefinedDiscrTree α))) := ⟨← IO.mkRef none⟩
  let ref := EnvExtension.getState ext (← getEnv)
  -- empty the reference `ref`, so that the reference count stays 1
  let importTree? ← ref.modifyGet fun tree? => (tree?, none)
  let importTree ← importTree?.getDM do
    profileitM Exception  "RefinedDiscrTree import initialization" (← getOptions) <|
      withTheReader Core.Context withTreeCtx <|
        createImportedDiscrTree cNGen (← getEnv) addEntry constantsPerTask capacityPerTask
  let (importCandidates, importTree) ← getMatch importTree ty false false
  ref.set (some importTree)
  MonadExcept.ofExcept importCandidates

/-- Returns candidates from this module that match the expression. -/
def findModuleMatches (moduleRef : ModuleDiscrTreeRef α) (ty : Expr) : MetaM (MatchResult α) := do
  profileitM Exception  "RefinedDiscrTree local search" (← getOptions) do
    let discrTree ← moduleRef.ref.get
    let (localCandidates, localTree) ← getMatch discrTree ty false false
    moduleRef.ref.set localTree
    MonadExcept.ofExcept localCandidates

/--
`findMatches` combines `findImportMatches` and `findModuleMatches`.

* `ext` should be an environment extension with an `IO.Ref` for caching the `RefinedDiscrTree`.
* `addEntry` is the function for creating `RefinedDiscrTree` entries from constants.
* `ty` is the expression type.
* `constantsPerTask` is the number of constants in imported modules to be used for each
  new task.
* `capacityPerTask` is the initial capacity of the `HashMap` at the root of the
  `RefinedDiscrTree` for each new task.
-/
def findMatches (ext : EnvExtension (IO.Ref (Option (RefinedDiscrTree α))))
    (addEntry : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry))))
    (ty : Expr) (constantsPerTask : Nat := 1000) (capacityPerTask : Nat := 128) :
    MetaM (MatchResult α × MatchResult α) := do
  let moduleMatches ← findModuleMatches (← createModuleTreeRef addEntry) ty
  let importMatches ← findImportMatches ext addEntry ty constantsPerTask capacityPerTask
  return (moduleMatches, importMatches)

end Lean.Meta.RefinedDiscrTree
