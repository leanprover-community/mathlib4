/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

/-! # Guide: Conversion mode tactic

This is a curated guide to point you toward how `conv` mode works and what tactics are available.
It is not meant to be comprehensive, but rather a "cheat sheet." See also the
[`conv` introduction](https://leanprover-community.github.io/mathlib4_docs/docs/Conv/Introduction.html).

## Syntax

The syntax for the `conv` tactic is
```
"conv" ("at" ident)? ("in" ("(occs :=" ("*" <|> num+) ")")? term)? "=>" convSeq
```
where `convSeq` is any sequence of "`conv` tactics", which are tactics specifically written
for `conv` mode.

The `in` clause is exactly the same as the arguments to the `conv` tactic `pattern`.
```lean
conv in ...pattArgs... =>
  ...
```
is short for
```lean
conv =>
  pattern ...patArgs...
  ...
```
Note that `conv in (occs := 1 2 3) pat => ...` starts with three goals (one for each occurrence),
but `conv in (occs := *) pat => ...` starts with a single goal that converts in all occurrences
simultaneously.

Mathlib also provides `conv_lhs` and `conv_rhs` variants to immediately apply either the
`lhs` or `rhs` tactic.

## What is `conv` mode?

`conv` mode is essentially the normal tactic mode but with two differences.

1. Only "`conv` tactics" can appear in the `conv` block. These are tactics with syntax
   in the `conv` category.

2. The goals are all of the form `⊢ lhs = ?rhs` with `?rhs` a metavariable, but the goals
   are annotated in such a way that they display as `| lhs`.

Each `conv` tactic is aware that the goal is of this form, and in addition to solving for the
goal like normal, they also solve for the `?rhs` metavariable in some controlled way.
For example, the `rfl` tactic uses `rfl` to solve the goal, which sets `?rhs := lhs`.
Other tactics, like `congr`, partially solve for `?rhs` and create new goal metavariables
for each unsolved-for hole.

Once all the tactics have had a chance to run, `conv` mode itself uses `rfl` to solve
any remaining goals (note that in `conv` mode, every goal can be solved for by `rfl`!), and
then it uses the resulting `lhs = rhs` proof to rewrite the goal in the surrounding normal
tactic mode.

## Conv tactics from Lean 4, Batteries, and Mathlib

Unless they're annotated with "Batteries" or "Mathlib", the following tactics are defined
in Lean 4 core.

### Control

* `done` checks that there are no `conv` goals remaining.

* `skip` does nothing. It can be used to be the single tactic in an otherwise empty `conv` block.
  It does *not* skip a `conv` goal.

* `rfl` skips/closes a `conv` goal by using `rfl`. (Remember, the actual goal is `⊢ lhs = ?rhs`, so
  this sets `?rhs := lhs` and uses `rfl` to prove `lhs = lhs`.)

* `conv => convSeq` is a nested `conv`. It uses `conv` to change the current goal without
  closing it. For example, this is how you can do a `conv`-targeted rewrite of the current
  expression and then apply `conv` tactics to the result.

* `all_goals convSeq` runs the `conv` tactics on every `conv` goal, collecting all the produced
  subgoals (if any).

* `any_goals convSeq` is like `all_goals` but succeeds if the tactic sequence succeeds for any
  of the goals.

* `case tag => convSeq` focuses on a goal with a given tag, runs the tactic sequence, and then
  auto-closes the focused goal with `rfl`. Has the same syntax as the `case` tactic.

* `case' tag => convSeq` is like `case` but does not auto-close the goal if the tactics
  do not close it.

* `next => convSeq` and `next x1 ... xn => convSeq` are like the `next` tactic, but they
  auto-close the focused goal with `rfl`.

* `· convSeq` focuses on the current goal and auto-closes it with `rfl`.

* `focus => convSeq` focuses on the current goal. It does not auto-close the goal, unlike `next`.

* `{ convSeq }` is like `next`.

* `first | convSeq1 | convSeq2 | ...` tries each `conv` sequence one at a time until one
  of them succeeds, or else fails.

* `try convSeq` runs the `conv` sequence and succeeds even if it fails.
  Same as `first | convSeq | skip`.

* `repeat convSeq` repeatedly runs `convSeq` until it fails.

* `( convSeq )` is for grouping. Useful when using `conv` tactic combinators.

* `conv1 <;> conv2` is for running `conv1` and running `conv2` on every goal produced by `conv`.

* `tactic => tacticSeq` converts the goal into `⊢ lhs = ?rhs` form and applies the tactic sequence.
  The tactic does not have to solve the goal completely, and remaining goals are turned back
  into `conv` goals. (Internal: there's also a `tactic' => tacticSeq` that does not remove
  the `conv` annotations from the goal before applying the tactic sequence.)

* `discharge => tacticSeq` takes a goal `| p` with `p` a proposition, uses the tactic sequence
  to prove `⊢ p`, and then closes the goal to convert `p` to `True`. (Mathlib)

* `with_reducible convSeq` changes the transparency settings to `reducible` while evaluating the
  `conv` sequence. (Mathlib)

### Navigation

* `congr` (synonym: `args`) creates subgoals for every immediate subexpression of the expression.
  You can use `rfl` to skip any of these subgoals.

* `lhs` (synonym: `left`) traverses into the second-to-last argument of the expression.
  (Implemented using `congr`.)

* `rhs` (synonym: `right`) traverses into the last argument of the expression.
  (Implemented using `congr`.)

* `arg i` (and `arg @i`) traverses into the `i`th explicit argument (resp. the `i`th argument)
  of the expression. (Implemented using `congr`.)

* `ext` (synonym: `intro`) traverses into lambda, forall, and `let` expressions.
  `ext x` gives the resulting binder the name `x`.
  `ext x y z ...` applies `ext` once for each provided binder.

* `enter [...]` is a compact way to describe a path to a subterm.
  * `enter [i]` (where `i` is a natural number) is equivalent to `arg i`.
  * `enter [@i]` is equivalent to `arg @i`.
  * `enter [x]` (where `x` is an identifier) is equivalent to `ext x`.
  * `enter [a,b,c,...]` is `enter [a]; enter [b]; enter [c]; enter [...]`.

* `pattern` is for navigating into subexpressions that match a given pattern
  * `pattern pat` traverses to the first subterm of the target that matches `pat`.
  * `pattern (occs := *) pat` traverses to every subterm of the target that matches `pat`
    which is not contained in another match of `pat`. It generates one subgoal.
  * `pattern (occs := 1 2 4) pat` matches occurrences `1, 2, 4` of `pat` and produces
    three subgoals. Occurrences are numbered left to right from the outside in.

### Manipulation

* `change t` changes the expression to `t` if the expression and `t` are definitionally equal.

* `equals t => tacticSeq` changes the current expression, say `e`, to `t`, and asks you to prove
   the equality `e = t`. (Batteries)

* `rw [thms...]` rewrites the expression using the given theorems. The syntax is similar to `rw`.

* `erw [thms...]` rewrites the expression using the given theorems. The syntax is similar to `erw`.

* `simp [thms...]` applies `simp` to rewrite the expression. The syntax is similar to `simp`.

* `dsimp [thms...]` applies `dsimp` to rewrite the expression. The syntax is similar to `dsimp`.

* `simp_match` simplifies `match` expressions.

* `apply e` applies `e` to the goal (which remember is `⊢ lhs = ?rhs`) using the `apply` tactic.
  Strange results may occur if the hypotheses of `e` are not equalities.

* `refine e` applies `e` to the goal (which remember is `⊢ lhs = ?rhs`) using the `refine` tactic.
  Strange results may occur if the placeholders in `e` are not equalities.

* `exact e` closes the goal, where `e : lhs = ?rhs`. (Batteries)

* Mathlib provides a number of tactics as `conv` tactics:
  * `abel` and `abel_nf`
  * `ring` and `ring_nf`
  * `norm_cast`
  * `norm_num1` and `norm_num`
  * `push_neg`

* `apply_congr` applies a relevant `@[congr]` lemma, which can be better suited for a function
  than the congruence lemma that the `congr` tactic might generate. (Mathlib)

* `slice i j` (for category theory) reassociates a composition of morphisms to focus on
  the composition of morphisms `i` through `j`. (Mathlib)

### Reductions

* `whnf` reduces the expression to weak-head normal form.

* `zeta` applies zeta reduction to the expression (i.e., substitutes all `let` expressions
and expands all local variables).

* `reduce` reduces the expression like the `#reduce` command.
  (Documentation says "for debugging purposes only.")

* `unfold id1 id2 ...` unfolds the definitions for the given constants using each
  definitions equational lemmas. For recursive definitions, only one layer of unfolding
  is performed.

* `delta id1 id2 ...` applies delta reduction for the given constants (i.e., substitutes
  the values of each constant). It is primitive: it ignores definitional equations and
  uses the raw definition of each constant. Using `unfold` is preferred.

### Debugging, for internal use, or otherwise technical

* `trace_state` prints the current goal state (runs the `trace_state` tactic)

* `fail_if_success convSeq` fails if the `conv` sequence succeeds.

* `guard_expr` and `guard_target` for asserting that certain expressions are equal to others.
  (Batteries)

* `unreachable!`, which is the same as the `unreachable!` tactic. (Batteriess)

* `run_tac doSeq` evaluates a monadic value and runs it as a tactic using `tactic'`. (Mathlib)

## Tactics and commands related to `conv`

* `conv_lhs ... => ...` and `conv_rhs ... => ...` are like `conv`, but they immediately use
  `lhs` or `rhs` (respectively). (Mathlib)

* `conv' ... => ...` is like `conv` but assumes the goal is already annotated as a `conv` goal.
  Used internally to go back and forth between tactic mode and conv mode.

* `#conv convTactic => e` is a command to apply the `convTactic` to the expression `e`, yielding
  the converted expression (and dropping the generated proof).
  This is used to implement `#simp`, `#whnf`, `#norm_num`, and `#push_neg`. (Mathlib)


-/
