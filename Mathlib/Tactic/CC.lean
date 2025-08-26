/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Miyahara Kō
-/
import Mathlib.Tactic.CC.Addition

/-!
# Congruence closure

The congruence closure tactic `cc` tries to solve the goal by chaining
equalities from context and applying congruence (i.e. if `a = b`, then `f a = f b`).
It is a finishing tactic, i.e. it is meant to close
the current goal, not to make some inconclusive progress.
A mostly trivial example would be:

```lean
example (a b c : ℕ) (f : ℕ → ℕ) (h: a = b) (h' : b = c) : f a = f c := by
  cc
```

As an example requiring some thinking to do by hand, consider:

```lean
example (f : ℕ → ℕ) (x : ℕ)
    (H1 : f (f (f x)) = x) (H2 : f (f (f (f (f x)))) = x) :
    f x = x := by
  cc
```

The tactic works by building an equality matching graph. It's a graph where
the vertices are terms and they are linked by edges if they are known to
be equal. Once you've added all the equalities in your context, you take
the transitive closure of the graph and, for each connected component
(i.e. equivalence class) you can elect a term that will represent the
whole class and store proofs that the other elements are equal to it.
You then take the transitive closure of these equalities under the
congruence lemmas.

The `cc` implementation in Lean does a few more tricks: for example it
derives `a = b` from `Nat.succ a = Nat.succ b`, and `Nat.succ a != Nat.zero` for any `a`.

* The starting reference point is Nelson, Oppen, [Fast decision procedures based on congruence
  closure](http://www.cs.colorado.edu/~bec/courses/csci5535-s09/reading/nelson-oppen-congruence.pdf),
  Journal of the ACM (1980)

* The congruence lemmas for dependent type theory as used in Lean are described in
  [Congruence closure in intensional type theory](https://leanprover.github.io/papers/congr.pdf)
  (de Moura, Selsam IJCAR 2016).
-/

universe u

open Lean Meta Elab Tactic Std

namespace Mathlib.Tactic.CC

namespace CCState

open CCM

/-- Make an new `CCState` from the given `config`. -/
def mkCore (config : CCConfig) : CCState :=
  let s : CCState := { config with }
  s.mkEntryCore (.const ``True []) true false |>.mkEntryCore (.const ``False []) true false

/-- Create a congruence closure state object from the given `config` using the hypotheses in the
current goal. -/
def mkUsingHsCore (config : CCConfig) : MetaM CCState := do
  let ctx ← getLCtx
  let ctx ← instantiateLCtxMVars ctx
  let (_, c) ← CCM.run (ctx.forM fun dcl => do
    unless dcl.isImplementationDetail do
      if ← isProp dcl.type then
        add dcl.type dcl.toExpr) { mkCore config with }
  return c.toCCState

/-- Returns the root expression for each equivalence class in the graph.
If the `Bool` argument is set to `true` then it only returns roots of non-singleton classes. -/
def rootsCore (ccs : CCState) (nonsingleton : Bool) : List Expr :=
  ccs.getRoots #[] nonsingleton |>.toList

/-- Increment the Global Modification time. -/
def incGMT (ccs : CCState) : CCState :=
  { ccs with gmt := ccs.gmt + 1 }

/-- Add the given expression to the graph. -/
def internalize (ccs : CCState) (e : Expr) : MetaM CCState := do
  let (_, c) ← CCM.run (CCM.internalize e) { ccs with }
  return c.toCCState

/-- Add the given proof term as a new rule.
The proof term `H` must be an `Eq _ _`, `HEq _ _`, `Iff _ _`, or a negation of these. -/
def add (ccs : CCState) (H : Expr) : MetaM CCState := do
  let type ← inferType H
  unless ← isProp type do
    throwError "CCState.add failed, given expression is not a proof term"
  let (_, c) ← CCM.run (CCM.add type H) { ccs with }
  return c.toCCState

/-- Check whether two expressions are in the same equivalence class. -/
def isEqv (ccs : CCState) (e₁ e₂ : Expr) : MetaM Bool := do
  let (b, _) ← CCM.run (CCM.isEqv e₁ e₂) { ccs with }
  return b

/-- Check whether two expressions are not in the same equivalence class. -/
def isNotEqv (ccs : CCState) (e₁ e₂ : Expr) : MetaM Bool := do
  let (b, _) ← CCM.run (CCM.isNotEqv e₁ e₂) { ccs with }
  return b

/-- Returns a proof term that the given terms are equivalent in the given `CCState` -/
def eqvProof (ccs : CCState) (e₁ e₂ : Expr) : MetaM Expr := do
  let (some r, _) ← CCM.run (CCM.getEqProof e₁ e₂) { ccs with }
    | throwError "CCState.eqvProof failed to build proof"
  return r

/-- `proofFor cc e` constructs a proof for e if it is equivalent to true in `CCState` -/
def proofFor (ccs : CCState) (e : Expr) : MetaM Expr := do
  let (some r, _) ← CCM.run (CCM.getEqProof e (.const ``True [])) { ccs with }
    | throwError "CCState.proofFor failed to build proof"
  mkAppM ``of_eq_true #[r]

/-- `refutationFor cc e` constructs a proof for `Not e` if it is equivalent to `False` in `CCState`
-/
def refutationFor (ccs : CCState) (e : Expr) : MetaM Expr := do
  let (some r, _) ← CCM.run (CCM.getEqProof e (.const ``False [])) { ccs with }
    | throwError "CCState.refutationFor failed to build proof"
  mkAppM ``of_eq_false #[r]

/-- If the given state is inconsistent, return a proof for `False`. Otherwise fail. -/
def proofForFalse (ccs : CCState) : MetaM Expr := do
  let (some pr, _) ← CCM.run CCM.getInconsistencyProof { ccs with }
    | throwError "CCState.proofForFalse failed, state is not inconsistent"
  return pr

/-- Create a congruence closure state object using the hypotheses in the current goal. -/
def mkUsingHs : MetaM CCState :=
  CCState.mkUsingHsCore {}

/-- The root expressions for each equivalence class in the graph. -/
def roots (s : CCState) : List Expr :=
  CCState.rootsCore s true

instance : ToMessageData CCState :=
  ⟨fun s => CCState.ppEqcs s true⟩

/-- Continue to append following expressions in the equivalence class of `e` to `r` until `f` is
found. -/
partial def eqcOfCore (s : CCState) (e : Expr) (f : Expr) (r : List Expr) : List Expr :=
  let n := s.next e
  if n == f then e :: r else eqcOfCore s n f (e :: r)

/-- The equivalence class of `e`. -/
def eqcOf (s : CCState) (e : Expr) : List Expr :=
  s.eqcOfCore e e []

/-- The size of the equivalence class of `e`. -/
def eqcSize (s : CCState) (e : Expr) : Nat :=
  s.eqcOf e |>.length

/-- Fold `f` over the equivalence class of `c`, accumulating the result in `a`.
Loops until the element `first` is encountered.

See `foldEqc` for folding `f` over all elements of the equivalence class. -/
partial def foldEqcCore {α} (s : CCState) (f : α → Expr → α) (first : Expr) (c : Expr) (a : α) :
    α :=
  let new_a := f a c
  let next := s.next c
  if next == first then new_a else foldEqcCore s f first next new_a

/-- Fold the function of `f` over the equivalence class of `e`. -/
def foldEqc {α} (s : CCState) (e : Expr) (a : α) (f : α → Expr → α) : α :=
  foldEqcCore s f e e a

/-- Fold the monadic function of `f` over the equivalence class of `e`. -/
def foldEqcM {α} {m : Type → Type} [Monad m] (s : CCState) (e : Expr) (a : α)
    (f : α → Expr → m α) : m α :=
  foldEqc s e (return a) fun act e => do
    let a ← act
    f a e

end CCState

/-- Option to control whether to show a deprecation warning for the `cc` tactic. -/
register_option mathlib.tactic.cc.warning : Bool := {
  defValue := true
  descr := "Show a deprecation warning when using the `cc` tactic"
}

/--
Applies congruence closure to solve the given metavariable.
This procedure tries to solve the goal by chaining
equalities from context and applying congruence (i.e. if `a = b`, then `f a = f b`).

The tactic works by building an equality matching graph. It's a graph where
the vertices are terms and they are linked by edges if they are known to
be equal. Once you've added all the equalities in your context, you take
the transitive closure of the graph and, for each connected component
(i.e. equivalence class) you can elect a term that will represent the
whole class and store proofs that the other elements are equal to it.
You then take the transitive closure of these equalities under the
congruence lemmas.
The `cc` implementation in Lean does a few more tricks: for example it
derives `a = b` from `Nat.succ a = Nat.succ b`, and `Nat.succ a != Nat.zero` for any `a`.
* The starting reference point is Nelson, Oppen, [Fast decision procedures based on congruence
  closure](http://www.cs.colorado.edu/~bec/courses/csci5535-s09/reading/nelson-oppen-congruence.pdf),
  Journal of the ACM (1980)
* The congruence lemmas for dependent type theory as used in Lean are described in
[Congruence closure in intensional type theory](https://leanprover.github.io/papers/congr.pdf)
(de Moura, Selsam IJCAR 2016).
-/
def _root_.Lean.MVarId.cc (m : MVarId) (cfg : CCConfig := {}) : MetaM Unit := do
  -- Check if warning should be shown
  if ← getBoolOption `mathlib.tactic.cc.warning true then
    logWarning "The tactic `cc` is deprecated since 2025-07-31, please use `grind` instead.\n\n\
      Please report any regressions at https://github.com/leanprover/lean4/issues/.\n\
      Note that `cc` supports some goals that `grind` doesn't,\n\
      but these rely on higher-order unification and can result in unpredictable performance.\n\
      If a downstream library is relying on this functionality,\n\
      please report this in an issue and we'll help find a solution."

  let (_, m) ← m.intros
  m.withContext do
    let s ← CCState.mkUsingHsCore cfg
    let t ← m.getType >>= instantiateMVars
    let s ← s.internalize t
    if s.inconsistent then
        let pr ← s.proofForFalse
        mkAppOptM ``False.elim #[t, pr] >>= m.assign
    else
      let tr := Expr.const ``True []
      let b ← s.isEqv t tr
      if b then
        let pr ← s.eqvProof t tr
        mkAppM ``of_eq_true #[pr] >>= m.assign
      else
        let dbg ← getBoolOption `trace.Meta.Tactic.cc.failure false
        if dbg then
          throwError m!"cc tactic failed, equivalence classes: {s}"
        else
          throwError "cc tactic failed"

/--
Allow elaboration of `CCConfig` arguments to tactics.
-/
declare_config_elab elabCCConfig CCConfig

open Parser.Tactic in
/--
The congruence closure tactic `cc` tries to solve the goal by chaining
equalities from context and applying congruence (i.e. if `a = b`, then `f a = f b`).
It is a finishing tactic, i.e. it is meant to close
the current goal, not to make some inconclusive progress.
A mostly trivial example would be:

```lean
example (a b c : ℕ) (f : ℕ → ℕ) (h : a = b) (h' : b = c) : f a = f c := by
  cc
```

As an example requiring some thinking to do by hand, consider:

```lean
example (f : ℕ → ℕ) (x : ℕ)
    (H1 : f (f (f x)) = x) (H2 : f (f (f (f (f x)))) = x) :
    f x = x := by
  cc
``` -/
elab (name := _root_.Mathlib.Tactic.cc) "cc" cfg:optConfig : tactic => do
  let cfg ← elabCCConfig cfg
  withMainContext <| liftMetaFinishingTactic (·.cc cfg)

end Mathlib.Tactic.CC
