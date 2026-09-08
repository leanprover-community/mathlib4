/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Tactic.Algebra.Basic
public import Mathlib.Tactic.Module
public meta import Mathlib.Tactic.Ring.RingNF

/-! # `module_nf` - a normalization tactic for module expressions.

`module_nf` rewrites every linear combination `a • x + ... + b • y` appearing at the targeted
locations into a normal form, collecting the scalars of common terms and normalizing them with
`ring_nf`.  In particular, a goal `⊢ a • x + ... + b • y = c • x + ... + d • y` is closed when
the two sides have the same normal form, otherwise the rewritten goal is left open, and
`module_nf` can be used non-terminally.

Like `match_scalars` and `module`, linear combinations are parsed from `+`, `-`, `•` and `0`, other
subexpressions (including variables) are atoms, and the scalars are interpreted in the largest
scalar ring encountered, and subtraction requires a ring (see `match_scalars` for the requirements
on scalar types).

Examples:
```
example [AddCommMonoid M] [CommSemiring R] [Module R M] (a b : R) (x : M) :
    a • x + b • x = (a + b) • x := by
  module_nf

example [AddCommMonoid V] (x y : V) : x + (y + x) = x + x + y := by
  module_nf  -- both sides normalize to `2 • x + y`

example [AddCommMonoid M] [CommSemiring R] [Module R M] (f : M → M) (a b : R) (x : M) :
    f (a • x + b • x) = f ((a + b) • x) := by
  module_nf  -- rewrites under `f`

example [AddCommMonoid M] [CommSemiring R] [Module R M] (a b : R) (x : M)
    (h : a • x + b • x = 0) : (b + a) • x = 0 := by
  module_nf at h ⊢
  exact h
```

The scalar ring is inferred once per invocation by examining the locations targeted by the tactic,
so that the scalar rings of independently rewritten locations agree:

```
example [AddCommGroup M] (x : M) : x + x = (2 : ℤ) • x := by
  module_nf  -- mixed scalars: the ring is inferred jointly, so both sides normalize over ℤ
```

The common scalar ring can also be specified explicitly with `module_nf with R`, which normalizes
every location's scalars over `R`. For example:

```
example [AddCommGroup M] [Field K] [Module K M] (x y : M) (h : x + x = y) :
    (2 : K) • x = y := by
  module_nf with K at h
  exact h
```

Locations whose scalar ring is not comparable with `R` keep their own ring. For example:

```
example [CommRing S] [CommRing T] [AddCommGroup M] [Module S M] [Module T M]
    (s : S) (x y : M) (h : s • x + s • x = y) : (s * 2) • x = y := by
  module_nf with T at h  -- `h`'s scalars are not comparable with `T` and keep their ring `S`
  exact h
```

Scalar actions collected through an algebra tower are lowered back to the smallest ring that
expresses them:

```
example [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M]
    (a b : R) (u : S) (x y : M) (P : M → Prop)
    (h : P (b • x + y)) : P (a • x + u • y + (1 - u) • y - (a - b) • x) := by
  module_nf  -- the `R`-actions collect in `S` and lower back to `R`
  exact h
```

When inferring the common scalar ring, the tactic descends through equalities and arithmetic
operations `+`, `-`, `*`, `^`, `•` at each location but not through any other context, e.g.
conjunctions, applications, `≤`. So if there are several subexpressions at a location that are
separated by such a context then normalization may result in mixed scalar rings. For example:

```
example [AddCommGroup M] (x : M) (P : M → Prop) (h : P ((2 : ℤ) • x)) :
    P (x + x) ∧ P ((2 : ℤ) • x) := by
  module_nf
  -- `⊢ P (2 • x) ∧ P ((2 : ℤ) • x)`: the first conjunct normalized over `ℕ`, not `ℤ`,
  -- so `exact ⟨h, h⟩` would fail here
```

The scalar rings can be aligned by specifying `ℤ` explicitly:

```
example [AddCommGroup M] (x : M) (P : M → Prop) (h : P ((2 : ℤ) • x)) :
    P (x + x) ∧ P ((2 : ℤ) • x) := by
  module_nf with ℤ
  exact ⟨h, h⟩
```

## Implementation notes

The rewriting is performed by `Mathlib.Tactic.Module.eval` and reuses the same parsing
infrastructure as `match_scalars`. Nested module expressions are rewritten using `AtomM.recurse` and
the scalar ring of the normalized expression is inferred jointly across targeted locations or
specified explicitly.
-/

public meta section

open Lean hiding Module
open Qq Parser.Tactic Elab.Tactic Meta

namespace Mathlib.Tactic.ModuleNF

/-- Infer the scalar ring over which the scalar rings appearing in `es` should be normalized.

This is similar to `Mathlib.Tactic.Algebra.inferBase` which infers a base using the ring / field
structure of the ambient type. -/
def inferBase (es : Array Expr) : MetaM (Σ u : Level, Q(Type u)) := do
  let rings := (← es.toList.mapM Algebra.collectScalarRings).flatten
  let rings ← rings.eraseDups.mapM getLevelQ'
  match rings with
  | [] => return ⟨0, q(ℕ)⟩
  | r :: rs => rs.foldlM Algebra.pickLargerRing r

/-- Infer a common base scalar ring across all locations targeted by `loc`.

The locations read are exactly those that `transformAtNondepPropLocation` rewrites when the
tactic runs, so the inferred ring reflects the rewrite set. -/
def inferBaseAtLocation (loc : Location) : TacticM (Σ u : Level, Q(Type u)) :=
  withMainContext do
    inferBase (← (← mapNondepPropLocation loc (fun fvarId => fvarId.getType) getMainTarget).mapM
      (whnf ·))

/-- Rewrite `e`, an expression in some `AddCommMonoid`, into `module`'s internal normal form using
`Mathlib.Tactic.Module.eval`. -/
def evalExpr (base : Σ u : Level, Q(Type u)) (postCtx : Simp.Context) (e : Expr) :
    AtomM Simp.Result := do
  let e ← withReducible <| whnf e
  -- An expression that is not an application must necessarily be an atom.
  -- `Module.eval` also checks for atoms, but this check avoids instance search and `Module.parse`.
  guard e.isApp
  let ⟨_, M, e⟩ ← inferTypeQ' e
  let iM : Q(AddCommMonoid $M) ← synthInstanceQ q(AddCommMonoid $M)
  Mathlib.Tactic.Module.eval iM base postCtx e

/-- The `Simp.Context` used by `ModuleNF.cleanup`. -/
def cleanupCtx : MetaM Simp.Context := do
  let thms ← [``one_smul, ``zero_smul, ``add_zero, ``zero_add, ``mul_one,
    ``one_mul, ``neg_one_smul, ``algebraMap_smul].foldlM (·.addConst ·) ({} : SimpTheorems)
  Simp.mkContext { failIfUnchanged := false }
    (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)

/-- Clean up a rewritten expression with the `cleanupCtx` lemmas. -/
def cleanup (ctx : Simp.Context) (r : Simp.Result) : MetaM Simp.Result := do
  r.mkEqTrans (← Simp.main r.expr ctx (methods := Simp.mkDefaultMethodsCore {})).1

/-- Run the `module_nf` rewrite on the expression `e`.

`s` is a reference to the `AtomM` state, shared between all locations visited by a single
`module_nf` call. This ensures they normalize with a consistent atom ordering. -/
def moduleNFCore (s : IO.Ref AtomM.State) (base : Σ u : Level, Q(Type u)) (e : Expr) :
    ReaderT Simp.Context MetaM Simp.Result := do
  let postCtx ← read
  let cleanCtx ← cleanupCtx
  AtomM.recurse s { red := .instances } (wellBehavedDischarge := true) (evalExpr base postCtx)
    (cleanup cleanCtx) e

/-- `module_nf` normalizes the goal, by rewriting every linear combination `a • x + ... + b • y`
into a normal form, collecting the scalars of common terms and normalizing them with `ring_nf`. If
the goal is an equality and the two sides have the same normal form, `module_nf` closes the goal.
Otherwise the rewritten goal is left open, and `module_nf` can be used non-terminally.

Like `match_scalars` and `module`, linear combinations are parsed from `+`, `-`, `•` and `0`, other
subexpressions (including variables) are atoms, and the scalars are interpreted in the largest
scalar ring encountered, and subtraction requires a ring (see `match_scalars` for the requirements
on scalar types).

* `module_nf at loc` rewrites at the location(s) `loc`.
* `module_nf with R` uses `R` as the common ring of scalars.

Examples:

```lean
example [AddCommMonoid M] [CommSemiring R] [Module R M] (a b : R) (x : M) :
    a • x + b • x = (a + b) • x := by
  module_nf

example [AddCommMonoid M] [CommSemiring R] [Module R M] (a b : R) (x : M)
    (h : a • x + b • x = 0) : (b + a) • x = 0 := by
  module_nf at h ⊢
  exact h

example [AddCommGroup M] (x : M) (P : M → Prop) (h : P ((2 : ℤ) • x)) :
    P (x + x) ∧ P ((2 : ℤ) • x) := by
  module_nf with ℤ
  exact ⟨h, h⟩
```
-/
syntax (name := moduleNF) "module_nf" (" with " term)? (location)? : tactic

elab_rules : tactic
  | `(tactic| module_nf $[with $R:term]? $[$loc:location]?) => withMainContext do
    let loc := expandOptLocation (mkOptionalNode loc)
    let base ← match R with
      | some R => do
        let ⟨u, B⟩ ← getLevelQ' (← elabTerm R none)
        unless (← trySynthInstance q(Semiring.{u} $B)) matches .some _ do
          throwError "module_nf failed: {B} is not a semiring"
        pure ⟨u, B⟩
      | none => inferBaseAtLocation loc
    let s ← IO.mkRef {}
    let postCtx ← Mathlib.Tactic.Module.postprocessCtx
    transformAtNondepPropLocation (moduleNFCore s base) "module_nf" loc .error false postCtx

end Mathlib.Tactic.ModuleNF

end
