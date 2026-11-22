/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public meta import Lean.Elab.Tactic.Conv

import Mathlib.Init

/-!
# The `cat_nf` simp set

This file defines a simp set `cat_nf` which records normal forms in category theory.

This file also defines a utility elaborator `cat_nf%` to simplify a term or a proof using
this simp set.

-/

public meta section

/-- The `cat_nf` simp set records normal forms in category theory.

Definitional unfolding theorems for functors, natural transformations and other categorical
structures usually belong to this simp set.

The standard practices for normalizing expressions in category theory are
- Compositions are right-associated, i.e. `f ≫ g ≫ h` is the normal form of `(f ≫ g) ≫ h`.
- Identities are removed: `𝟙 _ ≫ f` and `f ≫ 𝟙 _` both normalize to `f`.
- Functor-like behaviors are applied. For instance, functorial projections are applied,
  which means that eg `φ.app x ≫ ψ.app x` is the normal form of `(φ ≫ ψ).app x`.

To keep this simp set confluent and predictable, please do not tag commutative diagrams with
`cat_nf`: instances of `NatTrans.naturality` should not be tagged. Similarly,
`CommaMorphism.w` should not be tagged.
-/
register_simp_attr cat_nf

open Lean Meta Elab Command Std Tactic

/-- `cat_nf% foo` simplifies the term `foo` using the `cat_nf` simp set.

If `foo` is a proof, then its type is simplified instead.
For instance, `cat_nf% (f ≫ g) ≫ h` will be the term `f ≫ g ≫ h`, while
`cat_nf% (η : 𝟭 _ ⟶ L ⋙ R).naturality f` will be a term of type
`f ≫ η.app _ = η.app _ ≫ R.map (L.map f)`.

Use this elaborator to avoid the pattern
```
have h : … := …
simp only [Category.assoc, Functor.map_comp, …] at h
…
```
-/
elab (name := catNFPercent) "cat_nf%" t:term : term => do
  let e ← Term.elabTerm t none
  let isPrf ← isProof e
  let lhs ← if isPrf then inferType e else pure e
  let go : TacticM Expr := do
    let ⟨rhs, p⟩ ← Lean.Elab.Tactic.Conv.convert lhs do
      evalTactic (← `(tactic| simp only [cat_nf]))
    if isPrf then
      mkEqMP p e
    else
      return rhs
  let fresh ← mkFreshExprMVar default
  go { elaborator := .anonymous } |>.run' { goals := [fresh.mvarId!] }

end
