/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek, Robert Y. Lewis, Floris van Doorn
-/
import Lean
import Mathlib.Util.TermUnsafe

namespace Lean.Expr
/-!
# ReplaceRec

We define a more flexible version of `Expr.replace` where we can use recursive calls even when
replacing a subexpression. We completely mimic the implementation of `Expr.replace`. -/
namespace ReplaceRecImpl

abbrev cacheSize : USize := 8192

structure State where
  -- Remark: our "unsafe" implementation relies on the fact that `()` is not a valid Expr
  keys    : Array Expr
  results : Array Expr

abbrev ReplaceM := StateM State

@[inline] unsafe def cache (i : USize) (key : Expr) (result : Expr) : ReplaceM Expr := do
  modify fun ⟨keys, results⟩ => { keys := keys.uset i key lcProof, results := results.uset i result lcProof };
  pure result

@[inline] unsafe def replaceUnsafeM (f? : Expr → Option (Array Expr × (Array Expr → Expr)))
  (size : USize) (e : Expr) : ReplaceM Expr := do
  let rec @[specialize] visit (e : Expr) : ReplaceM Expr := do
    let c ← get
    let h := ptrAddrUnsafe e
    let i := h % size
    if ptrAddrUnsafe (c.keys.uget i lcProof) == h then
      pure <| c.results.uget i lcProof
    else match f? e with
      | some (es, g) => do
        let esNew ← es.mapM visit
        cache i e (g esNew)
      | none      => match e with
        | Expr.forallE _ d b _   => cache i e <| e.updateForallE! (← visit d) (← visit b)
        | Expr.lam _ d b _       => cache i e <| e.updateLambdaE! (← visit d) (← visit b)
        | Expr.mdata _ b _       => cache i e <| e.updateMData! (← visit b)
        | Expr.letE _ t v b _    => cache i e <| e.updateLet! (← visit t) (← visit v) (← visit b)
        | Expr.app f a _         => cache i e <| e.updateApp! (← visit f) (← visit a)
        | Expr.proj _ _ b _      => cache i e <| e.updateProj! (← visit b)
        | e                      => pure e
  visit e

unsafe def initCache : State :=
  { keys    := mkArray cacheSize.toNat (cast lcProof ()), -- `()` is not a valid `Expr`
    results := mkArray cacheSize.toNat arbitrary }

end ReplaceRecImpl
open ReplaceRecImpl

/-- A version of `Expr.replace` where we can use recursive calls even if we replace a subexpression.
  When reaching a subexpression `e` we call `f? e` to see if we want to do anything with this
  expression. If `f? e = none` we proceed to the children of `e`. If
  `f? e = some (#[e₁, ..., eₙ], g)`, we first recursively apply this function to
  `#[e₁, ..., eₙ]` to get new expressions `#[f₁, ..., fₙ]`.
  Then we replace `e` by `g [f₁, ..., fₙ]`.

  Important: In order for this function to terminate, the `[e₁, ..., eₙ]` must all be smaller than
  `e` according to some measure  (and this measure must also be strictly decreasing on the w.r.t.
  the structural subterm relation). -/
def replaceRec (f? : Expr → Option (Array Expr × (Array Expr → Expr))) (e : Expr) : Expr :=
  unsafe (replaceUnsafeM f? cacheSize e).run' initCache

end Lean.Expr
