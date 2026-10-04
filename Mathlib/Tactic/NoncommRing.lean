/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Kim Morrison, Oliver Nash
-/
module

public import Mathlib.Algebra.Group.Action.Defs  -- shake: keep (metaprogram output dependency)
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Tactic.Hint
public import Lean.Elab.Tactic.Try
public meta import Lean.Meta.Sym.Arith.Module
public meta import Lean.Meta.Tactic.Simp.Main

/-! # The `noncomm_ring` tactic

Solve goals in not necessarily commutative rings.

This tactic is rudimentary, but useful for solving simple goals in noncommutative rings. One
glaring flaw is that numeric powers are unfolded entirely with `pow_succ` and can easily exceed the
maximum recursion depth.

`noncomm_ring` distributes products using `simp only` and collects additive terms using
Lean's shared arithmetic certificates. It closes additive equalities when possible and otherwise
normalizes additive expressions in the goal.
-/

public meta section

namespace Mathlib.Tactic.NoncommRing

section nat_lit_mul
variable {R : Type*} [NonAssocSemiring R] (r : R) (n : ℕ)

lemma nat_lit_mul_eq_nsmul [n.AtLeastTwo] : ofNat(n) * r = OfNat.ofNat n • r := by
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
lemma mul_nat_lit_eq_nsmul [n.AtLeastTwo] : r * ofNat(n) = OfNat.ofNat n • r := by
  simp only [nsmul_eq_mul', Nat.cast_ofNat]

end nat_lit_mul

open Lean Meta Elab Tactic Sym

elab "noncomm_ring_nf" : tactic => liftMetaTactic1 fun g => SymM.run do
  let target ← instantiateMVars (← g.getType)
  if let some proof ← Arith.proveAddEq? target then
    g.assign proof
    return none
  let ctx ← Meta.Simp.mkContext { zetaDelta := false, singlePass := true }
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← controlAt MetaM fun runInMeta =>
    Meta.Simp.main target ctx (methods := { post := fun e => do
      let .step e h .. ← runInMeta (Arith.normalizeAdd? e) | return .continue
      return .done { expr := e, proof? := some h } })
  let some proof := r.proof? | throwError "no additive expression changed"
  return ← g.replaceTargetEq r.expr proof

open Lean.Parser.Tactic
/-- `noncomm_ring` simplifies expressions in not-necessarily-commutative rings in the main goal
then tries closing it by "cheap" (reducible) `rfl`.
This tactic supports the operators `+`, `*`, `-`, `^` and `•` (for scalar multiplication by
natural numbers or integers).

If the ring is commutative, prefer the `ring` tactic instead, which is more powerful and efficient.
The tactic distributes products and collects additive terms. The simplification step can be
customized using the options listed below.

Limitation: numeric powers are unfolded entirely with `pow_succ` and can easily exceed the
maximum recursion depth.

* `noncomm_ring [h]` adds the term `h` as simplification lemma, rewriting from left to right.
  Multiple arguments can be combined as `noncomm_ring [h₁, ..., hₙ]`.
* `noncomm_ring [← h]` adds the term `h` as simplification lemma, rewriting from right to left.
* `noncomm_ring [*]` simplifies using all hypotheses in the local context.
* `noncomm_ring (config := cfg)` uses `cfg` as configuration for the simplification step.
  See `Lean.Meta.Simp.Config` for more details.
* `noncomm_ring (discharger := tac)` uses the tactic sequence `tac` to discharge assumptions
  to the simplification lemmas. This only applies to user-supplied lemmas, since the default lemmas
  used by `noncomm_ring` do not require a discharger.

Example:
```lean
example {R : Type*} [Ring R] (a b c : R) : a * (b + c + c - b) = 2 * a * c := by
  noncomm_ring
```
-/
syntax (name := noncomm_ring) "noncomm_ring" optConfig (discharger)?
  (" [" ((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : tactic

macro_rules
  | `(tactic| noncomm_ring $cfg:optConfig $[$disch]? $[[$rules,*]]?) => do
    let rules' := rules.getD ⟨#[]⟩
    let tac ← `(tactic|
      (first | simp $cfg:optConfig $(disch)? only [
          -- Expand everything out.
          add_mul, mul_add, sub_eq_add_neg,
          -- Right associate all products.
          mul_assoc,
          -- Expand powers to numerals.
          pow_one, pow_zero, pow_succ,
          -- Replace multiplication by numerals with `zsmul`.
          one_mul, mul_one, zero_mul, mul_zero,
          nat_lit_mul_eq_nsmul, mul_nat_lit_eq_nsmul,
          -- Pull scalar multiplication out of products.
          mul_smul_comm, smul_mul_assoc,
          -- Pull out negations.
          neg_mul, mul_neg,
          -- user-specified simp lemmas
          $rules',*] |
        fail "`noncomm_ring` simp lemmas don't apply; try `abel` instead") <;>
      noncomm_ring_nf <;> try rfl)
    -- if a manual rewrite rule is provided, we repeat the tactic
    -- (since collecting terms might allow the rewrite to apply again)
    if rules.isSome then `(tactic| repeat1 ($tac;)) else `(tactic| $tac)

end Mathlib.Tactic.NoncommRing

/-!
We register `noncomm_ring` with the `hint` tactic.
-/

register_hint 1000 noncomm_ring
register_try?_tactic (priority := 1000) noncomm_ring
