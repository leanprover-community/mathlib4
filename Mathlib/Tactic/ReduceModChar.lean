/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.ReduceModChar.Ext

/-!
# `reduce_mod_char` tactic

Define the `reduce_mod_char` tactic, which traverses expressions looking for numerals `n`,
such that the type of `n` is a ring of (positive) characteristic `p`, and reduces these
numerals modulo `p`, to lie between `0` and `p`.

## Implementation

The main entry point is `ReduceModChar.derive`, which uses `simp` to traverse expressions and
calls `matchAndNorm` on each subexpression.
The type of each subexpression is matched syntactically to determine if it is a ring with positive
characteristic in `typeToCharP`. Using syntactic matching should be faster than trying to infer
a `CharP` instance on each subexpression.
The actual reduction happens in `normIntNumeral`. This is written to be compatible with `norm_num`
so it can serve as a drop-in replacement for some `norm_num`-based routines (specifically, the
intended use is as an option for the `ring` tactic).

In addition to the main functionality, we call `normNeg` and `normNegCoeffMul` to replace negation
with multiplication by `p - 1`, and simp lemmas tagged `@[reduce_mod_char]` to clean up the
resulting expression: e.g. `1 * X + 0` becomes `X`.
-/

open Lean Meta Simp
open Lean.Elab
open Tactic
open Qq

set_option autoImplicit true

namespace Tactic

namespace ReduceModChar

open Mathlib.Meta.NormNum

lemma CharP.intCast_eq_mod (R : Type _) [Ring R] (p : ℕ) [CharP R p] (k : ℤ) :
    (k : R) = (k % p : ℤ) := by
  calc
    (k : R) = ↑(k % p + p * (k / p)) := by rw [Int.emod_add_ediv]
    _ = ↑(k % p) := by simp [CharP.cast_eq_zero R]

lemma CharP.isInt_of_mod {α : Type _} [Ring α] {n n' : ℕ} (inst : CharP α n) {e : α}
    (he : IsInt e e') (hn : IsNat n n') (h₂ : IsInt (e' % n') r) : IsInt e r :=
  ⟨by rw [he.out, CharP.intCast_eq_mod α n, show n = n' from hn.out, h₂.out, Int.cast_id]⟩

/-- Given an integral expression `e : t` such that `t` is a ring of characteristic `n`,
reduce `e` modulo `n`. -/
partial def normIntNumeral {α : Q(Type u)} (n : Q(ℕ)) (e : Q($α)) (instRing : Q(Ring $α))
    (instCharP : Q(CharP $α $n)) : MetaM (Result e) := do
  let ⟨ze, ne, pe⟩ ← Result.toInt instRing (← Mathlib.Meta.NormNum.derive e)
  let ⟨n', pn⟩ ← deriveNat n q(instAddMonoidWithOneNat)
  let rr ← evalIntMod.go _ _ ze q(IsInt.raw_refl $ne) _ <|
    .isNat q(instAddMonoidWithOne) _ q(isNat_natCast _ _ (IsNat.raw_refl $n'))
  let ⟨zr, nr, pr⟩ ← rr.toInt q(Int.instRing)
  return .isInt instRing nr zr q(CharP.isInt_of_mod $instCharP $pe $pn $pr)

lemma CharP.neg_eq_sub_one_mul {α : Type _} [Ring α] (n : ℕ) (inst : CharP α n) (b : α)
    (a : ℕ) (a' : α) (p : IsNat (n - 1 : α) a) (pa : a = a') :
    -b = a' * b := by
  rw [← pa, ← p.out, ← neg_one_mul]
  simp

/-- Given an expression `(-e) : t` such that `t` is a ring of characteristic `n`,
simplify this to `(n - 1) * e`.

This should be called only when `normIntNumeral` fails, because `normIntNumeral` would otherwise
be more useful by evaluating `-e` mod `n` to an actual numeral.
-/
@[nolint unusedHavesSuffices] -- the `=Q` is necessary for type checking
partial def normNeg {α : Q(Type u)} (n : Q(ℕ)) (e : Q($α)) (_instRing : Q(Ring $α))
    (instCharP : Q(CharP $α $n)) :
    MetaM Simp.Result := do
  let .app f (b : Q($α)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq f q(Neg.neg (α := $α))
  let r ← (derive (α := α) q($n - 1))
  match r with
  | .isNat sα a p => do
    have : instAddMonoidWithOne =Q $sα := ⟨⟩
    let ⟨a', pa'⟩ ← mkOfNat α sα a
    let pf : Q(-$b = $a' * $b) := q(CharP.neg_eq_sub_one_mul $n $instCharP $b $a $a' $p $pa')
    return { expr := q($a' * $b), proof? := pf }
  | .isNegNat _ _ _ =>
    throwError "normNeg: nothing useful to do in negative characteristic"
  | _ => throwError "normNeg: evaluating `{n} - 1` should give an integer result"

lemma CharP.neg_mul_eq_sub_one_mul {α : Type _} [Ring α] (n : ℕ) (inst : CharP α n) (a b : α)
    (na : ℕ) (na' : α) (p : IsNat ((n - 1) * a : α) na) (pa : na = na') :
    -(a * b) = na' * b := by
  rw [← pa, ← p.out, ← neg_one_mul]
  simp

/-- Given an expression `-(a * b) : t` such that `t` is a ring of characteristic `n`,
and `a` is a numeral, simplify this to `((n - 1) * a) * b`. -/
@[nolint unusedHavesSuffices] -- the `=Q` is necessary for type checking
partial def normNegCoeffMul {α : Q(Type u)} (n : Q(ℕ)) (e : Q($α)) (_instRing : Q(Ring $α))
    (instCharP : Q(CharP $α $n)) :
    MetaM Simp.Result := do
  let .app neg (.app (.app mul (a : Q($α))) (b : Q($α))) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq neg q(Neg.neg (α := $α))
  guard <|← withNewMCtxDepth <| isDefEq mul q(HMul.hMul (α := $α))
  let r ← (derive (α := α) q(($n - 1) * $a))
  match r with
  | .isNat sα na np => do
    have : AddGroupWithOne.toAddMonoidWithOne =Q $sα := ⟨⟩
    let ⟨na', npa'⟩ ← mkOfNat α sα na
    let pf : Q(-($a * $b) = $na' * $b) :=
      q(CharP.neg_mul_eq_sub_one_mul $n $instCharP $a $b $na $na' $np $npa')
    return { expr := q($na' * $b), proof? := pf }
  | .isNegNat _ _ _ =>
    throwError "normNegCoeffMul: nothing useful to do in negative characteristic"
  | _ => throwError "normNegCoeffMul: evaluating `{n} - 1` should give an integer result"

/-- A `TypeToCharPResult α` indicates if `α` can be determined to be a ring of characteristic `p`.
-/
inductive TypeToCharPResult (α : Q(Type u))
  | intLike (n : Q(ℕ)) (instRing : Q(Ring $α)) (instCharP : Q(CharP $α $n))
  | failure

instance : Inhabited (TypeToCharPResult α) := ⟨.failure⟩

/-- Determine the characteristic of a ring from the type.
This should be fast, so this pattern-matches on the type, rather than searching for a
`CharP` instance.
Use `typeToCharP (expensive := true)` to do more work in finding the characteristic,
in particular it will search for a `CharP` instance in the context. -/
partial def typeToCharP (expensive := false) (t : Q(Type u)) : MetaM (TypeToCharPResult t) :=
match Expr.getAppFnArgs t with
| (``ZMod, #[(n : Q(ℕ))]) =>
  return .intLike n
    (q((ZMod.commRing _).toRing) : Q(Ring (ZMod $n)))
    (q(ZMod.charP _) : Q(CharP (ZMod $n) $n))
| (``Polynomial, #[(R : Q(Type u)), _]) => do match ← typeToCharP (expensive := expensive) R with
  | (.intLike n _ _) =>
    return .intLike n
      (q(Polynomial.ring) : Q(Ring (Polynomial $R)))
      (q(Polynomial.instCharP _) : Q(CharP (Polynomial $R) $n))
  | .failure => return .failure
| _ => if ! expensive then return .failure else do
  -- Fallback: run an expensive procedures to determine a characteristic,
  -- by looking for a `CharP` instance.
  withNewMCtxDepth do
    /- If we want to support semirings, here we could implement the `natLike` fallback. -/
    let .some instRing ← trySynthInstanceQ q(Ring $t) | return .failure

    let n ← mkFreshExprMVarQ q(ℕ)
    let .some instCharP ← findLocalDeclWithType? q(CharP $t $n) | return .failure

    return .intLike (← instantiateMVarsQ n) instRing (.fvar instCharP)

/-- Given an expression `e`, determine whether it is a numeric expression in characteristic `n`,
and if so, reduce `e` modulo `n`.

This is not a `norm_num` plugin because it does not match on the syntax of `e`,
rather it matches on the type of `e`.

Use `matchAndNorm (expensive := true)` to do more work in finding the characteristic of
the type of `e`.
-/
partial def matchAndNorm (expensive := false) (e : Expr) : MetaM Simp.Result := do
  let α ← inferType e
  let u_succ : Level ← getLevel α
  let (.succ u) := u_succ | throwError "expected {α} to be a `Type _`, not `Sort {u_succ}`"
  have α : Q(Type u) := α
  match ← typeToCharP (expensive := expensive) α with
    | (.intLike n instRing instCharP) =>
      -- Handle the numeric expressions first, e.g. `-5` (which shouldn't become `-1 * 5`)
      normIntNumeral n e instRing instCharP >>= Result.toSimpResult <|>
      normNegCoeffMul n e instRing instCharP <|> -- `-(3 * X) → ((n - 1) * 3) * X`
      normNeg n e instRing instCharP -- `-X → (n - 1) * X`

    /- Here we could add a `natLike` result using only a `Semiring` instance.
    This would activate only the less-powerful procedures
    that cannot handle subtraction.
    -/

    | .failure =>
      throwError "inferred type `{α}` does not have a known characteristic"

-- We use a few `simp` lemmas to preprocess the expression and clean up subterms like `0 * X`.
attribute [reduce_mod_char] sub_eq_add_neg
attribute [reduce_mod_char] zero_add add_zero zero_mul mul_zero one_mul mul_one
attribute [reduce_mod_char] eq_self_iff_true -- For closing non-numeric goals, e.g. `X = X`

/-- Reduce all numeric subexpressions of `e` modulo their characteristic.

Use `derive (expensive := true)` to do more work in finding the characteristic of
the type of `e`.
-/
partial def derive (expensive := false) (e : Expr) : MetaM Simp.Result := do
  withTraceNode `Tactic.reduce_mod_char (fun _ => return m!"{e}") do
  let e ← instantiateMVars e

  let config : Simp.Config := {
    zeta := false
    beta := false
    eta  := false
    proj := false
    iota := false
  }
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ext? ← getSimpExtension? `reduce_mod_char
  let ext ← match ext? with
  | some ext => pure ext
  | none => throwError "internal error: reduce_mod_char not registered as simp extension"
  let ctx : Simp.Context := {
    config := config,
    congrTheorems := congrTheorems,
    simpTheorems := #[← ext.getTheorems]
  }
  let discharge := Mathlib.Meta.NormNum.discharge ctx
  let r : Simp.Result := {expr := e}
  let pre := Simp.preDefault #[] >> fun e =>
      try return (Simp.Step.done (← matchAndNorm (expensive := expensive) e))
      catch _ => pure .continue
  let post := Simp.postDefault #[]
  let r ← r.mkEqTrans (← Simp.main r.expr ctx (methods := { pre, post, discharge? := discharge })).1

  return r

/-- Reduce all numeric subexpressions of the goal modulo their characteristic. -/
partial def reduceModCharTarget (expensive := false) : TacticM Unit := do
  liftMetaTactic1 fun goal ↦ do
    let tgt ← instantiateMVars (← goal.getType)
    let prf ← derive (expensive := expensive) tgt
    if prf.expr.consumeMData.isConstOf ``True then
      match prf.proof? with
      | some proof => goal.assign (← mkOfEqTrue proof)
      | none => goal.assign (mkConst ``True.intro)
      return none
    else
      applySimpResultToTarget goal tgt prf

/-- Reduce all numeric subexpressions of the given hypothesis modulo their characteristic. -/
partial def reduceModCharHyp (expensive := false) (fvarId : FVarId) : TacticM Unit :=
  liftMetaTactic1 fun goal ↦ do
    let hyp ← instantiateMVars (← fvarId.getDecl).type
    let prf ← derive (expensive := expensive) hyp
    return (← applySimpResultToLocalDecl goal fvarId prf false).map (·.snd)

open Parser.Tactic Elab.Tactic

/--
The tactic `reduce_mod_char` looks for numeric expressions in characteristic `p`
and reduces these to lie between `0` and `p`.

For example:
```
example : (5 : ZMod 4) = 1 := by reduce_mod_char
example : (X ^ 2 - 3 * X + 4 : (ZMod 4)[X]) = X ^ 2 + X := by reduce_mod_char
```

It also handles negation, turning it into multiplication by `p - 1`,
and similarly subtraction.

This tactic uses the type of the subexpression to figure out if it is indeed of positive
characteristic, for improved performance compared to trying to synthesise a `CharP` instance.
The variant `reduce_mod_char!` also tries to use `CharP R n` hypotheses in the context.
(Limitations of the typeclass system mean the tactic can't search for a `CharP R n` instance if
`n` is not yet known; use `have : CharP R n := inferInstance; reduce_mod_char!` as a workaround.)
-/
syntax (name := reduce_mod_char) "reduce_mod_char" (location)? : tactic
@[inherit_doc reduce_mod_char]
syntax (name := reduce_mod_char!) "reduce_mod_char!" (location)? : tactic

elab_rules : tactic
| `(tactic| reduce_mod_char $[$loc]?) => unsafe do
  match expandOptLocation (Lean.mkOptionalNode loc) with
  | Location.targets hyps target => do
    (← getFVarIds hyps).forM reduceModCharHyp
    if target then reduceModCharTarget
  | Location.wildcard => do
    (← (← getMainGoal).getNondepPropHyps).forM reduceModCharHyp
    reduceModCharTarget
| `(tactic| reduce_mod_char! $[$loc]?) => unsafe do
  match expandOptLocation (Lean.mkOptionalNode loc) with
  | Location.targets hyps target => do
    (← getFVarIds hyps).forM (reduceModCharHyp (expensive := true))
    if target then reduceModCharTarget (expensive := true)
  | Location.wildcard => do
    (← (← getMainGoal).getNondepPropHyps).forM (reduceModCharHyp (expensive := true))
    reduceModCharTarget (expensive := true)

end ReduceModChar

end Tactic
