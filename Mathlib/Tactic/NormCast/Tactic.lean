/-
Copyright (c) 2019 Paul-Nicolas Madelaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Nicolas Madelaine, Robert Y. Lewis, Mario Carneiro, Gabriel Ebner
-/

import Mathlib.Tactic.NormCast.Ext
import Mathlib.Tactic.OpenPrivate

open Lean Meta

namespace Tactic.NormCast

open private mkEqTrans from Lean.Meta.Tactic.Simp.Main

def mkEqSymm (e : Expr) (r : Simp.Result) : MetaM Simp.Result :=
  ({ expr := e, proof? := · }) <$>
  match r.proof? with
  | none => pure none
  | some p => some <$> Meta.mkEqSymm p

/-- Prove `a = b` using the given simp set. -/
def proveEqUsing (s : SimpTheorems) (a b : Expr) : MetaM (Option Simp.Result) := do
  let go : SimpM (Option Simp.Result) := do
    let methods := Simp.DefaultMethods.methods
    let a' ← Simp.simp a methods
    let b' ← Simp.simp b methods
    unless ← isDefEq a'.expr b'.expr do return none
    mkEqTrans a' (← mkEqSymm b b')
  withReducible do (go { simpTheorems := s, congrTheorems := ← getSimpCongrTheorems }).run' {}

/-- Prove `a = b` by simplifying using move and squash lemmas. -/
def proveEqUsingDown (a b : Expr) : MetaM (Option Simp.Result) := do
  trace[Tactic.norm_cast] "proving: {← mkEq a b}"
  proveEqUsing (← normCastExt.down.getTheorems) a b

def mkCoe (e : Expr) (ty : Expr) : MetaM Expr := do
  let eType ← inferType e
  let u ← getLevel eType
  let v ← getLevel ty
  let coeTInstType := mkAppN (mkConst ``CoeT [u, v]) #[eType, e, ty]
  let inst ← synthInstance coeTInstType
  expandCoe <| mkAppN (mkConst ``CoeT.coe [u, v]) #[eType, e, ty, inst]

/--
This is the main heuristic used alongside the elim and move lemmas.
The goal is to help casts move past operators by adding intermediate casts.
An Expression of the shape: op (↑(x : α) : γ) (↑(y : β) : γ)
is rewritten to:            op (↑(↑(x : α) : β) : γ) (↑(y : β) : γ)
when (↑(↑(x : α) : β) : γ) = (↑(x : α) : γ) can be proven with a squash lemma
-/
def splittingProcedure (expr : Expr) : MetaM Simp.Result := do
  let Expr.app (Expr.app op x ..) y .. := expr | return {expr}

  let Expr.forallE _ γ (Expr.forallE _ γ' ty ..) .. ← inferType op | return {expr}
  if γ'.hasLooseBVars || ty.hasLooseBVars then return {expr}
  unless ← isDefEq γ γ' do return {expr}

  let some x' ← isCoeOf? x | return {expr}
  let some y' ← isCoeOf? y | return {expr}
  let α ← inferType x'
  let β ← inferType y'

  -- TODO: fast timeout
  try
    let x2 ← mkCoe (← mkCoe x' β) γ
    let some x_x2 ← proveEqUsingDown x x2 | failure
    Simp.mkCongrFun (← Simp.mkCongr {expr := op} x_x2) y
  catch _ => try
    let y2 ← mkCoe (← mkCoe y' α) γ
    let some y_y2 ← proveEqUsingDown y y2 | failure
    Simp.mkCongr {expr := mkApp op x} y_y2
  catch _ =>
    return {expr}

/--
Discharging function used during simplification in the "squash" step.

TODO: normCast takes a list of Expressions to use as lemmas for the discharger
TODO: a tactic to print the results the discharger fails to proove
-/
def prove (e : Expr) : SimpM (Option Expr) :=
  return none -- FIXME assumption

/--
Core rewriting function used in the "squash" step, which moves casts upwards
and eliminates them.

It tries to rewrite an expression using the elim and move lemmas.
On failure, it calls the splitting procedure heuristic.
-/
def upwardAndElim (e : Expr) : SimpM Simp.Step := do
  let thms ← getSimpTheorems
  let r ← Simp.rewrite e thms.post thms.erased prove (tag := "squash")
  if r.expr != e then return Simp.Step.visit r
  Simp.Step.visit <$> splittingProcedure e

/--
The core simplification routine of `normCast`.
-/
def derive (e : Expr) : MetaM Simp.Result := do
  let e ← instantiateMVars e

  let config : Simp.Config := {
    zeta := false
    beta := false
    eta  := false
    proj := false
    iota := false
  }
  let congrTheorems ← getSimpCongrTheorems

  let r := {expr := e}

  -- step 2: casts are moved upwards and eliminated
  let r ← mkEqTrans r <|<- Simp.main r.expr
    { config, congrTheorems, simpTheorems := ← normCastExt.up.getTheorems }
    { pre := upwardAndElim }
  trace[Tactic.norm_cast] "after upwardAndElim: {r.expr}"

  -- step 3: casts are squashed
  let r ← mkEqTrans r <|<- simp r.expr {
    simpTheorems := ← normCastExt.squash.getTheorems
    config, congrTheorems
  }
  trace[Tactic.norm_cast] "after squashing: {r.expr}"

  return r

/--
A small variant of `pushCast` suited for non-interactive use.

`derivePushCast extra_lems e` returns an Expression `e'` and a proof that `e = e'`.
-/
def derivePushCast (extra_lems : List simp_arg_type) (e : Expr) : MetaM Simp.Result :=
do (s, _) ← mk_simp_set tt [`pushCast] extra_lems,
   (e, prf, _) ← simplify (s.erase [`int.coe_nat_succ]) [] e
                  {fail_if_unchanged := ff} `eq tactic.assumption,
   return (e, prf)

/-- `auxModCast e` runs `normCast` on `e` and returns the result. If `include_goal` is true, it
also normalizes the goal. -/
meta def auxModCast (e : Expr) (include_goal : bool := tt) : tactic Expr :=
match e with
| local_const _ lc _ _ := do
  e ← get_local lc,
  replace_at derive [e] include_goal,
  get_local lc
| e := do
  t ← infer_type e,
  e ← assertv `this t e,
  replace_at derive [e] include_goal,
  get_local `this
end

/-- `exactModCast e` runs `normCast` on the goal and `e`, and tries to use `e` to close the
goal. -/
meta def exactModCast (e : Expr) : tactic unit :=
decorate_error "exactModCast failed:" $ do
  new_e ← auxModCast e,
  exact new_e

/-- `applyModCast e` runs `normCast` on the goal and `e`, and tries to apply `e`. -/
meta def applyModCast (e : Expr) : tactic (list (name × Expr)) :=
decorate_error "applyModCast failed:" $ do
  new_e ← auxModCast e,
  apply new_e

/-- `assumptionModCast` runs `normCast` on the goal. For each local hypothesis `h`, it also
normalizes `h` and tries to use that to close the goal. -/
meta def assumptionModCast : tactic unit :=
decorate_error "assumptionModCast failed:" $ do
  let cfg : simp_config :=
  { fail_if_unchanged := ff,
    canonize_instances := ff,
    canonize_proofs := ff,
    proj := ff },
  replace_at derive [] tt,
  ctx ← local_context,
  ctx.mfirst (λ h, auxModCast h ff >>= tactic.exact)

end tactic

namespace tactic.interactive
open tactic normCast

/--
Normalize casts at the given locations by moving them "upwards".
As opposed to simp, normCast can be used without necessarily closing the goal.
-/
meta def normCast (loc : parse location) : tactic unit :=
do
  ns ← loc.get_locals,
  tt ← replace_at derive ns loc.include_goal | fail "normCast failed to simplify",
  when loc.include_goal $ try tactic.reflexivity,
  when loc.include_goal $ try tactic.triv,
  when (¬ ns.empty) $ try tactic.contradiction

/--
Rewrite with the given rules and normalize casts between steps.
-/
meta def rwModCast (rs : parse rw_rules) (loc : parse location) : tactic unit :=
decorate_error "rwModCast failed:" $ do
  let cfg_norm : simp_config := {},
  let cfg_rw : rewrite_cfg := {},
  ns ← loc.get_locals,
  monad.mapm' (λ r : rw_rule, do
    save_info r.pos,
    replace_at derive ns loc.include_goal,
    rw ⟨[r], none⟩ loc {}
  ) rs.rules,
  replace_at derive ns loc.include_goal,
  skip

/--
Normalize the goal and the given Expression, then close the goal with exact.
-/
meta def exactModCast (e : parse texpr) : tactic unit :=
do
  e ← iTo_expr e <|> do
  { ty ← target,
    e ← iTo_expr_strict ``(%%e : %%ty),
    pty ← pp ty, ptgt ← pp e,
    fail ("exactModCast failed, Expression type not directly " ++
    "inferrable. Try:\n\nexactModCast ...\nshow " ++
    to_fmt pty ++ ",\nfrom " ++ ptgt : format) },
  tactic.exactModCast e

/--
Normalize the goal and the given Expression, then apply the Expression to the goal.
-/
meta def applyModCast (e : parse texpr) : tactic unit :=
do
  e ← iTo_expr_for_apply e,
  concat_tags $ tactic.applyModCast e

/--
Normalize the goal and every Expression in the local context, then close the goal with assumption.
-/
meta def assumptionModCast : tactic unit :=
tactic.assumptionModCast

end tactic.interactive

namespace conv.interactive
open conv
open normCast (derive)

/-- the converter version of `normCast' -/
meta def normCast : conv unit := replace_lhs derive

end conv.interactive

-- TODO: move this elsewhere?
@[norm_cast] lemma ite_cast {α β} [has_lift_t α β]
  {c : Prop} [decidable c] {a b : α} :
  ↑(ite c a b) = ite c (↑a : β) (↑b : β) :=
by by_cases h : c; simp [h]

@[norm_cast] lemma dite_cast {α β} [has_lift_t α β]
  {c : Prop} [decidable c] {a : c → α} {b : ¬ c → α} :
  ↑(dite c a b) = dite c (λ h, (↑(a h) : β)) (λ h, (↑(b h) : β)) :=
by by_cases h : c; simp [h]

add_hint_tactic "norm_cast at *"

/-
The `norm_cast` family of tactics is used to normalize casts inside Expressions.
It is basically a simp tactic with a specific set of lemmas to move casts
upwards in the Expression.
Therefore it can be used more safely as a non-terminating tactic.
It also has special handling of numerals.

For instance, given an assumption
```lean
a b : ℤ
h : ↑a + ↑b < (10 : ℚ)
```

writing `norm_cast at h` will turn `h` into
```lean
h : a + b < 10
```

You can also use `exact_mod_cast`, `apply_mod_cast`, `rw_mod_cast`
or `assumption_mod_cast`.
Writing `exact_mod_cast h` and `apply_mod_cast h` will normalize the goal and
`h` before using `exact h` or `apply h`.
Writing `assumption_mod_cast` will normalize the goal and for every
Expression `h` in the context it will try to normalize `h` and use
`exact h`.
`rw_mod_cast` acts like the `rw` tactic but it applies `norm_cast` between steps.

`push_cast` rewrites the Expression to move casts toward the leaf nodes.
This uses `norm_cast` lemmas in the forward direction.
For example, `↑(a + b)` will be written to `↑a + ↑b`.
It is equivalent to `simp only with push_cast`.
It can also be used at hypotheses with `push_cast at h`
and with extra simp lemmas with `push_cast [int.add_zero]`.

```lean
example (a b : ℕ) (h1 : ((a + b : ℕ) : ℤ) = 10) (h2 : ((a + b + 0 : ℕ) : ℤ) = 10) :
  ((a + b : ℕ) : ℤ) = 10 :=
begin
  push_cast,
  push_cast at h1,
  push_cast [int.add_zero] at h2,
end
```

The implementation and behavior of the `norm_cast` family is described in detail at
<https://lean-forward.github.io/norm_cast/norm_cast.pdf>.
-/
-- add_tactic_doc
-- { name := "norm_cast",
--   category   := doc_category.tactic,
--   decl_names := [``tactic.interactive.norm_cast, ``tactic.interactive.rw_mod_cast,
--                  ``tactic.interactive.apply_mod_cast, ``tactic.interactive.assumption_mod_cast,
--                  ``tactic.interactive.exact_mod_cast, ``tactic.interactive.push_cast],
--   tags       := ["coercions", "simplification"] }
-- TODO

