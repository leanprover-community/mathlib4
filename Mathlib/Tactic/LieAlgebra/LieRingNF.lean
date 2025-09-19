/-
Copyright (c) 2025 Zixun Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Zixun Guo, Wanyi He, Jingting Wang
-/
import Mathlib.Tactic.LieAlgebra.Basic
import Mathlib.Tactic.Module
import Mathlib.Util.AtomM.Recurse

/-!
# `lie_ring_nf` tactic

A tactic that uses `lie_ring` to simplify expressions to Lyndon normal form.
It is expected that this tactic is one of the building blocks to the `lie_algebra` tactic.

The implementation of this tactic follows the `ring_nf` tactic.
-/

open Lean Meta Elab Mathlib.Tactic Qq

namespace Mathlib.Tactic

open Mathlib.Tactic.LieRing

namespace LieRingNF

/-- The mode of simplification for `lie_ring_nf` tactic. -/
inductive LieRingMode
  /-- If set to `.simple`, simp lemmas will be applied to the result to make it more concise. -/
  | simple
  /-- If set to `.raw`, the normal form will be the raw result returned from the internal
  representation of this tactic. -/
  | raw
  deriving Inhabited, BEq, Repr

/-- The config for `lie_ring_nf` tactic. -/
structure Config extends AtomM.Recurse.Config where
  /-- The mode of normalizing the expressions in `LieRing` -/
  mode : LieRingMode := LieRingMode.simple
  deriving Inhabited, BEq, Repr

-- See https://github.com/leanprover/lean4/issues/10295
attribute [nolint unusedArguments] Mathlib.Tactic.LieRingNF.instReprConfig.repr

/-- Default elaborator of `LieRingNF.config` -/
declare_config_elab elabConfig Config

/-- Evaluate an expression `e` into a normalized form. -/
def evalExpr (e : Expr) : AtomM Simp.Result := do
  let e ← withReducible <| whnf e
  guard e.isApp -- all interesting expressions we consider are applications
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let sα ← synthInstanceQ (q(LieRing $α) : Q(Type u))
  let ⟨a, _, pa⟩ ← if ← isAtom α e then failure -- No point rewriting atoms
    else
    -- Notice that in our design, when we come across `u • ⁅a, b⁆ + v • ⁅c, d⁆`,
    -- we pass `⁅a, b⁆` and `⁅c, d⁆` to `eval` separately, rather than the whole expr.
    let .const n _ := (← withReducible <| whnf e).getAppFn | failure
    match n with
    | ``Bracket.bracket => eval sα e
    | _ => failure
  pure {expr := a, proof? := pa}

section SimpLemmas
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {n d : ℕ}

private theorem zero_smul1 (a : L) : (0 : R) • a = 0 := zero_smul _ _
private theorem add_zero1 (a : L) : a + 0 = a := add_zero _
private theorem one_smul1 (a : L) : (1 : R) • a = a := one_smul _ _
private theorem neg_smul1 (r : R) (a : L) : (-r) • a = -(r • a) := by simp
private theorem lie_smul_left (r : R) (a b : L) : ⁅(r • a), b⁆ = r • ⁅a, b⁆ := by simp
private theorem lie_smul_right (r : R) (a b : L) : ⁅a, (r • b)⁆ = r • ⁅a, b⁆ := by simp
private theorem lie_nsmul_left (n : ℕ) (a b : L) : ⁅(n • a), b⁆ = n • ⁅a, b⁆ := by simp
private theorem lie_nsmul_right (n : ℕ) (a b : L) : ⁅a, n • b⁆ = n • ⁅a, b⁆ := by simp
private theorem add_lie_left (a b c : L) : ⁅(a + b), c⁆ = ⁅a, c⁆ + ⁅b, c⁆ := by simp
private theorem add_lie_right (a b c : L) : ⁅a, (b + c)⁆ = ⁅a, b⁆ + ⁅a, c⁆ := by simp
private theorem nat_rawCast_0 : (Nat.rawCast 0 : R) = 0 := by simp
private theorem nat_rawCast_1 : (Nat.rawCast 1 : R) = 1 := by simp
private theorem nat_rawCast_2 [Nat.AtLeastTwo n] : (Nat.rawCast n : R) = OfNat.ofNat n := rfl
private theorem int_rawCast_neg {R} [Ring R] :
    (Int.rawCast (.negOfNat n) : R) = -Nat.rawCast n := by simp
private theorem rat_rawCast_pos {R} [DivisionRing R] :
    (Rat.rawCast (.ofNat n) d : R) = Nat.rawCast n / Nat.rawCast d := by simp
private theorem rat_rawCast_neg {R} [DivisionRing R] :
    (Rat.rawCast (.negOfNat n) d : R) = Int.rawCast (.negOfNat n) / Nat.rawCast d := by simp

end SimpLemmas

/-- The theorems used in the simplification process. -/
private def simp_theorems : MetaM SimpTheorems := do
  let thms : SimpTheorems := {}
  let thms ← [ ``lie_smul_left, ``lie_smul_right, ``lie_nsmul_left, ``lie_nsmul_right,
    ``add_lie_left, ``add_lie_right, ``add_zero1, ``zero_smul1, ``one_smul1,
    ``neg_smul1, ``sub_neg
  ].foldlM (·.addConst ·) thms
  let thms ← [``nat_rawCast_0, ``nat_rawCast_1, ``nat_rawCast_2, ``int_rawCast_neg,
    ``rat_rawCast_neg, ``rat_rawCast_pos].foldlM (·.addConst · (post := false)) thms
  pure thms

/-- The `simp` context used in the simplification process. -/
private def simp_ctx (cfg : LieRingNF.Config) : MetaM Simp.Context := do
  let thms ← simp_theorems
  Simp.mkContext { zetaDelta := cfg.zetaDelta }
    (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)

/-- The cleanup process after normalizing the expression using `evalExpr` to a more human-friendly
format. -/
def cleanup (cfg : LieRingNF.Config) (r : Simp.Result) : MetaM Simp.Result := do
  match cfg.mode with
  | .raw => pure r
  | .simple => do
    let ctx ← simp_ctx cfg
    pure <| ←
      r.mkEqTrans (← Simp.main r.expr ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1

open Elab.Tactic Parser.Tactic
/--
Simplification tactic for expressions in the language of Lie rings,
which rewrites all `LieRing` expressions into a normal form.
* `lie_ring_nf!` will use a more aggressive reducibility setting to identify atoms.
* `lie_ring_nf (config := cfg)` allows for additional configuration:
  * `red`: the reducibility setting (overridden by `!`)
  * `recursive`: if true, `lie_ring_nf` will also recurse into atoms
* In tactic mode, `lie_ring_nf at h` can be used to rewrite in a hypothesis.

  Please notice that `lie_ring_nf` is not designed to simplify coefficients of lie algebra.
  We suggest using `module` after `lie_ring_nf` or simply `lie_algebra` to close the goal
  of equation.
-/
elab (name := lie_ringNF) "lie_ring_nf" tk:"!"? cfg:optConfig loc:(location)? : tactic => do
  let mut cfg ← elabConfig cfg
  if tk.isSome then cfg := { cfg with red := .default }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  -- We have to run the simp process first to extract all scalars before running our tactic.
  let m : Expr → MetaM Simp.Result := fun tgt => do
    let r ← Simp.main tgt (← simp_ctx cfg) (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})
    pure <| ← r.1.mkEqTrans (← AtomM.recurse s cfg.toConfig evalExpr (cleanup cfg) r.1.expr)
  transformAtLocation (m ·) "lie_ring_nf" loc (failIfUnchanged := false)

@[inherit_doc lie_ringNF] macro "lie_ring_nf!" cfg:optConfig loc:(location)? : tactic =>
  `(tactic| lie_ring_nf ! $cfg:optConfig $(loc)?)

/-- This tactic simply call `module` after `lie_ring`.
  See the documentation for `lie_ring` for more details about configuration.
-/
elab (name := lie_algebra) "lie_algebra" cfg:optConfig : tactic =>
  withMainContext do
    let s ← saveState
    try
      evalTactic (← `(tactic| lie_ring_nf $cfg:optConfig))
      if (← getGoals).isEmpty then return
      evalTactic (← `(tactic| module))
      if (← getGoals).isEmpty then return else throwError "failed"
    catch _ =>
      restoreState s
      throwError "tactic failed!"

end Mathlib.Tactic.LieRingNF
