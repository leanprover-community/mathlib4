/-
Copyright (c) 2025 Zixun Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Zixun Guo, Wanyi He, Jingting Wang
-/
import Mathlib.Tactic.LieAlgebra.Basic
import Mathlib.Tactic.Module

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

private inductive LieRingConfig
  | simple
  | raw
deriving Inhabited, BEq, Repr

private structure Config where
  /-- The reducibility setting to use when comparing atoms for defEq -/
  red := TransparencyMode.reducible
  /-- If it is `true`, atoms inside ring expressions will be reduced recursively -/
  recursive := true
  /-- The strategy to use for normalizing the expressions in `LieRing` -/
  strategy : LieRingConfig := LieRingConfig.simple
  deriving Inhabited, BEq, Repr

/-- Default elaborator -/
declare_config_elab elabConfig Config

private structure Context where
  ctx : Simp.Context
  simp : Simp.Result → SimpM Simp.Result

private abbrev M := ReaderT Context AtomM

private partial def rewrite (parent : Expr) (root := true) : M Simp.Result :=
  fun nctx rctx s ↦ do
    let pre : Simp.Simproc := fun e =>
      try
        guard <| root || parent != e -- recursion guard
        let e ← withReducible <| whnf e
        guard e.isApp -- all interesting expressions are applications
        let ⟨u, α, e⟩ ← inferTypeQ' e
        let sα ← synthInstanceQ (q(LieRing $α) : Q(Type u))
        let ⟨a, _, pa⟩ ← if ← isAtom α e rctx s then
          (failure : MetaM (Result (ExSum sα) e)) -- No point rewriting atoms
        else
          -- notice that in our design,
          -- when we come across `u • ⁅a, b⁆ + v • ⁅c, d⁆`, we pass `⁅a, b⁆` and `⁅c, d⁆` to `eval`
          -- separately, rather than the whole expr.
          let .const n _ := (← withReducible <| whnf e).getAppFn | failure
          match n with
          | ``Bracket.bracket =>
            eval sα e rctx s
          | _ =>
            -- if it is not a Lie bracket, recursively rewrite the arguments
            -- after failure, the simp process automatically continues into subexpressions
            failure
        let r ← nctx.simp { expr := a, proof? := pa }
        if ← withReducible <| isDefEq r.expr e then return .done { expr := r.expr }
        pure (.done r)
      catch _ => pure <| .continue
    let post := Simp.postDefault #[]
    (·.1) <$> Simp.main parent nctx.ctx (methods := { pre, post })

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

private partial def M.run
    {α : Type} (s : IO.Ref AtomM.State) (cfg : LieRingNF.Config) (x : M α) : MetaM α := do
  let ctx ← Simp.mkContext { singlePass := cfg.strategy matches .raw}
    (simpTheorems := #[← Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) {}])
    (congrTheorems := ← getSimpCongrTheorems)
  let simp ← match cfg.strategy with
  | .raw => pure pure
  | .simple => do
    let thms : SimpTheorems := {}
    let thms ← [ ``lie_smul_left, ``lie_smul_right, ``lie_nsmul_left, ``lie_nsmul_right,
      ``add_lie_left, ``add_lie_right, ``add_zero1, ``zero_smul1, ``one_smul1,
      ``neg_smul1, ``sub_neg
    ].foldlM (·.addConst ·) thms
    let thms ← [``nat_rawCast_0, ``nat_rawCast_1, ``nat_rawCast_2, ``int_rawCast_neg,
      ``rat_rawCast_neg, ``rat_rawCast_pos].foldlM (·.addConst · (post := false)) thms
    let ctx' := ctx.setSimpTheorems #[thms]
    pure fun r' : Simp.Result ↦ do
      r'.mkEqTrans (← Simp.main r'.expr ctx' (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1
  let nctx := { ctx, simp }
  let rec
    /-- The recursive context. -/
    rctx := { red := cfg.red, evalAtom },
    /-- The atom evaluator calls either `LieRingNF.rewrite` recursively,
    or nothing depending on `cfg.recursive`. -/
    evalAtom := if cfg.recursive
      then fun e ↦ rewrite e false nctx rctx s
      else fun e ↦ pure { expr := e }
  x nctx rctx s

open Elab.Tactic Parser.Tactic
/-- Use `lie_ring_nf` to rewrite the main goal. -/
private def lieRingNFTarget
    (s : IO.Ref AtomM.State) (cfg : Config) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let r ← M.run s cfg <| rewrite tgt
  if r.expr.consumeMData.isConstOf ``True then
    goal.assign (← mkOfEqTrue (← r.getProof))
    replaceMainGoal []
  else
    replaceMainGoal [← applySimpResultToTarget goal tgt r]

/-- Use `lie_ring_nf` to rewrite hypothesis `h`. -/
private def lieRingNFLocalDecl (s : IO.Ref AtomM.State) (cfg : Config) (fvarId : FVarId) :
    TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← fvarId.getType)
  let goal ← getMainGoal
  let myres ← M.run s cfg <| rewrite tgt
  match ← applySimpResultToLocalDecl goal fvarId myres false with
  | none => replaceMainGoal []
  | some (_, newGoal) => replaceMainGoal [newGoal]

/--
Simplification tactic for expressions in the language of lie rings,
which rewrites all `LieRing` expressions into a normal form.
* `lie_ring_nf!` will use a more aggressive reducibility setting to identify atoms.
* `lie_ring_nf (config := cfg)` allows for additional configuration:
  * `red`: the reducibility setting (overridden by `!`)
  * `recursive`: if true, `lie_ring_nf` will also recurse into atoms
* `lie_ring_nf` works as both a tactic and a conv tactic.
  In tactic mode, `lie_ring_nf at h` can be used to rewrite in a hypothesis.

  Pay attention to that `lie_ring_nf` is not designed to simplify coefficients of lie algebra.
  We suggest using `module` after `lie_ring_nf` or simply `lie_algebra` to close the goal
  of equation.
-/
elab (name := lie_ringNF) "lie_ring_nf" tk:"!"? cfg:optConfig loc:(location)? : tactic => do
  let mut cfg ← elabConfig cfg
  if tk.isSome then cfg := { cfg with red := .default }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  withLocation loc (lieRingNFLocalDecl s cfg) (lieRingNFTarget s cfg)
    fun _ ↦ throwError "lie_ring_nf failed"

@[inherit_doc lie_ringNF] macro "lie_ring_nf!" cfg:optConfig loc:(location)? : tactic =>
  `(tactic| lie_ring_nf ! $cfg:optConfig $(loc)?)

@[inherit_doc lie_ringNF] syntax (name := ringNFConv) "lie_ring_nf" "!"? optConfig : conv

/--
Tactic for proving equations in `LieRing`.

* This version of `lie_ring1` uses `lie_ring_nf` to simplify in atoms.
* The variant `lie_ring1_nf!` will use a more aggressive reducibility setting
  to determine equality of atoms.
-/
elab (name := lie_ring1NF) "lie_ring1_nf" tk:"!"? cfg:optConfig : tactic => do
  let mut cfg ← elabConfig cfg
  if tk.isSome then cfg := { cfg with red := .default }
  let s ← IO.mkRef {}
  liftMetaMAtMain fun g ↦ M.run s cfg <| proveEq g

@[inherit_doc lie_ring1NF] macro "lie_ring1_nf!" cfg:optConfig : tactic =>
  `(tactic| lie_ring1_nf ! $cfg:optConfig)

@[inherit_doc lie_ringNF] macro "lie_ring_nf!" cfg:optConfig : conv =>
  `(conv| lie_ring_nf ! $cfg:optConfig)

/-- This tactic simply call `module` after `lie_ring`.
  See the documentation for `lie_ring` for more details about configuration.
-/
elab (name := lie_algebra) "lie_algebra" cfg:optConfig : tactic =>
  withMainContext do
    let s ← saveState
    try
      evalTactic (← `(tactic| lie_ring_nf $cfg:optConfig))
      if (← getGoals).isEmpty then
        return
      evalTactic (← `(tactic| module))
      if (← getGoals).isEmpty then return else throwError "failed"
    catch _ =>
      restoreState s
      throwError "tactic failed!"

end Mathlib.Tactic.LieRingNF
