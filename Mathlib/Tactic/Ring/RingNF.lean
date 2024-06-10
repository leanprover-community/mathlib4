/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Anne Baanen
-/
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.TryThis
import Mathlib.Tactic.Conv
import Mathlib.Util.Qq

/-!
# `ring_nf` tactic

A tactic which uses `ring` to rewrite expressions. This can be used non-terminally to normalize
ring expressions in the goal such as `⊢ P (x + x + x)` ~> `⊢ P (x * 3)`, as well as being able to
prove some equations that `ring` cannot because they involve ring reasoning inside a subterm,
such as `sin (x + y) + sin (y + x) = 2 * sin (x + y)`.

-/

set_option autoImplicit true

-- In this file we would like to be able to use multi-character auto-implicits.
set_option relaxedAutoImplicit true

namespace Mathlib.Tactic
open Lean hiding Rat
open Qq Meta

namespace Ring

/-- True if this represents an atomic expression. -/
def ExBase.isAtom : ExBase sα a → Bool
  | .atom _ => true
  | _ => false

/-- True if this represents an atomic expression. -/
def ExProd.isAtom : ExProd sα a → Bool
  | .mul va₁ (.const 1 _) (.const 1 _) => va₁.isAtom
  | _ => false

/-- True if this represents an atomic expression. -/
def ExSum.isAtom : ExSum sα a → Bool
  | .add va₁ va₂ => match va₂ with -- FIXME: this takes a while to compile as one match
    | .zero => va₁.isAtom
    | _ => false
  | _ => false

end Ring

namespace RingNF
open Ring

/-- The normalization style for `ring_nf`. -/
inductive RingMode where
  /-- Sum-of-products form, like `x + x * y * 2 + z ^ 2`. -/
  | SOP
  /-- Raw form: the representation `ring` uses internally. -/
  | raw
  deriving Inhabited, BEq, Repr

/-- Configuration for `ring_nf`. -/
structure Config where
  /-- the reducibility setting to use when comparing atoms for defeq -/
  red := TransparencyMode.reducible
  /-- if true, atoms inside ring expressions will be reduced recursively -/
  recursive := true
  /-- The normalization style. -/
  mode := RingMode.SOP
  deriving Inhabited, BEq, Repr

/-- Function elaborating `RingNF.Config`. -/
declare_config_elab elabConfig Config

/-- The read-only state of the `RingNF` monad. -/
structure Context where
  /-- A basically empty simp context, passed to the `simp` traversal in `RingNF.rewrite`. -/
  ctx : Simp.Context
  /-- A cleanup routine, which simplifies normalized polynomials to a more human-friendly
  format. -/
  simp : Simp.Result → SimpM Simp.Result

/-- The monad for `RingNF` contains, in addition to the `AtomM` state,
a simp context for the main traversal and a simp function (which has another simp context)
to simplify normalized polynomials. -/
abbrev M := ReaderT Context AtomM

/--
A tactic in the `RingNF.M` monad which will simplify expression `parent` to a normal form.
* `root`: true if this is a direct call to the function.
  `RingNF.M.run` sets this to `false` in recursive mode.
-/
def rewrite (parent : Expr) (root := true) : M Simp.Result :=
  fun nctx rctx s ↦ do
    let pre : Simp.Simproc := fun e =>
      try
        guard <| root || parent != e -- recursion guard
        let e ← withReducible <| whnf e
        guard e.isApp -- all interesting ring expressions are applications
        let ⟨u, α, e⟩ ← inferTypeQ' e
        let sα ← synthInstanceQ (q(CommSemiring $α) : Q(Type u))
        let c ← mkCache sα
        let ⟨a, _, pa⟩ ← match ← isAtomOrDerivable sα c e rctx s with
        | none => eval sα c e rctx s -- `none` indicates that `eval` will find something algebraic.
        | some none => failure -- No point rewriting atoms
        | some (some r) => pure r -- Nothing algebraic for `eval` to use, but `norm_num` simplifies.
        let r ← nctx.simp { expr := a, proof? := pa }
        if ← withReducible <| isDefEq r.expr e then return .done { expr := r.expr }
        pure (.done r)
      catch _ => pure <| .continue
    let post := Simp.postDefault #[]
    (·.1) <$> Simp.main parent nctx.ctx (methods := { pre, post })

variable [CommSemiring R]

theorem add_assoc_rev (a b c : R) : a + (b + c) = a + b + c := (add_assoc ..).symm
theorem mul_assoc_rev (a b c : R) : a * (b * c) = a * b * c := (mul_assoc ..).symm
theorem mul_neg {R} [Ring R] (a b : R) : a * -b = -(a * b) := by simp
theorem add_neg {R} [Ring R] (a b : R) : a + -b = a - b := (sub_eq_add_neg ..).symm
theorem nat_rawCast_0 : (Nat.rawCast 0 : R) = 0 := by simp
theorem nat_rawCast_1 : (Nat.rawCast 1 : R) = 1 := by simp
theorem nat_rawCast_2 [Nat.AtLeastTwo n] : (Nat.rawCast n : R) = OfNat.ofNat n := rfl
theorem int_rawCast_neg {R} [Ring R] : (Int.rawCast (.negOfNat n) : R) = -Nat.rawCast n := by simp
theorem rat_rawCast_pos {R} [DivisionRing R] :
    (Rat.rawCast (.ofNat n) d : R) = Nat.rawCast n / Nat.rawCast d := by simp
theorem rat_rawCast_neg {R} [DivisionRing R] :
    (Rat.rawCast (.negOfNat n) d : R) = Int.rawCast (.negOfNat n) / Nat.rawCast d := by simp

/--
Runs a tactic in the `RingNF.M` monad, given initial data:

* `s`: a reference to the mutable state of `ring`, for persisting across calls.
  This ensures that atom ordering is used consistently.
* `cfg`: the configuration options
* `x`: the tactic to run
-/
partial def M.run
    (s : IO.Ref AtomM.State) (cfg : RingNF.Config) (x : M α) : MetaM α := do
  let ctx := {
    simpTheorems := #[← Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) {}]
    congrTheorems := ← getSimpCongrTheorems
    config.singlePass := cfg.mode matches .raw }
  let simp ← match cfg.mode with
  | .raw => pure pure
  | .SOP =>
    let thms : SimpTheorems := {}
    let thms ← [``add_zero, ``add_assoc_rev, ``_root_.mul_one, ``mul_assoc_rev,
      ``_root_.pow_one, ``mul_neg, ``add_neg].foldlM (·.addConst ·) thms
    let thms ← [``nat_rawCast_0, ``nat_rawCast_1, ``nat_rawCast_2, ``int_rawCast_neg,
      ``rat_rawCast_neg, ``rat_rawCast_pos].foldlM (·.addConst · (post := false)) thms
    let ctx' := { ctx with simpTheorems := #[thms] }
    pure fun r' : Simp.Result ↦ do
      r'.mkEqTrans (← Simp.main r'.expr ctx' (methods := ← Lean.Meta.Simp.mkDefaultMethods)).1
  let nctx := { ctx, simp }
  let rec
    /-- The recursive context. -/
    rctx := { red := cfg.red, evalAtom },
    /-- The atom evaluator calls either `RingNF.rewrite` recursively,
    or nothing depending on `cfg.recursive`. -/
    evalAtom := if cfg.recursive
      then fun e ↦ rewrite e false nctx rctx s
      else fun e ↦ pure { expr := e }
  x nctx rctx s

/-- Overrides the default error message in `ring1` to use a prettified version of the goal. -/
initialize ringCleanupRef.set fun e => do
  M.run (← IO.mkRef {}) { recursive := false } fun nctx _ _ =>
    return (← nctx.simp { expr := e } ({} : Lean.Meta.Simp.Methods).toMethodsRef nctx.ctx
      |>.run {}).1.expr

open Elab.Tactic Parser.Tactic
/-- Use `ring_nf` to rewrite the main goal. -/
def ringNFTarget (s : IO.Ref AtomM.State) (cfg : Config) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let r ← M.run s cfg <| rewrite tgt
  if r.expr.consumeMData.isConstOf ``True then
    goal.assign (← mkOfEqTrue (← r.getProof))
    replaceMainGoal []
  else
    replaceMainGoal [← applySimpResultToTarget goal tgt r]

/-- Use `ring_nf` to rewrite hypothesis `h`. -/
def ringNFLocalDecl (s : IO.Ref AtomM.State) (cfg : Config) (fvarId : FVarId) :
    TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← fvarId.getType)
  let goal ← getMainGoal
  let myres ← M.run s cfg <| rewrite tgt
  match ← applySimpResultToLocalDecl goal fvarId myres false with
  | none => replaceMainGoal []
  | some (_, newGoal) => replaceMainGoal [newGoal]

/--
Simplification tactic for expressions in the language of commutative (semi)rings,
which rewrites all ring expressions into a normal form.
* `ring_nf!` will use a more aggressive reducibility setting to identify atoms.
* `ring_nf (config := cfg)` allows for additional configuration:
  * `red`: the reducibility setting (overridden by `!`)
  * `recursive`: if true, `ring_nf` will also recurse into atoms
* `ring_nf` works as both a tactic and a conv tactic.
  In tactic mode, `ring_nf at h` can be used to rewrite in a hypothesis.
-/
elab (name := ringNF) "ring_nf" tk:"!"? cfg:(config ?) loc:(location)? : tactic => do
  let mut cfg ← elabConfig cfg
  if tk.isSome then cfg := { cfg with red := .default }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  withLocation loc (ringNFLocalDecl s cfg) (ringNFTarget s cfg)
    fun _ ↦ throwError "ring_nf failed"

@[inherit_doc ringNF] macro "ring_nf!" cfg:(config)? loc:(location)? : tactic =>
  `(tactic| ring_nf ! $(cfg)? $(loc)?)

@[inherit_doc ringNF] syntax (name := ringNFConv) "ring_nf" "!"? (config)? : conv

/--
Tactic for solving equations of *commutative* (semi)rings, allowing variables in the exponent.

* This version of `ring1` uses `ring_nf` to simplify in atoms.
* The variant `ring1_nf!` will use a more aggressive reducibility setting
  to determine equality of atoms.
-/
elab (name := ring1NF) "ring1_nf" tk:"!"? cfg:(config ?) : tactic => do
  let mut cfg ← elabConfig cfg
  if tk.isSome then cfg := { cfg with red := .default }
  let s ← IO.mkRef {}
  liftMetaMAtMain fun g ↦ M.run s cfg <| proveEq g

@[inherit_doc ring1NF] macro "ring1_nf!" cfg:(config)? : tactic => `(tactic| ring1_nf ! $(cfg)?)

/-- Elaborator for the `ring_nf` tactic. -/
@[tactic ringNFConv] def elabRingNFConv : Tactic := fun stx ↦ match stx with
  | `(conv| ring_nf $[!%$tk]? $(_cfg)?) => withMainContext do
    let mut cfg ← elabConfig stx[2]
    if tk.isSome then cfg := { cfg with red := .default }
    let s ← IO.mkRef {}
    Conv.applySimpResult (← M.run s cfg <| rewrite (← instantiateMVars (← Conv.getLhs)))
  | _ => Elab.throwUnsupportedSyntax

@[inherit_doc ringNF] macro "ring_nf!" cfg:(config)? : conv => `(conv| ring_nf ! $(cfg)?)

/--
Tactic for evaluating expressions in *commutative* (semi)rings, allowing for variables in the
exponent.

* `ring!` will use a more aggressive reducibility setting to determine equality of atoms.
* `ring1` fails if the target is not an equality.

For example:
```
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
```
-/
macro (name := ring) "ring" : tactic =>
  `(tactic| first | ring1 | try_this ring_nf)
@[inherit_doc ring] macro "ring!" : tactic =>
  `(tactic| first | ring1! | try_this ring_nf!)

/--
The tactic `ring` evaluates expressions in *commutative* (semi)rings.
This is the conv tactic version, which rewrites a target which is a ring equality to `True`.

See also the `ring` tactic.
-/
macro (name := ringConv) "ring" : conv =>
  `(conv| first | discharge => ring1 | try_this ring_nf)
@[inherit_doc ringConv] macro "ring!" : conv =>
  `(conv| first | discharge => ring1! | try_this ring_nf!)
