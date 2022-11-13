/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Tim Baanen
-/
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Conv

/-!
# `ring_nf` tactic

A tactic which uses `ring` to rewrite expressions. This can be used non-terminally to normalize
ring expressions in the goal such as `⊢ P (x + x + x)` ~> `⊢ P (x * 3)`, as well as being able to
prove some equations that `ring` cannot because they involve ring reasoning inside a subterm,
such as `sin (x + y) + sin (y + x) = 2 * sin (x + y)`.

-/

namespace Mathlib.Tactic.Ring
open Lean Qq Meta

variable {α : Q(Type u)} (sα : Q(CommSemiring $α)) [CommSemiring R]

theorem add_assoc_rev (a b c : R) : a + (b + c) = a + b + c := (add_assoc ..).symm
theorem mul_assoc_rev (a b c : R) : a * (b * c) = a * b * c := (mul_assoc ..).symm
theorem mul_neg {R} [Ring R] (a b : R) : a * -b = -(a * b) := by simp
theorem add_neg {R} [Ring R] (a b : R) : a + -b = a - b := (sub_eq_add_neg ..).symm
theorem nat_rawCast_0 : (Nat.rawCast 0 : R) = 0 := by simp
theorem nat_rawCast_1 : (Nat.rawCast 1 : R) = 1 := by simp
theorem nat_rawCast_2 [Nat.AtLeastTwo n] : (Nat.rawCast n : R) = OfNat.ofNat n := rfl
theorem int_rawCast_1 {R} [Ring R] : (Int.rawCast (.negOfNat 1) : R) = -1 := by
  simp [Int.negOfNat_eq]
theorem int_rawCast_2 {R} [Ring R] [Nat.AtLeastTwo n] :
    (Int.rawCast (.negOfNat n) : R) = -OfNat.ofNat n := by
  simp [Int.negOfNat_eq, OfNat.ofNat]

/-- True if this represents an atomic expression. -/
def ExBase.isAtom : ExBase sα a → Bool
  | .atom _ => true
  | _ => false

/-- True if this represents an atomic expression. -/
def ExProd.isAtom : ExProd sα a → Bool
  | .mul va₁ (.const 1) (.const 1) => va₁.isAtom
  | _ => false

/-- True if this represents an atomic expression. -/
def ExSum.isAtom : ExSum sα a → Bool
  | .add va₁ va₂ => match va₂ with -- FIXME: this takes a while to compile as one match
    | .zero => va₁.isAtom
    | _ => false
  | _ => false

/-- The normalization style for `ring_nf`. -/
inductive RingMode where
  /-- Sum-of-products form, like `x + x * y * 2 + z ^ 2`. -/
  | SOP
  /-- Raw form: the representation `ring` uses internally. -/
  | raw
  deriving Inhabited, BEq, Repr

/-- Configuration for `ring_nf`. -/
structure RingNF.Config where
  /-- the reducibility setting to use when comparing atoms for defeq -/
  red := TransparencyMode.reducible
  /-- if true, atoms inside ring expressions will be reduced recursively -/
  recursive := true
  /-- The normalization style. -/
  mode := RingMode.SOP
  deriving Inhabited, BEq, Repr

/-- Function elaborating `RingNF.Config`. -/
declare_config_elab elabRingNFConfig RingNF.Config

/--
The core of `ring_nf`, which rewrites the expression `e` into `ring` normal form.

* `s`: a reference to the mutable state of `ring`, for persisting across calls.
  This ensures that atom ordering is used consistently.
* `cfg`: the configuration options
* `e`: the expression to rewrite
-/
partial def ringNFCore (s : IO.Ref State) (cfg : RingNF.Config) (e : Expr) :
    MetaM Simp.Result := do
  let ctx := {
    simpTheorems := #[← Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) {}]
    congrTheorems := ← getSimpCongrTheorems }
  let simp ← match cfg.mode with
  | .raw => pure pure
  | .SOP =>
    let thms : SimpTheorems := {}
    let thms ← [``add_zero, ``add_assoc_rev, ``_root_.mul_one, ``mul_assoc_rev,
      ``_root_.pow_one, ``mul_neg, ``add_neg].foldlM (·.addConst ·) thms
    let thms ← [``nat_rawCast_0, ``nat_rawCast_1, ``nat_rawCast_2, ``int_rawCast_1, ``int_rawCast_2
      ].foldlM (·.addConst · (post := false)) thms
    let ctx' := { ctx with simpTheorems := #[thms] }
    pure fun r' : Simp.Result => do
      Simp.mkEqTrans r' (← Simp.main r'.expr ctx' (methods := Simp.DefaultMethods.methods)).1
  let rec
    /-- The recursive case of `ringNF`.
    * `root`: true when the function is called directly from `ringNFCore`
      and false when called by `evalAtom` in recursive mode.
    * `parent`: The input expression to simplify. In `pre` we make use of both `parent` and `e`
      to determine if we are at the top level in order to prevent a loop
      `go -> eval -> evalAtom -> go` which makes no progress.
    -/
    go root parent :=
      let pre e :=
        try
          guard <| root || parent != e -- recursion guard
          let e ← withReducible <| whnf e
          guard e.isApp -- all interesting ring expressions are applications
          let ⟨.succ u, α, e⟩ ← inferTypeQ e | failure
          let sα ← synthInstanceQ (q(CommSemiring $α) : Q(Type u))
          let c := { rα := (← trySynthInstanceQ (q(Ring $α) : Q(Type u))).toOption }
          let ⟨a, va, pa⟩ ← eval sα c e { red := cfg.red, evalAtom } s
          guard !va.isAtom
          let r ← simp { expr := a, proof? := pa }
          if ← withReducible <| isDefEq r.expr e then return .done { expr := r.expr }
          pure (.done r)
        catch _ => pure <| .visit { expr := e }
      let post := (Simp.postDefault · fun _ => none)
      (·.1) <$> Simp.main parent ctx (methods := { pre, post }),
    /-- The `evalAtom` implementation passed to `eval` calls `go` if `cfg.recursive` is true,
    and does nothing otherwise. -/
    evalAtom := if cfg.recursive then go false else fun e => pure { expr := e }
  go true e

open Elab.Tactic Parser.Tactic
/-- Use `ring_nf` to rewrite the main goal. -/
def ringNFTarget (s : IO.Ref State) (cfg : RingNF.Config) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let r ← ringNFCore s cfg tgt
  if r.expr.isConstOf ``True then
    goal.assign (← mkOfEqTrue (← r.getProof))
    replaceMainGoal []
  else
    replaceMainGoal [← applySimpResultToTarget goal tgt r]

/-- Use `ring_nf` to rewrite hypothesis `h`. -/
def ringNFLocalDecl (s : IO.Ref State) (cfg : RingNF.Config) (fvarId : FVarId) :
    TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← fvarId.getType)
  let goal ← getMainGoal
  let myres ← ringNFCore s cfg tgt
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
elab (name := ringNF) "ring_nf" tk:"!"? cfg:(config ?) loc:(ppSpace location)? : tactic => do
  let mut cfg ← elabRingNFConfig cfg
  if tk.isSome then cfg := { cfg with red := .default }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  withLocation loc (ringNFLocalDecl s cfg) (ringNFTarget s cfg)
    fun _ => throwError "ring_nf failed"

@[inherit_doc ringNF] macro "ring_nf!" cfg:(config)? loc:(ppSpace location)? : tactic =>
  `(tactic| ring_nf ! $(cfg)? $(loc)?)

@[inherit_doc ringNF] syntax (name := ringNFConv) "ring_nf" "!"? (config)? : conv

/-- Elaborator for the `ring_nf` tactic. -/
@[tactic ringNFConv] def elabRingNFConv : Tactic := fun stx => match stx with
  | `(conv| ring_nf $[!%$tk]? $(_cfg)?) => withMainContext do
    let mut cfg ← elabRingNFConfig stx[2]
    if tk.isSome then cfg := { cfg with red := .default }
    let s ← IO.mkRef {}
    Conv.applySimpResult (← ringNFCore s cfg (← instantiateMVars (← Conv.getLhs)))
  | _ => Elab.throwUnsupportedSyntax

@[inherit_doc ringNF] macro "ring_nf!" cfg:(config)? : conv => `(conv| ring_nf ! $(cfg)?)

/--
Tactic for evaluating expressions in *commutative* (semi)rings, allowing for variables in the
exponent.

* `ring!` will use a more aggessive reducibility setting to determine equality of atoms.
* `ring1` fails if the target is not an equality.

For example:
```
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
```
-/
macro (name := ring) "ring" : tactic =>
  `(tactic| first | ring1 | ring_nf; trace "Try this: ring_nf")
@[inherit_doc ring] macro "ring!" : tactic =>
  `(tactic| first | ring1! | ring_nf!; trace "Try this: ring_nf!")

/--
The tactic `ring` evaluates expressions in *commutative* (semi)rings.
This is the conv tactic version, which rewrites a target which is a ring equality to `True`.

See also the `ring` tactic.
-/
macro (name := ringConv) "ring" : conv =>
  `(conv| first | discharge => ring1 | ring_nf; tactic => trace "Try this: ring_nf")
@[inherit_doc ringConv] macro "ring!" : conv =>
  `(conv| first | discharge => ring1! | ring_nf!; tactic => trace "Try this: ring_nf!")
