/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Anne Baanen
-/
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.TryThis
import Mathlib.Tactic.Conv
import Mathlib.Util.AtLocation
import Mathlib.Util.AtomM.Recurse
import Mathlib.Util.Qq

/-!
# `ring_nf` tactic

A tactic which uses `ring` to rewrite expressions. This can be used non-terminally to normalize
ring expressions in the goal such as `⊢ P (x + x + x)` ~> `⊢ P (x * 3)`, as well as being able to
prove some equations that `ring` cannot because they involve ring reasoning inside a subterm,
such as `sin (x + y) + sin (y + x) = 2 * sin (x + y)`.

-/

namespace Mathlib.Tactic
open Lean
open Qq Meta

namespace Ring

variable {u : Level} {arg : Q(Type u)} {sα : Q(CommSemiring $arg)} {a : Q($arg)}

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
structure Config extends AtomM.Recurse.Config where
  /-- if true, then fail if no progress is made -/
  failIfUnchanged := true
  /-- The normalization style. -/
  mode := RingMode.SOP
  deriving Inhabited, BEq, Repr

-- See https://github.com/leanprover/lean4/issues/10295
attribute [nolint unusedArguments] Mathlib.Tactic.RingNF.instReprConfig.repr

/-- Function elaborating `RingNF.Config`. -/
declare_config_elab elabConfig Config

/--
Evaluates an expression `e` into a normalized representation as a polynomial.

This is a variant of `Mathlib.Tactic.Ring.eval`, the main driver of the `ring` tactic.
It differs in
* operating on `Expr` (input) and `Simp.Result` (output), rather than typed `Qq` versions of these;
* throwing an error if the expression `e` is an atom for the `ring` tactic.
-/
def evalExpr (e : Expr) : AtomM Simp.Result := do
  let e ← withReducible <| whnf e
  guard e.isApp -- all interesting ring expressions are applications
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let sα ← synthInstanceQ q(CommSemiring $α)
  let c ← mkCache sα
  let ⟨a, _, pa⟩ ← match ← isAtomOrDerivable q($sα) c q($e) with
  | none => eval sα c e -- `none` indicates that `eval` will find something algebraic.
  | some none => failure -- No point rewriting atoms
  | some (some r) => pure r -- Nothing algebraic for `eval` to use, but `norm_num` simplifies.
  pure { expr := a, proof? := pa }

variable {R : Type*} [CommSemiring R] {n d : ℕ}

theorem add_assoc_rev (a b c : R) : a + (b + c) = a + b + c := (add_assoc ..).symm
theorem mul_assoc_rev (a b c : R) : a * (b * c) = a * b * c := (mul_assoc ..).symm
theorem mul_neg {R} [Ring R] (a b : R) : a * -b = -(a * b) := by simp
theorem add_neg {R} [Ring R] (a b : R) : a + -b = a - b := (sub_eq_add_neg ..).symm
theorem nat_rawCast_0 : (Nat.rawCast 0 : R) = 0 := by simp
theorem nat_rawCast_1 : (Nat.rawCast 1 : R) = 1 := by simp
theorem nat_rawCast_2 [Nat.AtLeastTwo n] : (Nat.rawCast n : R) = OfNat.ofNat n := rfl
theorem int_rawCast_neg {R} [Ring R] : (Int.rawCast (.negOfNat n) : R) = -Nat.rawCast n := by simp
theorem nnrat_rawCast {R} [DivisionSemiring R] :
    (NNRat.rawCast n d : R) = Nat.rawCast n / Nat.rawCast d := by simp
theorem rat_rawCast_neg {R} [DivisionRing R] :
    (Rat.rawCast (.negOfNat n) d : R) = Int.rawCast (.negOfNat n) / Nat.rawCast d := by simp

/-- A cleanup routine, which simplifies normalized polynomials to a more human-friendly format. -/
def cleanup (cfg : RingNF.Config) (r : Simp.Result) : MetaM Simp.Result := do
  match cfg.mode with
  | .raw => pure r
  | .SOP => do
    let thms : SimpTheorems := {}
    let thms ← [``add_zero, ``add_assoc_rev, ``_root_.mul_one, ``mul_assoc_rev,
      ``_root_.pow_one, ``mul_neg, ``add_neg].foldlM (·.addConst ·) thms
    let thms ← [``nat_rawCast_0, ``nat_rawCast_1, ``nat_rawCast_2, ``int_rawCast_neg,
       ``nnrat_rawCast, ``rat_rawCast_neg].foldlM (·.addConst · (post := false)) thms
    let ctx ← Simp.mkContext { zetaDelta := cfg.zetaDelta }
      (simpTheorems := #[thms])
      (congrTheorems := ← getSimpCongrTheorems)
    pure <| ←
      r.mkEqTrans (← Simp.main r.expr ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1

/-- Overrides the default error message in `ring1` to use a prettified version of the goal. -/
initialize ringCleanupRef.set fun e => do
  return (← cleanup {} { expr := e }).expr

open Elab.Tactic Parser.Tactic

/--
Simplification tactic for expressions in the language of commutative (semi)rings,
which rewrites all ring expressions into a normal form.
* `ring_nf!` will use a more aggressive reducibility setting to identify atoms.
* `ring_nf (config := cfg)` allows for additional configuration:
  * `red`: the reducibility setting (overridden by `!`)
  * `zetaDelta`: if true, local let variables can be unfolded (overridden by `!`)
  * `recursive`: if true, `ring_nf` will also recurse into atoms
* `ring_nf` works as both a tactic and a conv tactic.
  In tactic mode, `ring_nf at h` can be used to rewrite in a hypothesis.

This can be used non-terminally to normalize ring expressions in the goal such as
`⊢ P (x + x + x)` ~> `⊢ P (x * 3)`, as well as being able to prove some equations that
`ring` cannot because they involve ring reasoning inside a subterm, such as
`sin (x + y) + sin (y + x) = 2 * sin (x + y)`.
-/
elab (name := ringNF) "ring_nf" tk:"!"? cfg:optConfig loc:(location)? : tactic => do
  let mut cfg ← elabConfig cfg
  if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  let m := AtomM.recurse s cfg.toConfig evalExpr (cleanup cfg)
  transformAtLocation (m ·) "ring_nf" loc cfg.failIfUnchanged false

@[inherit_doc ringNF] macro "ring_nf!" cfg:optConfig loc:(location)? : tactic =>
  `(tactic| ring_nf ! $cfg:optConfig $(loc)?)

@[inherit_doc ringNF] syntax (name := ringNFConv) "ring_nf" "!"? optConfig : conv

/--
Tactic for solving equations of *commutative* (semi)rings, allowing variables in the exponent.

* This version of `ring1` uses `ring_nf` to simplify in atoms.
* The variant `ring1_nf!` will use a more aggressive reducibility setting
  to determine equality of atoms.
-/
elab (name := ring1NF) "ring1_nf" tk:"!"? cfg:optConfig : tactic => do
  let mut cfg ← elabConfig cfg
  if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let s ← IO.mkRef {}
  liftMetaMAtMain fun g ↦ AtomM.RecurseM.run s cfg.toConfig evalExpr (cleanup cfg) <| proveEq g

@[inherit_doc ring1NF] macro "ring1_nf!" cfg:optConfig : tactic =>
  `(tactic| ring1_nf ! $cfg:optConfig)

/-- Elaborator for the `ring_nf` tactic. -/
@[tactic ringNFConv] def elabRingNFConv : Tactic := fun stx ↦ match stx with
  | `(conv| ring_nf $[!%$tk]? $cfg:optConfig) => withMainContext do
    let mut cfg ← elabConfig cfg
    if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
    let s ← IO.mkRef {}
    Conv.applySimpResult
      (← AtomM.recurse s cfg.toConfig evalExpr (cleanup cfg) (← instantiateMVars (← Conv.getLhs)))
  | _ => Elab.throwUnsupportedSyntax

@[inherit_doc ringNF] macro "ring_nf!" cfg:optConfig : conv =>
  `(conv| ring_nf ! $cfg:optConfig)

/--
Tactic for evaluating expressions in *commutative* (semi)rings, allowing for variables in the
exponent. If the goal is not appropriate for `ring` (e.g. not an equality) `ring_nf` will be
suggested.

* `ring!` will use a more aggressive reducibility setting to determine equality of atoms.
* `ring1` fails if the target is not an equality.

For example:
```
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
example (x : ℕ) (h : x * 2 > 5): x + x > 5 := by ring; assumption -- suggests ring_nf
```
-/
macro (name := ring) "ring" : tactic =>
  `(tactic| first | ring1 | try_this ring_nf
  "\n\nThe `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
  \nNote that `ring` works primarily in *commutative* rings. \
  If you have a noncommutative ring, abelian group or module, consider using \
  `noncomm_ring`, `abel` or `module` instead.")
@[inherit_doc ring] macro "ring!" : tactic =>
  `(tactic| first | ring1! | try_this ring_nf!
  "\n\nThe `ring!` tactic failed to close the goal. Use `ring_nf!` to obtain a normal form.
  \nNote that `ring!` works primarily in *commutative* rings. \
  If you have a noncommutative ring, abelian group or module, consider using \
  `noncomm_ring`, `abel` or `module` instead.")

/--
The tactic `ring` evaluates expressions in *commutative* (semi)rings.
This is the conv tactic version, which rewrites a target which is a ring equality to `True`.

See also the `ring` tactic.
-/
macro (name := ringConv) "ring" : conv =>
  `(conv| first | discharge => ring1 | try_this ring_nf
  "\n\nThe `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
  \nNote that `ring` works primarily in *commutative* rings. \
  If you have a noncommutative ring, abelian group or module, consider using \
  `noncomm_ring`, `abel` or `module` instead.")
@[inherit_doc ringConv] macro "ring!" : conv =>
  `(conv| first | discharge => ring1! | try_this ring_nf!
  "\n\nThe `ring!` tactic failed to close the goal. Use `ring_nf!` to obtain a normal form.
  \nNote that `ring!` works primarily in *commutative* rings. \
  If you have a noncommutative ring, abelian group or module, consider using \
  `noncomm_ring`, `abel` or `module` instead.")

end RingNF

end Mathlib.Tactic
