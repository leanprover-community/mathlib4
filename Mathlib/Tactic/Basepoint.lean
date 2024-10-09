/-
Copyright (c) 2024 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Algebra.AddTorsor

/-!
# A tactic for moving calculations from affine space to vector space
-/

open Lean Elab Meta Qq

theorem foo_iff {V P : Type*} [AddCommGroup V] (i : AddTorsor V P) {a b : V} {x₀ y z : P}
    (hy : y = a +ᵥ x₀) (hz : z = b +ᵥ x₀) :
    y = z ↔ a = b :=
  hy ▸ hz ▸ vadd_right_cancel_iff x₀

theorem foo {V P : Type*} [AddCommGroup V] [AddTorsor V P] {a b : V} {x₀ y z : P}
    (hy : y = a +ᵥ x₀) (hz : z = b +ᵥ x₀) (h : a = b) :
    y = z :=
  hy ▸ hz ▸ h ▸ rfl

theorem bar_iff {V : Type*} [AddCommGroup V] {a b lhs rhs : V}
    (hy : lhs = a) (hz : rhs = b) :
    lhs = rhs ↔ a = b:=
  hy ▸ hz ▸ Iff.rfl

theorem bar {V : Type*} [AddCommGroup V] {a b lhs rhs : V}
    (hy : lhs = a) (hz : rhs = b) (h : a = b) :
    lhs = rhs :=
  hy ▸ hz ▸ h ▸ rfl

variable {u v : Level} {V : Q(Type u)} {P : Q(Type v)}

mutual

partial def parseAddTorsor (iV : Q(AddCommGroup $V)) (iVP : Q(AddTorsor $V $P)) (x₀ x : Q($P)) :
    MetaM (Σ a : Q($V), Q($x = $a +ᵥ $x₀)) := do
  match x with
  | ~q(@HVAdd.hVAdd _ _ _ (@instHVAdd $V' _ $i) $a $y) =>
    guard (V == V')
    have a : Q($V) := a
    let ⟨a', ha⟩ ← parseAddCommGroup iV iVP x₀ a
    let ⟨b, hb⟩ ← parseAddTorsor iV iVP x₀ y
    pure ⟨q($a' + $b), q(sorry)⟩
  | _ =>
    if x == x₀ then
      pure ⟨q(0), q(sorry)⟩
    else
      pure ⟨q($x -ᵥ $x₀), q(sorry)⟩

partial def parseAddCommGroup (iV : Q(AddCommGroup $V)) (iVP : Q(AddTorsor $V $P)) (x₀ : Q($P))
    (a : Q($V)) :
    MetaM (Σ b : Q($V), Q($a = $b)) := do
  match a with
  | ~q(@VSub.vsub _ $P' $i $x $y) =>
    guard (P == P')
    have x : Q($P) := x
    have y : Q($P) := y
    if y == x₀ then
      if x == x₀ then
        pure ⟨q(0), q(sorry)⟩
      else
        let ⟨b, hb⟩ ← parseAddTorsor iV iVP x₀ x
        pure ⟨b, q(sorry)⟩
    else
      let ⟨b, hb⟩ ← parseAddTorsor iV iVP x₀ x
      let ⟨c, hc⟩ ← parseAddTorsor iV iVP x₀ y
      pure ⟨q($b - $c), q(sorry)⟩
  | ~q($a + $a') =>
    let ⟨b, hb⟩ ← parseAddCommGroup iV iVP x₀ a
    let ⟨b', hb'⟩ ← parseAddCommGroup iV iVP x₀ a'
    pure ⟨q($b + $b'), q(sorry)⟩
  | ~q($a - $a') =>
    let ⟨b, hb⟩ ← parseAddCommGroup iV iVP x₀ a
    let ⟨b', hb'⟩ ← parseAddCommGroup iV iVP x₀ a'
    pure ⟨q($b - $b'), q(sorry)⟩
  | ~q(@HSMul.hSMul _ _ _ (@instHSMul _ _ $i) $r $a) =>
    let ⟨b, hb⟩ ← parseAddCommGroup iV iVP x₀ a
    pure ⟨q($r • $b), q(sorry)⟩
  | _ => pure ⟨a, q(sorry)⟩

end

def mkBasepointIff (V x₀ : Expr) (e : Q(Prop)) : MetaM (Σ e' : Q(Prop), Q($e ↔ $e')) := do
  /- Parse the first provided expression `V` as a type carrying an `AddCommGroup V` instance. -/
  let .sort u₀ ← whnf (← inferType V) | unreachable!
  let some u := u₀.dec | unreachable!
  have V : Q(Type u) := V
  let iV ← synthInstanceQ q(AddCommGroup.{u} $V)
  /- Parse the type of the second provided expression as a type `P` carrying an `AddTorsor V P`
  instance. -/
  let P ← inferType x₀
  let .sort v₀ ← whnf (← inferType P) | unreachable!
  let some v := v₀.dec | unreachable!
  have P : Q(Type v) := P
  let iVP ← synthInstanceQ q(AddTorsor.{u, v} $V $P)
  /- Parse the second provided expression as a term of type `P`. -/
  have x₀ : Q($P) := x₀
  /- Parse the goal as an equality in `P` of two expressions `lhs` and `rhs`. -/
  let some (ty, lhs, rhs) := e.eq? |
    throwError "proposition {e} is not an equality"
  if ty == V then
    have lhs : Q($V) := lhs
    have rhs : Q($V) := rhs
    /- Express LHS and RHS as `a`, `b` respectively (with `P` subexpressions fully normalized)-/
    let ⟨a, pf₁⟩ ← parseAddCommGroup iV iVP x₀ lhs
    let ⟨b, pf₂⟩ ← parseAddCommGroup iV iVP x₀ rhs
    let e' : Q(Prop) := q($a = $b)
    let pf : Q($lhs = $rhs ↔ $e') := (q(bar_iff $pf₁ $pf₂))
    return ⟨e', pf⟩
  else if ty == P then
    have lhs : Q($P) := lhs
    have rhs : Q($P) := rhs
    /- Express LHS and RHS as `a +ᵥ x₀`, `b + x₀` respectively -/
    let ⟨a, pf₁⟩ ← parseAddTorsor iV iVP x₀ lhs
    let ⟨b, pf₂⟩ ← parseAddTorsor iV iVP x₀ rhs
    let e' : Q(Prop) := q($a = $b)
    let pf : Q($lhs = $rhs ↔ $e') := (q(foo_iff $iVP $pf₁ $pf₂))
    return ⟨e', pf⟩
  else
    throwError "only support equalities in {V} or {P}"

open Tactic in
/-- Use `ring_nf` to rewrite hypothesis `h`. -/
def basepointLocalDecl (V x₀ : Expr) (fvarId : FVarId) :
    TacticM Unit := withMainContext do
  let lctx ← getLCtx
  let ldecl := LocalContext.get! lctx fvarId
  let mainGoal ← getMainGoal
  let mainGoal ← mainGoal.tryClear fvarId
  let e : Q(Prop) ← fvarId.getType
  let ⟨e', pf⟩ ← mkBasepointIff V x₀ e
  -- can't qq this step for some reason
  let new_pf : Expr := (← mkAppM ``Iff.mp #[pf, .fvar fvarId])
  let (_, mainGoal) ← mainGoal.note ldecl.userName new_pf
  replaceMainGoal <| [mainGoal]

def evalBasepoint (V x₀ : Expr) (g : MVarId) : MetaM (List MVarId) := do
  let e : Q(Prop) := ← g.getType'
  let ⟨(e' : Q(Prop)), (pf : Q($e ↔ $e'))⟩ ← mkBasepointIff V x₀ e
  let mvar ← mkFreshExprMVar e'
  -- can't qq this step for some reason
  g.assign (← mkAppM ``Iff.mpr #[pf, mvar])
  return [mvar.mvarId!]

open Parser.Tactic in
elab "basepoint" tV:(ppSpace colGt term) "," tx₀:(ppSpace colGt term) loc:(location)? :
    tactic => Tactic.withMainContext <| do
  let loc := (loc.map Tactic.expandLocation).getD (.targets #[] true)
  let V ← Term.elabTerm tV none
  let x₀ ← Term.elabTerm tx₀ none
  Tactic.withLocation loc (basepointLocalDecl V x₀)
    (Tactic.liftMetaTactic <| evalBasepoint V x₀)
    fun _ ↦ throwError "basepoint tactic failed"


section Test
variable {V P : Type*} [AddCommGroup V] [AddTorsor V P]

example {x y z : P} (h : x = y) : True := by
  basepoint V, x at h
  sorry

example {x y z : P} : (x -ᵥ ((z -ᵥ x) +ᵥ x)) +ᵥ y = ((z -ᵥ x) +ᵥ x -ᵥ z) +ᵥ z := by
  basepoint V, x
  sorry

example {x y z : P} : x -ᵥ ((z -ᵥ x) +ᵥ x) = (z -ᵥ x) +ᵥ x -ᵥ z := by
  let w : P := sorry
  basepoint V, w
  sorry

variable {R : Type*} [SMul R V] [AddCommGroup R] [One R]

example {t : R} {x y z : P} :
    (1 - t) • (x -ᵥ (t • (z -ᵥ x) +ᵥ x)) = t • (t • (z -ᵥ x) +ᵥ x -ᵥ z) := by
  basepoint V, x
  sorry

end Test
