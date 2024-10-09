import Mathlib.Algebra.AddTorsor

open Lean Elab Meta Qq

theorem foo {V P : Type*} [AddCommGroup V] [AddTorsor V P] {a b : V} {x₀ y z : P}
    (hy : y = a +ᵥ x₀) (hz : z = b +ᵥ x₀) (h : a = b) :
    y = z :=
  hy ▸ hz ▸ h ▸ rfl

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
  | _ =>
    pure ⟨a, q(sorry)⟩

end

/-
a • v = a • (v - x₀)
-/

def evalBasepoint (V P x₀ : Expr) (g : MVarId) : MetaM (List MVarId) := do
  /- Parse the first provided expression `V` as a type carrying an `AddCommGroup V` instance. -/
  let .sort u₀ ← whnf (← inferType V) | unreachable!
  let some u := u₀.dec | unreachable!
  let (V : Q(Type u)) := V
  let iV ← synthInstanceQ q(AddCommGroup.{u} $V)
  /- Parse the second provided expression `P` as a type carrying an `AddTorsor V P` instance. -/
  let .sort v₀ ← whnf (← inferType P) | unreachable!
  let some v := v₀.dec | unreachable!
  let (P : Q(Type v)) := P
  let iVP ← synthInstanceQ q(AddTorsor.{u, v} $V $P)
  /- Parse the third provided expression as a term of type `P`. -/
  have x₀ : Q($P) := x₀
  /- Parse the goal as an equality in `P` of two expressions `lhs` and `rhs`. -/
  let some (ty, lhs, rhs) := (← g.getType').eq? |
    throwError "goal {← g.getType} is not an equality"
  if ty == V then
    have lhs : Q($V) := lhs
    have rhs : Q($V) := rhs
    /- Express LHS and RHS as `a`, `b` respectively (with `P` subexpressions fully normalized)-/
    let ⟨a, pf₁⟩ ← parseAddCommGroup iV iVP x₀ lhs
    let ⟨b, pf₂⟩ ← parseAddCommGroup iV iVP x₀ rhs
    let mvar : Q($a = $b) ← mkFreshExprMVar q($a = $b)
    g.assign q(bar $pf₁ $pf₂ $mvar)
    return [mvar.mvarId!]
  else if ty == P then
    have lhs : Q($P) := lhs
    have rhs : Q($P) := rhs
    /- Express LHS and RHS as `a +ᵥ x₀`, `b + x₀` respectively -/
    let ⟨a, pf₁⟩ ← parseAddTorsor iV iVP x₀ lhs
    let ⟨b, pf₂⟩ ← parseAddTorsor iV iVP x₀ rhs
    let mvar : Q($a = $b) ← mkFreshExprMVar q($a = $b)
    g.assign q(foo $pf₁ $pf₂ $mvar)
    return [mvar.mvarId!]
  else
    throwError "only support equalities in {V} or {P}"

elab "basepoint" tV:(ppSpace colGt term) "," tP:(ppSpace colGt term) "," tx₀:(ppSpace colGt term) :
    tactic => do
  let V ← Term.elabTerm tV none
  let P ← Term.elabTerm tP none
  let x₀ ← Term.elabTerm tx₀ none
  Tactic.liftMetaTactic <| evalBasepoint V P x₀


section Test
variable {V P : Type*} [AddCommGroup V] [AddTorsor V P]

example {x y z : P} : (x -ᵥ ((z -ᵥ x) +ᵥ x)) +ᵥ y = ((z -ᵥ x) +ᵥ x -ᵥ z) +ᵥ z := by
  basepoint V, P, x
  sorry

example {x y z : P} : x -ᵥ ((z -ᵥ x) +ᵥ x) = (z -ᵥ x) +ᵥ x -ᵥ z := by
  basepoint V, P, x
  sorry

variable {R : Type*} [SMul R V] [AddCommGroup R] [One R]

example {t : R} {x y z : P} :
    (1 - t) • (x -ᵥ (t • (z -ᵥ x) +ᵥ x)) = t • (t • (z -ᵥ x) +ᵥ x -ᵥ z) := by
  basepoint V, P, x
  sorry

end Test
