
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue, Anne Baanen
-/
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Util.AtomM
import Mathlib.Algebra.Polynomial.Basic

namespace Mathlib.Tactic
namespace Poly


open Mathlib.Meta Qq NormNum Lean.Meta AtomM

attribute [local instance] monadLiftOptionMetaM

open Lean (MetaM Expr mkRawNatLit)

/-- TODOS:
 * subtraction and negation: requires new typeclass assumptions, caching mechanism
 * scalar multiplication
 * parsing ofNats as constants
 * given two normalised polynomials, equate the coefficients and provide side goals.
 * normalize the constant expressions while parsing the polynomial.
   Should be doable using the internals of norm_num
 * (potentially) allow variables in exponents. Need a good normalization procedure to make sure exponents stay aligned.

-/

noncomputable def monomial {α : Type*} [Semiring α] (n : ℕ) (a : α) := Polynomial.monomial n a

theorem monomial_eq  {α : Type*} [Semiring α] (n : ℕ) (a : α) : monomial n a = .C a * .X ^ n := by
  simp_rw [monomial, ← Polynomial.C_mul_X_pow_eq_monomial]

theorem monomial_mul {α : Type*} [CommSemiring α] {m n c : ℕ} (a b : α) (h : m + n = c) :
    monomial m a * monomial n b = monomial c (a * b) := by
  unfold monomial
  rw [← h, Polynomial.monomial_mul_monomial]

mutual

inductive ExMon : ∀ {u : Lean.Level} {α : Q(Type u)}, (sα : Q(CommSemiring $α)) →
    (e : Q(Polynomial $α)) → Type
  | mon {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)} (n : ℕ) (e : Q($α))
    : ExMon sα q(monomial $n $e)

inductive ExSum : ∀ {u : Lean.Level} {α : Q(Type u)}, (sα : Q(CommSemiring $α)) →
    (e : Q(Polynomial $α)) → Type
  /-- Zero is a polynomial. `e` is the expression `0`. -/
  | zero {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)} : ExSum sα q(0)
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)} {a b : Q(Polynomial $α)} :
    ExMon sα a → ExSum sα b → ExSum sα q($a + $b)

end

def ExMon.exponent
    {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)} {a : Q(Polynomial $α)} :
    ExMon sα a → ℕ
  | .mon n _ => n

def ExMon.exp_eq
    {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)} {a b : Q(Polynomial $α)} :
    ExMon sα a → ExMon sα b → Bool
    | .mon n _, .mon m _ => n == m
    -- | _, _ => false
def ExMon.e
    {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)} {a : Q(Polynomial $α)} :
    ExMon sα a → Expr
  | .mon _ e => e

def ExMon.toSum
    {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)} {a : Q(Polynomial $α)}
    (m : ExMon sα a) : ExSum sα q($a+0) :=
  .add m (.zero)

def ExMon.cmp
    {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)} {a b : Q(Polynomial $α)} :
    ExMon sα a → ExMon sα b → Ordering
  | .mon n _, .mon m _ =>
    compare n m


/--
The result of evaluating an (unnormalized) expression `e` into the type family `E`
(one of `ExSum`, `ExProd`, `ExBase`) is a (normalized) element `e'`
and a representation `E e'` for it, and a proof of `e = e'`.
-/
structure Result {u : Lean.Level} {α : Q(Type u)} (E : Q($α) → Type) (e : Q($α)) where
  /-- The normalized result. -/
  expr : Q($α)
  /-- The data associated to the normalization. -/
  val : E expr
  /-- A proof that the original expression is equal to the normalized result. -/
  proof : Q($e = $expr)

/- Here we will need to take care: the expression we end up with is a sum of monomials. We then want
to compare the coefficents and create side goals for the user. -/

section evals
variable {u : Lean.Level}
variable {α : Q(Type u)} (sα : Q(CommSemiring $α)) {R : Type*} [CommSemiring R]
variable {a a' a₁ a₂ a₃ b b' b₁ b₂ b₃ c c₁ c₂ : R}

theorem monomial_add {α : Type*} [Semiring α] {m n : ℕ} (a b : α) (h : m = n) :
    monomial m a + monomial n b = monomial m (a + b) := by
  unfold monomial
  rw [h]
  exact Eq.symm (Polynomial.monomial_add n a b)

theorem add_pf_zero_add (b : R) : 0 + b = b := by simp

theorem add_pf_add_zero (a : R) : a + 0 = a := by simp

def evalAddMon {a b : Q(Polynomial $α)} (va : ExMon sα a) (vb : ExMon sα b) :
    OptionT Lean.Core.CoreM (Result (u:=u) (ExMon sα) q($a + $b)) := do
  Lean.Core.checkSystem decl_name%.toString
  match va, vb with
  | .mon m e₁, .mon n e₂ =>
    if h : m = n then
      let pf : Q($m = $n) := h ▸ q(rfl)
      return ⟨q(monomial $m ($e₁ + $e₂)),
        .mon m q($e₁ + $e₂), q(monomial_add (m := $m) (n := $n) $e₁ $e₂ $pf)⟩
    else
      OptionT.fail

theorem add_pf_add_overlap
    (_ : a₁ + b₁ = c₁) (_ : a₂ + b₂ = c₂) : (a₁ + a₂ : R) + (b₁ + b₂) = c₁ + c₂ := by
  subst_vars; simp [add_assoc, add_left_comm]

theorem add_pf_add_lt (a₁ : R) (_ : a₂ + b = c) : (a₁ + a₂) + b = a₁ + c := by simp [*, add_assoc]

theorem add_pf_add_gt (b₁ : R) (_ : a + b₂ = c) : a + (b₁ + b₂) = b₁ + c := by
  subst_vars; simp [add_left_comm]

partial def evalAdd {a b : Q(Polynomial $α)} (va : ExSum sα a) (vb : ExSum sα b) :
    Lean.Core.CoreM <| Result (u := u) (ExSum sα) q($a + $b) := do
  Lean.Core.checkSystem decl_name%.toString
  match va, vb with
  | .zero, vb => return ⟨b, vb, q(add_pf_zero_add $b)⟩
  | va, .zero => return ⟨a, va, q(add_pf_add_zero $a)⟩
  | .add (a := a₁) (b := _a₂) va₁ va₂, .add (a := b₁) (b := _b₂) vb₁ vb₂ =>
    match ← (evalAddMon sα va₁ vb₁).run with
    | some (⟨_, vc₁, pc₁⟩) =>
      let ⟨_, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
      return ⟨_, .add vc₁ vc₂, q(add_pf_add_overlap $pc₁ $pc₂)⟩
    | none =>
      if let .lt := va₁.cmp vb₁ then
        let ⟨_c, vc, (pc : Q($_a₂ + ($b₁ + $_b₂) = $_c))⟩ ← evalAdd va₂ vb
        return ⟨_, .add va₁ vc, q(add_pf_add_lt $a₁ $pc)⟩
      else
        let ⟨_c, vc, (pc : Q($a₁ + $_a₂ + $_b₂ = $_c))⟩ ← evalAdd va vb₂
        return ⟨_, .add vb₁ vc, q(add_pf_add_gt $b₁ $pc)⟩


theorem monomial_zero (a : R) : monomial 0 a = .C a := by
  simp [monomial]

theorem evalC_pf (a : R) : .C a = monomial 0 a + 0 := by
  simp [monomial_zero]

partial def evalC (a : Q($α)) :
    Lean.Core.CoreM <| Result (u := u) (ExSum sα) q(Polynomial.C $a) := do
  return ⟨q(monomial 0 $a + 0), (ExMon.mon 0 a).toSum, q(evalC_pf $a)⟩

theorem evalX_pf : .X = monomial 1 (1:R) + 0 := by
  simp [monomial_eq]

partial def evalX :
    Lean.Core.CoreM <| Result (u := u) (ExSum sα) q(Polynomial.X)  := do
  return ⟨q(monomial 1 1 + 0), (ExMon.mon _ _).toSum, q(evalX_pf)⟩

theorem mul_pf_zero_mul (b : R) : 0 * b = 0 := by simp
theorem mul_pf_mul_zero (a : R) : a * 0 = 0 := by simp

partial def evalMonMulMon {a b : Q(Polynomial $α)} (va : ExMon sα a) (vb : ExMon sα b) :
    Lean.Core.CoreM <| Result (u := u) (ExMon sα) q($a * $b) := do
  match va, vb with
  | .mon m e₁, .mon n e₂ =>
    let c : ℕ := m + n
    have h : c = m + n := rfl
    have pf : Q($m + $n = $c ) := h ▸ q(rfl)
    return ⟨q(monomial $c ($e₁ * $e₂)), .mon c q($e₁ * $e₂), q(monomial_mul _ _ $pf)⟩


theorem evalMulMon_pf (h : a₁ * b = a') (h' : a₂ * b = b'): (a₁ + a₂) * b = a' + b' := by
  subst_vars
  rw [add_mul]

partial def evalMulMon {a b : Q(Polynomial $α)} (va : ExSum sα a) (vb : ExMon sα b) :
    Lean.Core.CoreM <| Result (u := u) (ExSum sα) q($a * $b) := do
  Lean.Core.checkSystem decl_name%.toString
  match va with
  | .zero => return ⟨q(0), .zero, q(mul_pf_zero_mul $b)⟩
  | .add (a := a₁) (b := _a₂) va₁ va₂ =>
    let ⟨am_mul, vam_mul, pam_mul⟩ ← evalMonMulMon sα va₁ vb
    let ⟨a_mul, va_mul, pa_mul⟩ ← evalMulMon va₂ vb
    return ⟨q($am_mul + $a_mul), .add vam_mul va_mul, q(evalMulMon_pf $pam_mul $pa_mul)⟩

theorem evalMul_pf {s : R} (h : a * b₁ = a') (h' : a * b₂ = b') (h'' : a' + b' = s) :
  a * (b₁ + b₂) = s := by
  subst_vars
  rw [mul_add]

partial def evalMul {a b : Q(Polynomial $α)} (va : ExSum sα a) (vb : ExSum sα b) :
    Lean.Core.CoreM <| Result (u := u) (ExSum sα) q($a * $b) := do
  Lean.Core.checkSystem decl_name%.toString
  match  vb with
  | .zero => return ⟨q(0), .zero, q(mul_pf_mul_zero $a)⟩
  | .add (a := b₁) (b := _b₂) vb₁ vb₂ =>
    let ⟨_, vab₁, pab₁⟩ ← evalMulMon sα va vb₁
    let ⟨_, vab₂, pab₂⟩ ← evalMul va vb₂
    let ⟨s, vs, ps⟩ ← evalAdd sα vab₁ vab₂
    return ⟨s, vs, q(evalMul_pf $pab₁ $pab₂ $ps)⟩

theorem pow_pf_pow_zero {a : Polynomial R} {b : ℕ} (hb : b = 0) :
     a ^ b = monomial 0 (1:R) + (0:Polynomial R) := by
  simp [monomial_zero, hb]

theorem pow_pf_pow_odd {hf hf2 : R} {b : ℕ} (hb : b % 2 = 1) (hhf : a ^ (b/2) = hf)
    (hhf2 : hf * hf = hf2) (h : a * hf2 = b') :
    a ^ b = b' := by
  subst_vars
  rw [← pow_add, ← two_mul, mul_comm, ← pow_succ, add_comm, ← hb, Nat.mod_add_div]

theorem pow_pf_pow_even {hf hf2 : R} {b : ℕ} (hb : b % 2 = 0) (hhf : a ^ (b/2) = hf)
    (hhf2 : hf * hf = hf2):
    a ^ b = hf2 := by
  subst_vars
  rw [← Nat.dvd_iff_mod_eq_zero] at hb
  rw [← pow_add, ← two_mul, mul_comm, Nat.div_mul_cancel hb]

def mkRawNatLitQq (n : Nat) : Q(Nat) := mkRawNatLit n
def mkDecideProofQq (p : Q(Prop)) : MetaM Q($p) := mkDecideProof p

/-- This eval runs in MetaM because we use a decide proof - this should be changed to a `rfl` proof.-/
def evalPow {a : Q(Polynomial $α)} (b : ℕ) (va : ExSum sα a) :
    MetaM <| Result (u := u) (ExSum sα) q($a ^ $b) := do
  if h0 : b = 0 then
    -- is this the right way to do this?
    let p : Q($b = 0) := by rw[h0]; exact q(rfl)
    let pf : Q($a^$b = .monomial 0 1 + 0) := q(pow_pf_pow_zero $p)
    return ⟨q(monomial 0 1 + 0), (ExMon.mon (sα := sα) 0 q(1)).toSum, pf⟩
  else
    let ⟨hf, vhf, phf⟩ ← evalPow (b/2) va
    let ⟨hf2, vhf2, phf2⟩ ← evalMul sα vhf vhf
    if hb : b % 2 = 1 then
      -- TODO: turn this into a `rfl` proof?
      let pb : Q($b % 2 = 1) ← mkDecideProofQq q($b % 2 = 1)
      let ⟨a', va', pa'⟩ ← evalMul sα va vhf2
      return ⟨a', va', q(pow_pf_pow_odd $pb $phf $phf2 $pa')⟩
    else
      let pb : Q($b % 2 = 0) ← mkDecideProofQq q($b % 2 = 0)
      return ⟨hf2, vhf2, q(pow_pf_pow_even $pb $phf $phf2)⟩


theorem add_congr (_ : a = a') (_ : b = b') (_ : a' + b' = c) : (a + b : R) = c := by
  subst_vars; rfl

theorem mul_congr (_ : a = a') (_ : b = b') (_ : a' * b' = c) : (a * b : R) = c := by
  subst_vars; rfl

theorem pow_congr {b b' : ℕ} (_ : a = a') (_ : b = b') (_ : a' ^ b' = c) : (a ^ b : R) = c := by
  subst_vars; rfl

/--
Evaluates expression `e` of type `α` into a normalized representation as a polynomial.
This is the main driver of `ring`, which calls out to `evalAdd`, `evalMul` etc.
-/
partial def eval {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    (e : Q(Polynomial $α)) : MetaM (Result (u := u) (ExSum sα) e) := Lean.withIncRecDepth do
  let els : MetaM (Result (u := u) (ExSum sα) e) := do
    throwError m!"poly failed : unsupported expression : {e}"
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n with
  | ``HAdd.hAdd | ``Add.add => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval sα a
      let ⟨_, vb, pb⟩ ← eval sα b
      let ⟨c, vc, p⟩ ← evalAdd sα va vb
      pure ⟨c, vc, (q(add_congr $pa $pb $p) : Expr)⟩
    | _ => els
  | ``DFunLike.coe => match e with
    | ~q(.C $a) => do
      let ⟨a, va, p⟩ ← evalC sα a
      return ⟨a, va, p⟩
    | _ => els
  | ``Polynomial.X => match e with
    | ~q(.X) => do
      let ⟨a, va, p⟩ ← evalX sα
      return ⟨a, va, p⟩
  | ``HMul.hMul | ``Mul.mul => match e with
    | ~q($a * $b) =>
      let ⟨_, va, pa⟩ ← eval sα a
      let ⟨_, vb, pb⟩ ← eval sα b
      let ⟨c, vc, p⟩ ← evalMul sα va vb
      pure ⟨c, vc, q(mul_congr $pa $pb $p)⟩
  | ``HPow.hPow | ``Pow.pow => match e with
    | ~q($a ^ ($eb : ℕ)) =>
      let ⟨blit, pf_isNat⟩ ← try NormNum.deriveNat eb q(Nat.instAddMonoidWithOne) catch
        | _ => throwError "Failed to normalize {eb} to a natural literal 1"
      if ! Expr.isRawNatLit blit then
        /- This code should be unreachable? -/
        throwError s!"Failed to normalize {eb} to a natural literal 3"
      let b : ℕ := blit.natLit!
      have : @Nat.cast ℕ AddMonoidWithOne.toNatCast $blit =Q $b := ⟨⟩
      let pb : Q($eb = $b) := q(($pf_isNat).out.trans $this)
      let ⟨_, va, pa⟩ ← eval sα a
      let ⟨c, vc, p⟩ ← evalPow sα b va
      return ⟨c, vc, q(pow_congr $pa $pb $p)⟩
    | _ => els
  | _ => els


theorem eq_congr {a b a' b' : Polynomial R} (ha : a = a') (hb : b = b') (h : a' = b') : a = b := by
  subst ha hb
  exact h

theorem monomial_add_congr (n : ℕ) {P Q : Polynomial R} (hab : a = b) (hPQ : P = Q) :
    monomial n a + P = monomial n b + Q := by
  subst_vars
  rfl

theorem monomial_zero_right (n : ℕ) : monomial n (0:R) = 0 := by
  simp [monomial]

theorem monomial_zero_add_congr (n : ℕ) {P Q : Polynomial R} (hab : b = 0) (hPQ : P = Q) :
    P = monomial n b + Q := by
  rw [hPQ, hab, monomial_zero_right (R := R) n, zero_add]

theorem monomial_add_zero_congr (n : ℕ) {P Q : Polynomial R} (hab : a = 0) (hPQ : P = Q) :
    monomial n a + P = Q := by
  rw [hPQ, hab, monomial_zero_right (R := R) n, zero_add]

end evals

open Lean Parser.Tactic Elab Command Elab.Tactic Meta Qq
-- set_option profiler true

def ExSum.eq_exSum
    {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)} {a b : Q(Polynomial $α)}
    (goal : MVarId) (e₁ e₂ : Q(Polynomial $α)) (exa : ExSum sα a) (exb : ExSum sα b)
    : MetaM (List MVarId):=
  match exa, exb with
  | .zero, .zero => do
      goal.assign q(rfl : (0: Polynomial $α) = 0)
      return []
  | .add ema exa, .add emb exb => do
    have m : ℕ := ema.exponent
    have n : ℕ := emb.exponent
    have ea : Q($α) := ema.e
    have eb : Q($α) := emb.e
    /- TODO: isolate reused code. -/
    if m == n then
      IO.println "m = n"
      /- goal is of the form `monomial n e₁ + _ = monomial n e₂ + _`-/
      /- Something here feels wrong, I don't like having to do the `@monomial` thing.
        Should I merge `ExSum` and `Result`?-/
      have g : Q($ea = $eb) := ← mkFreshExprMVarQ q($ea = $eb)
      let ~q(monomial _ _ + $P) := e₁
        | throwError "error a"
      let ~q(monomial _ _ + $Q) := e₂
        | throwError "error b"
      have goal' : Q($P = $Q) := ← mkFreshExprMVarQ q($P = $Q)
      goal.assign q(monomial_add_congr (R := $α) $n $g $goal')
      let goals ← exa.eq_exSum goal'.mvarId! P Q exb
      return g.mvarId! :: goals
    else if m < n then
      IO.println "m < n"
      let ~q(monomial _ _ + $P) := e₁
        | throwError "error g"
      have g : Q($ea = 0) := ← mkFreshExprMVarQ q($ea = 0)
      have goal' : Q($P = $e₂) := ← mkFreshExprMVarQ q($P = $e₂)
      goal.assign q(monomial_add_zero_congr (R := $α) $m $g $goal')
      let goals ← exa.eq_exSum goal'.mvarId! P e₂ (.add emb exb)
      return g.mvarId! :: goals
    else
      IO.println "m > n"
      let ~q(monomial _ _ + $Q) := e₂
        | throwError "error c"
      have g : Q($eb = 0) := ← mkFreshExprMVarQ q($eb = 0)
      have goal' : Q($e₁ = $Q) := ← mkFreshExprMVarQ q($e₁ = $Q)
      goal.assign q(monomial_zero_add_congr (R := $α) $n $g $goal')
      let goals ← (ExSum.add ema exa).eq_exSum goal'.mvarId! e₁ Q exb
      return g.mvarId! :: goals
  | .add ema exa , .zero => do
      IO.println "add, zero"
      have m : ℕ := ema.exponent
      have ea : Q($α) := ema.e
      let ~q(monomial _ _ + $P) := e₁
        | throwError "error g"
      have g : Q($ea = 0) := ← mkFreshExprMVarQ q($ea = 0)
      have goal' : Q($P = $e₂) := ← mkFreshExprMVarQ q($P = $e₂)
      goal.assign q(monomial_add_zero_congr (R := $α) $m $g $goal')
      let goals ← exa.eq_exSum goal'.mvarId! P e₂ .zero
      return g.mvarId! :: goals
  | .zero, .add emb exb  => do
      have n : ℕ := emb.exponent
      have eb : Q($α) := emb.e
      let ~q(monomial _ _ + $Q) := e₂
        | throwError "error c"
      have g : Q($eb = 0) := ← mkFreshExprMVarQ q($eb = 0)
      have goal' : Q($e₁ = $Q) := ← mkFreshExprMVarQ q($e₁ = $Q)
      goal.assign q(monomial_zero_add_congr (R := $α) $n $g $goal')
      let goals ← (ExSum.zero).eq_exSum goal'.mvarId! e₁ Q exb
      return g.mvarId! :: goals


def normalize : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let some (α, e₁, e₂) :=
    (← whnfR <|← instantiateMVars <|← goal.getType).eq?
    | throwError "poly failed: not an equality of polynomials"
  let ⟨α, _⟩ ← (α.app2? ``Polynomial)
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  have sα : Q(CommSemiring $α) := ← synthInstanceQ q(CommSemiring $α)
  have e₁ : Q(Polynomial $α) := e₁
  have e₂ : Q(Polynomial $α) := e₂
  let ⟨a, exa, pa⟩ ← eval sα e₁
  let ⟨b, exb, pb⟩ ← eval sα e₂
  let g' ← mkFreshExprMVarQ q($a = $b)
  goal.assign q(eq_congr $pa $pb $g' : $e₁ = $e₂)
  let l ← ExSum.eq_exSum g'.mvarId! a b exa exb
  Tactic.pushGoals l

elab (name := poly) "poly" : tactic => normalize

set_option linter.unusedTactic false

example : Polynomial.C 1 + Polynomial.C 1 = Polynomial.C 2  := by
  poly
  rfl

example : .X + .X = .X + (.X : Polynomial ℚ) := by
  poly
  rfl

example : Polynomial.C (3:ℚ) * .X + .X = .C 4 * .X := by
  poly
  norm_num

example : (.C 1 + Polynomial.X)^(5/2)  = .X * .X + .C 2 * .X + .C 1 := by
  poly <;> norm_num

example : .X^2 + .C (-1) = (.X + Polynomial.C (-1 : ℚ)) * (.X + .C 1) := by
  poly <;> norm_num

example : (.X + Polynomial.C (-1 : ℚ)) * (.X + .C 1) = .X^2 + .C (-1) := by
  poly <;> norm_num


example (a : ℚ) (ha : a = 0) : Polynomial.C a * .X = .C (1 - 1) := by
  poly <;> subst ha <;> norm_num

example (a : ℚ) (ha : a = 0) : .C (1 - 1) = Polynomial.C a * .X  := by
  poly <;> subst ha <;> norm_num

end Mathlib.Tactic.Poly
