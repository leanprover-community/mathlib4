
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue, Anne Baanen
-/
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Util.AtomM
import Mathlib.Algebra.Polynomial.Basic
/- TODO: remove this import. it's mainly used to prove `a • p = .C a * p`, but it transitively
  imports `ring` -/
import Mathlib.Algebra.Polynomial.Coeff

namespace Mathlib.Tactic
namespace Poly


open Mathlib.Meta Qq NormNum Lean.Meta AtomM

attribute [local instance] monadLiftOptionMetaM

open Lean (MetaM Expr mkRawNatLit)

/-- TODOS:
 * Currently there's a simp only preprocessing step. This should instead be done using an
   explicit simp set rather than `evalTactic`
 * subtraction and negation: requires new typeclass assumptions, caching mechanism
--  * apply an appropriate discharger to side goals (currently : norm_num)
 * normalize the constant expressions while parsing the polynomial.
   Should be doable using the internals of norm_num
 * (potentially) allow variables in exponents.
   Need a good normalization procedure to make sure exponents stay aligned.

-/

noncomputable def monomial {α : Type*} [Semiring α] (n : ℕ) (a : α) := Polynomial.monomial n a

theorem monomial_eq  {α : Type*} [Semiring α] (n : ℕ) (a : α) : monomial n a = .C a * .X ^ n := by
  simp_rw [monomial, ← Polynomial.C_mul_X_pow_eq_monomial]

mutual

inductive ExMon : ∀ {u : Lean.Level} {α : Q(Type u)}, (sα : Q(CommSemiring $α)) →
    (e : Q(Polynomial $α)) → Type
  | mon {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)} {en : Q(ℕ)} (n : ℕ) (e : Q($α))
    : ExMon sα q(monomial $en $e)

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
    ExMon sα a → Q($α)
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

theorem monomial_add {α : Type*} [Semiring α] {m n : ℕ} (a b c : α) (hc : a + b = c) (h : m = n) :
    monomial m a + monomial n b = monomial m c := by
  unfold monomial
  rw [h, ← hc]
  exact Eq.symm (Polynomial.monomial_add n a b)

theorem add_pf_zero_add (b : R) : 0 + b = b := by simp

theorem add_pf_add_zero (a : R) : a + 0 = a := by simp

def evalAddMon {a b : Q(Polynomial $α)} (va : ExMon sα a) (vb : ExMon sα b) :
    OptionT MetaM (Result (u:=u) (ExMon sα) q($a + $b)) := do
  Lean.Core.checkSystem decl_name%.toString
  match va, vb with
  | .mon (en := em) m e₁, .mon (en := en) n e₂ =>
    if m = n then
      have : $em =Q $en := ⟨⟩
      /- TODO : use correct nurmnum extensions instead of calling eval -/
      -- let res ← NormNum.eval q($e₁ + $e₂)
      -- have expr : Q($α) := res.expr
      -- let some (pf : Q($e₁ + $e₂ = $expr)) := res.proof?
      --   | throwError "case not handled 1"
      have expr : Q($α) := q($e₁ + $e₂)
      have : ($e₁ + $e₂) =Q $expr := ⟨⟩
      return ⟨q(monomial $em $expr),
        .mon m q($expr), q(monomial_add (m := $em) (n := $en) $e₁ $e₂ $expr rfl rfl)⟩
    else
      OptionT.fail

theorem add_pf_add_overlap
    (_ : a₁ + b₁ = c₁) (_ : a₂ + b₂ = c₂) : (a₁ + a₂ : R) + (b₁ + b₂) = c₁ + c₂ := by
  subst_vars; simp [add_assoc, add_left_comm]

theorem add_pf_add_lt (a₁ : R) (_ : a₂ + b = c) : (a₁ + a₂) + b = a₁ + c := by simp [*, add_assoc]

theorem add_pf_add_gt (b₁ : R) (_ : a + b₂ = c) : a + (b₁ + b₂) = b₁ + c := by
  subst_vars; simp [add_left_comm]

partial def evalAdd {a b : Q(Polynomial $α)} (va : ExSum sα a) (vb : ExSum sα b) :
    MetaM <| Result (u := u) (ExSum sα) q($a + $b) := do
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
  return ⟨q(monomial 1 1 + 0), (ExMon.mon 1 _).toSum, q(evalX_pf)⟩

theorem mul_pf_zero_mul (b : R) : 0 * b = 0 := by simp
theorem mul_pf_mul_zero (a : R) : a * 0 = 0 := by simp

theorem monomial_mul {α : Type*} [CommSemiring α] {m n k : ℕ} (a b c : α) (hc : a * b = c)
    (h : m + n = k) :
    monomial m a * monomial n b = monomial k c := by
  unfold monomial
  rw [← h, ← hc, Polynomial.monomial_mul_monomial]


partial def evalMonMulMon {a b : Q(Polynomial $α)} (va : ExMon sα a) (vb : ExMon sα b) :
    MetaM <| Result (u := u) (ExMon sα) q($a * $b) := do
  match va, vb with
  | .mon (en := em) m e₁, .mon (en := en) n e₂ =>
    let c : ℕ := m + n
    have ec : Q(ℕ) := q($c)
    have : ($em + $en) =Q $ec := ⟨⟩
    -- let res ←  NormNum.eval q($e₁ * $e₂)
    -- have expr : Q($α) := res.expr
    -- let some (pf : Q($e₁ * $e₂ = $expr)) := res.proof?
    --   | throwError "case not handled 1"
      have expr : Q($α) := q($e₁ * $e₂)
      have : ($e₁ * $e₂) =Q $expr := ⟨⟩
    return ⟨q(monomial $ec ($expr)), .mon c q($expr), q(monomial_mul _ _ _ rfl rfl)⟩


theorem evalMulMon_pf (h : a₁ * b = a') (h' : a₂ * b = b'): (a₁ + a₂) * b = a' + b' := by
  subst_vars
  rw [add_mul]

partial def evalMulMon {a b : Q(Polynomial $α)} (va : ExSum sα a) (vb : ExMon sα b) :
    MetaM <| Result (u := u) (ExSum sα) q($a * $b) := do
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
    MetaM <| Result (u := u) (ExSum sα) q($a * $b) := do
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

/- Close the goal P = Q by equating coefficients. -/
partial def ExSum.eq_exSum
    {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)} {a b : Q(Polynomial $α)}
    (goal : MVarId) (e₁ e₂ : Q(Polynomial $α)) (exSum_a : ExSum sα a) (exSum_b : ExSum sα b)
    : MetaM (List MVarId) :=
  match exSum_a, exSum_b with
  | .zero, .zero => do
      goal.assign q(rfl : (0: Polynomial $α) = 0)
      return []
  | .add (b := P) ema exa, .add (b := Q) emb exb => do
    have m : ℕ := ema.exponent
    have n : ℕ := emb.exponent
    have ea : Q($α) := ema.e
    have eb : Q($α) := emb.e
    /- TODO: isolate reused code. -/
    if m == n then
      IO.println "m = n"
      /- goal is of the form `monomial n e₁ + _ = monomial n e₂ + _`-/
      have g : Q($ea = $eb) := ← mkFreshExprMVarQ q($ea = $eb)
      have goal' : Q($P = $Q) := ← mkFreshExprMVarQ q($P = $Q)
      goal.assign q(monomial_add_congr (R := $α) $n $g $goal')
      let goals ← exa.eq_exSum goal'.mvarId! P Q exb
      return g.mvarId! :: goals
    else if m < n then
      IO.println "m < n"
      have g : Q($ea = 0) := ← mkFreshExprMVarQ q($ea = 0)
      have goal' : Q($P = $e₂) := ← mkFreshExprMVarQ q($P = $e₂)
      goal.assign q(monomial_add_zero_congr (R := $α) $m $g $goal')
      let goals ← exa.eq_exSum goal'.mvarId! P e₂ exSum_b
      return g.mvarId! :: goals
    else
      IO.println "m > n"
      have g : Q($eb = 0) := ← mkFreshExprMVarQ q($eb = 0)
      have goal' : Q($e₁ = $Q) := ← mkFreshExprMVarQ q($e₁ = $Q)
      goal.assign q(monomial_zero_add_congr (R := $α) $n $g $goal')
      let goals ← exSum_a.eq_exSum goal'.mvarId! e₁ Q exb
      return g.mvarId! :: goals
  /- Same as m < n case -/
  | .add (b := P) ema exa , .zero => do
      IO.println "add, zero"
      have m : ℕ := ema.exponent
      have g : Q($ema.e = 0) := ← mkFreshExprMVarQ q($ema.e = 0)
      have goal' : Q($P = $e₂) := ← mkFreshExprMVarQ q($P = $e₂)
      goal.assign q(monomial_add_zero_congr (R := $α) $m $g $goal')
      let goals ← exa.eq_exSum goal'.mvarId! P e₂ exSum_b
      return g.mvarId! :: goals
  /- Same as m > n case -/
  | .zero, .add (b := Q) emb exb  => do
      have n : ℕ := emb.exponent
      have g : Q($emb.e = 0) := ← mkFreshExprMVarQ q($emb.e = 0)
      have goal' : Q($e₁ = $Q) := ← mkFreshExprMVarQ q($e₁ = $Q)
      goal.assign q(monomial_zero_add_congr (R := $α) $n $g $goal')
      let goals ← exSum_a.eq_exSum goal'.mvarId! e₁ Q exb
      return g.mvarId! :: goals

theorem poly_nsmul_eq_C_mul {R : Type*} [Semiring R] {p : Polynomial R} (a : ℕ) :
    a • p = .C a * p := by
  simp only [nsmul_eq_mul, map_natCast]

theorem poly_zsmul_eq_C_mul {R : Type*} [Ring R] {p : Polynomial R} (a : ℤ) :
    a • p = .C a * p := by
  simp only [zsmul_eq_mul, map_intCast]

theorem poly_ofNat {R : Type*} [Semiring R] (n : ℕ) [Nat.AtLeastTwo n] :
    (ofNat(n) : Polynomial R) = Polynomial.C (n : R) := rfl
theorem poly_zero : 0 = Polynomial.C 0 := by simp
theorem poly_one : 1 = Polynomial.C 1 := rfl

def normalize : TacticM Unit := withMainContext do
  /- TODO : -/
  evalTactic <| ← `(tactic|
    simp -failIfUnchanged only [Polynomial.smul_eq_C_mul, poly_ofNat, poly_zero, poly_one,
      ← Polynomial.C_mul_X_pow_eq_monomial, poly_nsmul_eq_C_mul, poly_zsmul_eq_C_mul])
  let goal ← try getMainGoal catch
    | _ => return
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
  /- TODO: we probably want to do some sort of normalization of intermediate expressions.
    `norm_num` does not seem set up to do this very well. Much of the work is actually done by
    `simp`, namely `a+0 -> a` and `a*1 -> a`. -/
  for g in l do
    let l ← evalTacticAt (← `(tactic| norm_num)) g
    Tactic.pushGoals l
    -- NormNum.normNumAt g (← getSimpContext)

elab (name := poly) "poly" : tactic => normalize

set_option linter.unusedTactic false

example : Polynomial.C 1 + Polynomial.C 1 = Polynomial.C 2  := by
  poly

example : .X + .X = .X + (.X : Polynomial ℚ) := by
  poly

example : Polynomial.C (3:ℚ) * .X + .X = .C 4 * .X := by
  poly

example : (.C 1 + Polynomial.X)^(5/2)  = .X * .X +  2 • .X + .C 1 := by
  poly

example : .X^2 + .C (-1) = (.X + Polynomial.C (-1 : ℚ)) * (.X + .C 1) := by
  poly

example : (.X + Polynomial.C (-1 : ℚ)) * (.X + .C 1) = .X^2 + .C (-1) := by
  poly


example (a : ℚ) : (Polynomial.C a * .X)^7 = .C (a^7) * .X^7 := by
  poly
  simp_rw [← mul_assoc, pow_succ, pow_zero, one_mul]

example (a : ℚ) (ha : a = 0) : Polynomial.C a * .X = .C (1 - 1) := by
  poly
  exact ha

example (a : ℚ) (ha : a = 0) : .C (1 - 1) = Polynomial.C a * .X  := by
  poly
  exact ha

example {a : ℚ} : a • Polynomial.X = .C a * Polynomial.X := by
  poly

example : 8 * Polynomial.X = .C 8 * Polynomial.X := by
  poly

example : (1+Polynomial.X : Polynomial ℕ)^3 = 1 + 3*.X + 3 * .X^2 + .X^3 := by
  poly

-- #synth HSMul ℕ (Polynomial ℚ) (Polynomial ℚ)
-- #synth HSMul ℕ (Polynomial ℚ) (Polynomial ℚ)

example : Polynomial.monomial 4 (3/2:ℤ) = (1 : ℕ) • .X^4 := by
  poly

example : Polynomial.monomial 4 (4/2:ℚ) = (2 : ℤ) • .X^4 := by
  poly

example (a : ℚ) : (.C a + Polynomial.X)^(1+7/3)
  = .X ^ 3 + .C (3 * a) * .X^2  + .C (3 * a^2) * .X  + .C (a^3) := by
  poly <;> ring

example (a : ℚ) : (.C a + Polynomial.X)^(1+7/3)
  = .X ^ 3 + .C (3 * a) * .X^2  + .C (3 * a^2) * .X  + .C (a^3) := by
  poly <;> ring

example (a : ℚ) : (.C a + Polynomial.X)^2 = .X ^ 2 + .C (2 * a) * .X + .C (a^2) := by
  poly
  /-
  a : ℚ
  ⊢ a + a = 2 * a
  a : ℚ
  ⊢ a * a = a ^ 2
  -/
  repeat sorry


example (a : ℚ) : (.C a + Polynomial.X)^(3)
  = .X ^ 3 + .C (3 * a) * .X^2  + .C (3 * a^2) * .X  + .C (a^3) := by
  poly <;> ring
-- set_option profiler true


end Mathlib.Tactic.Poly
