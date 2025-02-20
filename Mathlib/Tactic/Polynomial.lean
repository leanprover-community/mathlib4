
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
        .mon m  q($e₁ + $e₂), q(monomial_add (m := $m) (n := $n) $e₁ $e₂ $pf)⟩
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
    -- | some (.zero pc₁) =>
    --   let ⟨c₂, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
    --   return ⟨c₂, vc₂, q(add_pf_add_overlap_zero $pc₁ $pc₂)⟩
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


theorem add_congr (_ : a = a') (_ : b = b') (_ : a' + b' = c) : (a + b : R) = c := by
  subst_vars; rfl

theorem mul_congr (_ : a = a') (_ : b = b') (_ : a' * b' = c) : (a * b : R) = c := by
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
  IO.println s!"head name is {n}"
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
  | _ => els


theorem eq_congr {a b a' b' : Polynomial R} (ha : a = a') (hb : b = b') (h : a' = b') : a = b := by
  subst ha hb
  exact h

end evals

open Lean Parser.Tactic Elab Command Elab.Tactic Meta Qq

-- set_option diagnostics true

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
  IO.println (s!"synthed instance {sα}")
  have e₁ : Q(Polynomial $α) := e₁
  have e₂ : Q(Polynomial $α) := e₂
  let ⟨a, _, pa⟩ ← eval sα e₁
  let ⟨b, _, pb⟩ ← eval sα e₂
  let g' ← mkFreshExprMVarQ q($a = $b)
  goal.assign q(eq_congr $pa $pb $g' : $e₁ = $e₂)
  IO.println g'
  Tactic.pushGoal g'.mvarId!





elab (name := poly) "poly" tk:"!"? : tactic => do (normalize)



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


example : (.C 1 + Polynomial.X)*(.C 1 + .X)  = .X * .X + .C 2 * .X + .C 1 := by
  poly
  norm_num

end Mathlib.Tactic.Poly
