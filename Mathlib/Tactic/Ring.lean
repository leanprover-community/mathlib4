/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue
-/
import Lean.Elab.Tactic.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NormNum

/-!
# `ring`

Evaluate expressions in the language of commutative (semi)rings.
Based on <http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf> .
-/

open Lean Parser.Tactic Elab Command Elab.Tactic Meta

@[macro_inline] def Ordering.then : Ordering → Ordering → Ordering
  | .eq, f => f
  | o, _ => o

namespace Mathlib.Tactic
namespace Ring
open Mathlib.Meta Qq NormNum

/-- This cache contains data required by the `ring` tactic during execution. -/
structure Context :=
  /-- The reducibility setting for definitional equality of atoms -/
  red : TransparencyMode

structure State :=
  atoms : Array Expr := #[]

def State.numAtoms (s : State) := s.atoms.size

/-- The monad that `ring` works in. This is a reader monad containing a cache and
the list of atoms-up-to-defeq encountered thus far, used for atom sorting. -/
abbrev RingM := ReaderT Context <| StateRefT State MetaM

def RingM.run (red : TransparencyMode) (m : RingM α) : MetaM α := do
  (m { red }).run' {}

/-- Get the index corresponding to an atomic expression, if it has already been encountered, or
put it in the list of atoms and return the new index, otherwise. -/
def addAtom (e : Expr) : RingM Nat := do
  let c ← get
  for h : i in [:c.numAtoms] do
    have : i < c.atoms.size := h.2
    if ← withTransparency (← read).red <| isDefEq e c.atoms[i] then
      return i
  modifyGet fun c => (c.atoms.size, { c with atoms := c.atoms.push e })

abbrev instCommSemiringNat : CommSemiring ℕ := inferInstance
def sℕ : Q(CommSemiring ℕ) := q(instCommSemiringNat)

mutual

inductive ExBase : ∀ {α : Q(Type u)}, Q(CommSemiring $α) → Q($α) → Type
  /-- An atomic expression `e` with id `id`. -/
  | atom (id : ℕ) : ExBase sα e
  /-- A sum of monomials. -/
  | sum (_ : ExSum sα e) : ExBase sα e

inductive ExExp : ∀ {α : Q(Type u)}, Q(CommSemiring $α) → Q($α) → Type
  /-- A power expression `a ^ b`. -/
  | exp {α : Q(Type u)} {sα : Q(CommSemiring $α)} (a : Q($α)) (b : Q(ℕ)) :
    ExBase sα a → ExProd sℕ b → ExExp sα q($a ^ $b)

inductive ExProd : ∀ {α : Q(Type u)}, Q(CommSemiring $α) → Q($α) → Type
  /-- A coefficient `value`, which must not be `0`. `e` is a raw int cast. -/
  | const (value : ℤ) : ExProd sα e
  /-- A product `a * b`. -/
  | mul {α : Q(Type u)} {sα : Q(CommSemiring $α)} (a b : Q($α)) :
    ExExp sα a → ExProd sα b → ExProd sα q($a * $b)

inductive ExSum : ∀ {α : Q(Type u)}, Q(CommSemiring $α) → Q($α) → Type
  /-- Zero. `e` is the expression `0`. -/
  | zero {α : Q(Type u)} {sα : Q(CommSemiring $α)} : ExSum sα q((0 : $α))
  /-- A sum of monomials `a + b`. -/
  | add {α : Q(Type u)} {sα : Q(CommSemiring $α)} (a b : Q($α)) :
    ExProd sα a → ExSum sα b → ExSum sα q($a + $b)
end

mutual
-- partial only to speed up compilation
partial def ExBase.eq : ExBase sα a → ExBase sα b → Bool
  | .atom i, .atom j => i == j
  | .sum a, .sum b => a.eq b
  | _, _ => false

partial def ExExp.eq : ExExp sα a → ExExp sα b → Bool
  | .exp _ _ a₁ a₂, .exp _ _ b₁ b₂ => a₁.eq b₁ && a₂.eq b₂

partial def ExProd.eq : ExProd sα a → ExProd sα b → Bool
  | .const i, .const j => i == j
  | .mul _ _ a₁ a₂, .mul _ _ b₁ b₂ => a₁.eq b₁ && a₂.eq b₂
  | _, _ => false

partial def ExSum.eq : ExSum sα a → ExSum sα b → Bool
  | .zero, .zero => true
  | .add _ _ a₁ a₂, .add _ _ b₁ b₂ => a₁.eq b₁ && a₂.eq b₂
  | _, _ => false
end

mutual
-- partial only to speed up compilation
partial def ExBase.cmp : ExBase sα a → ExBase sα b → Ordering
  | .atom i, .atom j => compare i j
  | .sum a, .sum b => a.cmp b
  | .atom .., .sum .. => .lt
  | .sum .., .atom .. => .gt

partial def ExExp.cmp : ExExp sα a → ExExp sα b → Ordering
  | .exp _ _ a₁ a₂, .exp _ _ b₁ b₂ => (a₁.cmp b₁).then (a₂.cmp b₂)

partial def ExProd.cmp : ExProd sα a → ExProd sα b → Ordering
  | .const i, .const j => compare i j
  | .mul _ _ a₁ a₂, .mul _ _ b₁ b₂ => (a₁.cmp b₁).then (a₂.cmp b₂)
  | .const .., .mul .. => .lt
  | .mul .., .const .. => .gt

partial def ExSum.cmp : ExSum sα a → ExSum sα b → Ordering
  | .zero, .zero => .eq
  | .add _ _ a₁ a₂, .add _ _ b₁ b₂ => (a₁.cmp b₁).then (a₂.cmp b₂)
  | .zero, .add .. => .lt
  | .add .., .zero => .gt
end

instance : Ord (ExBase sα e) := ⟨(·.cmp ·)⟩
instance : Ord (ExExp sα e) := ⟨(·.cmp ·)⟩
instance : Ord (ExProd sα e) := ⟨(·.cmp ·)⟩
instance : Ord (ExSum sα e) := ⟨(·.cmp ·)⟩
instance : LE (ExBase sα e) := leOfOrd
instance : LE (ExExp sα e) := leOfOrd
instance : LE (ExProd sα e) := leOfOrd
instance : LE (ExSum sα e) := leOfOrd
instance : BEq (ExBase sα e) := ⟨(·.cmp · == .eq)⟩
instance : BEq (ExExp sα e) := ⟨(·.cmp · == .eq)⟩
instance : BEq (ExProd sα e) := ⟨(·.cmp · == .eq)⟩
instance : BEq (ExSum sα e) := ⟨(·.cmp · == .eq)⟩

structure Result {α : Q(Type u)} (E : Q($α) → Type) (e : Q($α)) where
  expr : Q($α)
  val : E expr
  proof? : Q($e = $expr)

def mkInhabited (e') (v : E e') : Inhabited (Result E e) := ⟨e', v, default⟩

instance : Inhabited (Result (ExBase sα) e) := mkInhabited default <| .atom 0
instance : Inhabited (Result (ExSum sα) e) := mkInhabited _ .zero
instance : Inhabited (Result (ExProd sα) e) := mkInhabited default <| .const 0
instance : Inhabited (Result (ExExp sα) e) :=
  mkInhabited _ <| .exp default default (.atom 0) (.const 0)

variable {α : Q(Type u)} (sα : Q(CommSemiring $α)) [CommSemiring R]

def ExProd.mkNat (n : ℕ) : (e : Q($α)) × ExProd sα e :=
  let lit : Q(ℕ) := mkRawNatLit n
  ⟨q((($lit).rawCast : $α)), .const n⟩

def ExProd.mkNegNat (_ : Q(Ring $α)) (n : ℕ) : (e : Q($α)) × ExProd sα e :=
  let lit : Q(ℕ) := mkRawNatLit n
  ⟨q(((Int.negOfNat $lit).rawCast : $α)), .const (-n)⟩

section
variable {sα}

def ExExp.toProd (v : ExExp sα e) : ExProd sα q($e * (nat_lit 1).rawCast) := .mul _ _ v (.const 1)

def ExProd.toSum (v : ExProd sα e) : ExSum sα q($e + 0) := .add _ _ v .zero

def ExProd.coeff : ExProd sα e → ℤ
  | .const z => z
  | .mul _ _ _ v => v.coeff
end

inductive Overlap (e : Q($α)) where
  | zero (_ : Q(IsNat $e (nat_lit 0)))
  | nonzero (_ : Result (ExProd sα) e)

theorem add_overlap_pf (x : R) (pq_pf : a + b = c) :
    x * a + x * b = x * c := by subst_vars; simp [mul_add]

theorem add_overlap_pf_zero (x : R) : IsNat (a + b) (nat_lit 0) → IsNat (x * a + x * b) (nat_lit 0)
  | ⟨h⟩ => ⟨by simp [h, ← mul_add]⟩

def evalAddOverlap (va : ExProd sα a) (vb : ExProd sα b) : Option (Overlap sα q($a + $b)) :=
  match va, vb with
  | .const za, .const zb => do
    let ra := Result.ofRawInt za a; let rb := Result.ofRawInt zb b
    let res ← NormNum.evalAdd.core q($a + $b) _ _ ra rb
    match res with
    | .isNat _ (.lit (.natVal 0)) p => pure <| .zero p
    | rc => let ⟨zc, c, pc⟩ := rc.toRawEq; pure <| .nonzero ⟨c, .const zc, pc⟩
  | .mul a₁ _ va₁ va₂, .mul _ _ vb₁ vb₂ => do
    guard (va₁.eq vb₁)
    match ← evalAddOverlap va₂ vb₂ with
    | .zero p => pure <| .zero (q(add_overlap_pf_zero $a₁ $p) : Expr)
    | .nonzero ⟨c, vc, p⟩ =>
      pure <| .nonzero ⟨_, .mul a₁ c va₁ vc, (q(add_overlap_pf $a₁ $p) : Expr)⟩
  | _, _ => none

theorem add_pf_zero_add (b : R) : 0 + b = b := by simp

theorem add_pf_add_zero (a : R) : a + 0 = a := by simp

theorem add_pf_add_overlap
    (_ : a₁ + b₁ = c₁) (_ : a₂ + b₂ = c₂) : (a₁ + a₂ : R) + (b₁ + b₂) = c₁ + c₂ := by
  subst_vars; simp [add_assoc, add_left_comm]

theorem add_pf_add_overlap_zero
    (h : IsNat (a₁ + b₁) (nat_lit 0)) (h₄ : a₂ + b₂ = c) : (a₁ + a₂ : R) + (b₁ + b₂) = c := by
  subst_vars; rw [add_add_add_comm, h.to_eq, add_pf_zero_add]

theorem add_pf_add_lt (a₁ : R) (_ : a₂ + b = c) : (a₁ + a₂) + b = a₁ + c := by simp [*, add_assoc]

theorem add_pf_add_gt (b₁ : R) (_ : a + b₂ = c) : a + (b₁ + b₂) = b₁ + c := by
  subst_vars; simp [add_left_comm]

partial def evalAdd (va : ExSum sα a) (vb : ExSum sα b) : Result (ExSum sα) q($a + $b) :=
  match va, vb with
  | .zero, vb => ⟨b, vb, q(add_pf_zero_add $b)⟩
  | va, .zero => ⟨a, va, q(add_pf_add_zero $a)⟩
  | .add a₁ _a₂ va₁ va₂, .add b₁ _b₂ vb₁ vb₂ =>
    match evalAddOverlap sα va₁ vb₁ with
    | some (.nonzero ⟨c₁, vc₁, pc₁⟩) =>
      let ⟨c₂, vc₂, pc₂⟩ := evalAdd va₂ vb₂
      ⟨_, .add c₁ c₂ vc₁ vc₂, q(add_pf_add_overlap $pc₁ $pc₂)⟩
    | some (.zero pc₁) =>
      let ⟨c₂, vc₂, pc₂⟩ := evalAdd va₂ vb₂
      ⟨c₂, vc₂, q(add_pf_add_overlap_zero $pc₁ $pc₂)⟩
    | none =>
      if let .lt := va₁.cmp vb₁ then
        let ⟨c, vc, (pc : Q($_a₂ + ($b₁ + $_b₂) = $c))⟩ := evalAdd va₂ vb
        ⟨_, .add a₁ c va₁ vc, q(add_pf_add_lt $a₁ $pc)⟩
      else
        let ⟨c, vc, (pc : Q($a₁ + $_a₂ + $_b₂ = $c))⟩ := evalAdd va vb₂
        ⟨_, .add b₁ c vb₁ vc, q(add_pf_add_gt $b₁ $pc)⟩

theorem one_mul (a : R) : (nat_lit 1).rawCast * a = a := by simp [Nat.rawCast]

theorem mul_one (a : R) : a * (nat_lit 1).rawCast = a := by simp [Nat.rawCast]

theorem mul_pf_left (a₁ : R) (_ : a₂ * b = c) : (a₁ * a₂ : R) * b = a₁ * c := by
  subst_vars; rw [mul_assoc]

theorem mul_pf_right (b₁ : R) (_ : a * b₂ = c) : a * (b₁ * b₂) = b₁ * c := by
  subst_vars; rw [mul_left_comm]

theorem mul_pp_pf_overlap (x : R) (_ : ea + eb = e) (_ : a₂ * b₂ = c) :
    (x ^ ea * a₂ : R) * (x ^ eb * b₂) = x ^ e * c := by
  subst_vars; simp [pow_add, mul_mul_mul_comm]

partial def evalMulProd (va : ExProd sα a) (vb : ExProd sα b) : Result (ExProd sα) q($a * $b) :=
  match va, vb with
  | .const za, .const zb =>
    if za = 1 then
      ⟨b, .const zb, (q(one_mul $b) : Expr)⟩
    else if zb = 1 then
      ⟨a, .const za, (q(mul_one $a) : Expr)⟩
    else
      let ra := Result.ofRawInt za a; let rb := Result.ofRawInt zb b
      let ⟨zc, c, pc⟩ := (NormNum.evalMul.core q($a * $b) _ _ ra rb).get!.toRawEq
      ⟨c, .const zc, pc⟩
  | .mul a₁ _ va₁ va₂, .const _ =>
    let ⟨_, vc, pc⟩ := evalMulProd va₂ vb
    ⟨_, .mul _ _ va₁ vc, (q(mul_pf_left $a₁ $pc) : Expr)⟩
  | .const _, .mul b₁ _ vb₁ vb₂ =>
    let ⟨_, vc, pc⟩ := evalMulProd va vb₂
    ⟨_, .mul _ _ vb₁ vc, (q(mul_pf_right $b₁ $pc) : Expr)⟩
  | .mul a₁ _ va₁ va₂, .mul b₁ _ vb₁ vb₂ => Id.run do
    let ⟨xa, _, vxa, vea⟩ := va₁; let ⟨_, _, vxb, veb⟩ := vb₁
    if vxa.eq vxb then
      if let some (.nonzero ⟨_, ve, pe⟩) := evalAddOverlap sℕ vea veb then
        let ⟨_, vc, pc⟩ := evalMulProd va₂ vb₂
        return ⟨_, .mul _ _ ⟨_, _, vxa, ve⟩ vc, (q(mul_pp_pf_overlap $xa $pe $pc) : Expr)⟩
    if let .lt := va₁.cmp vb₁ then
      let ⟨_, vc, pc⟩ := evalMulProd va₂ vb
      ⟨_, .mul _ _ va₁ vc, (q(mul_pf_left $a₁ $pc) : Expr)⟩
    else
      let ⟨_, vc, pc⟩ := evalMulProd va vb₂
      ⟨_, .mul _ _ vb₁ vc, (q(mul_pf_right $b₁ $pc) : Expr)⟩

theorem mul_zero (a : R) : a * 0 = 0 := by simp

theorem mul_add (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : c₁ + 0 + c₂ = d) :
    a * (b₁ + b₂) = d := by subst_vars; simp [_root_.mul_add]

def evalMul₁ (va : ExProd sα a) (vb : ExSum sα b) : Result (ExSum sα) q($a * $b) :=
  match vb with
  | .zero => ⟨_, .zero, q(mul_zero $a)⟩
  | .add _ _ vb₁ vb₂ =>
    let ⟨_, vc₁, pc₁⟩ := evalMulProd sα va vb₁
    let ⟨_, vc₂, pc₂⟩ := evalMul₁ va vb₂
    let ⟨_, vd, pd⟩ := evalAdd sα vc₁.toSum vc₂
    ⟨_, vd, q(mul_add $pc₁ $pc₂ $pd)⟩

theorem zero_mul (b : R) : 0 * b = 0 := by simp

theorem add_mul (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : c₁ + c₂ = d) :
    (a₁ + a₂) * b = d := by subst_vars; simp [_root_.add_mul]

def evalMul (va : ExSum sα a) (vb : ExSum sα b) : Result (ExSum sα) q($a * $b) :=
  match va with
  | .zero => ⟨_, .zero, q(zero_mul $b)⟩
  | .add _ _ va₁ va₂ =>
    let ⟨_, vc₁, pc₁⟩ := evalMul₁ sα va₁ vb
    let ⟨_, vc₂, pc₂⟩ := evalMul va₂ vb
    let ⟨_, vd, pd⟩ := evalAdd sα vc₁ vc₂
    ⟨_, vd, q(add_mul $pc₁ $pc₂ $pd)⟩

theorem neg_one_mul {R} [Ring R] {a b : R} (_ : (Int.negOfNat (nat_lit 1)).rawCast * a = b) :
    -a = b := by subst_vars; simp [Int.negOfNat]

theorem neg_mul {R} [Ring R] (a₁ : R) {a₂ b : R}
    (_ : -a₂ = b) : -(a₁ * a₂) = a₁ * b := by subst_vars; simp

def evalNegProd (rα : Q(Ring $α)) (va : ExProd sα a) : Result (ExProd sα) q(-$a) :=
  match va with
  | .const za =>
    let lit : Q(ℕ) := mkRawNatLit 1
    let ⟨m1, _⟩ := ExProd.mkNegNat sα rα 1
    let rm := Result.isNegNat rα lit (q(IsInt.of_raw $α (.negOfNat $lit)) : Expr)
    let ra := Result.ofRawInt za a
    let ⟨zb, b, (pb : Q((Int.negOfNat (nat_lit 1)).rawCast * $a = $b))⟩ :=
      (NormNum.evalMul.core q($m1 * $a) _ _ rm ra).get!.toRawEq
    ⟨b, .const zb, (q(neg_one_mul (R := $α) $pb) : Expr)⟩
  | .mul a₁ _ va₁ va₂ =>
    let ⟨_, vb, pb⟩ := evalNegProd rα va₂
    ⟨_, .mul _ _ va₁ vb, (q(neg_mul $a₁ $pb) : Expr)⟩

theorem neg_zero {R} [Ring R] : -(0 : R) = 0 := by simp

theorem neg_add {R} [Ring R] {a₁ a₂ b₁ b₂ : R}
    (_ : -a₁ = b₁) (_ : -a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂ := by subst_vars; simp [add_comm]

def evalNeg (rα : Q(Ring $α)) (va : ExSum sα a) : Result (ExSum sα) q(-$a) :=
  match va with
  | .zero => ⟨_, .zero, (q(neg_zero (R := $α)) : Expr)⟩
  | .add _ _ va₁ va₂ =>
    let ⟨_, vb₁, pb₁⟩ := evalNegProd sα rα va₁
    let ⟨_, vb₂, pb₂⟩ := evalNeg rα va₂
    ⟨_, .add _ _ vb₁ vb₂, (q(neg_add $pb₁ $pb₂) : Expr)⟩

theorem sub_pf {R} [Ring R] {a b c d : R}
    (_ : -b = c) (_ : a + c = d) : a - b = d := by subst_vars; simp [sub_eq_add_neg]

def evalSub (rα : Q(Ring $α)) (va : ExSum sα a) (vb : ExSum sα b) : Result (ExSum sα) q($a - $b) :=
  let ⟨_c, vc, pc⟩ := evalNeg sα rα vb
  let ⟨d, vd, (pd : Q($a + $_c = $d))⟩ := evalAdd sα va vc
  ⟨d, vd, (q(sub_pf $pc $pd) : Expr)⟩

theorem pow_prod_atom (a : R) (b) : a ^ b = (a + 0) ^ b * (nat_lit 1).rawCast := by simp

def evalPowProdAtom (va : ExProd sα a) (vb : ExProd sℕ b) : Result (ExProd sα) q($a ^ $b) :=
  ⟨_, (ExExp.exp _ _ (.sum va.toSum) vb).toProd, q(pow_prod_atom $a $b)⟩

theorem pow_atom (a : R) (b) : a ^ b = a ^ b * (nat_lit 1).rawCast + 0 := by simp

def evalPowAtom (va : ExBase sα a) (vb : ExProd sℕ b) : Result (ExSum sα) q($a ^ $b) :=
  ⟨_, (ExExp.exp _ _ va vb).toProd.toSum, q(pow_atom $a $b)⟩

theorem const_pos (n : ℕ) (h : Nat.ble 1 n = true) : 0 < (n.rawCast : ℕ) := Nat.le_of_ble_eq_true h

theorem mul_exp_pos (n) (h₁ : 0 < a₁) (h₂ : 0 < a₂) : 0 < a₁ ^ n * a₂ :=
  Nat.mul_pos (Nat.pos_pow_of_pos _ h₁) h₂

theorem add_pos_left (a₂) (h : 0 < a₁) : 0 < a₁ + a₂ := Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

theorem add_pos_right (a₁) (h : 0 < a₂) : 0 < a₁ + a₂ := Nat.lt_of_lt_of_le h (Nat.le_add_left ..)

mutual

def ExBase.evalPos (va : ExBase sℕ a) : Option Q(0 < $a) :=
  match va with
  | .atom _ => none
  | .sum va => va.evalPos

def ExProd.evalPos (va : ExProd sℕ a) : Option Q(0 < $a) :=
  match va with
  | .const n =>
    -- it must be positive because it is a nonzero nat literal
    have lit : Q(ℕ) := a.appArg!
    let p : Q(Nat.ble 1 $lit = true) := (q(Eq.refl true) : Expr)
    some (q(const_pos $lit $p) : Expr)
  | .mul _ _ ⟨_, ea₁, vxa₁, _⟩ va₂ => do
    let pa₁ ← vxa₁.evalPos
    let pa₂ ← va₂.evalPos
    some q(mul_exp_pos $ea₁ $pa₁ $pa₂)

def ExSum.evalPos (va : ExSum sℕ a) : Option Q(0 < $a) :=
  match va with
  | .zero => none
  | .add a₁ a₂ va₁ va₂ => do
    match va₁.evalPos with
    | some p => some q(add_pos_left $a₂ $p)
    | none => let p ← va₂.evalPos; some q(add_pos_right $a₁ $p)

end

theorem pow_one (a : R) : a ^ nat_lit 1 = a := by simp

theorem pow_bit0 (_ : (a : R) ^ k = b) (_ : b * b = c) : a ^ (Nat.mul (nat_lit 2) k) = c := by
  subst_vars; simp [Nat.succ_mul, pow_add]

theorem pow_bit1 (_ : (a : R) ^ k = b) (_ : b * b = c) (_ : c * a = d) :
    a ^ (Nat.add (Nat.mul (nat_lit 2) k) (nat_lit 1)) = d := by
  subst_vars; simp [Nat.succ_mul, pow_add]

partial def evalPowNat (va : ExSum sα a) (n : Q(ℕ)) : Result (ExSum sα) q($a ^ $n) :=
  let nn := n.natLit!
  if nn = 1 then
    ⟨_, va, (q(pow_one $a) : Expr)⟩
  else
    let nm := nn >>> 1
    have m : Q(ℕ) := mkRawNatLit nm
    if nn &&& 1 = 0 then
      let ⟨_, vb, pb⟩ := evalPowNat va m
      let ⟨_, vc, pc⟩ := evalMul sα vb vb
      ⟨_, vc, (q(pow_bit0 $pb $pc) : Expr)⟩
    else
      let ⟨_, vb, pb⟩ := evalPowNat va m
      let ⟨_, vc, pc⟩ := evalMul sα vb vb
      let ⟨_, vd, pd⟩ := evalMul sα vc va
      ⟨_, vd, (q(pow_bit1 $pb $pc $pd) : Expr)⟩

theorem one_pow (b : ℕ) : ((nat_lit 1).rawCast : R) ^ b = (nat_lit 1).rawCast := by simp

theorem mul_pow (_ : ea₁ * b = c₁) (_ : a₂ ^ b = c₂) :
    (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂ := by subst_vars; simp [_root_.mul_pow, pow_mul]

def evalPowProd (va : ExProd sα a) (vb : ExProd sℕ b) : Result (ExProd sα) q($a ^ $b) :=
  let res : Option (Result (ExProd sα) q($a ^ $b)) := do
    match va, vb with
    | .const 1, _ => some ⟨_, va, (q(one_pow (R := $α) $b) : Expr)⟩
    | .const za, .const zb =>
      guard (0 ≤ zb)
      let ra := Result.ofRawInt za a
      have lit : Q(ℕ) := b.appArg!
      let rb := (q(IsNat.of_raw ℕ $lit) : Expr)
      let ⟨zc, c, pc⟩ := (← NormNum.evalPow.core q($a ^ $b) _ b lit rb ra).toRawEq
      some ⟨c, .const zc, pc⟩
    | .mul _ _ ⟨_, _, vxa₁, vea₁⟩ va₂, vb => do
      let ⟨_, vc₁, pc₁⟩ := evalMulProd sℕ vea₁ vb
      let ⟨_, vc₂, pc₂⟩ := evalPowProd va₂ vb
      some ⟨_, .mul _ _ ⟨_, _, vxa₁, vc₁⟩ vc₂, q(mul_pow $pc₁ $pc₂)⟩
    | _, _ => none
  res.getD (evalPowProdAtom sα va vb)

structure ExtractCoeff (e : Q(ℕ)) where
  k : Q(ℕ)
  e' : Q(ℕ)
  ve' : ExProd sℕ e'
  p : Q($e = $e' * $k)

theorem coeff_one (k : ℕ) : k.rawCast = (nat_lit 1).rawCast * k := by simp

theorem coeff_mul (a₁ : ℕ) (_ : a₂ = c₂ * k) : a₁ * a₂ = (a₁ * c₂) * k := by
  subst_vars; rw [mul_assoc]

def extractCoeff (va : ExProd sℕ a) : ExtractCoeff a :=
  match va with
  | .const n =>
    have k : Q(ℕ) := a.appArg!
    ⟨k, q((nat_lit 1).rawCast), .const 1, (q(coeff_one $k) : Expr)⟩
  | .mul a₁ _ va₁ va₂ =>
    let ⟨k, _, vc, pc⟩ := extractCoeff va₂
    ⟨k, _, .mul _ _ va₁ vc, q(coeff_mul $a₁ $pc)⟩

theorem pow_one_cast (a : R) : a ^ (nat_lit 1).rawCast = a := by simp

theorem zero_pow (_ : 0 < b) : (0 : R) ^ b = 0 := match b with | b+1 => by simp [pow_succ]

theorem single_pow (_ : (a : R) ^ b = c) : (a + 0) ^ b = c + 0 := by simp [*]

theorem pow_nat (_ : b = c * k) (_ : a ^ c = d) (_ : d ^ k = e) : (a : R) ^ b = e := by
  subst_vars; simp [pow_mul]

partial def evalPow₁ (va : ExSum sα a) (vb : ExProd sℕ b) : Result (ExSum sα) q($a ^ $b) :=
  match va, vb with
  | _, .const 1 => ⟨_, va, (q(pow_one_cast $a) : Expr)⟩
  | .zero, vb => match vb.evalPos with
    | some p => ⟨_, .zero, q(zero_pow (R := $α) $p)⟩
    | none => evalPowAtom sα (.sum .zero) vb
  | va, vb =>
    if vb.coeff > 1 then
      let ⟨k, _, vc, pc⟩ := extractCoeff vb
      let ⟨_, vd, pd⟩ := evalPow₁ va vc
      let ⟨_, ve, pe⟩ := evalPowNat sα vd k
      ⟨_, ve, q(pow_nat $pc $pd $pe)⟩
    else match va with
      | .add _ _ va .zero =>
        let ⟨_, vc, pc⟩ := evalPowProd sα va vb
        ⟨_, vc.toSum, q(single_pow $pc)⟩
      | va => evalPowAtom sα (.sum va) vb

theorem pow_zero (a : R) : a ^ 0 = (nat_lit 1).rawCast + 0 := by simp

theorem pow_add (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c₂) (_ : c₁ * c₂ = d) :
  (a : R) ^ (b₁ + b₂) = d := by subst_vars; simp [_root_.pow_add]

def evalPow (va : ExSum sα a) (vb : ExSum sℕ b) : Result (ExSum sα) q($a ^ $b) :=
  match vb with
  | .zero => ⟨_, (ExProd.mkNat sα 1).2.toSum, q(pow_zero $a)⟩
  | .add _ _ vb₁ vb₂ =>
    let ⟨_, vc₁, pc₁⟩ := evalPow₁ sα va vb₁
    let ⟨_, vc₂, pc₂⟩ := evalPow va vb₂
    let ⟨_, vd, pd⟩ := evalMul sα vc₁ vc₂
    ⟨_, vd, q(pow_add $pc₁ $pc₂ $pd)⟩

/-- This cache contains data required by the `ring` tactic during execution. -/
structure Cache (α : Q(Type u)) :=
  rα : Option Q(Ring $α)

theorem cast_pos : IsNat (a : R) n → a = n.rawCast + 0
  | ⟨e⟩ => by simp [e]

theorem cast_zero : IsNat (a : R) (nat_lit 0) → a = 0
  | ⟨e⟩ => by simp [e]

theorem cast_neg [Ring R] : IsInt (a : R) (.negOfNat n) → a = (Int.negOfNat n).rawCast + 0
  | ⟨e⟩ => by simp [e]

def evalCast : NormNum.Result e → Option (Result (ExSum sα) e)
  | .isNat _sα (.lit (.natVal 0)) (p : Expr) => clear% _sα
    let p : Q(IsNat $e (nat_lit 0)) := p
    pure ⟨_, .zero, (q(cast_zero $p) : Expr)⟩
  | .isNat _sα lit (p : Expr) => clear% _sα
    let p : Q(IsNat $e $lit) := p
    pure ⟨_, (ExProd.mkNat sα lit.natLit!).2.toSum, (q(cast_pos $p) : Expr)⟩
  | .isNegNat rα lit p =>
    pure ⟨_, (ExProd.mkNegNat _ rα lit.natLit!).2.toSum, (q(cast_neg $p) : Expr)⟩
  | _ => none

theorem atom_pf (a : R) : a = a ^ (nat_lit 1).rawCast * (nat_lit 1).rawCast + 0 := by simp

def evalAtom (e : Q($α)) : RingM (Result (ExSum sα) e) := do
  let i ← addAtom e
  pure ⟨_, (ExExp.exp e _ (.atom i) (ExProd.mkNat sℕ 1).2).toProd.toSum, (q(atom_pf $e) : Expr)⟩

theorem add_congr (_ : a = a') (_ : b = b')
    (_ : a' + b' = c) : (a + b : R) = c := by subst_vars; rfl

theorem mul_congr (_ : a = a') (_ : b = b')
    (_ : a' * b' = c) : (a * b : R) = c := by subst_vars; rfl

theorem pow_congr (_ : a = a') (_ : b = b')
    (_ : a' ^ b' = c) : (a ^ b : R) = c := by subst_vars; rfl

theorem neg_congr {R} [Ring R] {a a' b : R} (_ : a = a')
    (_ : -a' = b) : (-a : R) = b := by subst_vars; rfl

theorem sub_congr {R} [Ring R] {a a' b b' c : R} (_ : a = a') (_ : b = b')
    (_ : a' - b' = c) : (a - b : R) = c := by subst_vars; rfl

def Cache.nat : Cache q(ℕ) := { rα := none }

partial def eval {u} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    (c : Cache α) (e : Q($α)) : RingM (Result (ExSum sα) e) := do
  match e with
  | ~q($a + $b) =>
    let ⟨_, va, pa⟩ ← eval sα c a
    let ⟨_, vb, pb⟩ ← eval sα c b
    let ⟨c, vc, p⟩ := evalAdd sα va vb
    pure ⟨c, vc, (q(add_congr $pa $pb $p) : Expr)⟩
  | ~q($a * $b) =>
    let ⟨_, va, pa⟩ ← eval sα c a
    let ⟨_, vb, pb⟩ ← eval sα c b
    let ⟨c, vc, p⟩ := evalMul sα va vb
    pure ⟨c, vc, (q(mul_congr $pa $pb $p) : Expr)⟩
  | ~q($a ^ $b) =>
    let ⟨_, va, pa⟩ ← eval sα c a
    let ⟨_, vb, pb⟩ ← eval sℕ .nat b
    let ⟨c, vc, p⟩ := evalPow sα va vb
    pure ⟨c, vc, (q(pow_congr $pa $pb $p) : Expr)⟩
  | _ =>
    let els := do
      try evalCast sα (← derive e)
      catch _ => evalAtom sα e
    let some rα := c.rα | els
    match e with
    | ~q(-$a) =>
      let ⟨_, va, pa⟩ ← eval sα c a
      let ⟨b, vb, p⟩ := evalNeg sα rα va
      pure ⟨b, vb, (q(neg_congr $pa $p) : Expr)⟩
    | ~q($a - $b) => do
      let ⟨_, va, pa⟩ ← eval sα c a
      let ⟨_, vb, pb⟩ ← eval sα c b
      let ⟨c, vc, p⟩ := evalSub sα rα va vb
      pure ⟨c, vc, (q(sub_congr $pa $pb $p) : Expr)⟩
    | _ => els

def _root_.Lean.LOption.toOption {α} : LOption α → Option α
  | .some a => some a
  | _ => none

theorem of_eq (_ : (a : R) = c) (_ : b = c) : a = b := by subst_vars; rfl

elab "ring1" tk:"!"? : tactic => liftMetaMAtMain fun g => do
  let some (α, e₁, e₂) := (← instantiateMVars (← g.getType)).eq?
    | throwError "ring failed: not an equality"
  let red := if tk.isSome then .default else .reducible
  let .sort (.succ u) ← whnf (← inferType α) | throwError "not a type{indentExpr α}"
  RingM.run red do
    have α : Q(Type u) := α
    have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
    let sα ← synthInstanceQ (q(CommSemiring $α) : Q(Type u))
    let c := { rα := (← trySynthInstanceQ (q(Ring $α) : Q(Type u))).toOption }
    let ⟨a, va, pa⟩ ← eval sα c e₁
    let ⟨b, vb, pb⟩ ← eval sα c e₂
    unless va.eq vb do
      throwError "ring failed, ring expressions not equal: \n{a}\n  !=\n{b}"
    let pb : Q($e₂ = $a) := pb
    g.assign q(of_eq $pa $pb)

macro "ring1!" : tactic => `(tactic| ring1 !)

macro "ring" tk:"!"? : tactic => `(tactic| ring1 $[!%$tk]?)
macro "ring!" : tactic => `(tactic| ring !)
