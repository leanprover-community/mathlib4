/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue, Tim Baanen
-/
import Lean.Elab.Tactic.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Util.AtomM

/-!
# `ring` tactic

A tactic for solving equations in commutative (semi)rings,
where the exponents can also contain variables.
Based on <http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf> .

More precisely, expressions of the following form are supported:
- constants (non-negative integers)
- variables
- coefficients (any rational number, embedded into the (semi)ring)
- addition of expressions
- multiplication of expressions (`a * b`)
- scalar multiplication of expressions (`n • a`; the multiplier must have type `ℕ`)
- exponentiation of expressions (the exponent must have type `ℕ`)
- subtraction and negation of expressions (if the base is a full ring)

The extension to exponents means that something like `2 * 2^n * b = b * 2^(n+1)` can be proved,
even though it is not strictly speaking an equation in the language of commutative rings.

## Implementation notes

The basic approach to prove equalities is to normalise both sides and check for equality.
The normalisation is guided by building a value in the type `ExSum` at the meta level,
together with a proof (at the base level) that the original value is equal to
the normalised version.

The outline of the file:
- Define a mutual inductive family of types `ExSum`, `ExProd`, `ExBase`,
  which can represent expressions with `+`, `*`, `^` and rational numerals.
  The mutual induction ensures that associativity and distributivity are applied,
  by restricting which kinds of subexpressions appear as arguments to the various operators.
- Represent addition, multiplication and exponentiation in the `ExSum` type,
  thus allowing us to map expressions to `ExSum` (the `eval` function drives this).
  We apply associativity and distributivity of the operators here (helped by `Ex*` types)
  and commutativity as well (by sorting the subterms; unfortunately not helped by anything).
  Any expression not of the above formats is treated as an atom (the same as a variable).

There are some details we glossed over which make the plan more complicated:
- The order on atoms is not initially obvious.
  We construct a list containing them in order of initial appearance in the expression,
  then use the index into the list as a key to order on.
- For `pow`, the exponent must be a natural number, while the base can be any semiring `α`.
  We swap out operations for the base ring `α` with those for the exponent ring `ℕ`
  as soon as we deal with exponents.

## Caveats and future work

The normalized form of an expression is the one that is useful for the tactic,
but not as nice to read. To remedy this, the user-facing normalization calls `ringNFCore`.

Subtraction cancels out identical terms, but division does not.
That is: `a - a = 0 := by ring_exp` solves the goal,
but `a / a := 1 by ring_exp` doesn't.
Note that `0 / 0` is generally defined to be `0`,
so division cancelling out is not true in general.

Multiplication of powers can be simplified a little bit further:
`2 ^ n * 2 ^ n = 4 ^ n := by ring_exp` could be implemented
in a similar way that `2 * a + 2 * a = 4 * a := by ring_exp` already works.
This feature wasn't needed yet, so it's not implemented yet.

## Tags

ring, semiring, exponent, power
-/


namespace Mathlib.Tactic
namespace Ring
open Mathlib.Meta Qq NormNum Lean.Meta AtomM
open Lean (MetaM Expr mkRawNatLit)

/-- A shortcut instance for `CommSemiring ℕ` used by ring. -/
def instCommSemiringNat : CommSemiring ℕ := inferInstance

/--
A typed expression of type `CommSemiring ℕ` used when we are working on
ring subexpressions of type `ℕ`.
-/
def sℕ : Q(CommSemiring ℕ) := q(instCommSemiringNat)

mutual

/-- The base `e` of a normalized exponent expression. -/
inductive ExBase : ∀ {α : Q(Type u)}, Q(CommSemiring $α) → (e : Q($α)) → Type
  /--
  An atomic expression `e` with id `id`.

  Atomic expressions are those which `ring` cannot parse any further.
  For instance, `a + (a % b)` has `a` and `(a % b)` as atoms.
  The `ring1` tactic does not normalize the subexpressions in atoms, but `ring_nf` does.

  Atoms in fact represent equivalence classes of expressions, modulo definitional equality.
  The field `index : ℕ` should be a unique number for each class,
  while `value : expr` contains a representative of this class.
  The function `resolve_atom` determines the appropriate atom for a given expression.
  -/
  | atom (id : ℕ) : ExBase sα e
  /-- A sum of monomials.  -/
  | sum (_ : ExSum sα e) : ExBase sα e

/--
A monomial, which is a product of powers of `ExBase` expressions,
terminated by a (nonzero) constant coefficient.
-/
inductive ExProd : ∀ {α : Q(Type u)}, Q(CommSemiring $α) → (e : Q($α)) → Type
  /-- A coefficient `value`, which must not be `0`. `e` is a raw int cast. -/
  | const (value : ℤ) : ExProd sα e
  /-- A product `x ^ e * b` is a monomial if `b` is a monomial. Here `x` is a `ExBase`
  and `e` is a `ExProd` representing a monomial expression in `ℕ` (it is a monomial instead of
  a polynomial because we eagerly normalize `x ^ (a + b) = x ^ a * x ^ b`.) -/
  | mul {α : Q(Type u)} {sα : Q(CommSemiring $α)} {x : Q($α)} {e : Q(ℕ)} {b : Q($α)} :
    ExBase sα x → ExProd sℕ e → ExProd sα b → ExProd sα q($x ^ $e * $b)

/-- A polynomial expression, which is a sum of monomials. -/
inductive ExSum : ∀ {α : Q(Type u)}, Q(CommSemiring $α) → (e : Q($α)) → Type
  /-- Zero is a polynomial. `e` is the expression `0`. -/
  | zero {α : Q(Type u)} {sα : Q(CommSemiring $α)} : ExSum sα q(0 : $α)
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {α : Q(Type u)} {sα : Q(CommSemiring $α)} {a b : Q($α)} :
    ExProd sα a → ExSum sα b → ExSum sα q($a + $b)
end

mutual -- partial only to speed up compilation

/-- Equality test for expressions. This is not a `BEq` instance because it is heterogeneous. -/
partial def ExBase.eq : ExBase sα a → ExBase sα b → Bool
  | .atom i, .atom j => i == j
  | .sum a, .sum b => a.eq b
  | _, _ => false

@[inherit_doc ExBase.eq]
partial def ExProd.eq : ExProd sα a → ExProd sα b → Bool
  | .const i, .const j => i == j
  | .mul a₁ a₂ a₃, .mul b₁ b₂ b₃ => a₁.eq b₁ && a₂.eq b₂ && a₃.eq b₃
  | _, _ => false

@[inherit_doc ExBase.eq]
partial def ExSum.eq : ExSum sα a → ExSum sα b → Bool
  | .zero, .zero => true
  | .add a₁ a₂, .add b₁ b₂ => a₁.eq b₁ && a₂.eq b₂
  | _, _ => false
end

mutual -- partial only to speed up compilation
/--
A total order on normalized expressions.
This is not an `Ord` instance because it is heterogeneous.
-/
partial def ExBase.cmp : ExBase sα a → ExBase sα b → Ordering
  | .atom i, .atom j => compare i j
  | .sum a, .sum b => a.cmp b
  | .atom .., .sum .. => .lt
  | .sum .., .atom .. => .gt

@[inherit_doc ExBase.cmp]
partial def ExProd.cmp : ExProd sα a → ExProd sα b → Ordering
  | .const i, .const j => compare i j
  | .mul a₁ a₂ a₃, .mul b₁ b₂ b₃ => (a₁.cmp b₁).then (a₂.cmp b₂) |>.then (a₃.cmp b₃)
  | .const .., .mul .. => .lt
  | .mul .., .const .. => .gt

@[inherit_doc ExBase.cmp]
partial def ExSum.cmp : ExSum sα a → ExSum sα b → Ordering
  | .zero, .zero => .eq
  | .add a₁ a₂, .add b₁ b₂ => (a₁.cmp b₁).then (a₂.cmp b₂)
  | .zero, .add .. => .lt
  | .add .., .zero => .gt
end

instance : Inhabited (Σ e, (ExBase sα) e) := ⟨default, .atom 0⟩
instance : Inhabited (Σ e, (ExSum sα) e) := ⟨_, .zero⟩
instance : Inhabited (Σ e, (ExProd sα) e) := ⟨default, .const 0⟩

mutual

/-- Converts `ExBase sα` to `ExBase sβ`, assuming `sα` and `sβ` are defeq. -/
partial def ExBase.cast : ExBase sα a → Σ a, ExBase sβ a
  | .atom i => ⟨a, .atom i⟩
  | .sum a => let ⟨_, vb⟩ := a.cast; ⟨_, .sum vb⟩

/-- Converts `ExProd sα` to `ExProd sβ`, assuming `sα` and `sβ` are defeq. -/
partial def ExProd.cast : ExProd sα a → Σ a, ExProd sβ a
  | .const i => ⟨a, .const i⟩
  | .mul a₁ a₂ a₃ => ⟨_, .mul a₁.cast.2 a₂ a₃.cast.2⟩

/-- Converts `ExSum sα` to `ExSum sβ`, assuming `sα` and `sβ` are defeq. -/
partial def ExSum.cast : ExSum sα a → Σ a, ExSum sβ a
  | .zero => ⟨_, .zero⟩
  | .add a₁ a₂ => ⟨_, .add a₁.cast.2 a₂.cast.2⟩

end

/--
The result of evaluating an (unnormalized) expression `e` into the type family `E`
(one of `ExSum`, `ExProd`, `ExBase`) is a (normalized) element `e'`
and a representation `E e'` for it, and a proof of `e = e'`.
-/
structure Result {α : Q(Type u)} (E : Q($α) → Type) (e : Q($α)) where
  /-- The normalized result. -/
  expr : Q($α)
  /-- The data associated to the normalization. -/
  val : E expr
  /-- A proof that the original expression is equal to the normalized result. -/
  proof : Q($e = $expr)

instance [Inhabited (Σ e, E e)] : Inhabited (Result E e) :=
  let ⟨e', v⟩ : Σ e, E e := default; ⟨e', v, default⟩

variable {α : Q(Type u)} (sα : Q(CommSemiring $α)) [CommSemiring R]

/--
Constructs the expression corresponding to `.const n`.
(The `.const` constructor does not check that the expression is correct.)
-/
def ExProd.mkNat (n : ℕ) : (e : Q($α)) × ExProd sα e :=
  let lit : Q(ℕ) := mkRawNatLit n
  ⟨q(($lit).rawCast : $α), .const n⟩

/--
Constructs the expression corresponding to `.const (-n)`.
(The `.const` constructor does not check that the expression is correct.)
-/
def ExProd.mkNegNat (_ : Q(Ring $α)) (n : ℕ) : (e : Q($α)) × ExProd sα e :=
  let lit : Q(ℕ) := mkRawNatLit n
  ⟨q((Int.negOfNat $lit).rawCast : $α), .const (-n)⟩

section
variable {sα}

/-- Embed an exponent (a `ExBase, ExProd` pair) as a `ExProd` by multiplying by 1. -/
def ExBase.toProd (va : ExBase sα a) (vb : ExProd sℕ b) :
  ExProd sα q($a ^ $b * (nat_lit 1).rawCast) := .mul va vb (.const 1)

/-- Embed `ExProd` in `ExSum` by adding 0. -/
def ExProd.toSum (v : ExProd sα e) : ExSum sα q($e + 0) := .add v .zero

/-- Get the leading coefficient of a `ExProd`. -/
def ExProd.coeff : ExProd sα e → ℤ
  | .const z => z
  | .mul _ _ v => v.coeff
end

/--
Two monomials are said to "overlap" if they differ by a constant factor, in which case the
constants just add. When this happens, the constant may be either zero (if the monomials cancel)
or nonzero (if they add up); the zero case is handled specially.
-/
inductive Overlap (e : Q($α)) where
  /-- The expression `e` (the sum of monomials) is equal to `0`. -/
  | zero (_ : Q(IsNat $e (nat_lit 0)))
  /-- The expression `e` (the sum of monomials) is equal to another monomial
  (with nonzero leading coefficient). -/
  | nonzero (_ : Result (ExProd sα) e)

theorem add_overlap_pf (x : R) (e) (pq_pf : a + b = c) :
    x ^ e * a + x ^ e * b = x ^ e * c := by subst_vars; simp [mul_add]

theorem add_overlap_pf_zero (x : R) (e) :
    IsNat (a + b) (nat_lit 0) → IsNat (x ^ e * a + x ^ e * b) (nat_lit 0)
  | ⟨h⟩ => ⟨by simp [h, ← mul_add]⟩

/--
Given monomials `va, vb`, attempts to add them together to get another monomial.
If the monomials are not compatible, returns `none`.
For example, `xy + 2xy = 3xy` is a `.nonzero` overlap, while `xy + xz` returns `none`
and `xy + -xy = 0` is a `.zero` overlap.
-/
def evalAddOverlap (va : ExProd sα a) (vb : ExProd sα b) : Option (Overlap sα q($a + $b)) :=
  match va, vb with
  | .const za, .const zb => do
    let ra := Result.ofRawInt za a; let rb := Result.ofRawInt zb b
    let res ← NormNum.evalAdd.core q($a + $b) _ _ ra rb
    match res with
    | .isNat _ (.lit (.natVal 0)) p => pure <| .zero p
    | rc => let ⟨zc, c, pc⟩ := rc.toRawIntEq.get!; pure <| .nonzero ⟨c, .const zc, pc⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, .mul vb₁ vb₂ vb₃ => do
    guard (va₁.eq vb₁ && va₂.eq vb₂)
    match ← evalAddOverlap va₃ vb₃ with
    | .zero p => pure <| .zero (q(add_overlap_pf_zero $a₁ $a₂ $p) : Expr)
    | .nonzero ⟨_, vc, p⟩ =>
      pure <| .nonzero ⟨_, .mul va₁ va₂ vc, (q(add_overlap_pf $a₁ $a₂ $p) : Expr)⟩
  | _, _ => none

theorem add_pf_zero_add (b : R) : 0 + b = b := by simp

theorem add_pf_add_zero (a : R) : a + 0 = a := by simp

theorem add_pf_add_overlap
    (_ : a₁ + b₁ = c₁) (_ : a₂ + b₂ = c₂) : (a₁ + a₂ : R) + (b₁ + b₂) = c₁ + c₂ := by
  subst_vars; simp [add_assoc, add_left_comm]

theorem add_pf_add_overlap_zero
    (h : IsNat (a₁ + b₁) (nat_lit 0)) (h₄ : a₂ + b₂ = c) : (a₁ + a₂ : R) + (b₁ + b₂) = c := by
  subst_vars; rw [add_add_add_comm, h.1, Nat.cast_zero, add_pf_zero_add]

theorem add_pf_add_lt (a₁ : R) (_ : a₂ + b = c) : (a₁ + a₂) + b = a₁ + c := by simp [*, add_assoc]

theorem add_pf_add_gt (b₁ : R) (_ : a + b₂ = c) : a + (b₁ + b₂) = b₁ + c := by
  subst_vars; simp [add_left_comm]

/-- Adds two polynomials `va, vb` together to get a normalized result polynomial.

* `0 + b = 0`
* `a + 0 = 0`
* `a * x + a * y = a * (x + y)` (for `x`, `y` coefficients; uses `evalAddOverlap`)
* `(a₁ + a₂) + (b₁ + b₂) = a₁ + (a₂ + (b₁ + b₂))` (if `a₁.lt b₁`)
* `(a₁ + a₂) + (b₁ + b₂) = b₁ + ((a₁ + a₂) + b₂)` (if not `a₁.lt b₁`)
-/
partial def evalAdd (va : ExSum sα a) (vb : ExSum sα b) : Result (ExSum sα) q($a + $b) :=
  match va, vb with
  | .zero, vb => ⟨b, vb, q(add_pf_zero_add $b)⟩
  | va, .zero => ⟨a, va, q(add_pf_add_zero $a)⟩
  | .add (a := a₁) (b := _a₂) va₁ va₂, .add (a := b₁) (b := _b₂) vb₁ vb₂ =>
    match evalAddOverlap sα va₁ vb₁ with
    | some (.nonzero ⟨_, vc₁, pc₁⟩) =>
      let ⟨_, vc₂, pc₂⟩ := evalAdd va₂ vb₂
      ⟨_, .add vc₁ vc₂, q(add_pf_add_overlap $pc₁ $pc₂)⟩
    | some (.zero pc₁) =>
      let ⟨c₂, vc₂, pc₂⟩ := evalAdd va₂ vb₂
      ⟨c₂, vc₂, q(add_pf_add_overlap_zero $pc₁ $pc₂)⟩
    | none =>
      if let .lt := va₁.cmp vb₁ then
        let ⟨_c, vc, (pc : Q($_a₂ + ($b₁ + $_b₂) = $_c))⟩ := evalAdd va₂ vb
        ⟨_, .add va₁ vc, q(add_pf_add_lt $a₁ $pc)⟩
      else
        let ⟨_c, vc, (pc : Q($a₁ + $_a₂ + $_b₂ = $_c))⟩ := evalAdd va vb₂
        ⟨_, .add vb₁ vc, q(add_pf_add_gt $b₁ $pc)⟩

theorem one_mul (a : R) : (nat_lit 1).rawCast * a = a := by simp [Nat.rawCast]

theorem mul_one (a : R) : a * (nat_lit 1).rawCast = a := by simp [Nat.rawCast]

theorem mul_pf_left (a₁ : R) (a₂) (_ : a₃ * b = c) : (a₁ ^ a₂ * a₃ : R) * b = a₁ ^ a₂ * c := by
  subst_vars; rw [mul_assoc]

theorem mul_pf_right (b₁ : R) (b₂) (_ : a * b₃ = c) : a * (b₁ ^ b₂ * b₃) = b₁ ^ b₂ * c := by
  subst_vars; rw [mul_left_comm]

theorem mul_pp_pf_overlap (x : R) (_ : ea + eb = e) (_ : a₂ * b₂ = c) :
    (x ^ ea * a₂ : R) * (x ^ eb * b₂) = x ^ e * c := by
  subst_vars; simp [pow_add, mul_mul_mul_comm]

/-- Multiplies two monomials `va, vb` together to get a normalized result monomial.

* `x * y = (x * y)` (for `x`, `y` coefficients)
* `x * (b₁ * b₂) = b₁ * (b₂ * x)` (for `x` coefficient)
* `(a₁ * a₂) * y = a₁ * (a₂ * y)` (for `y` coefficient)
* `(x ^ ea * a₂) * (x ^ eb * b₂) = x ^ (ea + eb) * (a₂ * b₂)`
    (if `ea` and `eb` are identical except coefficient)
* `(a₁ * a₂) * (b₁ * b₂) = a₁ * (a₂ * (b₁ * b₂))` (if `a₁.lt b₁`)
* `(a₁ * a₂) * (b₁ * b₂) = b₁ * ((a₁ * a₂) * b₂)` (if not `a₁.lt b₁`)
-/
partial def evalMulProd (va : ExProd sα a) (vb : ExProd sα b) : Result (ExProd sα) q($a * $b) :=
  match va, vb with
  | .const za, .const zb =>
    if za = 1 then
      ⟨b, .const zb, (q(one_mul $b) : Expr)⟩
    else if zb = 1 then
      ⟨a, .const za, (q(mul_one $a) : Expr)⟩
    else
      let ra := Result.ofRawInt za a; let rb := Result.ofRawInt zb b
      let ⟨zc, c, pc⟩ :=
        (NormNum.evalMul.core q($a * $b) _ _ q(CommSemiring.toSemiring) ra rb).get!.toRawIntEq.get!
      ⟨c, .const zc, pc⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, .const _ =>
    let ⟨_, vc, pc⟩ := evalMulProd va₃ vb
    ⟨_, .mul va₁ va₂ vc, (q(mul_pf_left $a₁ $a₂ $pc) : Expr)⟩
  | .const _, .mul (x := b₁) (e := b₂) vb₁ vb₂ vb₃ =>
    let ⟨_, vc, pc⟩ := evalMulProd va vb₃
    ⟨_, .mul vb₁ vb₂ vc, (q(mul_pf_right $b₁ $b₂ $pc) : Expr)⟩
  | .mul (x := xa) (e := ea) vxa vea va₂, .mul (x := xb) (e := eb) vxb veb vb₂ => Id.run do
    if vxa.eq vxb then
      if let some (.nonzero ⟨_, ve, pe⟩) := evalAddOverlap sℕ vea veb then
        let ⟨_, vc, pc⟩ := evalMulProd va₂ vb₂
        return ⟨_, .mul vxa ve vc, (q(mul_pp_pf_overlap $xa $pe $pc) : Expr)⟩
    if let .lt := (vxa.cmp vxb).then (vea.cmp veb) then
      let ⟨_, vc, pc⟩ := evalMulProd va₂ vb
      ⟨_, .mul vxa vea vc, (q(mul_pf_left $xa $ea $pc) : Expr)⟩
    else
      let ⟨_, vc, pc⟩ := evalMulProd va vb₂
      ⟨_, .mul vxb veb vc, (q(mul_pf_right $xb $eb $pc) : Expr)⟩

theorem mul_zero (a : R) : a * 0 = 0 := by simp

theorem mul_add (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : c₁ + 0 + c₂ = d) :
    a * (b₁ + b₂) = d := by subst_vars; simp [_root_.mul_add]

/-- Multiplies a monomial `va` to a polynomial `vb` to get a normalized result polynomial.

* `a * 0 = 0`
* `a * (b₁ + b₂) = (a * b₁) + (a * b₂)`
-/
def evalMul₁ (va : ExProd sα a) (vb : ExSum sα b) : Result (ExSum sα) q($a * $b) :=
  match vb with
  | .zero => ⟨_, .zero, q(mul_zero $a)⟩
  | .add vb₁ vb₂ =>
    let ⟨_, vc₁, pc₁⟩ := evalMulProd sα va vb₁
    let ⟨_, vc₂, pc₂⟩ := evalMul₁ va vb₂
    let ⟨_, vd, pd⟩ := evalAdd sα vc₁.toSum vc₂
    ⟨_, vd, q(mul_add $pc₁ $pc₂ $pd)⟩

theorem zero_mul (b : R) : 0 * b = 0 := by simp

theorem add_mul (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : c₁ + c₂ = d) :
    (a₁ + a₂) * b = d := by subst_vars; simp [_root_.add_mul]

/-- Multiplies two polynomials `va, vb` together to get a normalized result polynomial.

* `0 * b = 0`
* `(a₁ + a₂) * b = (a₁ * b) + (a₂ * b)`
-/
def evalMul (va : ExSum sα a) (vb : ExSum sα b) : Result (ExSum sα) q($a * $b) :=
  match va with
  | .zero => ⟨_, .zero, q(zero_mul $b)⟩
  | .add va₁ va₂ =>
    let ⟨_, vc₁, pc₁⟩ := evalMul₁ sα va₁ vb
    let ⟨_, vc₂, pc₂⟩ := evalMul va₂ vb
    let ⟨_, vd, pd⟩ := evalAdd sα vc₁ vc₂
    ⟨_, vd, q(add_mul $pc₁ $pc₂ $pd)⟩

theorem nat_cast_nat (n) : ((Nat.rawCast n : ℕ) : R) = Nat.rawCast n := by simp

theorem nat_cast_mul (a₂) (_ : ((a₁ : ℕ) : R) = b₁) (_ : ((a₃ : ℕ) : R) = b₃) :
    ((a₁ ^ a₂ * a₃ : ℕ) : R) = b₁ ^ a₂ * b₃ := by subst_vars; simp

theorem nat_cast_zero : ((0 : ℕ) : R) = 0 := Nat.cast_zero

theorem nat_cast_add (_ : ((a₁ : ℕ) : R) = b₁) (_ : ((a₂ : ℕ) : R) = b₂) :
    ((a₁ + a₂ : ℕ) : R) = b₁ + b₂ := by subst_vars; simp

mutual

/-- Applies `Nat.cast` to a nat polynomial to produce a polynomial in `α`.

* An atom `e` causes `↑e` to be allocated as a new atom.
* A sum delegates to `ExSum.evalNatCast`.
-/
partial def ExBase.evalNatCast (va : ExBase sℕ a) : AtomM (Result (ExBase sα) q($a)) :=
  match va with
  | .atom _ => do
    let a' : Q($α) := q($a)
    let i ← addAtom a'
    pure ⟨a', ExBase.atom i, (q(Eq.refl $a') : Expr)⟩
  | .sum va => do
    let ⟨_, vc, p⟩ ← va.evalNatCast
    pure ⟨_, .sum vc, p⟩

/-- Applies `Nat.cast` to a nat monomial to produce a monomial in `α`.

* `↑c = c` if `c` is a numeric literal
* `↑(a ^ n * b) = ↑a ^ n * ↑b`
-/
partial def ExProd.evalNatCast (va : ExProd sℕ a) : AtomM (Result (ExProd sα) q($a)) :=
  match va with
  | .const c =>
    have n : Q(ℕ) := a.appArg!
    pure ⟨q(Nat.rawCast $n), .const c, (q(nat_cast_nat (R := $α) $n) : Expr)⟩
  | .mul (e := a₂) va₁ va₂ va₃ => do
    let ⟨_, vb₁, pb₁⟩ ← va₁.evalNatCast
    let ⟨_, vb₃, pb₃⟩ ← va₃.evalNatCast
    pure ⟨_, .mul vb₁ va₂ vb₃, q(nat_cast_mul $a₂ $pb₁ $pb₃)⟩

/-- Applies `Nat.cast` to a nat polynomial to produce a polynomial in `α`.

* `↑0 = 0`
* `↑(a + b) = ↑a + ↑b`
-/
partial def ExSum.evalNatCast (va : ExSum sℕ a) : AtomM (Result (ExSum sα) q($a)) :=
  match va with
  | .zero => pure ⟨_, .zero, q(nat_cast_zero (R := $α))⟩
  | .add va₁ va₂ => do
    let ⟨_, vb₁, pb₁⟩ ← va₁.evalNatCast
    let ⟨_, vb₂, pb₂⟩ ← va₂.evalNatCast
    pure ⟨_, .add vb₁ vb₂, q(nat_cast_add $pb₁ $pb₂)⟩

end

theorem smul_nat (_ : (a * b : ℕ) = c) : a • b = c := by subst_vars; simp

theorem smul_eq_cast (_ : ((a : ℕ) : R) = a') (_ : a' * b = c) : a • b = c := by subst_vars; simp

/-- Constructs the scalar multiplication `n • a`, where both `n : ℕ` and `a : α` are normalized
polynomial expressions.

* `a • b = a * b` if `α = ℕ`
* `a • b = ↑a * b` otherwise
-/
def evalNSMul (va : ExSum sℕ a) (vb : ExSum sα b) : AtomM (Result (ExSum sα) q($a • $b)) := do
  if ← isDefEq sα sℕ then
    let ⟨_, va'⟩ := va.cast
    have _b : Q(ℕ) := b
    let ⟨(_c : Q(ℕ)), vc, (pc : Q($a * $_b = $_c))⟩ := evalMul sα va' vb
    pure ⟨_, vc, (q(smul_nat $pc) : Expr)⟩
  else
    let ⟨_, va', pa'⟩ ← va.evalNatCast sα
    let ⟨_, vc, pc⟩ := evalMul sα va' vb
    pure ⟨_, vc, (q(smul_eq_cast $pa' $pc) : Expr)⟩

theorem neg_one_mul {R} [Ring R] {a b : R} (_ : (Int.negOfNat (nat_lit 1)).rawCast * a = b) :
    -a = b := by subst_vars; simp [Int.negOfNat]

theorem neg_mul {R} [Ring R] (a₁ : R) (a₂) {a₃ b : R}
    (_ : -a₃ = b) : -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b := by subst_vars; simp

/-- Negates a monomial `va` to get another monomial.

* `-c = (-c)` (for `c` coefficient)
* `-(a₁ * a₂) = a₁ * -a₂`
-/
def evalNegProd (rα : Q(Ring $α)) (va : ExProd sα a) : Result (ExProd sα) q(-$a) :=
  match va with
  | .const za =>
    let lit : Q(ℕ) := mkRawNatLit 1
    let ⟨m1, _⟩ := ExProd.mkNegNat sα rα 1
    let rm := Result.isNegNat rα lit (q(IsInt.of_raw $α (.negOfNat $lit)) : Expr)
    let ra := Result.ofRawInt za a
    let ⟨zb, b, (pb : Q((Int.negOfNat (nat_lit 1)).rawCast * $a = $b))⟩ :=
      (NormNum.evalMul.core q($m1 * $a) _ _ q(CommSemiring.toSemiring) rm ra).get!.toRawIntEq.get!
    ⟨b, .const zb, (q(neg_one_mul (R := $α) $pb) : Expr)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃ =>
    let ⟨_, vb, pb⟩ := evalNegProd rα va₃
    ⟨_, .mul va₁ va₂ vb, (q(neg_mul $a₁ $a₂ $pb) : Expr)⟩

theorem neg_zero {R} [Ring R] : -(0 : R) = 0 := by simp

theorem neg_add {R} [Ring R] {a₁ a₂ b₁ b₂ : R}
    (_ : -a₁ = b₁) (_ : -a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂ := by subst_vars; simp [add_comm]

/-- Negates a polynomial `va` to get another polynomial.

* `-0 = 0` (for `c` coefficient)
* `-(a₁ + a₂) = -a₁ + -a₂`
-/
def evalNeg (rα : Q(Ring $α)) (va : ExSum sα a) : Result (ExSum sα) q(-$a) :=
  match va with
  | .zero => ⟨_, .zero, (q(neg_zero (R := $α)) : Expr)⟩
  | .add va₁ va₂ =>
    let ⟨_, vb₁, pb₁⟩ := evalNegProd sα rα va₁
    let ⟨_, vb₂, pb₂⟩ := evalNeg rα va₂
    ⟨_, .add vb₁ vb₂, (q(neg_add $pb₁ $pb₂) : Expr)⟩

theorem sub_pf {R} [Ring R] {a b c d : R}
    (_ : -b = c) (_ : a + c = d) : a - b = d := by subst_vars; simp [sub_eq_add_neg]

/-- Subtracts two polynomials `va, vb` to get a normalized result polynomial.

* `a - b = a + -b`
-/
def evalSub (rα : Q(Ring $α)) (va : ExSum sα a) (vb : ExSum sα b) : Result (ExSum sα) q($a - $b) :=
  let ⟨_c, vc, pc⟩ := evalNeg sα rα vb
  let ⟨d, vd, (pd : Q($a + $_c = $d))⟩ := evalAdd sα va vc
  ⟨d, vd, (q(sub_pf $pc $pd) : Expr)⟩

theorem pow_prod_atom (a : R) (b) : a ^ b = (a + 0) ^ b * (nat_lit 1).rawCast := by simp

/--
The fallback case for exponentiating polynomials is to use `ExBase.toProd` to just build an
exponent expression. (This has a slightly different normalization than `evalPowAtom` because
the input types are different.)

* `x ^ e = (x + 0) ^ e * 1`
-/
def evalPowProdAtom (va : ExProd sα a) (vb : ExProd sℕ b) : Result (ExProd sα) q($a ^ $b) :=
  ⟨_, (ExBase.sum va.toSum).toProd vb, q(pow_prod_atom $a $b)⟩

theorem pow_atom (a : R) (b) : a ^ b = a ^ b * (nat_lit 1).rawCast + 0 := by simp

/--
The fallback case for exponentiating polynomials is to use `ExBase.toProd` to just build an
exponent expression.

* `x ^ e = x ^ e * 1 + 0`
-/
def evalPowAtom (va : ExBase sα a) (vb : ExProd sℕ b) : Result (ExSum sα) q($a ^ $b) :=
  ⟨_, (va.toProd vb).toSum, q(pow_atom $a $b)⟩

theorem const_pos (n : ℕ) (h : Nat.ble 1 n = true) : 0 < (n.rawCast : ℕ) := Nat.le_of_ble_eq_true h

theorem mul_exp_pos (n) (h₁ : 0 < a₁) (h₂ : 0 < a₂) : 0 < a₁ ^ n * a₂ :=
  Nat.mul_pos (Nat.pos_pow_of_pos _ h₁) h₂

theorem add_pos_left (a₂) (h : 0 < a₁) : 0 < a₁ + a₂ := Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

theorem add_pos_right (a₁) (h : 0 < a₂) : 0 < a₁ + a₂ := Nat.lt_of_lt_of_le h (Nat.le_add_left ..)

mutual

/-- Attempts to prove that a polynomial expression in `ℕ` is positive.

* Atoms are not (necessarily) positive
* Sums defer to `ExSum.evalPos`
-/
partial def ExBase.evalPos (va : ExBase sℕ a) : Option Q(0 < $a) :=
  match va with
  | .atom _ => none
  | .sum va => va.evalPos

/-- Attempts to prove that a monomial expression in `ℕ` is positive.

* `0 < c` (where `c` is a numeral) is true by the normalization invariant (`c` is not zero)
* `0 < x ^ e * b` if `0 < x` and `0 < b`
-/
partial def ExProd.evalPos (va : ExProd sℕ a) : Option Q(0 < $a) :=
  match va with
  | .const n =>
    -- it must be positive because it is a nonzero nat literal
    have lit : Q(ℕ) := a.appArg!
    let p : Q(Nat.ble 1 $lit = true) := (q(Eq.refl true) : Expr)
    some (q(const_pos $lit $p) : Expr)
  | .mul (e := ea₁) vxa₁ _ va₂ => do
    let pa₁ ← vxa₁.evalPos
    let pa₂ ← va₂.evalPos
    some q(mul_exp_pos $ea₁ $pa₁ $pa₂)

/-- Attempts to prove that a polynomial expression in `ℕ` is positive.

* `0 < 0` fails
* `0 < a + b` if `0 < a` or `0 < b`
-/
partial def ExSum.evalPos (va : ExSum sℕ a) : Option Q(0 < $a) :=
  match va with
  | .zero => none
  | .add (a := a₁) (b := a₂) va₁ va₂ => do
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

/--
The main case of exponentiation of ring expressions is when `va` is a polynomial and `n` is a
nonzero literal expression, like `(x + y)^5`. In this case we work out the polynomial completely
into a sum of monomials.

* `x ^ 1 = x`
* `x ^ (2*n) = x ^ n * x ^ n`
* `x ^ (2*n+1) = x ^ n * x ^ n * x`
-/
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

/-- There are several special cases when exponentiating monomials:

* `1 ^ n = 1`
* `x ^ y = (x ^ y)` when `x` and `y` are constants
* `(a * b) ^ e = a ^ e * b ^ e`

In all other cases we use `evalPowProdAtom`.
-/
def evalPowProd (va : ExProd sα a) (vb : ExProd sℕ b) : Result (ExProd sα) q($a ^ $b) :=
  let res : Option (Result (ExProd sα) q($a ^ $b)) := do
    match va, vb with
    | .const 1, _ => some ⟨_, va, (q(one_pow (R := $α) $b) : Expr)⟩
    | .const za, .const zb =>
      guard (0 ≤ zb)
      let ra := Result.ofRawInt za a
      have lit : Q(ℕ) := b.appArg!
      let rb := (q(IsNat.of_raw ℕ $lit) : Expr)
      let ⟨zc, c, pc⟩ :=
        (← NormNum.evalPow.core q($a ^ $b) _ b lit rb q(CommSemiring.toSemiring) ra).toRawIntEq.get!
      some ⟨c, .const zc, pc⟩
    | .mul vxa₁ vea₁ va₂, vb => do
      let ⟨_, vc₁, pc₁⟩ := evalMulProd sℕ vea₁ vb
      let ⟨_, vc₂, pc₂⟩ := evalPowProd va₂ vb
      some ⟨_, .mul vxa₁ vc₁ vc₂, q(mul_pow $pc₁ $pc₂)⟩
    | _, _ => none
  res.getD (evalPowProdAtom sα va vb)

/--
The result of `extractCoeff` is a numeral and a proof that the original expression
factors by this numeral.
-/
structure ExtractCoeff (e : Q(ℕ)) where
  /-- A raw natural number literal. -/
  k : Q(ℕ)
  /-- The result of extracting the coefficient is a monic monomial. -/
  e' : Q(ℕ)
  /-- `e'` is a monomial. -/
  ve' : ExProd sℕ e'
  /-- The proof that `e` splits into the coefficient `k` and the monic monomial `e'`. -/
  p : Q($e = $e' * $k)

theorem coeff_one (k : ℕ) : k.rawCast = (nat_lit 1).rawCast * k := by simp

theorem coeff_mul (a₁ a₂ : ℕ) (_ : a₃ = c₂ * k) : a₁ ^ a₂ * a₃ = (a₁ ^ a₂ * c₂) * k := by
  subst_vars; rw [mul_assoc]

/-- Given a monomial expression `va`, splits off the leading coefficient `k` and the remainder
`e'`, stored in the `ExtractCoeff` structure.

* `c = 1 * c` (if `c` is a constant)
* `a * b = (a * b') * k` if `b = b' * k`
-/
def extractCoeff (va : ExProd sℕ a) : ExtractCoeff a :=
  match va with
  | .const n =>
    have k : Q(ℕ) := a.appArg!
    ⟨k, q((nat_lit 1).rawCast), .const 1, (q(coeff_one $k) : Expr)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃ =>
    let ⟨k, _, vc, pc⟩ := extractCoeff va₃
    ⟨k, _, .mul va₁ va₂ vc, q(coeff_mul $a₁ $a₂ $pc)⟩

theorem pow_one_cast (a : R) : a ^ (nat_lit 1).rawCast = a := by simp

theorem zero_pow (_ : 0 < b) : (0 : R) ^ b = 0 := match b with | b+1 => by simp [pow_succ]

theorem single_pow (_ : (a : R) ^ b = c) : (a + 0) ^ b = c + 0 := by simp [*]

theorem pow_nat (_ : b = c * k) (_ : a ^ c = d) (_ : d ^ k = e) : (a : R) ^ b = e := by
  subst_vars; simp [pow_mul]

/-- Exponentiates a polynomial `va` by a monomial `vb`, including several special cases.

* `a ^ 1 = a`
* `0 ^ e = 0` if `0 < e`
* `(a + 0) ^ b = a ^ b` computed using `evalPowProd`
* `a ^ b = (a ^ b') ^ k` if `b = b' * k` and `k > 1`

Otherwise `a ^ b` is just encoded as `a ^ b * 1 + 0` using `evalPowAtom`.
-/
partial def evalPow₁ (va : ExSum sα a) (vb : ExProd sℕ b) : Result (ExSum sα) q($a ^ $b) :=
  match va, vb with
  | _, .const 1 => ⟨_, va, (q(pow_one_cast $a) : Expr)⟩
  | .zero, vb => match vb.evalPos with
    | some p => ⟨_, .zero, q(zero_pow (R := $α) $p)⟩
    | none => evalPowAtom sα (.sum .zero) vb
  | ExSum.add va .zero, vb => -- TODO: using `.add` here takes a while to compile?
    let ⟨_, vc, pc⟩ := evalPowProd sα va vb
    ⟨_, vc.toSum, q(single_pow $pc)⟩
  | va, vb =>
    if vb.coeff > 1 then
      let ⟨k, _, vc, pc⟩ := extractCoeff vb
      let ⟨_, vd, pd⟩ := evalPow₁ va vc
      let ⟨_, ve, pe⟩ := evalPowNat sα vd k
      ⟨_, ve, q(pow_nat $pc $pd $pe)⟩
    else evalPowAtom sα (.sum va) vb

theorem pow_zero (a : R) : a ^ 0 = (nat_lit 1).rawCast + 0 := by simp

theorem pow_add (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c₂) (_ : c₁ * c₂ = d) :
  (a : R) ^ (b₁ + b₂) = d := by subst_vars; simp [_root_.pow_add]

/-- Exponentiates two polynomials `va, vb`.

* `a ^ 0 = 1`
* `a ^ (b₁ + b₂) = a ^ b₁ * a ^ b₂`
-/
def evalPow (va : ExSum sα a) (vb : ExSum sℕ b) : Result (ExSum sα) q($a ^ $b) :=
  match vb with
  | .zero => ⟨_, (ExProd.mkNat sα 1).2.toSum, q(pow_zero $a)⟩
  | .add vb₁ vb₂ =>
    let ⟨_, vc₁, pc₁⟩ := evalPow₁ sα va vb₁
    let ⟨_, vc₂, pc₂⟩ := evalPow va vb₂
    let ⟨_, vd, pd⟩ := evalMul sα vc₁ vc₂
    ⟨_, vd, q(pow_add $pc₁ $pc₂ $pd)⟩

/-- This cache contains data required by the `ring` tactic during execution. -/
structure Cache (α : Q(Type u)) :=
  /-- A ring instance on `α`, if available. -/
  rα : Option Q(Ring $α)

theorem cast_pos : IsNat (a : R) n → a = n.rawCast + 0
  | ⟨e⟩ => by simp [e]

theorem cast_zero : IsNat (a : R) (nat_lit 0) → a = 0
  | ⟨e⟩ => by simp [e]

theorem cast_neg {R} [Ring R] {a : R} : IsInt a (.negOfNat n) → a = (Int.negOfNat n).rawCast + 0
  | ⟨e⟩ => by simp [e]

/-- Converts a proof by `norm_num` that `e` is a numeral, into a normalization as a monomial:

* `e = 0` if `norm_num` returns `IsNat e 0`
* `e = Nat.rawCast n + 0` if `norm_num` returns `IsNat e n`
* `e = Int.rawCast n + 0` if `norm_num` returns `IsInt e n`
-/
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
theorem atom_pf' (p : (a : R) = a') :
    a = a' ^ (nat_lit 1).rawCast * (nat_lit 1).rawCast + 0 := by simp [*]

/--
Evaluates an atom, an expression where `ring` can find no additional structure.

* `a = a ^ 1 * 1 + 0`
-/
def evalAtom (e : Q($α)) : AtomM (Result (ExSum sα) e) := do
  let r ← (← read).evalAtom e
  have e' : Q($α) := r.expr
  let i ← addAtom e'
  let ve' := (ExBase.atom i (e := e')).toProd (ExProd.mkNat sℕ 1).2 |>.toSum
  pure ⟨_, ve', match r.proof? with
  | none => (q(atom_pf $e) : Expr)
  | some (p : Q($e = $e')) => (q(atom_pf' $p) : Expr)⟩

theorem add_congr (_ : a = a') (_ : b = b')
    (_ : a' + b' = c) : (a + b : R) = c := by subst_vars; rfl

theorem mul_congr (_ : a = a') (_ : b = b')
    (_ : a' * b' = c) : (a * b : R) = c := by subst_vars; rfl

theorem nsmul_congr (_ : (a : ℕ) = a') (_ : b = b')
    (_ : a' • b' = c) : (a • (b : R)) = c := by subst_vars; rfl

theorem pow_congr (_ : a = a') (_ : b = b')
    (_ : a' ^ b' = c) : (a ^ b : R) = c := by subst_vars; rfl

theorem neg_congr {R} [Ring R] {a a' b : R} (_ : a = a')
    (_ : -a' = b) : (-a : R) = b := by subst_vars; rfl

theorem sub_congr {R} [Ring R] {a a' b b' c : R} (_ : a = a') (_ : b = b')
    (_ : a' - b' = c) : (a - b : R) = c := by subst_vars; rfl

/-- A precomputed `Cache` for `ℕ`. -/
def Cache.nat : Cache q(ℕ) := { rα := none }

/--
Evaluates expression `e` of type `α` into a normalized representation as a polynomial.
This is the main driver of `ring`, which calls out to `evalAdd`, `evalMul` etc.
-/
partial def eval {u} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    (c : Cache α) (e : Q($α)) : AtomM (Result (ExSum sα) e) := do
  let els := do
    try evalCast sα (← derive e)
    catch _ => evalAtom sα e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα with
  | ``HAdd.hAdd, _ | ``Add.add, _ => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval sα c a
      let ⟨_, vb, pb⟩ ← eval sα c b
      let ⟨c, vc, p⟩ := evalAdd sα va vb
      pure ⟨c, vc, (q(add_congr $pa $pb $p) : Expr)⟩
    | _ => els
  | ``HMul.hMul, _ | ``Mul.mul, _ => match e with
    | ~q($a * $b) =>
      let ⟨_, va, pa⟩ ← eval sα c a
      let ⟨_, vb, pb⟩ ← eval sα c b
      let ⟨c, vc, p⟩ := evalMul sα va vb
      pure ⟨c, vc, (q(mul_congr $pa $pb $p) : Expr)⟩
    | _ => els
  | ``HSMul.hSMul, _ => match e with
    | ~q(($a : ℕ) • ($b : «$α»)) =>
      let ⟨_, va, pa⟩ ← eval sℕ .nat a
      let ⟨_, vb, pb⟩ ← eval sα c b
      let ⟨c, vc, p⟩ ← evalNSMul sα va vb
      pure ⟨c, vc, (q(nsmul_congr $pa $pb $p) : Expr)⟩
    | _ => els
  | ``HPow.hPow, _ | ``Pow.pow, _ => match e with
    | ~q($a ^ $b) =>
      let ⟨_, va, pa⟩ ← eval sα c a
      let ⟨_, vb, pb⟩ ← eval sℕ .nat b
      let ⟨c, vc, p⟩ := evalPow sα va vb
      pure ⟨c, vc, (q(pow_congr $pa $pb $p) : Expr)⟩
    | _ => els
  | ``Neg.neg, some rα => match e with
    | ~q(-$a) =>
      let ⟨_, va, pa⟩ ← eval sα c a
      let ⟨b, vb, p⟩ := evalNeg sα rα va
      pure ⟨b, vb, (q(neg_congr $pa $p) : Expr)⟩
  | ``HSub.hSub, some rα | ``Sub.sub, some rα => match e with
    | ~q($a - $b) => do
      let ⟨_, va, pa⟩ ← eval sα c a
      let ⟨_, vb, pb⟩ ← eval sα c b
      let ⟨c, vc, p⟩ := evalSub sα rα va vb
      pure ⟨c, vc, (q(sub_congr $pa $pb $p) : Expr)⟩
    | _ => els
  | _, _ => els

open Lean Parser.Tactic Elab Command Elab.Tactic Meta Qq

/-- Convert `undef` to `none` to make an `LOption` into an `Option`. -/
def _root_.Lean.LOption.toOption {α} : Lean.LOption α → Option α
  | .some a => some a
  | _ => none

theorem of_eq (_ : (a : R) = c) (_ : b = c) : a = b := by subst_vars; rfl

/--
This is a routine which is used to clean up the unsolved subgoal
of a failed `ring1` application. It is overridden in `Mathlib.Tactic.Ring.RingNF`
to apply the `ring_nf` simp set to the goal.
-/
initialize ringCleanupRef : IO.Ref (Expr → MetaM Expr) ← IO.mkRef pure

/-- Frontend of `ring1`: attempt to close a goal `g`, assuming it is an equation of semirings. -/
def proveEq (g : MVarId) : AtomM Unit := do
  let some (α, e₁, e₂) := (← instantiateMVars (← g.getType)).eq?
    | throwError "ring failed: not an equality"
  let .sort (.succ u) ← whnf (← inferType α) | throwError "not a type{indentExpr α}"
  have α : Q(Type u) := α
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let sα ← synthInstanceQ (q(CommSemiring $α) : Q(Type u))
  let c := { rα := (← trySynthInstanceQ (q(Ring $α) : Q(Type u))).toOption }
  profileitM Exception "ring" (← getOptions) do
    let ⟨a, va, pa⟩ ← eval sα c e₁
    let ⟨b, vb, pb⟩ ← eval sα c e₂
    unless va.eq vb do
      let g ← mkFreshExprMVar (← (← ringCleanupRef.get) q($a = $b))
      throwError "ring failed, ring expressions not equal\n{g.mvarId!}"
    let pb : Q($e₂ = $a) := pb
    g.assign q(of_eq $pa $pb)

/--
Tactic for solving equations of *commutative* (semi)rings,
allowing variables in the exponent.

* This version of `ring` fails if the target is not an equality.
* The variant `ring1!` will use a more aggressive reducibility setting
  to determine equality of atoms.
-/
elab (name := ring1) "ring1" tk:"!"? : tactic => liftMetaMAtMain fun g ↦ do
  AtomM.run (if tk.isSome then .default else .reducible) (proveEq g)

@[inherit_doc ring1] macro "ring1!" : tactic => `(tactic| ring1 !)
