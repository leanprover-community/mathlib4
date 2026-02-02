/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue, Anne Baanen
-/
module

public meta import Mathlib.Tactic.NormNum.Inv
public meta import Mathlib.Tactic.NormNum.Pow
public meta import Mathlib.Util.AtomM

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
That is: `a - a = 0 := by ring` solves the goal,
but `a / a := 1 by ring` doesn't.
Note that `0 / 0` is generally defined to be `0`,
so division cancelling out is not true in general.

Multiplication of powers can be simplified a little bit further:
`2 ^ n * 2 ^ n = 4 ^ n := by ring` could be implemented
in a similar way that `2 * a + 2 * a = 4 * a := by ring` already works.
This feature wasn't needed yet, so it's not implemented yet.

## Tags

ring, semiring, exponent, power
-/

@[expose] public meta section

assert_not_exists IsOrderedMonoid

namespace Mathlib.Tactic
namespace Ring.Common

open Mathlib.Meta Qq NormNum Lean.Meta AtomM

attribute [local instance] monadLiftOptionMetaM

open Lean (MetaM Expr mkRawNatLit)

/-- A shortcut instance for `CommSemiring ℕ` used by ring. -/
def instCommSemiringNat : CommSemiring ℕ := inferInstance

/--
A typed expression of type `CommSemiring ℕ` used when we are working on
ring subexpressions of type `ℕ`.
-/
def sℕ : Q(CommSemiring ℕ) := q(instCommSemiringNat)

/--
The data used by `ring` to represent coefficients. `e` is a raw rat cast.
-/
structure _root_.Mathlib.Tactic.Ring.BaseType {u : Lean.Level} {α : Q(Type u)}
    (sα : Q(CommSemiring $α)) (e : Q($α)) where
  /-- The value represented by `e`. Should not be zero. -/
  value : ℚ
  /-- If `value` is not an integer, then `hyp` should be a proof of `(value.den : α) ≠ 0`. -/
  hyp : Option Expr
deriving Inhabited

/-- The data used to represent coefficients in exponents. This is the same data that `ring` uses. -/
def btℕ (e : Q(ℕ)) : Type := Ring.BaseType sℕ q($e)

instance (e : Expr) : Inhabited <| btℕ e := ⟨⟨0, none⟩⟩

universe u v

/-!
## The ExNat types

The `Ex{Base,Prod,Sum}Nat` types are equivalent to `Ex{Base,Prod,Sum} btℕ sℕ`. `ExProdNat` is only
used to represent exponents in `ExProd`s. Before we added `BaseType` as a parameter, the `mul`
constructor of `ExProd` took the exponent as `ExProd sℕ q($e)` and `ExProdNat` did not exist.
Removing `ExProdNat` again would require passing `BaseType` as an argument to each constructor,
raising the universe level of `ExProd` from `Type` to `Type 1`, effectively making it noncomputable.

That is,

```
inductive ExProd : ∀ {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
    (sα : Q(CommSemiring $α)) (e : Q($α)), Type
  | const {u : Lean.Level} {α : Q(Type u)} {BaseType} {sα} {e : Q($α)} (value : BaseType e) :
      ExProd BaseType sα e
  | mul {u : Lean.Level} {α : Q(Type u)} {BaseType} {sα} {x : Q($α)} {e : Q(ℕ)} {b : Q($α)} :
    ExBase BaseType sα x → ExProd btℕ sℕ e → ExProd BaseType sα b →
      ExProd BaseType sα q($x ^ $e * $b)
```
would fail to compile because `ExProd` lives in `Type 1`. -/

mutual


/-- The base `e` of a normalized exponent expression in ℕ.
  Used to represent normalized natural number expressions in exponents.
  `ExBaseNat q($e)` is equivalent to `ExBase btℕ sℕ q($e)`, and one can cast between the two. -/
inductive ExBaseNat : (e : Q(ℕ)) → Type
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
  | atom {e} (id : ℕ) : ExBaseNat e
  /-- A sum of monomials. -/
  | sum {e} (_ : ExSumNat e) : ExBaseNat e

/-- A monomial, which is a product of powers of `ExBaseNat` expressions in ℕ,
  terminated by a (nonzero) constant coefficient.
  Used to represent normalized natural number expressions in exponents.
  `ExProdNat q($e)` is equivalent to `ExProd btℕ sℕ q($e)`, and one can cast between the two.
-/
inductive ExProdNat : (e : Q(ℕ)) → Type
  /-- A coefficient `value`, holding the data that `ring` uses to represent rational coefficients.
  In this case these happen to always be natural numbers. -/
  | const {e : Q(ℕ)} (value : btℕ e) : ExProdNat e
  /-- A product `x ^ e * b` is a monomial if `b` is a monomial. Here `x` is an `ExBaseNat`
  and `e` is an `ExProdNat` representing a monomial expression in `ℕ` (it is a monomial instead of
  a polynomial because we eagerly normalize `x ^ (a + b) = x ^ a * x ^ b`.) -/
  | mul {x : Q(ℕ)} {e : Q(ℕ)} {b : Q(ℕ)} :
    ExBaseNat x → ExProdNat e → ExProdNat b → ExProdNat q($x ^ $e * $b)

/-- A polynomial expression, which is a sum of monomials.
Used to represent normalized natural number expressions in exponents.
`ExProdNat q($e)` is equivalent to `ExProd btℕ sℕ q($e)`, and one can cast between the two. -/
inductive ExSumNat : (e : Q(ℕ)) → Type
  /-- Zero is a polynomial. `e` is the expression `0`. -/
  | zero : ExSumNat q(0)
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {a b : Q(ℕ)} : ExProdNat a → ExSumNat b → ExSumNat q($a + $b)
end


mutual

/-- The base `e` of a normalized exponent expression. -/
inductive ExBase {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
    (sα : Q(CommSemiring $α)) : (e : Q($α)) → Type
  /--
  An atomic expression `e` with id `id`.

  Atomic expressions are those which a `ring`-like tactic cannot parse any further.
  For instance, `a + (a % b)` has `a` and `(a % b)` as atoms.
  The `ring1` tactic does not normalize the subexpressions in atoms, but `ring_nf` does.

  Atoms in fact represent equivalence classes of expressions, modulo definitional equality.
  The field `index : ℕ` should be a unique number for each class,
  while `value : expr` contains a representative of this class.
  The function `resolve_atom` determines the appropriate atom for a given expression.
  -/
  | atom {e} (id : ℕ) : ExBase BaseType sα e
  /-- A sum of monomials. -/
  | sum {e} (_ : ExSum BaseType sα e) : ExBase BaseType sα e


/--
A monomial, which is a product of powers of `ExBase` expressions,
terminated by a (nonzero) constant coefficient.
-/
inductive ExProd {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
    (sα : Q(CommSemiring $α)) : (e : Q($α)) → Type
  /-- A coefficient `value`, which must not be `0`. `e` is a raw rat cast.
  If `value` is not an integer, then `hyp` should be a proof of `(value.den : α) ≠ 0`. -/
  | const {e : Q($α)} (value : BaseType e) : ExProd BaseType sα e
  /-- A product `x ^ e * b` is a monomial if `b` is a monomial. Here `x` is an `ExBase`
  and `e` is an `ExProdNat` representing a monomial expression in `ℕ` (it is a monomial instead of
  a polynomial because we eagerly normalize `x ^ (a + b) = x ^ a * x ^ b`.)
  -/
  | mul {x : Q($α)} {e : Q(ℕ)} {b : Q($α)} :
    ExBase BaseType sα x → ExProdNat e → ExProd BaseType sα b → ExProd BaseType sα q($x ^ $e * $b)

/-- A polynomial expression, which is a sum of monomials. -/
inductive ExSum {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
    (sα : Q(CommSemiring $α)) : (e : Q($α)) → Type
  /-- Zero is a polynomial. `e` is the expression `0`. -/
  | zero : ExSum BaseType sα q(0 : $α)
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {a b : Q($α)} :
    ExProd BaseType sα a → ExSum BaseType sα b → ExSum BaseType sα q($a + $b)
end

variable {u : Lean.Level}

/--
The result of evaluating an (unnormalized) expression `e` into the type family `E`
(typically one of `ExSum`, `ExProd`, `ExBase` or `BaseType`) is a (normalized) element `e'`
and a representation `E e'` for it, and a proof of `e = e'`.
-/
structure Result {α : Q(Type u)} (E : Q($α) → Type*) (e : Q($α)) where
  /-- The normalized result. -/
  expr : Q($α)
  /-- The data associated to the normalization. -/
  val : E expr
  /-- A proof that the original expression is equal to the normalized result. -/
  proof : Q($e = $expr)

instance {α : Q(Type u)} {E : Q($α) → Type} {e : Q($α)} [Inhabited (Σ e, E e)] :
    Inhabited (Result E e) :=
  let ⟨e', v⟩ : Σ e, E e := default; ⟨e', v, default⟩


/-- Defines how comparisons and binary equality are computed in the base type. These are seperated
from ringCompute because they can often be defined without using instance caches. -/
structure RingCompare {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
    (sα : Q(CommSemiring $α)) where
  /-- Returns whether two coefficients are equal -/
  eq (sα) : ∀ {x y : Q($α)}, BaseType x → BaseType y → Bool
  /-- Returns whether `x` is less than, equal to or greater than `y`. -/
  compare (sα) : ∀ {x y : Q($α)}, BaseType x → BaseType y → Ordering

whatsnew in
/-- Stores all of the normalization procedures on the coefficient type.

`ring` implements these using `norm_num`
`algebra` implements these using `ring` -/
structure RingCompute {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
  (sα : Q(CommSemiring $α)) extends RingCompare BaseType sα where
  /-- Evaluate the sum of two coefficents.
  If the result is zero returns a proof of this fact, which is used to remove zero terms. -/
  add (sα) : ∀ x y : Q($α), BaseType x → BaseType y →
    MetaM ((Result BaseType q($x + $y)) × (Option Q(IsNat ($x + $y) 0)))
  /-- Evaluate the product of two coefficents. -/
  mul (sα) : ∀ x y : Q($α), BaseType x → BaseType y → MetaM (Result BaseType q($x * $y))
  /-- Given a ring `β` with a scalar multiplication action on `α` and a `x : β`, cast `x` to `α`
  such that the scalar multiplication turns in to normal multiplication. Typically one can think of
  `α` as being an algebra over `β`, but this file does not know about `Algebra`s. -/
  cast  (sα) : ∀ (v : Lean.Level) (β : Q(Type v)) (sβ : Q(CommSemiring $β))
      (_ : Q(HSMul $β $α $α)) (x : Q($β)),
      (AtomM <| Result (ExSum (Ring.BaseType sβ) q($sβ)) q($x)) →
    AtomM (Σ y : Q($α), ExSum BaseType sα q($y) × Q(∀ a : $α, $x • a = $y * a))
  /-- Evaluate the negation of a coefficient. -/
  neg (sα) : ∀ x : Q($α), (rα : Q(CommRing $α)) → BaseType x → MetaM (Result BaseType q(-$x))
  /-- Raise a coefficient to some natural power.
  The exponent may not be a natural literal. If the tactic can only raise coefficients to the power
  of a literal (e.g. `ring`), it should check for this and return `none` otherwise. -/
  pow (sα) : ∀ x : Q($α), BaseType x → (b : Q(ℕ)) → (vb : ExProdNat q($b)) →
    OptionT MetaM (Result BaseType q($x ^ $b))
  /-- Evaluate the inverse of a coefficient. -/
  inv : ∀ {x : Q($α)}, (czα : Option Q(CharZero $α)) → (fα : Q(Semifield $α)) → BaseType x →
    AtomM (Option <| Result BaseType q($x⁻¹))
  /-- Evaluate an expression as a potential coefficient. -/
  derive (sα) : ∀ x : Q($α), MetaM (Result (ExSum BaseType sα) q($x))
  /-- Decides whether a coefficient is 1 and returns a proof if so. -/
  isOne (sα) : ∀ {x : Q($α)}, BaseType x → Option Q(NormNum.IsNat $x 1)
  /-- The number 1 represented as a BaseType. -/
  one (sα) : Result BaseType q((nat_lit 1).rawCast)

instance {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
    (sα : Q(CommSemiring $α)) : Coe (RingCompute BaseType sα) (RingCompare BaseType sα) where
  coe x := x.toRingCompare

instance : Inhabited (Σ e, (ExBaseNat) e) := ⟨default, .atom 0⟩
instance : Inhabited (Σ e, (ExSumNat) e) := ⟨_, .zero⟩
instance : Inhabited (Σ e, (ExProdNat) e) := ⟨default, .const default⟩

variable {u : Lean.Level} {α : Q(Type u)} {bt : Q($α) → Type} {sα : Q(CommSemiring $α)}
   [∀ e, Inhabited (bt e)]

instance : Inhabited (Σ e, (ExBase bt sα) e) := ⟨default, .atom 0⟩
instance : Inhabited (Σ e, (ExSum bt sα) e) := ⟨_, .zero⟩
instance : Inhabited (Σ e, (ExProd bt sα) e) := ⟨default, .const default⟩

variable (rc : RingCompute bt sα) (rcℕ : RingCompute btℕ sℕ)

mutual

/-- Cast `ExBaseNat` to `ExBase btℕ sℕ`. -/
partial def ExBaseNat.toExBase (e : Q(ℕ)) : ExBaseNat e → Σ e', ExBase btℕ sℕ e' := fun
  | .atom id => ⟨_, .atom (e := e) id⟩
  | .sum v => ⟨_, .sum v.toExSum.2⟩

/-- Cast `ExProdNat` to `ExProd btℕ sℕ`. -/
partial def ExProdNat.toExProd (e : Q(ℕ)) : ExProdNat e → Σ e', ExProd btℕ sℕ e' := fun
  | .const value => ⟨_, .const value⟩
  | .mul vx ve vt => ⟨_, .mul vx.toExBase.2 ve vt.toExProd.2⟩

/-- Cast `ExSumNat` to `ExSum btℕ sℕ`. -/
partial def ExSumNat.toExSum (e : Q(ℕ)) : ExSumNat e → Σ e', ExSum btℕ sℕ e' := fun
  | .zero => ⟨_, .zero (BaseType := btℕ) (sα := sℕ)⟩
  | .add va vb => ⟨_, .add va.toExProd.2 vb.toExSum.2⟩

end

mutual

/-- Cast `ExBase btℕ sℕ` to `ExBaseNat`. -/
partial def ExBase.toExBaseNat (e : Q(ℕ)) : ExBase btℕ sℕ e → Σ e', ExBaseNat e' := fun
  | .atom id => ⟨_, .atom (e := e) id⟩
  | .sum v => ⟨_, .sum v.toExSumNat.2⟩

/-- Cast `ExProd btℕ sℕ` to `ExProdNat`. -/
partial def ExProd.toExProdNat (e : Q(ℕ)) : ExProd btℕ sℕ e → Σ e', ExProdNat e' := fun
  | .const value => ⟨_, .const value⟩
  | .mul vx ve vt => ⟨_, .mul vx.toExBaseNat.2 ve vt.toExProdNat.2⟩

/-- Cast `ExSum btℕ sℕ` to `ExSumNat`. -/
partial def ExSum.toExSumNat (e : Q(ℕ)) : ExSum btℕ sℕ e → Σ e', ExSumNat e' := fun
  | .zero => ⟨_, .zero⟩
  | .add va vb => ⟨_, .add va.toExProdNat.2 vb.toExSumNat.2⟩

end

section

/-- Embed an exponent (an `ExBase, ExProd` pair) as an `ExProd` by multiplying by 1. -/
def ExBase.toProd
    {a : Q($α)} {b : Q(ℕ)}
    (va : ExBase bt sα a) (vb : ExProdNat b) :
    Result (ExProd bt sα) q($a ^ $b * (nat_lit 1).rawCast) :=
      let ⟨_, one, pf⟩ := rc.one
      ⟨_, .mul va vb (.const  (one)),
        (q(by rw [← $pf])) ⟩

/-- Embed `ExProd` in `ExSum` by adding 0. -/
def ExProd.toSum {e : Q($α)} (v : ExProd bt sα e) : ExSum bt sα q($e + 0) :=
  .add v .zero



-- Partial because the termination checker failed
mutual

variable (rcℕ : RingCompare btℕ sℕ)

/-- Equality test for expressions. This is not a `BEq` instance because it is heterogeneous. -/
partial def ExBase.eq
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} (rc : RingCompare bt sα)
    {a b : Q($α)} :
    ExBase bt sα a → ExBase bt sα b → Bool
  | .atom i, .atom j => i == j
  | .sum a, .sum b => a.eq rc b
  | _, _ => false

@[inherit_doc ExBase.eq]
partial def ExProd.eq
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} (rc : RingCompare bt sα)
    {a b : Q($α)} :
    ExProd bt sα a → ExProd bt sα b → Bool
  | .const i, .const j => rc.eq i j
  | .mul a₁ a₂ a₃, .mul b₁ b₂ b₃ => a₁.eq rc b₁ && a₂.toExProd.2.eq rcℕ b₂.toExProd.2 && a₃.eq rc b₃
  | _, _ => false

@[inherit_doc ExBase.eq]
partial def ExSum.eq
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} (rc : RingCompare bt sα)
    {a b : Q($α)} :
    ExSum bt sα a → ExSum bt sα b → Bool
  | .zero, .zero => true
  | .add a₁ a₂, .add b₁ b₂ => a₁.eq rc b₁ && a₂.eq rc b₂
  | _, _ => false
end

mutual

variable (rcℕ : RingCompute btℕ sℕ)

/--
A total order on normalized expressions.
This is not an `Ord` instance because it is heterogeneous.
-/
partial def ExBase.cmp {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)}
    (rc : RingCompare bt sα) {a b : Q($α)} :
    ExBase bt sα a → ExBase bt sα b → Ordering
  | .atom i, .atom j => compare i j
  | .sum a, .sum b => a.cmp rc b
  | .atom .., .sum .. => .lt
  | .sum .., .atom .. => .gt

@[inherit_doc ExBase.cmp]
partial def ExProd.cmp {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)}
    (rc : RingCompare bt sα) {a b : Q($α)} :
    ExProd bt sα a → ExProd bt sα b → Ordering
  | .const i, .const j => rc.compare i j
  | .mul a₁ a₂ a₃, .mul b₁ b₂ b₃ =>
    (a₁.cmp rc b₁).then (a₂.toExProd.2.cmp rcℕ b₂.toExProd.2) |>.then (a₃.cmp rc b₃)
  | .const _, .mul .. => .lt
  | .mul .., .const _ => .gt

@[inherit_doc ExBase.cmp]
partial def ExSum.cmp {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)}
    (rc : RingCompare bt sα) {a b : Q($α)} :
    ExSum bt sα a → ExSum bt sα b → Ordering
  | .zero, .zero => .eq
  | .add a₁ a₂, .add b₁ b₂ => (a₁.cmp rc b₁).then (a₂.cmp rc b₂)
  | .zero, .add .. => .lt
  | .add .., .zero => .gt
end

variable {R : Type*} [CommSemiring R]

section

/-- Get the leading coefficient of an `ExProd`. -/
def ExProd.coeff {e : Q($α)} :
    have : Inhabited <| Σ c, bt c := ⟨default, default⟩
  ExProd bt sα e → Σ c, bt c
  | .const q => ⟨_, q⟩
  | .mul _ _ v => v.coeff
end

variable (bt) (sα) in
/--
Two monomials are said to "overlap" if they differ by a constant factor, in which case the
constants just add. When this happens, the constant may be either zero (if the monomials cancel)
or nonzero (if they add up); the zero case is handled specially.
-/
inductive Overlap (e : Q($α)) : Type where
  /-- The expression `e` (the sum of monomials) is equal to `0`. -/
  | zero (_ : Q(IsNat $e (nat_lit 0)))
  /-- The expression `e` (the sum of monomials) is equal to another monomial
  (with nonzero leading coefficient). -/
  | nonzero (_ : Result (ExProd bt sα) e)

variable {a a' a₁ a₂ a₃ b b' b₁ b₂ b₃ c c₁ c₂ : R}

/-! ### Addition -/

theorem add_overlap_pf (x : R) (e) (pq_pf : a + b = c) :
    x ^ e * a + x ^ e * b = x ^ e * c := by subst_vars; simp [mul_add]

theorem add_overlap_pf_zero (x : R) (e) :
    IsNat (a + b) (nat_lit 0) → IsNat (x ^ e * a + x ^ e * b) (nat_lit 0)
  | ⟨h⟩ => ⟨by simp [h, ← mul_add]⟩

-- TODO: decide if this is a good idea globally in
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.60MonadLift.20Option.20.28OptionT.20m.29.60/near/469097834
private local instance {m} [Pure m] : MonadLift Option (OptionT m) where
  monadLift f := .mk <| pure f

/--
Given monomials `va, vb`, attempts to add them together to get another monomial.
If the monomials are not compatible, returns `none`.
For example, `xy + 2xy = 3xy` is a `.nonzero` overlap, while `xy + xz` returns `none`
and `xy + -xy = 0` is a `.zero` overlap.
-/
def evalAddOverlap {a b : Q($α)} (va : ExProd bt sα a) (vb : ExProd bt sα b) :
    OptionT MetaM (Overlap bt sα q($a + $b)) := do
  Lean.Core.checkSystem decl_name%.toString
  match va, vb with
  | .const za, .const zb => do
    let ⟨⟨_, zc, pf⟩, isZero⟩ ← rc.add (u := u) (sα := sα) _ _ za zb
    match isZero with
    | .some pf => pure <| .zero q($pf)
    | .none =>
      assumeInstancesCommute
      pure <| .nonzero ⟨_, .const zc, q($pf)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, .mul (x := b₁) (e := b₂) vb₁ vb₂ vb₃ => do
    guard (va₁.eq rcℕ rc vb₁ && va₂.toExProd.2.eq rcℕ rcℕ vb₂.toExProd.2)
    have : $a₁ =Q $b₁ := ⟨⟩; have : $a₂ =Q $b₂ := ⟨⟩
    match ← evalAddOverlap va₃ vb₃ with
    | .zero p => pure <| .zero q(add_overlap_pf_zero $a₁ $a₂ $p)
    | .nonzero ⟨_, vc, p⟩ =>
      pure <| .nonzero ⟨_, .mul va₁ va₂ vc, q(add_overlap_pf $a₁ $a₂ $p)⟩
  | _, _ => OptionT.fail

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

* `0 + b = b`
* `a + 0 = a`
* `a * x + a * y = a * (x + y)` (for `x`, `y` coefficients; uses `evalAddOverlap`)
* `(a₁ + a₂) + (b₁ + b₂) = a₁ + (a₂ + (b₁ + b₂))` (if `a₁.lt b₁`)
* `(a₁ + a₂) + (b₁ + b₂) = b₁ + ((a₁ + a₂) + b₂)` (if not `a₁.lt b₁`)
-/
partial def evalAdd {a b : Q($α)} (va : ExSum bt sα a) (vb : ExSum bt sα b) :
    MetaM <| Result (ExSum bt sα) q($a + $b) := do
  Lean.Core.checkSystem decl_name%.toString
  match va, vb with
  | .zero, vb => return ⟨b, vb, q(add_pf_zero_add $b)⟩
  | va, .zero => return ⟨a, va, q(add_pf_add_zero $a)⟩
  | .add (a := a₁) (b := _a₂) va₁ va₂, .add (a := b₁) (b := _b₂) vb₁ vb₂ =>
    have va := .add va₁ va₂; have vb := .add vb₁ vb₂ -- FIXME: why does `va@(...)` fail?
    match ← (evalAddOverlap rc rcℕ va₁ vb₁).run with
    | some (.nonzero ⟨_, vc₁, pc₁⟩) =>
      let ⟨_, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
      return ⟨_, .add vc₁ vc₂, q(add_pf_add_overlap $pc₁ $pc₂)⟩
    | some (.zero pc₁) =>
      let ⟨c₂, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
      return ⟨c₂, vc₂, q(add_pf_add_overlap_zero $pc₁ $pc₂)⟩
    | none =>
      if let .lt := va₁.cmp rcℕ rc vb₁ then
        let ⟨_c, vc, pc⟩ ← evalAdd va₂ vb
        return ⟨_, .add va₁ vc, q(add_pf_add_lt $a₁ $pc)⟩
      else
        let ⟨_c, vc, pc⟩ ← evalAdd va vb₂
        return ⟨_, .add vb₁ vc, q(add_pf_add_gt $b₁ $pc)⟩

/-! ### Multiplication -/

theorem one_mul (a : R) : (nat_lit 1).rawCast * a = a := by simp [Nat.rawCast]

theorem mul_one (a : R) : a * (nat_lit 1).rawCast = a := by simp [Nat.rawCast]

theorem mul_pf_left (a₁ : R) (a₂) (_ : a₃ * b = c) :
    (a₁ ^ a₂ * a₃ : R) * b = a₁ ^ a₂ * c := by
  subst_vars; rw [mul_assoc]

theorem mul_pf_right (b₁ : R) (b₂) (_ : a * b₃ = c) :
    a * (b₁ ^ b₂ * b₃) = b₁ ^ b₂ * c := by
  subst_vars; rw [mul_left_comm]

theorem mul_pp_pf_overlap {ea eb e : ℕ} (x : R) (_ : ea + eb = e) (_ : a₂ * b₂ = c) :
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
partial def evalMulProd {a b : Q($α)} (va : ExProd bt sα a) (vb : ExProd bt sα b) :
    MetaM <| Result (ExProd bt sα) q($a * $b) := do
  Lean.Core.checkSystem decl_name%.toString
  match va, vb with
  | .const za, .const zb =>
    let ⟨_, zc, pf⟩ ← rc.mul _ _ za zb
    assumeInstancesCommute
    return ⟨_, .const zc, q($pf)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, vb@(.const _) =>
    let ⟨_, vc, pc⟩ ← evalMulProd va₃ vb
    return ⟨_, .mul va₁ va₂ vc, q(mul_pf_left $a₁ $a₂ $pc)⟩
  | va@(.const _), .mul (x := b₁) (e := b₂) vb₁ vb₂ vb₃ =>
    let ⟨_, vc, pc⟩ ← evalMulProd va vb₃
    return ⟨_, .mul vb₁ vb₂ vc, q(mul_pf_right $b₁ $b₂ $pc)⟩
  | .mul (x := xa) (e := ea) vxa vea va₂, .mul (x := xb) (e := eb) vxb veb vb₂ =>
    have va := .mul vxa vea va₂; have vb := .mul vxb veb vb₂ -- FIXME: why does `va@(...)` fail?
    let ⟨ea', vea'⟩ := vea.toExProd
    let ⟨eb', veb'⟩ := veb.toExProd
    if vxa.eq rcℕ rc vxb then
      have : $xa =Q $xb := ⟨⟩
      if let some (.nonzero ⟨ec', vec', pec'⟩) ← (evalAddOverlap rcℕ rcℕ vea' veb').run then
        let ⟨_, vc, pc⟩ ← evalMulProd va₂ vb₂
        let ⟨ec, vec⟩ := vec'.toExProdNat
        have : $ea =Q $ea' := ⟨⟩
        have : $eb =Q $eb' := ⟨⟩
        have : $ec =Q $ec' := ⟨⟩
        return ⟨_, .mul vxa vec vc, q(mul_pp_pf_overlap $xa $pec' $pc)⟩
    if let .lt := (vxa.cmp rcℕ rc vxb).then (vea'.cmp rcℕ rcℕ veb') then
      let ⟨_, vc, pc⟩ ← evalMulProd va₂ vb
      return ⟨_, .mul vxa vea vc, q(mul_pf_left $xa $ea $pc)⟩
    else
      let ⟨_, vc, pc⟩ ← evalMulProd va vb₂
      return ⟨_, .mul vxb veb vc, q(mul_pf_right $xb $eb $pc)⟩

theorem mul_zero (a : R) : a * 0 = 0 := by simp

theorem mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : c₁ + 0 + c₂ = d) :
    a * (b₁ + b₂) = d := by
  subst_vars; simp [_root_.mul_add]

/-- Multiplies a monomial `va` to a polynomial `vb` to get a normalized result polynomial.

* `a * 0 = 0`
* `a * (b₁ + b₂) = (a * b₁) + (a * b₂)`
-/
def evalMul₁ {a b : Q($α)} (va : ExProd bt sα a) (vb : ExSum bt sα b) :
    MetaM <| Result (ExSum bt sα) q($a * $b) := do
  match vb with
  | .zero => return ⟨_, .zero, q(mul_zero $a)⟩
  | .add vb₁ vb₂ =>
    let ⟨_, vc₁, pc₁⟩ ← evalMulProd rc rcℕ va vb₁
    let ⟨_, vc₂, pc₂⟩ ← evalMul₁ va vb₂
    let ⟨_, vd, pd⟩ ← evalAdd rc rcℕ vc₁.toSum vc₂
    return ⟨_, vd, q(mul_add $pc₁ $pc₂ $pd)⟩

theorem zero_mul (b : R) : 0 * b = 0 := by simp

theorem add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : c₁ + c₂ = d) :
    (a₁ + a₂) * b = d := by subst_vars; simp [_root_.add_mul]

/-- Multiplies two polynomials `va, vb` together to get a normalized result polynomial.

* `0 * b = 0`
* `(a₁ + a₂) * b = (a₁ * b) + (a₂ * b)`
-/
def evalMul {a b : Q($α)} (va : ExSum bt sα a) (vb : ExSum bt sα b) :
    MetaM <| Result (ExSum bt sα) q($a * $b) := do
  match va with
  | .zero => return ⟨_, .zero, q(zero_mul $b)⟩
  | .add va₁ va₂ =>
    let ⟨_, vc₁, pc₁⟩ ← evalMul₁ rc rcℕ va₁ vb
    let ⟨_, vc₂, pc₂⟩ ← evalMul va₂ vb
    let ⟨_, vd, pd⟩ ← evalAdd rc rcℕ vc₁ vc₂
    return ⟨_, vd, q(add_mul $pc₁ $pc₂ $pd)⟩

/-! ### Negation -/

theorem neg_one_mul {R} [CommRing R] {a b : R} (_ : (-1 : R) * a = b) :
    -a = b := by subst_vars; simp

theorem neg_mul {R} [CommRing R] (a₁ : R) (a₂) {a₃ b : R}
    (_ : -a₃ = b) : -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b := by subst_vars; simp

/-- Negates a monomial `va` to get another monomial.

* `-c = (-c)` (for `c` coefficient)
* `-(a₁ * a₂) = a₁ * -a₂`
-/
def evalNegProd {a : Q($α)} (rα : Q(CommRing $α)) (va : ExProd bt sα a) :
    MetaM <| Result (ExProd bt sα) q(-$a) := do
  Lean.Core.checkSystem decl_name%.toString
  match va with
  | .const za =>
    let ⟨b, zb, pb⟩ ← rc.neg _ q($rα) za
    return ⟨b, .const zb,  q($pb)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃ =>
    let ⟨_, vb, pb⟩ ← evalNegProd rα va₃
    assumeInstancesCommute
    return ⟨_, .mul va₁ va₂ vb, q(neg_mul $a₁ $a₂ $pb)⟩

theorem neg_zero {R} [CommRing R] : -(0 : R) = 0 := by simp

theorem neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R}
    (_ : -a₁ = b₁) (_ : -a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂ := by
  subst_vars; simp [add_comm]

/-- Negates a polynomial `va` to get another polynomial.

* `-0 = 0` (for `c` coefficient)
* `-(a₁ + a₂) = -a₁ + -a₂`
-/
def evalNeg {a : Q($α)} (rα : Q(CommRing $α)) (va : ExSum bt sα a) :
    MetaM <| Result (ExSum bt sα) q(-$a) := do
  assumeInstancesCommute
  match va with
  | .zero => return ⟨_, .zero, q(neg_zero (R := $α))⟩
  | .add va₁ va₂ =>
    let ⟨_, vb₁, pb₁⟩ ← evalNegProd rc rα va₁
    let ⟨_, vb₂, pb₂⟩ ← evalNeg rα va₂
    return ⟨_, .add vb₁ vb₂, q(neg_add $pb₁ $pb₂)⟩

/-! ### Subtraction -/

theorem sub_pf {R} [CommRing R] {a b c d : R}
    (_ : -b = c) (_ : a + c = d) : a - b = d := by subst_vars; simp [sub_eq_add_neg]

/-- Subtracts two polynomials `va, vb` to get a normalized result polynomial.

* `a - b = a + -b`
-/
def evalSub {a b : Q($α)}
    (rα : Q(CommRing $α)) (va : ExSum bt sα a) (vb : ExSum bt sα b) :
    MetaM <| Result (ExSum bt sα) q($a - $b) := do
  let ⟨_c, vc, pc⟩ ← evalNeg rc rα vb
  let ⟨d, vd, pd⟩ ← evalAdd rc rcℕ va vc
  assumeInstancesCommute
  return ⟨d, vd, q(sub_pf $pc $pd)⟩

/-! ### Exponentiation -/

theorem pow_prod_atom (a : R) (b) {e : R} (h : (a + 0) ^ b * (nat_lit 1).rawCast = e) :
    a ^ b = e := by
  simp [← h]

/--
The fallback case for exponentiating polynomials is to use `ExBase.toProd` to just build an
exponent expression. (This has a slightly different normalization than `evalPowAtom` because
the input types are different.)

* `x ^ e = (x + 0) ^ e * 1`
-/
def evalPowProdAtom {a : Q($α)} {b : Q(ℕ)} (va : ExProd bt sα a) (vb : ExProdNat b) :
    Result (ExProd bt sα) q($a ^ $b) :=
    let ⟨_, vc, pc⟩ := (ExBase.sum va.toSum).toProd rc vb
  ⟨_, vc, q(pow_prod_atom $a $b $pc)⟩

theorem pow_atom (a : R) (b) {e : R} (h : a ^ b * (nat_lit 1).rawCast = e) :
    a ^ b = e + 0 := by
  simp [← h]

/--
The fallback case for exponentiating polynomials is to use `ExBase.toProd` to just build an
exponent expression.

* `x ^ e = x ^ e * 1 + 0`
-/
def evalPowAtom {a : Q($α)} {b : Q(ℕ)} (va : ExBase bt sα a) (vb : ExProdNat b) :
    Result (ExSum bt sα) q($a ^ $b) :=
  let ⟨_, vc, pc⟩ := (va.toProd rc vb)
  ⟨_, vc.toSum, q(pow_atom $a $b $pc)⟩

theorem const_pos (n : ℕ) (h : Nat.ble 1 n = true) : 0 < (n.rawCast : ℕ) := Nat.le_of_ble_eq_true h

theorem mul_exp_pos {a₁ a₂ : ℕ} (n) (h₁ : 0 < a₁) (h₂ : 0 < a₂) : 0 < a₁ ^ n * a₂ :=
  Nat.mul_pos (Nat.pow_pos h₁) h₂

theorem add_pos_left {a₁ : ℕ} (a₂) (h : 0 < a₁) : 0 < a₁ + a₂ :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

theorem add_pos_right {a₂ : ℕ} (a₁) (h : 0 < a₂) : 0 < a₁ + a₂ :=
  Nat.lt_of_lt_of_le h (Nat.le_add_left ..)

mutual -- partial only to speed up compilation

/-- Attempts to prove that a polynomial expression in `ℕ` is positive.

* Atoms are not (necessarily) positive
* Sums defer to `ExSum.evalPos`
-/
partial def ExBaseNat.evalPos {a : Q(ℕ)} (va : ExBaseNat a) : Option Q(0 < $a) :=
  match va with
  | .atom _ => none
  | .sum va => va.evalPos

/-- Attempts to prove that a monomial expression in `ℕ` is positive.

* `0 < c` (where `c` is a numeral) is true by the normalization invariant (`c` is not zero)
* `0 < x ^ e * b` if `0 < x` and `0 < b`
-/
partial def ExProdNat.evalPos {a : Q(ℕ)} (va : ExProdNat a) : Option Q(0 < $a) :=
  match va with
  | .const _ =>
    -- it must be positive because it is a nonzero nat literal
    have lit : Q(ℕ) := a.appArg!
    haveI : $a =Q Nat.rawCast $lit := ⟨⟩
    haveI p : Nat.ble 1 $lit =Q true := ⟨⟩
    some q(const_pos $lit $p)
  | .mul (e := ea₁) vxa₁ _ va₂ => do
    let pa₁ ← vxa₁.evalPos
    let pa₂ ← va₂.evalPos
    some q(mul_exp_pos $ea₁ $pa₁ $pa₂)

/-- Attempts to prove that a polynomial expression in `ℕ` is positive.

* `0 < 0` fails
* `0 < a + b` if `0 < a` or `0 < b`
-/
partial def ExSumNat.evalPos {a : Q(ℕ)} (va : ExSumNat a) : Option Q(0 < $a) :=
  match va with
  | .zero => none
  | .add (a := a₁) (b := a₂) va₁ va₂ => do
    match va₁.evalPos with
    | some p => some q(add_pos_left $a₂ $p)
    | none => let p ← va₂.evalPos; some q(add_pos_right $a₁ $p)

end

theorem pow_one (a : R) : a ^ nat_lit 1 = a := by simp

theorem pow_bit0 {k : ℕ} (_ : (a : R) ^ k = b) (_ : b * b = c) :
    a ^ (Nat.mul (nat_lit 2) k) = c := by
  subst_vars; simp [Nat.succ_mul, pow_add]

theorem pow_bit1 {k : ℕ} {d : R} (_ : (a : R) ^ k = b) (_ : b * b = c) (_ : c * a = d) :
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
partial def evalPowNat {a : Q($α)} (va : ExSum bt sα a) (n : Q(ℕ)) :
    MetaM <| Result (ExSum bt sα) q($a ^ $n) := do
  let nn := n.natLit!
  if nn = 1 then
    have : $n =Q 1 := ⟨⟩
    return ⟨_, va, q(pow_one $a)⟩
  else
    let nm := nn >>> 1
    have m : Q(ℕ) := mkRawNatLit nm
    if nn &&& 1 = 0 then
      have : $n =Q 2 * $m := ⟨⟩
      let ⟨_, vb, pb⟩ ← evalPowNat va m
      let ⟨_, vc, pc⟩ ← evalMul rc rcℕ vb vb
      return ⟨_, vc, q(pow_bit0 $pb $pc)⟩
    else
      have : $n =Q 2 * $m + 1 := ⟨⟩
      let ⟨_, vb, pb⟩ ← evalPowNat va m
      let ⟨_, vc, pc⟩ ← evalMul rc rcℕ vb vb
      let ⟨_, vd, pd⟩ ← evalMul rc rcℕ vc va
      return ⟨_, vd, q(pow_bit1 $pb $pc $pd)⟩

theorem one_pow {a : R} (b : ℕ) (ha : IsNat a 1) : a ^ b = a := by
  simp [ha.out]

theorem mul_pow {ea₁ b c₁ : ℕ} {xa₁ : R}
    (_ : ea₁ * b = c₁) (_ : a₂ ^ b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂ := by
  subst_vars; simp [_root_.mul_pow, pow_mul]

-- needed to lift from `OptionT CoreM` to `OptionT MetaM`
private local instance {m m'} [Monad m] [Monad m'] [MonadLiftT m m'] :
    MonadLiftT (OptionT m) (OptionT m') where
  monadLift x := OptionT.mk x.run

/-- There are several special cases when exponentiating monomials:

* `1 ^ n = 1`
* `x ^ y = (x ^ y)` when `x` and `y` are constants
* `(a * b) ^ e = a ^ e * b ^ e`

In all other cases we use `evalPowProdAtom`.
-/
def evalPowProd {a : Q($α)} {b : Q(ℕ)} (va : ExProd bt sα a) (vb : ExProdNat b) :
    MetaM <| Result (ExProd bt sα) q($a ^ $b) := do
  Lean.Core.checkSystem decl_name%.toString
  let res : OptionT MetaM (Result (ExProd bt sα) q($a ^ $b)) := do
    match va with
    | va@(.const za) =>
      match rc.isOne za with
      | .some pf =>
        return ⟨_, va, q(one_pow $b $pf)⟩
      | .none =>
        let ⟨_, zc, pc⟩ ← rc.pow _ za _ vb
        return ⟨_, .const zc, q($pc)⟩
    | .mul vxa₁ (e := ea₁) vea₁ va₂ =>
      let ⟨ea₁', vea₁'⟩ := vea₁.toExProd
      let ⟨b', vb'⟩ := vb.toExProd
      let ⟨c₁, vc₁, pc₁⟩ ← evalMulProd rcℕ rcℕ vea₁' vb'
      let ⟨c₁', vc₁'⟩ := vc₁.toExProdNat
      let ⟨_, vc₂, pc₂⟩ ← evalPowProd va₂ vb
      have : $c₁ =Q $c₁' := ⟨⟩
      have : $b =Q $b' := ⟨⟩
      have : $ea₁ =Q $ea₁' := ⟨⟩
      return ⟨_, .mul vxa₁ vc₁' vc₂, q(mul_pow $pc₁ $pc₂)⟩
  return (← res.run).getD (evalPowProdAtom rc va vb)

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
  ve' : ExProdNat e'
  /-- The proof that `e` splits into the coefficient `k` and the monic monomial `e'`. -/
  p : Q($e = $e' * $k)

theorem coeff_one (k : ℕ) {e : ℕ} (h : (nat_lit 1).rawCast = e) :
  k.rawCast = e * k := by simp [← h]

theorem coeff_mul {a₃ c₂ k : ℕ}
    (a₁ a₂ : ℕ) (_ : a₃ = c₂ * k) : a₁ ^ a₂ * a₃ = (a₁ ^ a₂ * c₂) * k := by
  subst_vars; rw [mul_assoc]

/-- Given a monomial expression `va`, splits off the leading coefficient `k` and the remainder
`e'`, stored in the `ExtractCoeff` structure.

* `c = 1 * c` (if `c` is a constant)
* `a * b = (a * b') * k` if `b = b' * k`
-/
def extractCoeff {a : Q(ℕ)} (va : ExProdNat a) : ExtractCoeff a :=
  match va with
  | .const _ => Id.run do
    have k : Q(ℕ) := a.appArg!
    have : $a =Q Nat.rawCast $k := ⟨⟩
    assumeInstancesCommute
    let ⟨_, one, pf⟩ := rcℕ.one
    return ⟨k, _, .const (one), q(coeff_one $k $pf)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃ =>
    let ⟨k, _, vc, pc⟩ := extractCoeff va₃
    ⟨k, _, .mul va₁ va₂ vc, q(coeff_mul $a₁ $a₂ $pc)⟩
termination_by structural a

theorem pow_one_cast (a : R) : a ^ (nat_lit 1).rawCast = a := by simp

theorem pow_one_cast_of_isNat (a : R) (b : ℕ) (hb : IsNat b 1) :
    a ^ b = a := by simp [hb.out]

theorem zero_pow {b : ℕ} (_ : 0 < b) : (0 : R) ^ b = 0 := match b with | b+1 => by simp [pow_succ]

theorem single_pow {b : ℕ} (_ : (a : R) ^ b = c) : (a + 0) ^ b = c + 0 := by
  simp [*]

theorem pow_nat {b c k : ℕ} {d e : R} (_ : b = c * k) (_ : a ^ c = d) (_ : d ^ k = e) :
    (a : R) ^ b = e := by
  subst_vars; simp [pow_mul]

/-- Exponentiates a polynomial `va` by a monomial `vb`, including several special cases.

* `a ^ 1 = a`
* `0 ^ e = 0` if `0 < e`
* `(a + 0) ^ b = a ^ b` computed using `evalPowProd`
* `a ^ b = (a ^ b') ^ k` if `b = b' * k` and `k > 1`

Otherwise `a ^ b` is just encoded as `a ^ b * 1 + 0` using `evalPowAtom`.
-/
partial def evalPow₁ {a : Q($α)} {b : Q(ℕ)} (va : ExSum bt sα a) (vb : ExProdNat b) :
    MetaM <| Result (ExSum bt sα) q($a ^ $b) := do
  let NotPowOne : MetaM <| Result (ExSum bt sα) q($a ^ $b) := do
    match va with
    | .zero => match vb.evalPos with
      | some p => return ⟨_, .zero, q(zero_pow (R := $α) $p)⟩
      | none => return evalPowAtom rc (.sum .zero) vb
    | ExSum.add va .zero => -- TODO: using `.add` here takes a while to compile?
      let ⟨_, vc, pc⟩ ← evalPowProd rc rcℕ va vb
      return ⟨_, vc.toSum, q(single_pow $pc)⟩
    | va =>
      -- FIXME: condition used to be k.coeff > 1. Should go back to something like this.
      let ⟨k, _, vc, pc⟩ := extractCoeff rcℕ vb
      if k.natLit! > 1 then
        let ⟨_, vd, pd⟩ ← evalPow₁ va vc
        let ⟨_, ve, pe⟩ ← evalPowNat rc rcℕ vd k
        return ⟨_, ve, q(pow_nat $pc $pd $pe)⟩
      else
        return evalPowAtom rc (.sum va) vb
  match vb with
  | .const zb =>
    match rcℕ.isOne zb with
    | .some pf =>
      assumeInstancesCommute
      return ⟨_, va, q(pow_one_cast_of_isNat $a _ $pf)⟩
    | .none => NotPowOne
  | _ =>
    NotPowOne

theorem pow_zero (a : R) {e : R} (h : (nat_lit 1).rawCast = e) :
    a ^ 0 = e + 0 := by simp [← h]

theorem pow_add {b₁ b₂ : ℕ} {d : R}
    (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d := by
  subst_vars; simp [_root_.pow_add]

/-- Exponentiates two polynomials `va, vb`.

* `a ^ 0 = 1`
* `a ^ (b₁ + b₂) = a ^ b₁ * a ^ b₂`
-/
def evalPow {a : Q($α)} {b : Q(ℕ)} (va : ExSum bt sα a) (vb : ExSumNat b) :
    MetaM <| Result (ExSum bt sα) q($a ^ $b) := do
  match vb with
  | .zero =>
    let ⟨_, one, pf⟩ := rc.one
    assumeInstancesCommute
    return ⟨_, (ExProd.const (one)).toSum, q(pow_zero $a $pf)⟩
  | .add vb₁ vb₂ =>
    let ⟨_, vc₁, pc₁⟩ ← evalPow₁ rc rcℕ va vb₁
    let ⟨_, vc₂, pc₂⟩ ← evalPow va vb₂
    let ⟨_, vd, pd⟩ ← evalMul rc rcℕ vc₁ vc₂
    return ⟨_, vd, q(pow_add $pc₁ $pc₂ $pd)⟩

/-- This cache contains data required by the `ring` tactic during execution. -/
structure Cache {α : Q(Type u)} (sα : Q(CommSemiring $α)) where
  /-- A ring instance on `α`, if available. -/
  rα : Option Q(CommRing $α)
  /-- A division semiring instance on `α`, if available. -/
  dsα : Option Q(Semifield $α)
  /-- A characteristic zero ring instance on `α`, if available. -/
  czα : Option Q(CharZero $α)

/-- Create a new cache for `α` by doing the necessary instance searches. -/
def mkCache {α : Q(Type u)} (sα : Q(CommSemiring $α)) : MetaM (Cache sα) :=
  return {
    rα := (← trySynthInstanceQ q(CommRing $α)).toOption
    dsα := (← trySynthInstanceQ q(Semifield $α)).toOption
    czα := (← trySynthInstanceQ q(CharZero $α)).toOption }

theorem toProd_pf (p : (a : R) = a') {e : ℕ} (hone : (nat_lit 1).rawCast = e) :
    a = a' ^ e * (nat_lit 1).rawCast := by simp [← hone, *]

theorem atom_pf (a : R) {e : ℕ} (hone : (nat_lit 1).rawCast = e)
    (hb : a ^ e * (nat_lit 1).rawCast = b) :
    a = b + 0 := by
  simp [← hone, ← hb]

theorem atom_pf' (p : (a : R) = a') {e : ℕ} (hone : (nat_lit 1).rawCast = e)
    (hb : a' ^ e * (nat_lit 1).rawCast = b) :
    a = b + 0 := by simp [← hone, ←hb, *]

/--
Evaluates an atom, an expression where `ring` can find no additional structure.

* `a = a ^ 1 * 1 + 0`
-/
def evalAtom (e : Q($α)) : AtomM (Result (ExSum bt sα) e) := do
  let r ← (← read).evalAtom e
  have e' : Q($α) := r.expr
  let (i, ⟨a', _⟩) ← addAtomQ e'
  let ⟨_, one, pf_one⟩ := rcℕ.one
  let one := ExProdNat.const (one)
  let ⟨_, vb, pb⟩ : Result (ExProd bt sα) _ := (ExBase.atom i (e := a')).toProd rc one
  let vc := vb.toSum
  pure ⟨_, vc, match r.proof? with
  | none =>
    have : $e =Q $e' := ⟨⟩
    q(atom_pf $e $pf_one $pb)
  | some (p : Q($e = $a')) =>
    q(atom_pf' $p $pf_one $pb)⟩

theorem inv_mul {R} [Semifield R] {a₁ a₂ a₃ b₁ b₃ c}
    (_ : (a₁⁻¹ : R) = b₁) (_ : (a₃⁻¹ : R) = b₃)
    (_ : b₃ * (b₁ ^ a₂ * (nat_lit 1).rawCast) = c) :
    (a₁ ^ a₂ * a₃ : R)⁻¹ = c := by subst_vars; simp

nonrec theorem inv_zero {R} [Semifield R] : (0 : R)⁻¹ = 0 := inv_zero

theorem inv_single {R} [Semifield R] {a b : R}
    (_ : (a : R)⁻¹ = b) : (a + 0)⁻¹ = b + 0 := by simp [*]
theorem inv_add {a₁ a₂ : ℕ} (_ : ((a₁ : ℕ) : R) = b₁) (_ : ((a₂ : ℕ) : R) = b₂) :
    ((a₁ + a₂ : ℕ) : R) = b₁ + b₂ := by
  subst_vars; simp

section

variable (dsα : Q(Semifield $α))

/-- Applies `⁻¹` to a polynomial to get an atom. -/
def evalInvAtom (a : Q($α)) : AtomM (Result (ExBase bt sα) q($a⁻¹)) := do
  let (i, ⟨b', _⟩) ← addAtomQ q($a⁻¹)
  pure ⟨b', ExBase.atom i, q(Eq.refl $b')⟩

/-- Inverts a polynomial `va` to get a normalized result polynomial.

* `c⁻¹ = (c⁻¹)` if `c` is a constant
* `(a ^ b * c)⁻¹ = a⁻¹ ^ b * c⁻¹`
-/
def ExProd.evalInv {a : Q($α)} (czα : Option Q(CharZero $α)) (va : ExProd bt sα a) :
    AtomM (Result (ExProd bt sα) q($a⁻¹)) := do
  Lean.Core.checkSystem decl_name%.toString
  match va with
  | .const c =>
    match ← rc.inv czα q($dsα) c with
    | some ⟨_, vd, pd⟩ => pure ⟨_, .const vd, q($pd)⟩
    | none =>
        let ⟨_, vc, pc⟩ ← evalInvAtom dsα a
        let ⟨_, one, pf⟩ := rcℕ.one
        let ⟨_, vc', pc'⟩ := vc.toProd rc (ExProdNat.const (one))
        pure ⟨_, vc', q($pc' ▸ toProd_pf $pc $pf)⟩
  | .mul (x := a₁) (e := _a₂) _va₁ va₂ va₃ => do
    let ⟨_b₁, vb₁, pb₁⟩ ← evalInvAtom dsα a₁
    let ⟨_b₃, vb₃, pb₃⟩ ← va₃.evalInv czα
    let ⟨_b₁', vb₁', pb₁'⟩ := (vb₁.toProd rc va₂)
    let ⟨c, vc, pc⟩ ← evalMulProd rc rcℕ vb₃ vb₁'
    assumeInstancesCommute
    pure ⟨c, vc, q(inv_mul $pb₁ $pb₃ ($pb₁' ▸ $pc))⟩

/-- Inverts a polynomial `va` to get a normalized result polynomial.

* `0⁻¹ = 0`
* `a⁻¹ = (a⁻¹)` if `a` is a nontrivial sum
-/
def ExSum.evalInv {a : Q($α)} (czα : Option Q(CharZero $α)) (va : ExSum bt sα a) :
    AtomM (Result (ExSum bt sα) q($a⁻¹)) :=
  match va with
  | ExSum.zero => pure ⟨_, .zero, (q(inv_zero (R := $α)) : Expr)⟩
  | ExSum.add va ExSum.zero => do
    let ⟨_, vb, pb⟩ ← va.evalInv rc rcℕ dsα czα
    pure ⟨_, vb.toSum, (q(inv_single $pb) : Expr)⟩
  | va => do
    let ⟨_, vb, pb⟩ ← evalInvAtom dsα a
    let ⟨_, one, pf⟩ := rcℕ.one
    let ⟨_', vb', pb'⟩ := vb.toProd rc (ExProdNat.const (one))
    assumeInstancesCommute
    pure ⟨_, vb'.toSum, q(atom_pf' $pb $pf $pb')⟩

end

theorem div_pf {R} [Semifield R] {a b c d : R}
    (_ : b⁻¹ = c) (_ : a * c = d) : a / b = d := by
  subst_vars; simp [div_eq_mul_inv]

/-- Divides two polynomials `va, vb` to get a normalized result polynomial.

* `a / b = a * b⁻¹`
-/
def evalDiv {a b : Q($α)} (rα : Q(Semifield $α)) (czα : Option Q(CharZero $α))
    (va : ExSum bt sα a) (vb : ExSum bt sα b) : AtomM (Result (ExSum bt sα) q($a / $b)) := do
  let ⟨_c, vc, pc⟩ ← vb.evalInv rc rcℕ rα czα
  let ⟨d, vd, pd⟩ ← evalMul rc rcℕ va vc
  assumeInstancesCommute
  pure ⟨d, vd, q(div_pf $pc $pd)⟩

theorem add_congr (_ : a = a') (_ : b = b') (_ : a' + b' = c) : (a + b : R) = c := by
  subst_vars; rfl

theorem mul_congr (_ : a = a') (_ : b = b') (_ : a' * b' = c) : (a * b : R) = c := by
  subst_vars; rfl

theorem nsmul_congr {a a' : ℕ} (_ : (a : ℕ) = a') (_ : b = b') (_ : a' • b' = c) :
    (a • (b : R)) = c := by
  subst_vars; rfl

theorem zsmul_congr {R} [CommRing R] {b b' c : R} {a a' : ℤ} (_ : (a : ℤ) = a') (_ : b = b')
    (_ : a' • b' = c) :
    (a • (b : R)) = c := by
  subst_vars; rfl

theorem pow_congr {b b' : ℕ} (_ : a = a') (_ : b = b')
    (_ : a' ^ b' = c) : (a ^ b : R) = c := by subst_vars; rfl

theorem neg_congr {R} [CommRing R] {a a' b : R} (_ : a = a')
    (_ : -a' = b) : (-a : R) = b := by subst_vars; rfl

theorem sub_congr {R} [CommRing R] {a a' b b' c : R} (_ : a = a') (_ : b = b')
    (_ : a' - b' = c) : (a - b : R) = c := by subst_vars; rfl

theorem inv_congr {R} [Semifield R] {a a' b : R} (_ : a = a')
    (_ : a'⁻¹ = b) : (a⁻¹ : R) = b := by subst_vars; rfl

theorem div_congr {R} [Semifield R] {a a' b b' c : R} (_ : a = a') (_ : b = b')
    (_ : a' / b' = c) : (a / b : R) = c := by subst_vars; rfl

theorem hsmul_congr {R α : Type*} [CommSemiring α] [HSMul R α α]
    {r s : R} {a b t c : α}
    (_ : r = s) (_ : a = b) (_ : ∀ (x : α), s • x = t * x) (_ : t * b = c) :
    r • a = c := by
  subst_vars
  simp [*]

/-- A precomputed `Cache` for `ℕ`. -/
def Cache.nat : Cache sℕ := { rα := none, dsα := none, czα := some q(inferInstance) }

/-- Checks whether `e` would be processed by `eval` as a ring expression,
or otherwise if it is an atom or something simplifiable via `norm_num`.

We use this in `ring_nf` to avoid rewriting atoms unnecessarily.

Returns:
* `none` if `eval` would process `e` as an algebraic ring expression
* `some none` if `eval` would treat `e` as an atom.
* `some (some r)` if `eval` would not process `e` as an algebraic ring expression,
  but `NormNum.derive` can nevertheless simplify `e`, with result `r`.
-/
-- Note this is not the same as whether the result of `eval` is an atom. (e.g. consider `x + 0`.)
def isAtomOrDerivable
    (c : Cache sα) (e : Q($α)) : AtomM (Option (Option (Result (ExSum bt sα) e))) := do
  let els := try
      pure <| some <| some (← rc.derive e)
    catch _ => pure (some none)
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα, c.dsα with
  | ``HAdd.hAdd, _, _ | ``Add.add, _, _
  | ``HMul.hMul, _, _ | ``Mul.mul, _, _
  | ``HSMul.hSMul, _, _
  | ``HPow.hPow, _, _ | ``Pow.pow, _, _
  | ``Neg.neg, some _, _
  | ``HSub.hSub, some _, _ | ``Sub.sub, some _, _
  | ``Inv.inv, _, some _
  | ``HDiv.hDiv, _, some _ | ``Div.div, _, some _ => pure none
  | _, _, _ => els

end

variable (rcRing : ∀ {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)},
  Cache sα → RingCompute (Ring.BaseType sα) sα) (rcℕ : RingCompute btℕ sℕ) in

/--
Evaluates expression `e` of type `α` into a normalized representation as a polynomial.
This is the main driver of `ring`, which calls out to `evalAdd`, `evalMul` etc.

* `rcRing` tells us how to normalize constants in the base type of a scalar multiplication.
* `rc` tells us how to normalize constants in `α`.
* `rcℕ` tells us how to normalize constants in exponents.
-/
partial def eval  {u : Lean.Level}
    {α : Q(Type u)} {bt : Q($α) → Type} {sα : Q(CommSemiring $α)} (rc : RingCompute bt sα)
    (c : Cache sα) (e : Q($α)) : AtomM (Result (ExSum bt sα) e) := Lean.withIncRecDepth do
  let els := do
    try rc.derive e
    catch _ => evalAtom rc rcℕ e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα, c.dsα with
  | ``HAdd.hAdd, _, _ | ``Add.add, _, _ => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalAdd rc rcℕ va vb
      pure ⟨c, vc, q(add_congr $pa $pb $p)⟩
    | _ => els
  | ``HMul.hMul, _, _ | ``Mul.mul, _, _ => match e with
    | ~q($a * $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalMul rc rcℕ va vb
      pure ⟨c, vc, q(mul_congr $pa $pb $p)⟩
    | _ => els
  | ``HSMul.hSMul, _, _ | ``SMul.smul, _, _ => match e with
    | ~q(@HSMul.hSMul $R $α' _ $inst $r $a') =>
      if ! (← isDefEq α α') then
        throwError "HSmul not implemented"
      have : u_2 =QL u := ⟨⟩
      have : $α =Q $α' := ⟨⟩
      have a : Q($α) := a'
      have : $a =Q $a' := ⟨⟩
      try
        let sR : Q(CommSemiring $R) ← synthInstanceQ q(CommSemiring $R)
        -- Lazily evaluate `vs` only if we actually need the normalized expression in `R`.
        let vs : AtomM <| Result (ExSum (Ring.BaseType sR) sR) q($r) := do
          -- TODO: special case Nat and Int for the cache?
          let cR ← mkCache sR
          eval (rcRing cR) cR r
        let ⟨_, vb, pb⟩ ← eval rc c a
        let ⟨_, vt, pt⟩ ← rc.cast _ _ q($sR) q(inferInstance) _ vs
        let ⟨_, vc, pc⟩ ← evalMul rc rcℕ vt vb
        return ⟨_, vc, q(hsmul_congr rfl $pb $pt $pc)⟩
      catch _ => els
    | _ => els
  | ``HPow.hPow, _, _ | ``Pow.pow, _, _ => match e with
    | ~q($a ^ $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨b, vb, pb⟩ ← eval rcℕ .nat b
      let ⟨b', vb'⟩ := vb.toExSumNat
      have : $b =Q $b' := ⟨⟩
      let ⟨c, vc, p⟩ ← evalPow rc rcℕ va vb'
      pure ⟨c, vc, q(pow_congr $pa $pb $p)⟩
    | _ => els
  | ``Neg.neg, some rα, _ => match e with
    | ~q(-$a) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨b, vb, p⟩ ← evalNeg rc rα va
      pure ⟨b, vb, q(neg_congr $pa $p)⟩
    | _ => els
  | ``HSub.hSub, some rα, _ | ``Sub.sub, some rα, _ => match e with
    | ~q($a - $b) => do
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalSub rc rcℕ rα va vb
      pure ⟨c, vc, q(sub_congr $pa $pb $p)⟩
    | _ => els
  | ``Inv.inv, _, some dsα => match e with
    | ~q($a⁻¹) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨b, vb, p⟩ ← va.evalInv rc rcℕ dsα c.czα
      pure ⟨b, vb, q(inv_congr $pa $p)⟩
    | _ => els
  | ``HDiv.hDiv, _, some dsα | ``Div.div, _, some dsα => match e with
    | ~q($a / $b) => do
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalDiv rc rcℕ dsα c.czα va vb
      pure ⟨c, vc, q(div_congr $pa $pb $p)⟩
    | _ => els
  | _, _, _ => els

end Mathlib.Tactic.Ring.Common
