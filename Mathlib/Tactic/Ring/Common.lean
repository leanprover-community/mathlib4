
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
namespace Algebra

open Mathlib.Meta Qq NormNum Lean.Meta AtomM

attribute [local instance] monadLiftOptionMetaM

open Lean (MetaM Expr mkRawNatLit)

/-- A shortcut instance for `CommSemiring ℕ` used by ring. -/
def instCommSemiringNat : CommSemiring ℕ := inferInstance

/-- A shortcut instance for `CommSemiring ℤ` used by ring. -/
def instCommSemiringInt : CommSemiring ℤ := inferInstance

/--
A typed expression of type `CommSemiring ℕ` used when we are working on
ring subexpressions of type `ℕ`.
-/
def sℕ : Q(CommSemiring ℕ) := q(instCommSemiringNat)

/--
A typed expression of type `CommSemiring ℤ` used when we are working on
ring subexpressions of type `ℤ`.
-/
def sℤ : Q(CommSemiring ℤ) := q(instCommSemiringInt)

-- TODO: the base type of the exponent should be ℚ (or ℕ?) w/ norm_num instances on it.
def btℕ (e : Q(ℕ)) : Type := NormNum.Result (u := 0) e

universe u v

mutual

/-- The base `e` of a normalized exponent expression. -/
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


/--
A monomial, which is a product of powers of `ExBase` expressions,
terminated by a (nonzero) constant coefficient.
-/
inductive ExProdNat : (e : Q(ℕ)) → Type
  /-- A coefficient `value`, which must not be `0`. `e` is a raw rat cast.
  If `value` is not an integer, then `hyp` should be a proof of `(value.den : α) ≠ 0`. -/
  | const {e : Q(ℕ)} (value : btℕ e) : ExProdNat e
  /-- A product `x ^ e * b` is a monomial if `b` is a monomial. Here `x` is an `ExBase`
  and `e` is an `ExProd` representing a monomial expression in `ℕ` (it is a monomial instead of
  a polynomial because we eagerly normalize `x ^ (a + b) = x ^ a * x ^ b`.) -/
  | mul {x : Q(ℕ)} {e : Q(ℕ)} {b : Q(ℕ)} :
    ExBaseNat x → ExProdNat e → ExProdNat b → ExProdNat q($x ^ $e * $b)

/-- A polynomial expression, which is a sum of monomials. -/
inductive ExSumNat : (e : Q(ℕ)) → Type
  /-- Zero is a polynomial. `e` is the expression `0`. -/
  | zero : ExSumNat q(0)
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {a b : Q(ℕ)} : ExProdNat a → ExSumNat b → ExSumNat q($a + $b)
end


mutual

/-- The base `e` of a normalized exponent expression. -/
inductive ExBase {u : Lean.Level} {α : Q(Type u)} (baseType : Q($α) → Type) (sα : Q(CommSemiring $α)) : (e : Q($α)) → Type
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
  | atom {e} (id : ℕ) : ExBase baseType sα e
  /-- A sum of monomials. -/
  | sum {e} (_ : ExSum baseType sα e) : ExBase baseType sα e


/--
A monomial, which is a product of powers of `ExBase` expressions,
terminated by a (nonzero) constant coefficient.
-/
inductive ExProd {u : Lean.Level} {α : Q(Type u)} (baseType : Q($α) → Type) (sα : Q(CommSemiring $α)) : (e : Q($α)) → Type
  /-- A coefficient `value`, which must not be `0`. `e` is a raw rat cast.
  If `value` is not an integer, then `hyp` should be a proof of `(value.den : α) ≠ 0`. -/
  | const {e : Q($α)} (value : baseType e) : ExProd baseType sα e
  /-- A product `x ^ e * b` is a monomial if `b` is a monomial. Here `x` is an `ExBase`
  and `e` is an `ExProd` representing a monomial expression in `ℕ` (it is a monomial instead of
  a polynomial because we eagerly normalize `x ^ (a + b) = x ^ a * x ^ b`.) -/
  | mul {x : Q($α)} {e : Q(ℕ)} {b : Q($α)} :
    ExBase baseType sα x → ExProdNat e → ExProd baseType sα b → ExProd baseType sα q($x ^ $e * $b)

/-- A polynomial expression, which is a sum of monomials. -/
inductive ExSum {u : Lean.Level} {α : Q(Type u)} (baseType : Q($α) → Type) (sα : Q(CommSemiring $α)) : (e : Q($α)) → Type
  /-- Zero is a polynomial. `e` is the expression `0`. -/
  | zero : ExSum baseType sα q(0 : $α)
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {a b : Q($α)} :
    ExProd baseType sα a → ExSum baseType sα b → ExSum baseType sα q($a + $b)
end

variable {u : Lean.Level}

/--
The result of evaluating an (unnormalized) expression `e` into the type family `E`
(one of `ExSum`, `ExProd`, `ExBase`) is a (normalized) element `e'`
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

class RingCompute {u : Lean.Level} {α : Q(Type u)} (baseType : Q($α) → Type)
  (sα : Q(CommSemiring $α)) where
  evalAdd (sα) : ∀ x y : Q($α), baseType x → baseType y → MetaM (Result baseType q($x + $y))
  evalMul (sα) : ∀ x y : Q($α), baseType x → baseType y → MetaM (Result baseType q($x * $y))
  evalNeg (sα) : ∀ x : Q($α), (rα : Q(CommRing $α)) → baseType x → MetaM (Result baseType q(-$x))
  evalPow (sα) : ∀ x : Q($α), baseType x → (lit : Q(ℕ)) →
    OptionT MetaM (Result baseType q($x ^ $lit))
  evalInv : ∀ {x : Q($α)}, (czα : Option Q(CharZero $α)) → (fα : Q(Semifield $α)) → baseType x →
    MetaM (Option <| Result baseType q($x⁻¹))
  derive (sα) : ∀ x : Q($α), MetaM (Result (ExSum baseType sα) q($x))
  eq (sα) : ∀ {x y : Q($α)}, baseType x → baseType y → Bool
  compare (sα) : ∀ {x y : Q($α)}, baseType x → baseType y → Ordering
  isZero (sα) : ∀ {x : Q($α)}, baseType x → Option Q(NormNum.IsNat $x 0)
  isOne (sα) : ∀ {x : Q($α)}, baseType x → Option Q(NormNum.IsNat $x 1)
  -- cast (sα) : ∀ (_ : Q($α)), Σ b, baseType b
  one (sα) : baseType q((nat_lit 1).rawCast)

@[reducible]
def Ring.baseType {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    (e : Q($α)) := NormNum.Result e

instance Ring.ringCompute {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) :
    RingCompute (Ring.baseType sα) sα where
  evalAdd x y zx zy := do
    let res ← zx.add zy q(inferInstance)
    return ⟨_, res, q(rfl)⟩
  evalMul x y zx zy := do
    let res ← zx.mul zy q(inferInstance)
    return ⟨_, res, q(rfl)⟩
  evalNeg x crα zx := do
    let res ← zx.neg q(inferInstance)
    return ⟨_, res, q(rfl)⟩
  evalPow x zx lit := do
    let rc ← (NormNum.evalPow.core q($x ^ $lit) q(HPow.hPow) q($x) lit lit q(sorry) sα zx).run
    match rc with
    | none => OptionT.fail
    | some rc => return ⟨_, rc, q(rfl)⟩
  evalInv czα sfα zx := do
    match (← (Lean.observing? <| zx.inv _ czα :)) with
    | some rc => return some ⟨_, rc, q(rfl)⟩
    | none => return none
  derive x := do
    -- TODO: actually implement.
    return ⟨_, .zero, q(sorry)⟩
  eq zx zy := zx.toRat == zy.toRat
  compare zx zy := compare zx.toRat zy.toRat
  isZero zx := do match zx with
  | .isNat _ lit pf =>
    if lit.natLit! == 0 then
      have : $lit =Q 0 := ⟨⟩
      assumeInstancesCommute
      return q($pf)
    else
      failure
  | _ => none
  isOne zx := do match zx with
  | .isNat _ lit pf =>
    if lit.natLit! == 1 then
      have : $lit =Q 1 := ⟨⟩
      assumeInstancesCommute
      return q($pf)
    else
      failure
  | _ => none
  one :=
    NormNum.Result.ofRawNat q(1 : $α)


instance : RingCompute (u := 0) btℕ sℕ := Ring.ringCompute sℕ

instance (e : Expr) : Inhabited <| btℕ e := by
  rw [btℕ]
  infer_instance

instance : Inhabited (Σ e, (ExBaseNat) e) := ⟨default, .atom 0⟩
instance : Inhabited (Σ e, (ExSumNat) e) := ⟨_, .zero⟩
instance : Inhabited (Σ e, (ExProdNat) e) := ⟨default, .const default⟩

variable {u : Lean.Level} {α : Q(Type u)} {bt : Q($α) → Type} {sα : Q(CommSemiring $α)}
   [∀ e, Inhabited (bt e)]

instance : Inhabited (Σ e, (ExBase bt sα) e) := ⟨default, .atom 0⟩
instance : Inhabited (Σ e, (ExSum bt sα) e) := ⟨_, .zero⟩
instance : Inhabited (Σ e, (ExProd bt sα) e) := ⟨default, .const default⟩

variable [RingCompute bt sα]

mutual

partial def ExBaseNat.toExBase (e : Q(ℕ)) : ExBaseNat e → Σ e', ExBase btℕ sℕ e' := fun
  | .atom id => ⟨_, .atom (e := e) id⟩
  | .sum v => ⟨_, .sum v.toExSum.2⟩

partial def ExProdNat.toExProd (e : Q(ℕ)) : ExProdNat e → Σ e', ExProd btℕ sℕ e' := fun
  | .const value => ⟨_, .const value⟩
  | .mul vx ve vt => ⟨_, .mul vx.toExBase.2 ve vt.toExProd.2⟩

partial def ExSumNat.toExSum (e : Q(ℕ)) : ExSumNat e → Σ e', ExSum btℕ sℕ e' := fun
  | .zero => ⟨_, .zero (baseType := btℕ) (sα := sℕ)⟩
  | .add va vb => ⟨_, .add va.toExProd.2 vb.toExSum.2⟩

end

mutual

partial def ExBase.toExBaseNat (e : Q(ℕ)) : ExBase btℕ sℕ e → Σ e', ExBaseNat e' := fun
  | .atom id => ⟨_, .atom (e := e) id⟩
  | .sum v => ⟨_, .sum v.toExSumNat.2⟩

partial def ExProd.toExProdNat (e : Q(ℕ)) : ExProd btℕ sℕ e → Σ e', ExProdNat e' := fun
  | .const value => ⟨_, .const value⟩
  | .mul vx ve vt => ⟨_, .mul vx.toExBaseNat.2 ve vt.toExProdNat.2⟩

partial def ExSum.toExSumNat (e : Q(ℕ)) : ExSum btℕ sℕ e → Σ e', ExSumNat e' := fun
  | .zero => ⟨_, .zero⟩
  | .add va vb => ⟨_, .add va.toExProdNat.2 vb.toExSumNat.2⟩

end


mutual

/-- Equality test for expressions. This is not a `BEq` instance because it is heterogeneous. -/
def ExBase.eq
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} [RingCompute bt sα]
    {a b : Q($α)} :
    ExBase bt sα a → ExBase bt sα b → Bool
  | .atom i, .atom j => i == j
  | .sum a, .sum b => a.eq b
  | _, _ => false

@[inherit_doc ExBase.eq]
def ExProd.eq
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} [RingCompute bt sα]
    {a b : Q($α)} :
    ExProd bt sα a → ExProd bt sα b → Bool
  | .const i, .const j => RingCompute.eq sα i j
  | .mul a₁ a₂ a₃, .mul b₁ b₂ b₃ => a₁.eq b₁ && a₂.toExProd.2.eq b₂.toExProd.2 && a₃.eq b₃
  | _, _ => false

@[inherit_doc ExBase.eq]
def ExSum.eq
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} [RingCompute bt sα]
    {a b : Q($α)} :
    ExSum bt sα a → ExSum bt sα b → Bool
  | .zero, .zero => true
  | .add a₁ a₂, .add b₁ b₂ => a₁.eq b₁ && a₂.eq b₂
  | _, _ => false
end

mutual
/--
A total order on normalized expressions.
This is not an `Ord` instance because it is heterogeneous.
-/
def ExBase.cmp
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} [RingCompute bt sα] {a b : Q($α)} :
    ExBase bt sα a → ExBase bt sα b → Ordering
  | .atom i, .atom j => compare i j
  | .sum a, .sum b => a.cmp b
  | .atom .., .sum .. => .lt
  | .sum .., .atom .. => .gt

@[inherit_doc ExBase.cmp]
def ExProd.cmp
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} [RingCompute bt sα] {a b : Q($α)} :
    ExProd bt sα a → ExProd bt sα b → Ordering
  | .const i, .const j => RingCompute.compare sα i j
  | .mul a₁ a₂ a₃, .mul b₁ b₂ b₃ => (a₁.cmp b₁).then (a₂.toExProd.2.cmp b₂.toExProd.2) |>.then (a₃.cmp b₃)
  | .const _, .mul .. => .lt
  | .mul .., .const _ => .gt

@[inherit_doc ExBase.cmp]
def ExSum.cmp
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} [RingCompute bt sα] {a b : Q($α)} :
    ExSum bt sα a → ExSum bt sα b → Ordering
  | .zero, .zero => .eq
  | .add a₁ a₂, .add b₁ b₂ => (a₁.cmp b₁).then (a₂.cmp b₂)
  | .zero, .add .. => .lt
  | .add .., .zero => .gt
end

variable [∀ e, Inhabited (bt e)]

-- #synth Inhabited (Σ e, (ExSum bt sβ) e)
-- #synth Inhabited (Σ e, (ExBase bt sβ) e)
-- #synth Inhabited (Σ e, (ExProd bt sβ) e)

mutual

/-- Converts `ExBase sα` to `ExBase sβ`, assuming `sα` and `sβ` are defeq. -/
unsafe def ExBase.cast {sβ : Q(CommSemiring $α)} [RingCompute bt sβ] {a : Q($α)} :
    ExBase bt sα a → Σ a, ExBase bt sβ a
  | .atom i => ⟨a, .atom i⟩
  | .sum a =>
      let ⟨_, vb⟩ := a.cast (sβ := sβ);
      ⟨_, .sum vb⟩

/-- Converts `ExProd sα` to `ExProd sβ`, assuming `sα` and `sβ` are defeq. -/
unsafe def ExProd.cast
    {sβ : Q(CommSemiring $α)} [RingCompute bt sβ] {a : Q($α)} :
    ExProd bt sα a → Σ a, ExProd bt sβ a
  | .const i => ⟨_, .const i⟩
  | .mul a₁ a₂ a₃ => ⟨_, .mul a₁.cast.2 a₂ a₃.cast.2⟩

/-- Converts `ExSum sα` to `ExSum sβ`, assuming `sα` and `sβ` are defeq. -/
unsafe def ExSum.cast
    {sβ : Q(CommSemiring $α)} [RingCompute bt sβ] {a : Q($α)} :
    ExSum bt sα a → Σ a, ExSum bt sβ a
  | .zero => ⟨_, .zero⟩
  | .add a₁ a₂ => ⟨_, .add a₁.cast.2 a₂.cast.2⟩

end

variable (sα)
variable {R : Type*} [CommSemiring R]

-- /--
-- Constructs the expression corresponding to `.const n`.
-- (The `.const` constructor does not check that the expression is correct.)
-- -/
-- def ExProd.mkNat (n : ℕ) : (e : Q($α)) × ExProd bt sα e :=
--   let lit : Q(ℕ) := .lit (.natVal n)
--   ⟨q(($lit).rawCast : $α), .const n⟩

-- /--
-- Constructs the expression corresponding to `.const (-n)`.
-- (The `.const` constructor does not check that the expression is correct.)
-- -/
-- def ExProd.mkNegNat (_ : Q(Ring $α)) (n : ℕ) : (e : Q($α)) × ExProd sα e :=
--   let lit : Q(ℕ) := mkRawNatLit n
--   ⟨q((Int.negOfNat $lit).rawCast : $α), .const (-n) none⟩

-- /--
-- Constructs the expression corresponding to `.const q h` for `q = n / d`
-- and `h` a proof that `(d : α) ≠ 0`.
-- (The `.const` constructor does not check that the expression is correct.)
-- -/
-- def ExProd.mkNNRat (_ : Q(DivisionSemiring $α)) (q : ℚ) (n : Q(ℕ)) (d : Q(ℕ)) (h : Expr) :
--     (e : Q($α)) × ExProd sα e :=
--   ⟨q(NNRat.rawCast $n $d : $α), .const q h⟩

-- /--
-- Constructs the expression corresponding to `.const q h` for `q = -(n / d)`
-- and `h` a proof that `(d : α) ≠ 0`.
-- (The `.const` constructor does not check that the expression is correct.)
-- -/
-- def ExProd.mkNegNNRat (_ : Q(DivisionRing $α)) (q : ℚ) (n : Q(ℕ)) (d : Q(ℕ)) (h : Expr) :
--     (e : Q($α)) × ExProd sα e :=
--   ⟨q(Rat.rawCast (.negOfNat $n) $d : $α), .const q h⟩

section

/-- Embed an exponent (an `ExBase, ExProd` pair) as an `ExProd` by multiplying by 1. -/
def ExBase.toProd
    {a : Q($α)} {b : Q(ℕ)}
    (va : ExBase bt sα a) (vb : ExProdNat b) :
    Result (ExProd bt sα) q($a ^ $b * (nat_lit 1).rawCast) :=
      ⟨_, .mul va vb (.const  (RingCompute.one sα (baseType := bt))),
        /- TODO: Remove unsafe cast -/
        (q(Eq.refl ($a ^ $b * (nat_lit 1).rawCast)):) ⟩

/-- Embed `ExProd` in `ExSum` by adding 0. -/
def ExProd.toSum {e : Q($α)} (v : ExProd bt sα e) : ExSum bt sα q($e + 0) :=
  .add v .zero

/-- Get the leading coefficient of an `ExProd`. -/
def ExProd.coeff {e : Q($α)} :
    have : Inhabited <| Σ c, bt c := ⟨default, default⟩
  ExProd bt sα e → Σ c, bt c
  | .const q => ⟨_, q⟩
  | .mul _ _ v => v.coeff
end


variable (bt) in
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
    let ⟨_, zc, pf⟩ ← RingCompute.evalAdd (u := u) (sα := sα) _ _ za zb
    match RingCompute.isZero sα zc with
    | .some pf => pure <| .zero pf
    | .none =>
      assumeInstancesCommute
      pure <| .nonzero ⟨_, .const zc, q($pf)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, .mul (x := b₁) (e := b₂) vb₁ vb₂ vb₃ => do
    guard (va₁.eq vb₁ && va₂.toExProd.2.eq vb₂.toExProd.2)
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
    match ← (evalAddOverlap sα va₁ vb₁).run with
    | some (.nonzero ⟨_, vc₁, pc₁⟩) =>
      let ⟨_, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
      return ⟨_, .add vc₁ vc₂, q(add_pf_add_overlap $pc₁ $pc₂)⟩
    | some (.zero pc₁) =>
      let ⟨c₂, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
      return ⟨c₂, vc₂, q(add_pf_add_overlap_zero $pc₁ $pc₂)⟩
    | none =>
      if let .lt := va₁.cmp vb₁ then
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
    let ⟨_, zc, pf⟩ ← RingCompute.evalMul sα _ _ za zb
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
    if vxa.eq vxb then
      have : $xa =Q $xb := ⟨⟩
      if let some (.nonzero ⟨ec', vec', pec'⟩) ← (evalAddOverlap sℕ vea' veb').run then
        let ⟨_, vc, pc⟩ ← evalMulProd va₂ vb₂
        let ⟨ec, vec⟩ := vec'.toExProdNat
        have : $ea =Q $ea' := ⟨⟩
        have : $eb =Q $eb' := ⟨⟩
        have : $ec =Q $ec' := ⟨⟩
        return ⟨_, .mul vxa vec vc, q(mul_pp_pf_overlap $xa $pec' $pc)⟩
    if let .lt := (vxa.cmp vxb).then (vea'.cmp veb') then
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
    let ⟨_, vc₁, pc₁⟩ ← evalMulProd sα va vb₁
    let ⟨_, vc₂, pc₂⟩ ← evalMul₁ va vb₂
    let ⟨_, vd, pd⟩ ← evalAdd sα vc₁.toSum vc₂
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
    let ⟨_, vc₁, pc₁⟩ ← evalMul₁ sα va₁ vb
    let ⟨_, vc₂, pc₂⟩ ← evalMul va₂ vb
    let ⟨_, vd, pd⟩ ← evalAdd sα vc₁ vc₂
    return ⟨_, vd, q(add_mul $pc₁ $pc₂ $pd)⟩

-- /-! ### Scalar multiplication by `ℕ` -/

-- theorem natCast_nat (n) : ((Nat.rawCast n : ℕ) : R) = Nat.rawCast n := by simp

-- theorem natCast_mul {a₁ a₃ : ℕ} (a₂) (_ : ((a₁ : ℕ) : R) = b₁)
--     (_ : ((a₃ : ℕ) : R) = b₃) : ((a₁ ^ a₂ * a₃ : ℕ) : R) = b₁ ^ a₂ * b₃ := by
--   subst_vars; simp

-- theorem natCast_zero : ((0 : ℕ) : R) = 0 := Nat.cast_zero

-- theorem natCast_add {a₁ a₂ : ℕ}
--     (_ : ((a₁ : ℕ) : R) = b₁) (_ : ((a₂ : ℕ) : R) = b₂) : ((a₁ + a₂ : ℕ) : R) = b₁ + b₂ := by
--   subst_vars; simp

-- mutual -- partial only to speed up compilation

-- /-- Applies `Nat.cast` to a nat polynomial to produce a polynomial in `α`.

-- * An atom `e` causes `↑e` to be allocated as a new atom.
-- * A sum delegates to `ExSum.evalNatCast`.
-- -/
-- partial def ExBase.evalNatCast {a : Q(ℕ)} (va : ExBase btℕ sℕ a) : AtomM (Result (ExBase bt sα) q($a)) :=
--   match va with
--   | .atom _ => do
--     let (i, ⟨b', _⟩) ← addAtomQ q($a)
--     pure ⟨b', ExBase.atom i, q(Eq.refl $b')⟩
--   | .sum va => do
--     let ⟨_, vc, p⟩ ← va.evalNatCast
--     pure ⟨_, .sum vc, p⟩

-- /-- Applies `Nat.cast` to a nat monomial to produce a monomial in `α`.

-- * `↑c = c` if `c` is a numeric literal
-- * `↑(a ^ n * b) = ↑a ^ n * ↑b`
-- -/
-- partial def ExProd.evalNatCast {a : Q(ℕ)} (va : ExProd btℕ sℕ a) : AtomM (Result (ExProd bt sα) q($a)) :=
--   match va with
--   | .const c =>
--     have n : Q(ℕ) := a.appArg!
--     have : $a =Q Nat.rawCast $n := ⟨⟩
--     pure ⟨q(Nat.rawCast $n), .const c hc, q(natCast_nat (R := $α) $n)⟩
--   | .mul (e := a₂) va₁ va₂ va₃ => do
--     let ⟨_, vb₁, pb₁⟩ ← va₁.evalNatCast
--     let ⟨_, vb₃, pb₃⟩ ← va₃.evalNatCast
--     pure ⟨_, .mul vb₁ va₂ vb₃, q(natCast_mul $a₂ $pb₁ $pb₃)⟩

-- /-- Applies `Nat.cast` to a nat polynomial to produce a polynomial in `α`.

-- * `↑0 = 0`
-- * `↑(a + b) = ↑a + ↑b`
-- -/
-- partial def ExSum.evalNatCast {a : Q(ℕ)} (va : ExSum btℕ sℕ a) : AtomM (Result (ExSum bt sα) q($a)) :=
--   match va with
--   | .zero => pure ⟨_, .zero, q(natCast_zero (R := $α))⟩
--   | .add va₁ va₂ => do
--     let ⟨_, vb₁, pb₁⟩ ← va₁.evalNatCast
--     let ⟨_, vb₂, pb₂⟩ ← va₂.evalNatCast
--     pure ⟨_, .add vb₁ vb₂, q(natCast_add $pb₁ $pb₂)⟩

-- end

-- theorem smul_nat {a b c : ℕ} (h : (a * b : ℕ) = c) : a • b = c := h

-- theorem smul_eq_cast {a : ℕ} (_ : ((a : ℕ) : R) = a') (_ : a' * b = c) : a • b = c := by
--   subst_vars; simp

-- /-- Constructs the scalar multiplication `n • a`, where both `n : ℕ` and `a : α` are normalized
-- polynomial expressions.

-- * `a • b = a * b` if `α = ℕ`
-- * `a • b = ↑a * b` otherwise
-- -/
-- def evalNSMul {a : Q(ℕ)} {b : Q($α)} (va : ExSum sℕ a) (vb : ExSum sα b) :
--     AtomM (Result (ExSum sα) q($a • $b)) := do
--   if ← isDefEq sα sℕ then
--     have : u =QL 0 := ⟨⟩; have : $α =Q ℕ := ⟨⟩; assumeInstancesCommute
--     let ⟨a', va'⟩ := va.cast
--     let ⟨_, vc, pc⟩ ← evalMul sα va' vb
--     have : $a =Q $a' := ⟨⟩
--     pure ⟨_, vc, q(smul_nat $pc)⟩
--   else
--     let ⟨_, va', pa'⟩ ← va.evalNatCast sα
--     let ⟨_, vc, pc⟩ ← evalMul sα va' vb
--     pure ⟨_, vc, q(smul_eq_cast $pa' $pc)⟩

-- /-! ### Scalar multiplication by `ℤ` -/

-- theorem natCast_int {R} [CommRing R] (n) : ((Nat.rawCast n : ℤ) : R) = Nat.rawCast n := by simp

-- theorem intCast_negOfNat_Int {R} [CommRing R] (n) :
--     ((Int.rawCast (Int.negOfNat n) : ℤ) : R) = Int.rawCast (Int.negOfNat n) := by simp

-- theorem intCast_mul {R} [CommRing R] {b₁ b₃ : R} {a₁ a₃ : ℤ} (a₂) (_ : ((a₁ : ℤ) : R) = b₁)
--     (_ : ((a₃ : ℤ) : R) = b₃) : ((a₁ ^ a₂ * a₃ : ℤ) : R) = b₁ ^ a₂ * b₃ := by
--   subst_vars; simp

-- theorem intCast_zero {R} [CommRing R] : ((0 : ℤ) : R) = 0 := Int.cast_zero

-- theorem intCast_add {R} [CommRing R] {b₁ b₂ : R} {a₁ a₂ : ℤ}
--     (_ : ((a₁ : ℤ) : R) = b₁) (_ : ((a₂ : ℤ) : R) = b₂) : ((a₁ + a₂ : ℤ) : R) = b₁ + b₂ := by
--   subst_vars; simp

-- mutual -- partial only to speed up compilation

-- /-- Applies `Int.cast` to an int polynomial to produce a polynomial in `α`.

-- * An atom `e` causes `↑e` to be allocated as a new atom.
-- * A sum delegates to `ExSum.evalIntCast`.
-- -/
-- partial def ExBase.evalIntCast {a : Q(ℤ)} (rα : Q(CommRing $α)) (va : ExBase sℤ a) :
--     AtomM (Result (ExBase sα) q($a)) :=
--   match va with
--   | .atom _ => do
--     let (i, ⟨b', _⟩) ← addAtomQ q($a)
--     pure ⟨b', ExBase.atom i, q(Eq.refl $b')⟩
--   | .sum va => do
--     let ⟨_, vc, p⟩ ← va.evalIntCast rα
--     pure ⟨_, .sum vc, p⟩


-- /-- Applies `Int.cast` to an int monomial to produce a monomial in `α`.

-- * `↑c = c` if `c` is a numeric literal
-- * `↑(a ^ n * b) = ↑a ^ n * ↑b`
-- -/
-- partial def ExProd.evalIntCast {a : Q(ℤ)} (rα : Q(CommRing $α)) (va : ExProd sℤ a) :
--     AtomM (Result (ExProd sα) q($a)) :=
--   match va with
--   | .const c hc => do
--     match a with
--     | ~q(Nat.rawCast $m) =>
--       pure ⟨q(Nat.rawCast $m), .const c hc, q(natCast_int (R := $α) $m)⟩
--     | ~q(Int.rawCast (Int.negOfNat $m)) =>
--       pure ⟨q(Int.rawCast (Int.negOfNat $m)), .const c hc, q(intCast_negOfNat_Int (R := $α) $m)⟩
--   | .mul (e := a₂) va₁ va₂ va₃ => do
--     let ⟨_, vb₁, pb₁⟩ ← va₁.evalIntCast rα
--     let ⟨_, vb₃, pb₃⟩ ← va₃.evalIntCast rα
--     assumeInstancesCommute
--     pure ⟨_, .mul vb₁ va₂ vb₃, q(intCast_mul $a₂ $pb₁ $pb₃)⟩

-- /-- Applies `Int.cast` to an int polynomial to produce a polynomial in `α`.

-- * `↑0 = 0`
-- * `↑(a + b) = ↑a + ↑b`
-- -/
-- partial def ExSum.evalIntCast {a : Q(ℤ)} (rα : Q(CommRing $α)) (va : ExSum sℤ a) :
--     AtomM (Result (ExSum sα) q($a)) :=
--   match va with
--   | .zero => do
--     assumeInstancesCommute
--     pure ⟨_, .zero, q(intCast_zero)⟩
--   | .add va₁ va₂ => do
--     let ⟨_, vb₁, pb₁⟩ ← va₁.evalIntCast rα
--     let ⟨_, vb₂, pb₂⟩ ← va₂.evalIntCast rα
--     assumeInstancesCommute
--     pure ⟨_, .add vb₁ vb₂, q(intCast_add $pb₁ $pb₂)⟩

-- end

-- theorem smul_int {a b c : ℤ} (h : (a * b : ℤ) = c) : a • b = c := h

-- theorem smul_eq_intCast {R} [CommRing R] {a' b c : R} {a : ℤ} (_ : ((a : ℤ) : R) = a')
--     (_ : a' * b = c) : a • b = c := by
--   subst_vars; simp

-- /-- Constructs the scalar multiplication `n • a`, where both `n : ℤ` and `a : α` are normalized
-- polynomial expressions.

-- * `a • b = a * b` if `α = ℤ`
-- * `a • b = a' * b` otherwise, where `a'` is `↑a` with the coercion pushed as deep as possible.
-- -/
-- def evalZSMul {a : Q(ℤ)} {b : Q($α)} (rα : Q(CommRing $α)) (va : ExSum sℤ a) (vb : ExSum sα b) :
--     AtomM (Result (ExSum sα) q($a • $b)) := do
--   if ← isDefEq sα sℤ then
--     have : u =QL 0 := ⟨⟩; have : $α =Q ℤ := ⟨⟩; assumeInstancesCommute
--     let ⟨a', va'⟩ := va.cast
--     let ⟨_, vc, pc⟩ ← evalMul sα va' vb
--     have : $a =Q $a' := ⟨⟩
--     pure ⟨_, vc, q(smul_int $pc)⟩
--   else
--     let ⟨_, va', pa'⟩ ← va.evalIntCast sα rα
--     let ⟨_, vc, pc⟩ ← evalMul sα va' vb
--     assumeInstancesCommute
--     pure ⟨_, vc, q(smul_eq_intCast $pa' $pc)⟩

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
    let ⟨b, zb, pb⟩ ← RingCompute.evalNeg sα _ q($rα) za
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
    let ⟨_, vb₁, pb₁⟩ ← evalNegProd sα rα va₁
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
  let ⟨_c, vc, pc⟩ ← evalNeg sα rα vb
  let ⟨d, vd, pd⟩ ← evalAdd sα va vc
  assumeInstancesCommute
  return ⟨d, vd, q(sub_pf $pc $pd)⟩

/-! ### Exponentiation -/

theorem pow_prod_atom (a : R) (b) : a ^ b = (a + 0) ^ b * (nat_lit 1).rawCast := by simp

/--
The fallback case for exponentiating polynomials is to use `ExBase.toProd` to just build an
exponent expression. (This has a slightly different normalization than `evalPowAtom` because
the input types are different.)

* `x ^ e = (x + 0) ^ e * 1`
-/
def evalPowProdAtom {a : Q($α)} {b : Q(ℕ)} (va : ExProd bt sα a) (vb : ExProdNat b) :
    Result (ExProd bt sα) q($a ^ $b) :=
    let ⟨_, vc, pc⟩ := (ExBase.sum va.toSum).toProd _ vb
  ⟨_, vc, q($pc ▸ pow_prod_atom $a $b)⟩

theorem pow_atom (a : R) (b) : a ^ b = a ^ b * (nat_lit 1).rawCast + 0 := by simp

/--
The fallback case for exponentiating polynomials is to use `ExBase.toProd` to just build an
exponent expression.

* `x ^ e = x ^ e * 1 + 0`
-/
def evalPowAtom {a : Q($α)} {b : Q(ℕ)} (va : ExBase bt sα a) (vb : ExProdNat b) :
    Result (ExSum bt sα) q($a ^ $b) :=
  let ⟨_, vc, pc⟩ := (va.toProd _ vb)
  ⟨_, vc.toSum, q($pc ▸ pow_atom $a $b)⟩

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
      let ⟨_, vc, pc⟩ ← evalMul sα vb vb
      return ⟨_, vc, q(pow_bit0 $pb $pc)⟩
    else
      have : $n =Q 2 * $m + 1 := ⟨⟩
      let ⟨_, vb, pb⟩ ← evalPowNat va m
      let ⟨_, vc, pc⟩ ← evalMul sα vb vb
      let ⟨_, vd, pd⟩ ← evalMul sα vc va
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
      match RingCompute.isOne sα za with
        --  want to continue onto other branch...
      | .some pf =>
        return ⟨_, va, q(one_pow $b $pf)⟩
      | .none =>
        match vb with
        | .const _ =>
          -- TODO: Decide if this is the best way to extract the exponent as a Nat.
          have lit : Q(ℕ) := b.appArg!
          let ⟨c, zc, pc⟩ ← RingCompute.evalPow sα _ za lit
          have : $b =Q $lit := ⟨⟩
          assumeInstancesCommute
          return ⟨c, .const zc, q($pc)⟩
        | _ => OptionT.fail
    | .mul vxa₁ (e := ea₁) vea₁ va₂ =>
      let ⟨ea₁', vea₁'⟩ := vea₁.toExProd
      let ⟨b', vb'⟩ := vb.toExProd
      let ⟨c₁, vc₁, pc₁⟩ ← evalMulProd (bt := btℕ) sℕ vea₁' vb'
      let ⟨c₁', vc₁'⟩ := vc₁.toExProdNat
      let ⟨_, vc₂, pc₂⟩ ← evalPowProd va₂ vb
      have : $c₁ =Q $c₁' := ⟨⟩
      have : $b =Q $b' := ⟨⟩
      have : $ea₁ =Q $ea₁' := ⟨⟩
      return ⟨_, .mul vxa₁ vc₁' vc₂, q(mul_pow $pc₁ $pc₂)⟩
    -- match va, vb with
    -- | .mul vxa₁ vea₁ va₂, vb =>
    -- | _, _ => OptionT.fail
  return (← res.run).getD (evalPowProdAtom sα va vb)


/-


def evalPowProd {a : Q($α)} {b : Q(ℕ)} (va : ExProd sα a) (vb : ExProd sℕ b) :
    MetaM <| Result (ExProd sα) q($a ^ $b) := do
  Lean.Core.checkSystem decl_name%.toString
  let res : OptionT MetaM (Result (ExProd sα) q($a ^ $b)) := do
    match va, vb with
    | va@(.const 1), _ =>
      have : $a =Q Nat.rawCast 1 := ⟨⟩
      return ⟨_, va, q(one_pow (R := $α) $b)⟩
    | .const za ha, .const zb hb =>
      assert! 0 ≤ zb
      let ra := Result.ofRawRat za a ha
      have lit : Q(ℕ) := b.appArg!
      let rb := q(IsNat.of_raw ℕ $lit)
      let rc ← NormNum.evalPow.core q($a ^ $b) q(HPow.hPow) q($a) q($b) lit rb
        q(CommSemiring.toSemiring) ra
      let ⟨zc, hc⟩ ← rc.toRatNZ
      let ⟨c, pc⟩ := rc.toRawEq
      return ⟨c, .const zc hc, pc⟩
    | .mul vxa₁ vea₁ va₂, vb =>
      let ⟨_, vc₁, pc₁⟩ ← evalMulProd sℕ vea₁ vb
      let ⟨_, vc₂, pc₂⟩ ← evalPowProd va₂ vb
      return ⟨_, .mul vxa₁ vc₁ vc₂, q(mul_pow $pc₁ $pc₂)⟩
    | _, _ => OptionT.fail
  return (← res.run).getD (evalPowProdAtom sα va vb)

-/

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

theorem coeff_one (k : ℕ) : k.rawCast = (nat_lit 1).rawCast * k := by simp

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
    return ⟨k, _, .const (RingCompute.one sℕ (u := 0)), q(coeff_one $k)⟩
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
      | none => return evalPowAtom sα (.sum .zero) vb
    | ExSum.add va .zero => -- TODO: using `.add` here takes a while to compile?
      let ⟨_, vc, pc⟩ ← evalPowProd sα va vb
      return ⟨_, vc.toSum, q(single_pow $pc)⟩
    | va =>
      -- FIXME: condition used to be k.coeff > 1. Should go back to something like this.
      let ⟨k, _, vc, pc⟩ := extractCoeff vb
      if k.natLit! > 1 then
        let ⟨_, vd, pd⟩ ← evalPow₁ va vc
        let ⟨_, ve, pe⟩ ← evalPowNat sα vd k
        return ⟨_, ve, q(pow_nat $pc $pd $pe)⟩
      else
        return evalPowAtom sα (.sum va) vb
  match vb with
  | .const zb =>
    match (RingCompute.isOne sℕ (u := 0) zb) with
    | .some pf =>
      assumeInstancesCommute
      return ⟨_, va, q(pow_one_cast_of_isNat $a _ $pf)⟩
    | .none => NotPowOne
  | vb =>
    NotPowOne

theorem pow_zero (a : R) : a ^ 0 = (nat_lit 1).rawCast + 0 := by simp

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
    let test : ExSum bt sα _ := (ExProd.const (RingCompute.one sα)).toSum
    assumeInstancesCommute
    return ⟨_,
      test
      ,
      q(pow_zero $a)⟩ --TODO: Why doesn't assumeInstancesCommute work here?
  | .add vb₁ vb₂ =>
    let ⟨_, vc₁, pc₁⟩ ← evalPow₁ sα va vb₁
    let ⟨_, vc₂, pc₂⟩ ← evalPow va vb₂
    let ⟨_, vd, pd⟩ ← evalMul sα vc₁ vc₂
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

theorem cast_pos {n : ℕ} : IsNat (a : R) n → a = n.rawCast + 0
  | ⟨e⟩ => by simp [e]

theorem cast_zero : IsNat (a : R) (nat_lit 0) → a = 0
  | ⟨e⟩ => by simp [e]

theorem cast_neg {n : ℕ} {R} [Ring R] {a : R} :
    IsInt a (.negOfNat n) → a = (Int.negOfNat n).rawCast + 0
  | ⟨e⟩ => by simp [e]

theorem cast_nnrat {n : ℕ} {d : ℕ} {R} [DivisionSemiring R] {a : R} :
    IsNNRat a n d → a = NNRat.rawCast n d + 0
  | ⟨_, e⟩ => by simp [e, div_eq_mul_inv]

theorem cast_rat {n : ℤ} {d : ℕ} {R} [DivisionRing R] {a : R} :
    IsRat a n d → a = Rat.rawCast n d + 0
  | ⟨_, e⟩ => by simp [e, div_eq_mul_inv]

theorem toProd_pf (p : (a : R) = a') :
    a = a' ^ (nat_lit 1).rawCast * (nat_lit 1).rawCast := by simp [*]
theorem atom_pf (a : R) : a = a ^ (nat_lit 1).rawCast * (nat_lit 1).rawCast + 0 := by simp
theorem atom_pf' (p : (a : R) = a') :
    a = a' ^ (nat_lit 1).rawCast * (nat_lit 1).rawCast + 0 := by simp [*]

/--
Evaluates an atom, an expression where `ring` can find no additional structure.

* `a = a ^ 1 * 1 + 0`
-/
def evalAtom (e : Q($α)) : AtomM (Result (ExSum bt sα) e) := do
  let r ← (← read).evalAtom e
  have e' : Q($α) := r.expr
  let (i, ⟨a', _⟩) ← addAtomQ e'
  let one := ExProdNat.const (RingCompute.one sℕ (u := 0))
  let ⟨_, vb, pb⟩ : Result (ExProd bt sα) _ := (ExBase.atom i (e := a')).toProd sα one
  let vc := vb.toSum
  pure ⟨_, vc, match r.proof? with
  | none =>
    have : $e =Q $e' := ⟨⟩
    q($pb ▸ atom_pf $e)
  | some (p : Q($e = $a')) =>
    q($pb ▸ atom_pf' $p)⟩

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
    match ← RingCompute.evalInv (sα := sα) czα q($dsα) c with
    | some ⟨_, vd, pd⟩ => pure ⟨_, .const vd, q($pd)⟩
    | none =>
        let ⟨_, vc, pc⟩ ← evalInvAtom sα dsα a
        let ⟨_, vc', pc'⟩ := vc.toProd _ (ExProdNat.const (RingCompute.one sℕ (u := 0)))
        -- TODO : instance issues
        pure ⟨_, vc', q($pc' ▸ toProd_pf $pc)⟩
  | .mul (x := a₁) (e := _a₂) _va₁ va₂ va₃ => do
    let ⟨_b₁, vb₁, pb₁⟩ ← evalInvAtom sα dsα a₁
    let ⟨_b₃, vb₃, pb₃⟩ ← va₃.evalInv czα
    let ⟨_b₁', vb₁', pb₁'⟩ := (vb₁.toProd _ va₂)
    let ⟨c, vc, pc⟩ ← evalMulProd sα vb₃ vb₁'
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
    let ⟨_, vb, pb⟩ ← va.evalInv sα dsα czα
    pure ⟨_, vb.toSum, (q(inv_single $pb) : Expr)⟩
  | va => do
    let ⟨_, vb, pb⟩ ← evalInvAtom sα dsα a
    let ⟨_', vb', pb'⟩ := vb.toProd _ (ExProdNat.const (RingCompute.one sℕ (u := 0)))
    assumeInstancesCommute
    -- FIXME: Instance issue
    pure ⟨_, vb'.toSum, q($pb' ▸ atom_pf' $pb)⟩

end

theorem div_pf {R} [Semifield R] {a b c d : R}
    (_ : b⁻¹ = c) (_ : a * c = d) : a / b = d := by
  subst_vars; simp [div_eq_mul_inv]

/-- Divides two polynomials `va, vb` to get a normalized result polynomial.

* `a / b = a * b⁻¹`
-/
def evalDiv {a b : Q($α)} (rα : Q(Semifield $α)) (czα : Option Q(CharZero $α))
    (va : ExSum bt sα a) (vb : ExSum bt sα b) : AtomM (Result (ExSum bt sα) q($a / $b)) := do
  let ⟨_c, vc, pc⟩ ← vb.evalInv sα rα czα
  let ⟨d, vd, pd⟩ ← evalMul sα va vc
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

/-- A precomputed `Cache` for `ℕ`. -/
def Cache.nat : Cache sℕ := { rα := none, dsα := none, czα := some q(inferInstance) }

/-- A precomputed `Cache` for `ℤ`. -/
def Cache.int : Cache sℤ :=
  { rα := some q(inferInstance), dsα := none, czα := some q(inferInstance) }

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
      pure <| some <| some (← RingCompute.derive sα e)
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

/--
Evaluates expression `e` of type `α` into a normalized representation as a polynomial.
This is the main driver of `ring`, which calls out to `evalAdd`, `evalMul` etc.
-/
partial def eval {u : Lean.Level} {α : Q(Type u)} {bt : Q($α) → Type} (sα : Q(CommSemiring $α))
    [RingCompute bt sα]
    (c : Cache sα) (e : Q($α)) : AtomM (Result (ExSum bt sα) e) := Lean.withIncRecDepth do
  let els := do
    try RingCompute.derive sα e
    catch _ => evalAtom sα e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα, c.dsα with
  | ``HAdd.hAdd, _, _ | ``Add.add, _, _ => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval sα c a
      let ⟨_, vb, pb⟩ ← eval sα c b
      let ⟨c, vc, p⟩ ← evalAdd sα va vb
      pure ⟨c, vc, q(add_congr $pa $pb $p)⟩
    | _ => els
  | ``HMul.hMul, _, _ | ``Mul.mul, _, _ => match e with
    | ~q($a * $b) =>
      let ⟨_, va, pa⟩ ← eval sα c a
      let ⟨_, vb, pb⟩ ← eval sα c b
      let ⟨c, vc, p⟩ ← evalMul sα va vb
      pure ⟨c, vc, q(mul_congr $pa $pb $p)⟩
    | _ => els
  | ``HSMul.hSMul, rα, _ => match rα, e with
    | _, ~q(@HSMul.hSMul $R $α' _ $inst $r $a) =>
      if ! (← isDefEq α α') then
        throwError "HSmul not implemented"
      -- TODO: special case Nat and Int for performance?
      have : u_2 =QL u := ⟨⟩
      have : $α =Q $α' := ⟨⟩
      have a : Q($α) := a
      let sR ← synthInstanceQ q(CommSemiring $R)
      let cR ← mkCache sR
      let ⟨_, vr, pr⟩ ← eval (bt := Ring.baseType sR) sR cR q($r)
      let ⟨_, va, pa⟩ ← eval (bt := bt) sα c q($a)
      let _ ← RingCompute.evalCast
      sorry
  --     let ⟨_, va, pa⟩ ← eval sℕ .nat a
  --     let ⟨_, vb, pb⟩ ← eval sα c b
  --     let ⟨c, vc, p⟩ ← evalNSMul sα va vb
  --     pure ⟨c, vc, q(nsmul_congr $pa $pb $p)⟩
  --   | some rα, ~q(($a : ℤ) • ($b : «$α»)) =>
  --     let ⟨_, va, pa⟩ ← eval sℤ .int a
  --     let ⟨_, vb, pb⟩ ← eval sα c b
  --     let ⟨c, vc, p⟩ ← evalZSMul sα rα va vb
  --     assumeInstancesCommute
  --     pure ⟨c, vc, q(zsmul_congr $pa $pb $p)⟩
    | _, _ => els
  | ``HPow.hPow, _, _ | ``Pow.pow, _, _ => match e with
    | ~q($a ^ $b) =>
      let ⟨_, va, pa⟩ ← eval sα c a
      let ⟨b, vb, pb⟩ ← eval (bt := btℕ) sℕ .nat b
      let ⟨b', vb'⟩ := vb.toExSumNat
      have : $b =Q $b' := ⟨⟩
      let ⟨c, vc, p⟩ ← evalPow sα va vb'
      pure ⟨c, vc, q(pow_congr $pa $pb $p)⟩
    | _ => els
  | ``Neg.neg, some rα, _ => match e with
    | ~q(-$a) =>
      let ⟨_, va, pa⟩ ← eval sα c a
      let ⟨b, vb, p⟩ ← evalNeg sα rα va
      pure ⟨b, vb, q(neg_congr $pa $p)⟩
    | _ => els
  | ``HSub.hSub, some rα, _ | ``Sub.sub, some rα, _ => match e with
    | ~q($a - $b) => do
      let ⟨_, va, pa⟩ ← eval sα c a
      let ⟨_, vb, pb⟩ ← eval sα c b
      let ⟨c, vc, p⟩ ← evalSub sα rα va vb
      pure ⟨c, vc, q(sub_congr $pa $pb $p)⟩
    | _ => els
  | ``Inv.inv, _, some dsα => match e with
    | ~q($a⁻¹) =>
      let ⟨_, va, pa⟩ ← eval sα c a
      let ⟨b, vb, p⟩ ← va.evalInv sα dsα c.czα
      pure ⟨b, vb, q(inv_congr $pa $p)⟩
    | _ => els
  | ``HDiv.hDiv, _, some dsα | ``Div.div, _, some dsα => match e with
    | ~q($a / $b) => do
      let ⟨_, va, pa⟩ ← eval sα c a
      let ⟨_, vb, pb⟩ ← eval sα c b
      let ⟨c, vc, p⟩ ← evalDiv sα dsα c.czα va vb
      pure ⟨c, vc, q(div_congr $pa $pb $p)⟩
    | _ => els
  | _, _, _ => els
end Algebra

end Mathlib.Tactic
