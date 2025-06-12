/-
Copyright (c) 2024 Heather Macbeth. All rights reserved.
ℤeleased under Apache 2.1 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.NormNum.Core
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring
import Mathlib.Util.AtomM
import Mathlib.Util.DischargerAsTactic
import Qq
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Simp.Main


/-! # A tactic for clearing denominators in fields

-/

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic List

namespace Mathlib.Tactic.FieldSimp

/-! ### Theory of lists of pairs (exponent, atom)

This section contains the lemmas which are orchestrated by the `field_simp` tactic
to prove goals in fields.  The basic object which these lemmas concern is `NF M`, a type synonym
for a list of ordered pairs in `ℤ × M`, where typically `M` is a field.
-/

/-- Basic theoretical "normal form" object of the `field_simp` tactic: a type
synonym for a list of ordered pairs in `ℤ × M`, where typically `M` is a field.  This is the
form to which the tactics reduce field expressions. -/
def NF (M : Type*) := List (ℤ × M)

namespace NF
variable {S : Type*} {M : Type*}

/-- Augment a `FieldSimp.NF M` object `l`, i.e. a list of pairs in `ℤ × M`, by prepending another
pair `p : ℤ × M`. -/
@[match_pattern]
def cons (p : ℤ × M) (l : NF M) : NF M := p :: l

@[inherit_doc cons] infixl:111 " ::ᵣ " => cons

/-- Evaluate a `FieldSimp.NF M` object `l`, i.e. a list of pairs in `ℤ × M`, to an element of `M`,
by forming the "multiplicative linear combination" it specifies: raise each `M` term to the power of
the corresponding `ℤ` term, then multiply them all together. -/
def eval [DivInvMonoid M] (l : NF M) : M := (l.map (fun (⟨r, x⟩ : ℤ × M) ↦ x ^ r)).prod

@[simp] theorem eval_cons [DivInvMonoid M] (p : ℤ × M) (l : NF M) :
    (p ::ᵣ l).eval = p.2 ^ p.1 * l.eval := by
  unfold eval cons
  rw [List.map_cons]
  rw [List.prod_cons]

theorem atom_eq_eval [DivInvMonoid M] (x : M) : x = NF.eval [(1, x)] := by simp [eval]

variable (M) in
theorem one_eq_eval [DivInvMonoid M] : (1:M) = NF.eval (M := M) [] := rfl

theorem mul_eq_eval₁ [DivInvMonoid M] (a₁ : ℤ × M) {a₂ : ℤ × M} {l₁ l₂ l : NF M}
    (h : l₁.eval * (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, mul_assoc]

theorem mul_eq_eval₂ [Field M] (r₁ r₂ : ℤ) (x : M) (hx : x ≠ 0)
    {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval * ((r₂, x) ::ᵣ l₂).eval = ((r₁ + r₂, x) ::ᵣ l).eval := by
  simp only [← h, eval_cons, zpow_add₀ hx, mul_assoc]
  congr! 1
  simp only [← mul_assoc]
  congr! 1
  rw [mul_comm]

theorem mul_eq_eval₃ [Field M] {a₁ : ℤ × M} (a₂ : ℤ × M)
    {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₂ ::ᵣ l).eval := by
  simp only [eval_cons, ← h]
  ring

theorem mul_eq_eval [Field M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
    (hx₂ : x₂ = l₂.eval) (h : l₁.eval * l₂.eval = l.eval) :
    x₁ * x₂ = l.eval := by
  rw [hx₁, hx₂, h]

theorem div_eq_eval₁ [Field M](a₁ : ℤ × M) {a₂ : ℤ × M} {l₁ l₂ l : NF M}
    (h : l₁.eval / (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval / (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, div_eq_mul_inv, mul_assoc]

theorem div_eq_eval₂ [Field M] (r₁ r₂ : ℤ) (x : M) (hx : x ≠ 0) {l₁ l₂ l : NF M}
    (h : l₁.eval / l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval / ((r₂, x) ::ᵣ l₂).eval = ((r₁ - r₂, x) ::ᵣ l).eval := by
  simp only [← h, eval_cons, zpow_sub₀ hx, div_eq_mul_inv, mul_inv, mul_zpow, zpow_neg, mul_assoc]
  congr! 1
  simp only [← mul_assoc]
  congr! 1
  rw [mul_comm]

theorem div_eq_eval₃ [Field M] {a₁ : ℤ × M} (a₂ : ℤ × M) {l₁ l₂ l : NF M}
    (h : (a₁ ::ᵣ l₁).eval / l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval / (a₂ ::ᵣ l₂).eval = ((-a₂.1, a₂.2) ::ᵣ l).eval := by
  simp only [eval_cons, zpow_neg, mul_inv, div_eq_mul_inv, ← h, ← mul_assoc]
  congr! 1
  rw [mul_comm, mul_assoc]

theorem div_eq_eval [Field M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval)
    (h : l₁.eval / l₂.eval = l.eval) :
    x₁ / x₂ = l.eval := by
  rw [hx₁, hx₂, h]

instance : Inv (NF M) where
  inv l := l.map fun (a, x) ↦ (-a, x)

-- generalize library `List.prod_inv`
theorem _root_.List.prod_inv₀ {K : Type*} [DivisionCommMonoid K] :
    ∀ (L : List K), L.prod⁻¹ = (map (fun x ↦ x⁻¹) L).prod
  | [] => by simp
  | x :: xs => by simp [mul_comm, prod_inv₀ xs]

theorem eval_inv [Field M] (l : NF M) : (l⁻¹).eval = l.eval⁻¹ := by
  simp only [NF.eval, List.map_map, List.prod_inv₀, NF.instInv]
  congr
  ext p
  simp

theorem zero_div_eq_eval [Field M] (l : NF M) : 1 / l.eval = (l⁻¹).eval := by
  simp [eval_inv]

theorem inv_eq_eval [Field M] {l : NF M} {x : M} (h : x = l.eval) :
    x⁻¹ = (l⁻¹).eval := by
  rw [h, eval_inv]

instance : Pow (NF M) ℤ where
  pow l r := l.map fun (a, x) ↦ (r * a, x)

@[simp] theorem zpow_apply (r : ℤ) (l : NF M) : l ^ r = l.map fun (a, x) ↦ (r * a, x) :=
  rfl

-- in the library somewhere?
theorem _root_.List.prod_zpow {β : Type*} [DivisionCommMonoid β] {r : ℤ} {l : List β} :
    l.prod ^ r = (map (fun x ↦ x ^ r) l).prod :=
  let fr : β →* β := ⟨⟨fun b ↦ b ^ r, one_zpow r⟩, (mul_zpow · · r)⟩
  map_list_prod fr l

theorem eval_zpow [Field M] {l : NF M} {x : M} (h : x = l.eval) (r : ℤ) : (l ^ r).eval = x ^ r := by
  unfold NF.eval at h ⊢
  simp only [h, prod_zpow, map_map, NF.zpow_apply]
  congr
  ext p
  simp [← zpow_mul, mul_comm]

theorem zpow_eq_eval [Field M] {l : NF M} (r : ℤ) {x : M} (hx : x = l.eval) :
    x ^ r = (l ^ r).eval := by
  rw [hx, eval_zpow]
  rfl

theorem eq_cons_cons [DivInvMonoid M] {r₁ r₂ : ℤ} (m : M) {l₁ l₂ : NF M} (h1 : r₁ = r₂)
    (h2 : l₁.eval = l₂.eval) :
    ((r₁, m) ::ᵣ l₁).eval = ((r₂, m) ::ᵣ l₂).eval := by
  simp only [NF.eval, NF.cons] at *
  simp [h1, h2]

theorem eq_cons_const [Field M] {r : ℤ} (m : M) {n : M}
    {l : NF M} (h1 : r = 0) (h2 : l.eval = n) :
    ((r, m) ::ᵣ l).eval = n := by
  simp only [NF.eval, NF.cons] at *
  simp [h1, h2]

theorem eq_const_cons [Field M] {r : ℤ} (m : M) {n : M}
    {l : NF M} (h1 : 0 = r) (h2 : n = l.eval) :
    n = ((r, m) ::ᵣ l).eval := by
  simp only [NF.eval, NF.cons] at *
  simp [← h1, h2]

end NF

variable {u v : Level}

/-! ### Lists of expressions representing exponents and atoms, and operations on such lists -/

/-- Basic meta-code "normal form" object of the `field_simp` tactic: a type synonym
for a list of ordered triples comprising an expression representing a term of a type `M` (where
typically `M` is a field), together with an integer "power" and a natural number "index".

The natural number represents the index of the `M` term in the `AtomM` monad: this is not enforced,
but is sometimes assumed in operations.  Thus when items `((a₁, x₁), k)` and `((a₂, x₂), k)`
appear in two different `FieldSimp.qNF` objects (i.e. with the same `ℕ`-index `k`), it is expected
that the expressions `x₁` and `x₂` are the same.  It is also expected that the items in a
`FieldSimp.qNF` list are in strictly increasing order by natural-number index.

By forgetting the natural number indices, an expression representing a `Mathlib.Tactic.FieldSimp.NF`
object can be built from a `FieldSimp.qNF` object; this construction is provided as
`Mathlib.Tactic.FieldSimp.qNF.toNF`. -/
abbrev qNF (M : Q(Type v)) := List ((ℤ × Q($M)) × ℕ)

namespace qNF

variable {M : Q(Type v)}

/-- Given `l` of type `qNF M`, i.e. a list of `(ℤ × Q($M)) × ℕ`s (two `Expr`s and a natural
number), build an `Expr` representing an object of type `NF M` (i.e. `List (ℤ × M)`) in the
in the obvious way: by forgetting the natural numbers and gluing together the integers and `Expr`s.
-/
def toNF (l : qNF M) : Q(NF $M) :=
  let l' : List Q(ℤ × $M) := (l.map Prod.fst).map (fun (a, x) ↦ q(($a, $x)))
  let qt : List Q(ℤ × $M) → Q(List (ℤ × $M)) := List.rec q([]) (fun e _ l ↦ q($e ::ᵣ $l))
  qt l'

/-- Given `l` of type `qNF M`, i.e. a list of `(ℤ × Q($M)) × ℕ`s (two `Expr`s and a natural
number), apply an expression representing a function with domain `ℤ` to each of the `Q(ℤ)`
components. -/
def onExponent (l : qNF M) (f : ℤ → ℤ) : qNF M :=
  l.map fun ((a, x), k) ↦ ((f a, x), k)

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), construct another such term `l`, which will have the property that in
the field `$M`, the product of the "multiplicative linear combinations" represented by `l₁` and
`l₂` is the multiplicative linear combination represented by `l`.

The construction assumes, to be valid, that the lists `l₁` and `l₂` are in strictly increasing order
by `ℕ`-component, and that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with
the same `ℕ`-component `k`, then the expressions `x₁` and `x₂` are equal.

The construction is as follows: merge the two lists, except that if pairs `(a₁, x₁)` and `(a₂, x₂)`
appear in `l₁`, `l₂` respectively with the same `ℕ`-component `k`, then contribute a term
`(a₁ + a₂, x₁)` to the output list with `ℕ`-component `k`. -/
def mul : qNF M → qNF M → qNF M
  | [], l => l
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ < k₂ then
      ((a₁, x₁), k₁) :: mul t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      ((a₁ + a₂, x₁), k₁) :: mul t₁ t₂
    else
      ((a₂, x₂), k₂) :: mul (((a₁, x₁), k₁) :: t₁) t₂

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), recursively construct a proof that in the field `$M`, the product of
the "multiplicative linear combinations" represented by `l₁` and `l₂` is the multiplicative linear
combination represented by `FieldSimp.qNF.mul l₁ l₁`. -/
def mkMulProof (iM : Q(Field $M)) (l₁ l₂ : qNF M) :
    Q((NF.eval $(l₁.toNF)) * NF.eval $(l₂.toNF) = NF.eval $((qNF.mul l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(one_mul (NF.eval $(l.toNF))):)
  | l, [] => (q(mul_one (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ < k₂ then
      let pf := mkMulProof iM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.mul_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkMulProof iM t₁ t₂
      let hx₁ : Q($x₁ ≠ 0) := q(sorry) -- FIXME we won't have this in general, need a case split on
      -- signs of `k₁` and `k₂`
      (q(NF.mul_eq_eval₂ $a₁ $a₂ $x₁ $hx₁ $pf):)
    else
      let pf := mkMulProof iM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.mul_eq_eval₃ ($a₂, $x₂) $pf):)

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), construct another such term `l`, which will have the property that in
the field `$M`, the quotient of the "multiplicative linear combinations" represented by `l₁` and
`l₂` is the multiplicative linear combination represented by `l`.

The construction assumes, to be valid, that the lists `l₁` and `l₂` are in strictly increasing order
by `ℕ`-component, and that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with
the same `ℕ`-component `k`, then the expressions `x₁` and `x₂` are equal.

The construction is as follows: merge the first list and the negation of the second list, except
that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with the same
`ℕ`-component `k`, then contribute a term `(a₁ - a₂, x₁)` to the output list with `ℕ`-component `k`.
-/
def div : qNF M → qNF M → qNF M
  | [], l => l.onExponent Neg.neg
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ < k₂ then
      ((a₁, x₁), k₁) :: div t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      ((a₁ - a₂, x₁), k₁) :: div t₁ t₂
    else
      ((-a₂, x₂), k₂) :: div (((a₁, x₁), k₁) :: t₁) t₂

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), recursively construct a proof that in the field `$M`, the quotient
of the "multiplicative linear combinations" represented by `l₁` and `l₂` is the multiplicative
linear combination represented by `FieldSimp.qNF.div l₁ l₁`. -/
def mkDivProof (iM : Q(Field $M)) (l₁ l₂ : qNF M) :
    Q(NF.eval $(l₁.toNF) / NF.eval $(l₂.toNF) = NF.eval $((qNF.div l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(NF.zero_div_eq_eval $(l.toNF)):)
  | l, [] => (q(div_zero (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ < k₂ then
      let pf := mkDivProof iM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.div_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkDivProof iM t₁ t₂
      let hx₁ : Q($x₁ ≠ 0) := q(sorry) -- FIXME we won't have this in general, need a case split on
      -- signs of `k₁` and `k₂`
      (q(NF.div_eq_eval₂ $a₁ $a₂ $x₁ $hx₁ $pf):)
    else
      let pf := mkDivProof iM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.div_eq_eval₃ ($a₂, $x₂) $pf):)

end qNF

/-! ### Core of the `field_simp` tactic -/

variable {M : Q(Type v)}

/-- The main algorithm behind the `field_simp` tactic: partially-normalizing an
expression in a field `M` into the form x1 ^ c1 * x2 ^ c2 * ... x_k ^ c_k,
where x1, x2, ... are distinct atoms in `M`, and c1, c2, ... are integers.

Possible TODO, if poor performance on large problems is witnessed: switch the implementation from
`AtomM` to `CanonM`, per the discussion
https://github.com/leanprover-community/mathlib4/pull/16593/files#r1749623191 -/
partial def normalize (iM : Q(Field $M)) (x : Q($M)) :
    AtomM (Σ l : qNF M, Q($x = NF.eval $(l.toNF))) := do
  match x with
  /- normalize a multiplication: `x₁ * x₂` -/
  | ~q($x₁ * $x₂) =>
    let ⟨l₁, pf₁⟩ ← normalize iM x₁
    let ⟨l₂, pf₂⟩ ← normalize iM x₂
    -- build the new list and proof
    let pf := qNF.mkMulProof iM l₁ l₂
    pure ⟨qNF.mul l₁ l₂, (q(NF.mul_eq_eval $pf₁ $pf₂ $pf):)⟩
  /- normalize a division: `x₁ - x₂` -/
  | ~q($x₁ / $x₂) =>
    let ⟨l₁, pf₁⟩ ← normalize iM x₁
    let ⟨l₂, pf₂⟩ ← normalize iM x₂
    -- build the new list and proof
    let pf := qNF.mkDivProof iM l₁ l₂
    pure ⟨qNF.div l₁ l₂, (q(NF.div_eq_eval $pf₁ $pf₂ $pf):)⟩
  /- normalize a inversion: `y⁻¹` -/
  | ~q($y⁻¹) =>
    let ⟨l, pf⟩ ← normalize iM y
    -- build the new list and proof
    pure ⟨l.onExponent Neg.neg, (q(NF.inv_eq_eval $pf):)⟩
  /- normalize an integer exponentiation: `y ^ (s : ℤ)` -/
  | ~q($y ^ ($s : ℤ)) =>
    let ⟨l, pf⟩ ← normalize iM y
    let some s := Expr.int? s | throwError "foo" -- treat as atom in this case
    -- build the new list and proof
    pure ⟨l.onExponent (HMul.hMul s), (q(NF.zpow_eq_eval $s $pf):)⟩
  /- normalize a `(1:M)` -/
  | ~q(1) =>
    pure ⟨[], q(NF.one_eq_eval $M)⟩
  /- anything else should be treated as an atom -/
  | _ =>
    let (k, ⟨x', _⟩) ← AtomM.addAtomQ x
    pure ⟨[((1, x'), k)], q(NF.atom_eq_eval $x')⟩

open Elab Tactic

-- Copy-pasted from https://github.com/hrmacbeth/metaprogramming/blob/main/Metaprogramming/Abel/Phase2_ConvProofs.lean

/-- Conv tactic for field_simp normalisation.
Wraps the `MetaM` normalization function `normalize`. -/
elab "field_simp2" : conv => do
  -- find the expression `x` to `conv` on
  let x ← Conv.getLhs
  -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
  let pf : Q((3:ℕ) = 3) := q(sorry)
  let ⟨u, K, _⟩ ← inferTypeQ' x
  -- find a `Field` instance on `K`
  let iK : Q(Field $K) ← synthInstanceQ q(Field $K)
  -- run the core normalization function `normalize` on `x`, relative to the atoms
  let ⟨l, pf⟩ ← AtomM.run .reducible <| normalize iK x
  let e : Expr := l.toNF
  let e' : Expr ← mkAppM `Mathlib.Tactic.FieldSimp.NF.eval #[e]
  -- convert `x` to the output of the normalization
  Conv.applySimpResult { expr := e', proof? := some pf }

variable {x y : ℚ}

/-- info: NF.eval [] -/
#guard_msgs in
#conv field_simp2 => (1 : ℚ)

/-- info: ((1, x) ::ᵣ []).eval -/
#guard_msgs in
#conv field_simp2 => (x)

/-- info: ((1, x + y) ::ᵣ []).eval -/
#guard_msgs in
#conv field_simp2 => (x + y)

/-- info: ((1, x) ::ᵣ ((1, y) ::ᵣ [])).eval -/
#guard_msgs in
#conv field_simp2 => (x * y)

/-- info: ((1, x) ::ᵣ ((-1, y) ::ᵣ [])).eval -/
#guard_msgs in
#conv field_simp2 => x / y

#conv field_simp2 => (x / (x + 1) + y / (y + 1))
