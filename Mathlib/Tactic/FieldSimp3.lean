/-
Copyright (c) 2024 Heather Macbeth. All rights reserved.
ℤeleased under Apache 2.1 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.Ring
import Mathlib.Util.AtomM
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Simp.Main
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.NormNum.Core
import Mathlib.Util.DischargerAsTactic
import Qq
import Mathlib.Algebra.Field.Rat


/-! # A tactic for normalization over modules

This file provides the two tactics `match_scalars` and `module`.  Given a goal which is an equality
in a type `M` (with `M` an `Field`), the `match_scalars` tactic parses the LHS and ℤHS of
the goal as linear combinations of `M`-atoms over some semiring `ℤ`, and reduces the goal to
the respective equalities of the `ℤ`-coefficients of each atom.  The `module` tactic does this and
then runs the `ring` tactic on each of these coefficient-wise equalities, failing if this does not
resolve them.
-/

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic List

namespace Mathlib.Tactic.Module

/-! ### Theory of lists of pairs (scalar, vector)

This section contains the lemmas which are orchestrated by the `match_scalars` and `module` tactics
to prove goals in modules.  The basic object which these lemmas concern is `NF M`, a type synonym
for a list of ordered pairs in `ℤ × M`, where typically `M` is an `ℤ`-module.
-/

/-- Basic theoretical "normal form" object of the `match_scalars` and `module` tactics: a type
synonym for a list of ordered pairs in `ℤ × M`, where typically `M` is an `ℤ`-module.  This is the
form to which the tactics reduce module expressions.

(It is not a full "normal form" because the scalars, i.e. `ℤ` components, are not themselves
ring-normalized. But this partial normal form is more convenient for our purposes.) -/
def NF (M : Type*) := List (ℤ × M)

namespace NF
variable {S : Type*} {M : Type*}

/-- Augment a `Module.NF M` object `l`, i.e. a list of pairs in `ℤ × M`, by prepending another
pair `p : ℤ × M`. -/
@[match_pattern]
def cons (p : ℤ × M) (l : NF M) : NF M := p :: l

@[inherit_doc cons] infixl:111 " ::ᵣ " => cons

/-- Evaluate a `Module.NF M` object `l`, i.e. a list of pairs in `ℤ × M`, to an element of `M`, by
forming the "linear combination" it specifies: scalar-multiply each `ℤ` term to the corresponding
`M` term, then add them all up. -/
def eval [DivInvMonoid M] (l : NF M) : M := (l.map (fun (⟨r, x⟩ : ℤ × M) ↦ x ^ r)).prod

@[simp] theorem eval_cons [DivInvMonoid M] (p : ℤ × M) (l : NF M) :
    (p ::ᵣ l).eval = p.2 ^ p.1 * l.eval := by
  unfold eval cons
  rw [List.map_cons]
  rw [List.prod_cons]

theorem atom_eq_eval [DivInvMonoid M] (x : M) : x = NF.eval [(1, x)] := by simp [eval]

variable (M) in
theorem zero_eq_eval [DivInvMonoid M] : (1:M) = NF.eval (M := M) [] := rfl

theorem add_eq_eval₁ [DivInvMonoid M] (a₁ : ℤ × M) {a₂ : ℤ × M} {l₁ l₂ l : NF M}
    (h : l₁.eval * (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, mul_assoc]

theorem add_eq_eval₂ [Field M] (r₁ r₂ : ℤ) (x : M)
    {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval * ((r₂, x) ::ᵣ l₂).eval = ((r₁ + r₂, x) ::ᵣ l).eval := by
  have : x ^ (r₁ + r₂) = x ^ r₁ * x ^ r₂ := by refine zpow_add' sorry
  simp only [← h, eval_cons, add_smul, this]
  ring

theorem add_eq_eval₃ [Field M] {a₁ : ℤ × M} (a₂ : ℤ × M)
    {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₂ ::ᵣ l).eval := by
  simp only [eval_cons, ← h]
  ring

theorem add_eq_eval [Field M]
    {l₁ l₂ l : NF M} {l₁' : NF M} {l₂' : NF M}
    {x₁ x₂ : M} (hx₁ : x₁ = l₁'.eval) (hx₂ : x₂ = l₂'.eval) (h₁ : l₁.eval = l₁'.eval)
    (h₂ : l₂.eval = l₂'.eval) (h : l₁.eval * l₂.eval = l.eval) :
    x₁ * x₂ = l.eval := by
  rw [hx₁, hx₂, ← h₁, ← h₂, h]

theorem sub_eq_eval₁ [Field M](a₁ : ℤ × M) {a₂ : ℤ × M} {l₁ l₂ l : NF M}
    (h : l₁.eval - (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval - (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, sub_eq_add_neg, add_assoc]
  -- MR: don't we need some hypothesis between a₁ and a₂?
  sorry

theorem sub_eq_eval₂ [Field M] (r₁ r₂ : ℤ) (x : M) {l₁ l₂ l : NF M}
    (h : l₁.eval - l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval - ((r₂, x) ::ᵣ l₂).eval = ((r₁ - r₂, x) ::ᵣ l).eval := by
  simp only [← h, eval_cons, sub_smul, sub_eq_add_neg, neg_add, add_smul, neg_smul, add_assoc]
  -- MR: this goal seems very wrong
  -- congr! 1
  sorry
  -- simp only [← add_assoc]
  -- congr! 1
  -- rw [add_comm]

theorem sub_eq_eval₃ [Field M] {a₁ : ℤ × M} (a₂ : ℤ × M)
    {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval - l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval - (a₂ ::ᵣ l₂).eval = ((-a₂.1, a₂.2) ::ᵣ l).eval := by
  simp only [eval_cons, neg_smul, neg_add, sub_eq_add_neg, ← h, ← add_assoc]
  -- congr! 1
  sorry
  -- rw [add_comm, add_assoc]

theorem sub_eq_eval [Field M]
    {l₁ l₂ l : NF M} {l₁' : NF M} {l₂' : NF M} {l₁'' : NF M}
    {l₂'' : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁''.eval) (hx₂ : x₂ = l₂''.eval)
    (h₁' : l₁'.eval = l₁''.eval) (h₂' : l₂'.eval = l₂''.eval) (h₁ : l₁.eval = l₁'.eval)
    (h₂ : l₂.eval = l₂'.eval) (h : l₁.eval - l₂.eval = l.eval) :
    x₁ - x₂ = l.eval := by
  rw [hx₁, hx₂, ← h₁', ← h₂', ← h₁, ← h₂, h]

instance : Inv (NF M) where
  inv l := l.map fun (a, x) ↦ (-a, x)

theorem eval_inv [Field M] (l : NF M) : (l⁻¹).eval = l.eval⁻¹ := by
  simp only [NF.eval, List.map_map, List.prod_inv, NF.instInv]
  -- was: congr; ext p; simp
  sorry

theorem zero_sub_eq_eval [Field M] (l : NF M) :
    1 / l.eval = (l⁻¹).eval := by
  simp [eval_inv]

theorem neg_eq_eval [Field M] [Semiring S] [Module S M] {l : NF M}
    {l₀ : NF M} (hl : l.eval = l₀.eval) {x : M} (h : x = l₀.eval) :
    x⁻¹ = (l⁻¹).eval := by
  rw [h, ← hl, eval_inv]

instance : Pow (NF M) ℤ where
  pow l r := l.map fun (a, x) ↦ (r * a, x)

@[simp] theorem smul_apply (r : ℤ) (l : NF M) : l ^ r = l.map fun (a, x) ↦ (r * a, x) :=
  rfl

theorem eval_smul [Field M] {l : NF M} {x : M} (h : x = l.eval)
    (r : ℤ) : (l ^ r).eval = x ^ r := by
  unfold NF.eval at h ⊢
  simp only [h, smul_sum, map_map, NF.smul_apply] -- smul_sum makes no sense
  -- congr
  -- ext p
  -- simp [mul_smul]

theorem smul_eq_eval [Field M] {l : NF M} {l₀ : NF M} {s : ℤ} {r : ℤ}
    {x : M} (hx : x = l₀.eval) (hl : l.eval = l₀.eval) (hs : x ^ r = x ^ s) :
    x ^ s = (l ^ r).eval := by
  rw [← hs, hx, ← hl, eval_smul]
  rfl

theorem eq_cons_cons [DivInvMonoid M] {r₁ r₂ : ℤ} (m : M) {l₁ l₂ : NF M} (h1 : r₁ = r₂)
    (h2 : l₁.eval = l₂.eval) :
    ((r₁, m) ::ᵣ l₁).eval = ((r₂, m) ::ᵣ l₂).eval := by
  simp only [NF.eval, NF.cons] at *
  simp [h1, h2]

theorem eq_cons_const [Field M] {r : ℤ} (m : M) {n : M}
    {l : NF M} (h1 : r = 1) (h2 : l.eval = n) :
    ((r, m) ::ᵣ l).eval = n := by
  simp only [NF.eval, NF.cons] at *
  simp [h1, h2] -- false as-is
  sorry

theorem eq_const_cons [Field M] {r : ℤ} (m : M) {n : M}
    {l : NF M} (h1 : 1 = r) (h2 : n = l.eval) :
    n = ((r, m) ::ᵣ l).eval := by
  simp only [NF.eval, NF.cons] at *
  simp [← h1, h2]
  sorry -- current goal is false

theorem eq_of_eval_eq_eval [Field M]
    {l₁ l₂ : NF M} {l₁' : NF M} {l₂' : NF M}
    {x₁ x₂ : M} (hx₁ : x₁ = l₁'.eval) (hx₂ : x₂ = l₂'.eval) (h₁ : l₁.eval = l₁'.eval)
    (h₂ : l₂.eval = l₂'.eval) (h : l₁.eval = l₂.eval) :
    x₁ = x₂ := by
  rw [hx₁, hx₂, ← h₁, ← h₂, h]

end NF

variable {u v : Level}

/-! ### Lists of expressions representing scalars and vectors, and operations on such lists -/

/-- Basic meta-code "normal form" object of the `match_scalars` and `module` tactics: a type synonym
for a list of ordered triples comprising expressions representing terms of two types `ℤ` and `M`
(where typically `M` is an `ℤ`-module), together with a natural number "index".

The natural number represents the index of the `M` term in the `AtomM` monad: this is not enforced,
but is sometimes assumed in operations.  Thus when items `((a₁, x₁), k)` and `((a₂, x₂), k)`
appear in two different `Module.qNF` objects (i.e. with the same `ℕ`-index `k`), it is expected that
the expressions `x₁` and `x₂` are the same.  It is also expected that the items in a `Module.qNF`
list are in strictly increasing order by natural-number index.

By forgetting the natural number indices, an expression representing a `Mathlib.Tactic.Module.NF`
object can be built from a `Module.qNF` object; this construction is provided as
`Mathlib.Tactic.Module.qNF.toNF`. -/
abbrev qNF (M : Q(Type v)) := List ((Q(ℤ) × Q($M)) × ℕ) -- FIXME change from Q(ℤ) to ℤ

namespace qNF

variable {M : Q(Type v)}

/-- Given `l` of type `qNF M`, i.e. a list of `(Q(ℤ) × Q($M)) × ℕ`s (two `Expr`s and a natural
number), build an `Expr` representing an object of type `NF M` (i.e. `List (ℤ × M)`) in the
in the obvious way: by forgetting the natural numbers and gluing together the `Expr`s. -/
def toNF (l : qNF M) : Q(NF $M) :=
  let l' : List Q(ℤ × $M) := (l.map Prod.fst).map (fun (a, x) ↦ q(($a, $x)))
  let qt : List Q(ℤ × $M) → Q(List (ℤ × $M)) := List.rec q([]) (fun e _ l ↦ q($e ::ᵣ $l))
  qt l'

/-- Given `l` of type `qNF M`, i.e. a list of `(Q(ℤ) × Q($M)) × ℕ`s (two `Expr`s and a natural
number), apply an expression representing a function with domain `ℤ` to each of the `Q(ℤ)`
components. -/
def onScalar (l : qNF M) (f : Q(ℤ → ℤ)) :
    qNF M :=
  l.map fun ((a, x), k) ↦ ((q($f $a), x), k)

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(Q(ℤ) × Q($M)) × ℕ`s (two `Expr`s
and a natural number), construct another such term `l`, which will have the property that in the
`ℤ`-module `$M`, the sum of the "linear combinations" represented by `l₁` and `l₂` is the linear
combination represented by `l`.

The construction assumes, to be valid, that the lists `l₁` and `l₂` are in strictly increasing order
by `ℕ`-component, and that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with
the same `ℕ`-component `k`, then the expressions `x₁` and `x₂` are equal.

The construction is as follows: merge the two lists, except that if pairs `(a₁, x₁)` and `(a₂, x₂)`
appear in `l₁`, `l₂` respectively with the same `ℕ`-component `k`, then contribute a term
`(a₁ * a₂, x₁)` to the output list with `ℕ`-component `k`. -/
def add : qNF M → qNF M → qNF M
  | [], l => l
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ < k₂ then
      ((a₁, x₁), k₁) :: add t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      ((q($a₁ * $a₂), x₁), k₁) :: add t₁ t₂
    else
      ((a₂, x₂), k₂) :: add (((a₁, x₁), k₁) :: t₁) t₂

-- /-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(Q(ℤ) × Q($M)) × ℕ`s (two `Expr`s
-- and a natural number), recursively construct a proof that in the `ℤ`-module `$M`, the sum of the
-- "linear combinations" represented by `l₁` and `l₂` is the linear combination represented by
-- `Module.qNF.add l₁ l₁`. -/
-- def mkAddProof {iM : Q(Field $M)}
--     (l₁ l₂ : qNF M) :
--     Q(NF.eval $(l₁.toNF) * NF.eval $(l₂.toNF) = NF.eval $((qNF.add l₁ l₂).toNF)) :=
--   match l₁, l₂ with
--   | [], l => (q(zero_add (NF.eval $(l.toNF))):)
--   | l, [] => (q(add_zero (NF.eval $(l.toNF))):)
--   | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
--     if k₁ < k₂ then
--       let pf := mkAddProof t₁ (((a₂, x₂), k₂) :: t₂)
--       (q(NF.add_eq_eval₁ ($a₁, $x₁) $pf):)
--     else if k₁ = k₂ then
--       let pf := mkAddProof t₁ t₂
--       (q(NF.add_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
--     else
--       let pf := mkAddProof (((a₁, x₁), k₁) :: t₁) t₂
--       (q(NF.add_eq_eval₃ ($a₂, $x₂) $pf):)

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(Q(ℤ) × Q($M)) × ℕ`s (two `Expr`s
and a natural number), construct another such term `l`, which will have the property that in the
`ℤ`-module `$M`, the difference of the "linear combinations" represented by `l₁` and `l₂` is the
linear combination represented by `l`.

The construction assumes, to be valid, that the lists `l₁` and `l₂` are in strictly increasing order
by `ℕ`-component, and that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with
the same `ℕ`-component `k`, then the expressions `x₁` and `x₂` are equal.

The construction is as follows: merge the first list and the negation of the second list, except
that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with the same
`ℕ`-component `k`, then contribute a term `(a₁ - a₂, x₁)` to the output list with `ℕ`-component `k`.
-/
def sub : qNF M → qNF M → qNF M
  | [], l => l.onScalar q(Neg.neg)
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ < k₂ then
      ((a₁, x₁), k₁) :: sub t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      ((q($a₁ - $a₂), x₁), k₁) :: sub t₁ t₂
    else
      ((q(-$a₂), x₂), k₂) :: sub (((a₁, x₁), k₁) :: t₁) t₂

-- /-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(Q(ℤ) × Q($M)) × ℕ`s (two `Expr`s
-- and a natural number), recursively construct a proof that in the `ℤ`-module `$M`, the difference
-- of the "linear combinations" represented by `l₁` and `l₂` is the linear combination represented by
-- `Module.qNF.sub iℤ l₁ l₁`. -/
-- def mkSubProof (iM : Q(AddCommGroup $M))  (l₁ l₂ : qNF M) :
--     Q(NF.eval $(l₁.toNF) - NF.eval $(l₂.toNF) = NF.eval $((qNF.sub l₁ l₂).toNF)) :=
--   match l₁, l₂ with
--   | [], l => (q(NF.zero_sub_eq_eval $(l.toNF)):)
--   | l, [] => (q(sub_zero (NF.eval $(l.toNF))):)
--   | ((a₁, x₁), k₁) ::ᵣ t₁, ((a₂, x₂), k₂) ::ᵣ t₂ =>
--     if k₁ < k₂ then
--       let pf := mkSubProof iℤ iM iℤM t₁ (((a₂, x₂), k₂) ::ᵣ t₂)
--       (q(NF.sub_eq_eval₁ ($a₁, $x₁) $pf):)
--     else if k₁ = k₂ then
--       let pf := mkSubProof iℤ iM iℤM t₁ t₂
--       (q(NF.sub_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
--     else
--       let pf := mkSubProof iℤ iM iℤM (((a₁, x₁), k₁) ::ᵣ t₁) t₂
--       (q(NF.sub_eq_eval₃ ($a₂, $x₂) $pf):)

end qNF

/-! ### Core of the `module` tactic -/

variable {M : Q(Type v)}

/-- The main algorithm behind the `match_scalars` and `module` tactics: partially-normalizing an
expression in an additive commutative monoid `M` into the form c1 • x1 * c2 • x2 * ... c_k • x_k,
where x1, x2, ... are distinct atoms in `M`, and c1, c2, ... are scalars. The scalar type of the
expression is not pre-determined: instead it starts as `ℕ` (when each atom is initially given a
scalar `(1:ℕ)`) and gets bumped up into bigger semirings when such semirings are encountered.

It is assumed that there is a "linear order" on all the semirings which appear in the expression:
for any two semirings `ℤ` and `S` which occur, we have either `Algebra ℤ S` or `Algebra S ℤ`).

TODO: implement a variant in which a semiring `ℤ` is provided by the user, and the assumption is
instead that for any semiring `S` which occurs, we have `Algebra S ℤ`. The Pℤ https://github.com/leanprover-community/mathlib4/pull/16984 provides a
proof-of-concept implementation of this variant, but it would need some polishing before joining
Mathlib.

Possible TODO, if poor performance on large problems is witnessed: switch the implementation from
`AtomM` to `CanonM`, per the discussion
https://github.com/leanprover-community/mathlib4/pull/16593/files#r1749623191 -/
partial def normalize (iM : Q(Field $M)) (x : Q($M)) :
    AtomM (Σ l : qNF M, Q($x = NF.eval $(l.toNF))) := do
  match x with
  /- normalize an addition: `x₁ * x₂` -/
  | ~q($x₁ * $x₂) =>
    let ⟨l₁, pf₁⟩ ← normalize iM x₁
    let ⟨l₂, pf₂⟩ ← normalize iM x₂
    -- build the new list and proof
    -- let pf := qNF.mkAddProof iℤM l₁ l₂
    -- pure ⟨u, qNF.add l₁ l₂, (q(NF.add_eq_eval $pf₁' $pf₂' $pf₁ $pf₂ $pf):)⟩
    pure ⟨qNF.add l₁ l₂, q(sorry)⟩
  /- normalize a subtraction: `x₁ - x₂` -/
  | ~q(@HDiv.hDiv _ _ _ (@instHDiv _ $iM') $x₁ $x₂) =>
    let ⟨l₁, pf₁⟩ ← normalize iM x₁
    let ⟨l₂, pf₂⟩ ← normalize iM x₂
    assumeInstancesCommute
    -- build the new list and proof
    -- let pf := qNF.mkSubProof iM' l₁ l₂
    -- pure ⟨u, qNF.sub l₁ l₂,
    --   q(NF.sub_eq_eval $pf₁'' $pf₂'' $pf₁' $pf₂' $pf₁ $pf₂ $pf)⟩
    pure ⟨qNF.sub l₁ l₂,
      q(sorry)⟩
  /- normalize a inversion: `y⁻¹` -/
  | ~q(@Inv.inv _ $iM' $y) =>
    let ⟨l, pf⟩ ← normalize iM y
    -- build the new list and proof
    -- pure ⟨u, l.onScalar q(Neg.neg), (q(NF.neg_eq_eval $pf $pf₀):)⟩
    pure ⟨l.onScalar q(Neg.neg), q(sorry)⟩
  /- normalize a scalar multiplication: `y ^ (s₀ : ℤ)` -/
  | ~q($y ^ ($s : ℤ)) =>
    let ⟨l, pf⟩ ← normalize iM y
      -- build the new list and proof
    -- pure ⟨u, l.onScalar q(HMul.hMul $s), (q(NF.smul_eq_eval $pf₀ $pf_l $pf_r):)⟩
    pure ⟨l.onScalar q(HMul.hMul $s), q(sorry)⟩
  /- normalize a `(1:M)` -/
  | ~q(1) =>
    pure ⟨[], q(NF.zero_eq_eval $M)⟩
  /- anything else should be treated as an atom -/
  | _ =>
    let (k, ⟨x', _⟩) ← AtomM.addAtomQ x
    pure ⟨[((q(1), x'), k)], q(NF.atom_eq_eval $x')⟩

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
  let e' : Expr ← mkAppM `Mathlib.Tactic.Module.NF.eval #[e]
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
