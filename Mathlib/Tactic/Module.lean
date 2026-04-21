/-
Copyright (c) 2024 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Tactic.Ring
public import Mathlib.Util.AtomM
public meta import Mathlib.Algebra.Algebra.Defs

/-! # A tactic for normalization over modules

This file provides the two tactics `match_scalars` and `module`.  Given a goal which is an equality
in a type `M` (with `M` an `AddCommMonoid`), the `match_scalars` tactic parses the LHS and RHS of
the goal as linear combinations of `M`-atoms over some semiring `R`, and reduces the goal to
the respective equalities of the `R`-coefficients of each atom.  The `module` tactic does this and
then runs the `ring` tactic on each of these coefficient-wise equalities, failing if this does not
resolve them.

The scalar type `R` is not pre-determined: instead it starts as `ℕ` (when each atom is initially
given a scalar `(1:ℕ)`) and gets bumped up into bigger semirings when such semirings are
encountered.  However, to permit this, it is assumed that there is a "linear order" on all the
semirings which appear in the expression: for any two semirings `R` and `S` which occur, we have
either `Algebra R S` or `Algebra S R`.
-/
set_option backward.defeqAttrib.useBackward true

public meta section

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic List

namespace Mathlib.Tactic.Module

@[expose] section

/-! ### Theory of lists of pairs (scalar, vector)

This section contains the lemmas which are orchestrated by the `match_scalars` and `module` tactics
to prove goals in modules.  The basic object which these lemmas concern is `NF R M`, a type synonym
for a list of ordered pairs in `R × M`, where typically `M` is an `R`-module.
-/

/-- Basic theoretical "normal form" object of the `match_scalars` and `module` tactics: a type
synonym for a list of ordered pairs in `R × M`, where typically `M` is an `R`-module.  This is the
form to which the tactics reduce module expressions.

(It is not a full "normal form" because the scalars, i.e. `R` components, are not themselves
ring-normalized. But this partial normal form is more convenient for our purposes.) -/
def NF (R : Type*) (M : Type*) := List (R × M)

namespace NF
variable {S : Type*} {R : Type*} {M : Type*}

/-- Augment a `Module.NF R M` object `l`, i.e. a list of pairs in `R × M`, by prepending another
pair `p : R × M`. -/
@[match_pattern]
def cons (p : R × M) (l : NF R M) : NF R M := p :: l

@[inherit_doc cons] infixl:100 " ::ᵣ " => cons

/-- Evaluate a `Module.NF R M` object `l`, i.e. a list of pairs in `R × M`, to an element of `M`, by
forming the "linear combination" it specifies: scalar-multiply each `R` term to the corresponding
`M` term, then add them all up. -/
def eval [Add M] [Zero M] [SMul R M] (l : NF R M) : M := (l.map (fun (⟨r, x⟩ : R × M) ↦ r • x)).sum

@[simp] theorem eval_cons [AddMonoid M] [SMul R M] (p : R × M) (l : NF R M) :
    (p ::ᵣ l).eval = p.1 • p.2 + l.eval := by
  rfl

theorem atom_eq_eval [AddMonoid M] (x : M) : x = NF.eval [(1, x)] := by simp [eval]

variable (M) in
theorem zero_eq_eval [AddMonoid M] : (0:M) = NF.eval (R := ℕ) (M := M) [] := rfl

theorem add_eq_eval₁ [AddMonoid M] [SMul R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M}
    (h : l₁.eval + (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval + (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, add_assoc]

theorem add_eq_eval₂ [Semiring R] [AddCommMonoid M] [Module R M] (r₁ r₂ : R) (x : M)
    {l₁ l₂ l : NF R M} (h : l₁.eval + l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval + ((r₂, x) ::ᵣ l₂).eval = ((r₁ + r₂, x) ::ᵣ l).eval := by
  simp only [← h, eval_cons, add_smul, add_assoc]
  congr! 1
  simp only [← add_assoc]
  congr! 1
  rw [add_comm]

theorem add_eq_eval₃ [Semiring R] [AddCommMonoid M] [Module R M] {a₁ : R × M} (a₂ : R × M)
    {l₁ l₂ l : NF R M} (h : (a₁ ::ᵣ l₁).eval + l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval + (a₂ ::ᵣ l₂).eval = (a₂ ::ᵣ l).eval := by
  simp only [eval_cons, ← h]
  nth_rw 4 [add_comm]
  simp only [add_assoc]
  congr! 2
  rw [add_comm]

theorem add_eq_eval {R₁ R₂ : Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁]
    [Module R₁ M] [Semiring R₂] [Module R₂ M] {l₁ l₂ l : NF R M} {l₁' : NF R₁ M} {l₂' : NF R₂ M}
    {x₁ x₂ : M} (hx₁ : x₁ = l₁'.eval) (hx₂ : x₂ = l₂'.eval) (h₁ : l₁.eval = l₁'.eval)
    (h₂ : l₂.eval = l₂'.eval) (h : l₁.eval + l₂.eval = l.eval) :
    x₁ + x₂ = l.eval := by
  rw [hx₁, hx₂, ← h₁, ← h₂, h]

theorem sub_eq_eval₁ [SMul R M] [AddGroup M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M}
    (h : l₁.eval - (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval - (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, sub_eq_add_neg, add_assoc]

theorem sub_eq_eval₂ [Ring R] [AddCommGroup M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M}
    (h : l₁.eval - l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval - ((r₂, x) ::ᵣ l₂).eval = ((r₁ - r₂, x) ::ᵣ l).eval := by
  simp only [← h, eval_cons, sub_eq_add_neg, neg_add, add_smul, neg_smul, add_assoc]
  congr! 1
  simp only [← add_assoc]
  congr! 1
  rw [add_comm]

theorem sub_eq_eval₃ [Ring R] [AddCommGroup M] [Module R M] {a₁ : R × M} (a₂ : R × M)
    {l₁ l₂ l : NF R M} (h : (a₁ ::ᵣ l₁).eval - l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval - (a₂ ::ᵣ l₂).eval = ((-a₂.1, a₂.2) ::ᵣ l).eval := by
  simp only [eval_cons, neg_smul, neg_add, sub_eq_add_neg, ← h, ← add_assoc]
  congr! 1
  rw [add_comm, add_assoc]

theorem sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} [AddCommGroup M] [Ring R] [Module R M] [Semiring R₁]
    [Module R₁ M] [Semiring R₂] [Module R₂ M] [Semiring S₁] [Module S₁ M] [Semiring S₂]
    [Module S₂ M] {l₁ l₂ l : NF R M} {l₁' : NF R₁ M} {l₂' : NF R₂ M} {l₁'' : NF S₁ M}
    {l₂'' : NF S₂ M} {x₁ x₂ : M} (hx₁ : x₁ = l₁''.eval) (hx₂ : x₂ = l₂''.eval)
    (h₁' : l₁'.eval = l₁''.eval) (h₂' : l₂'.eval = l₂''.eval) (h₁ : l₁.eval = l₁'.eval)
    (h₂ : l₂.eval = l₂'.eval) (h : l₁.eval - l₂.eval = l.eval) :
    x₁ - x₂ = l.eval := by
  rw [hx₁, hx₂, ← h₁', ← h₂', ← h₁, ← h₂, h]

instance [Neg R] : Neg (NF R M) where
  neg l := l.map fun (a, x) ↦ (-a, x)

theorem eval_neg [AddCommGroup M] [Ring R] [Module R M] (l : NF R M) : (-l).eval = - l.eval := by
  simp +instances only [NF.eval, List.map_map, List.sum_neg, NF.instNeg]
  congr
  ext p
  simp

theorem zero_sub_eq_eval [AddCommGroup M] [Ring R] [Module R M] (l : NF R M) :
    0 - l.eval = (-l).eval := by
  simp [eval_neg]

theorem neg_eq_eval [AddCommGroup M] [Semiring S] [Module S M] [Ring R] [Module R M] {l : NF R M}
    {l₀ : NF S M} (hl : l.eval = l₀.eval) {x : M} (h : x = l₀.eval) :
    - x = (-l).eval := by
  rw [h, ← hl, eval_neg]

instance [Mul R] : SMul R (NF R M) where
  smul r l := l.map fun (a, x) ↦ (r * a, x)

@[simp] theorem smul_apply [Mul R] (r : R) (l : NF R M) : r • l = l.map fun (a, x) ↦ (r * a, x) :=
  rfl

theorem eval_smul [AddCommMonoid M] [Semiring R] [Module R M] {l : NF R M} {x : M} (h : x = l.eval)
    (r : R) : (r • l).eval = r • x := by
  unfold NF.eval at h ⊢
  simp only [h, smul_sum, map_map, NF.smul_apply]
  congr
  ext p
  simp [mul_smul]

theorem smul_eq_eval {R₀ : Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₀]
    [Module R₀ M] [Semiring S] [Module S M] {l : NF R M} {l₀ : NF R₀ M} {s : S} {r : R}
    {x : M} (hx : x = l₀.eval) (hl : l.eval = l₀.eval) (hs : r • x = s • x) :
    s • x = (r • l).eval := by
  rw [← hs, hx, ← hl, eval_smul]
  rfl

theorem eq_cons_cons [AddMonoid M] [SMul R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂)
    (h2 : l₁.eval = l₂.eval) :
    ((r₁, m) ::ᵣ l₁).eval = ((r₂, m) ::ᵣ l₂).eval := by
  simp [h1, h2]

theorem eq_cons_const [AddCommMonoid M] [Semiring R] [Module R M] {r : R} (m : M) {n : M}
    {l : NF R M} (h1 : r = 0) (h2 : l.eval = n) :
    ((r, m) ::ᵣ l).eval = n := by
  simp [h1, h2]

theorem eq_const_cons [AddCommMonoid M] [Semiring R] [Module R M] {r : R} (m : M) {n : M}
    {l : NF R M} (h1 : 0 = r) (h2 : n = l.eval) :
    n = ((r, m) ::ᵣ l).eval := by
  simp [← h1, h2]

theorem eq_of_eval_eq_eval {R₁ R₂ : Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁]
    [Module R₁ M] [Semiring R₂] [Module R₂ M] {l₁ l₂ : NF R M} {l₁' : NF R₁ M} {l₂' : NF R₂ M}
    {x₁ x₂ : M} (hx₁ : x₁ = l₁'.eval) (hx₂ : x₂ = l₂'.eval) (h₁ : l₁.eval = l₁'.eval)
    (h₂ : l₂.eval = l₂'.eval) (h : l₁.eval = l₂.eval) :
    x₁ = x₂ := by
  rw [hx₁, hx₂, ← h₁, ← h₂, h]

variable (R)

/-- Operate on a `Module.NF S M` object `l`, i.e. a list of pairs in `S × M`, where `S` is some
commutative semiring, by applying to each `S`-component the algebra-map from `S` into a specified
`S`-algebra `R`. -/
def algebraMap [CommSemiring S] [Semiring R] [Algebra S R] (l : NF S M) : NF R M :=
  l.map (fun ⟨s, x⟩ ↦ (_root_.algebraMap S R s, x))

theorem eval_algebraMap [CommSemiring S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M]
    [MulAction R M] [IsScalarTower S R M] (l : NF S M) :
    (l.algebraMap R).eval = l.eval := by
  simp only [NF.eval, algebraMap, map_map]
  congr
  ext
  simp [IsScalarTower.algebraMap_smul]

end NF
end

public meta section
variable {u v : Level}

/-! ### Lists of expressions representing scalars and vectors, and operations on such lists -/

/-- Basic meta-code "normal form" object of the `match_scalars` and `module` tactics: a type synonym
for a list of ordered triples comprising expressions representing terms of two types `R` and `M`
(where typically `M` is an `R`-module), together with a natural number "index".

The natural number represents the index of the `M` term in the `AtomM` monad: this is not enforced,
but is sometimes assumed in operations.  Thus when items `((a₁, x₁), k)` and `((a₂, x₂), k)`
appear in two different `Module.qNF` objects (i.e. with the same `ℕ`-index `k`), it is expected that
the expressions `x₁` and `x₂` are the same.  It is also expected that the items in a `Module.qNF`
list are in strictly increasing order by natural-number index.

By forgetting the natural number indices, an expression representing a `Mathlib.Tactic.Module.NF`
object can be built from a `Module.qNF` object; this construction is provided as
`Mathlib.Tactic.Module.qNF.toNF`. -/
abbrev qNF (R : Q(Type u)) (M : Q(Type v)) := List ((Q($R) × Q($M)) × ℕ)

namespace qNF

variable {M : Q(Type v)} {R : Q(Type u)}

/-- Given `l` of type `qNF R M`, i.e. a list of `(Q($R) × Q($M)) × ℕ`s (two `Expr`s and a natural
number), build an `Expr` representing an object of type `NF R M` (i.e. `List (R × M)`) in the
in the obvious way: by forgetting the natural numbers and gluing together the `Expr`s. -/
def toNF (l : qNF R M) : Q(NF $R $M) :=
  let l' : List Q($R × $M) := (l.map Prod.fst).map (fun (a, x) ↦ q(($a, $x)))
  let qt : List Q($R × $M) → Q(List ($R × $M)) := List.rec q([]) (fun e _ l ↦ q($e ::ᵣ $l))
  qt l'

/-- Given `l` of type `qNF R₁ M`, i.e. a list of `(Q($R₁) × Q($M)) × ℕ`s (two `Expr`s and a natural
number), apply an expression representing a function with domain `R₁` to each of the `Q($R₁)`
components. -/
def onScalar {u₁ u₂ : Level} {R₁ : Q(Type u₁)} {R₂ : Q(Type u₂)} (l : qNF R₁ M) (f : Q($R₁ → $R₂)) :
    qNF R₂ M :=
  l.map fun ((a, x), k) ↦ ((q($f $a), x), k)

/-- Given two terms `l₁`, `l₂` of type `qNF R M`, i.e. lists of `(Q($R) × Q($M)) × ℕ`s (two `Expr`s
and a natural number), construct another such term `l`, which will have the property that in the
`$R`-module `$M`, the sum of the "linear combinations" represented by `l₁` and `l₂` is the linear
combination represented by `l`.

The construction assumes, to be valid, that the lists `l₁` and `l₂` are in strictly increasing order
by `ℕ`-component, and that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with
the same `ℕ`-component `k`, then the expressions `x₁` and `x₂` are equal.

The construction is as follows: merge the two lists, except that if pairs `(a₁, x₁)` and `(a₂, x₂)`
appear in `l₁`, `l₂` respectively with the same `ℕ`-component `k`, then contribute a term
`(a₁ + a₂, x₁)` to the output list with `ℕ`-component `k`. -/
meta def add (iR : Q(Semiring $R)) : qNF R M → qNF R M → qNF R M
  | [], l => l
  | l, [] => l
  | ((a₁, x₁), k₁) ::ᵣ t₁, ((a₂, x₂), k₂) ::ᵣ t₂ =>
    if k₁ < k₂ then
      ((a₁, x₁), k₁) ::ᵣ add iR t₁ (((a₂, x₂), k₂) ::ᵣ t₂)
    else if k₁ = k₂ then
      ((q($a₁ + $a₂), x₁), k₁) ::ᵣ add iR t₁ t₂
    else
      ((a₂, x₂), k₂) ::ᵣ add iR (((a₁, x₁), k₁) ::ᵣ t₁) t₂

/-- Given two terms `l₁`, `l₂` of type `qNF R M`, i.e. lists of `(Q($R) × Q($M)) × ℕ`s (two `Expr`s
and a natural number), recursively construct a proof that in the `$R`-module `$M`, the sum of the
"linear combinations" represented by `l₁` and `l₂` is the linear combination represented by
`Module.qNF.add iR l₁ l₁`. -/
meta def mkAddProof {iR : Q(Semiring $R)} {iM : Q(AddCommMonoid $M)} (iRM : Q(Module $R $M))
    (l₁ l₂ : qNF R M) :
    Q(NF.eval $(l₁.toNF) + NF.eval $(l₂.toNF) = NF.eval $((qNF.add iR l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(zero_add (NF.eval $(l.toNF))):)
  | l, [] => (q(add_zero (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) ::ᵣ t₁, ((a₂, x₂), k₂) ::ᵣ t₂ =>
    if k₁ < k₂ then
      let pf := mkAddProof iRM t₁ (((a₂, x₂), k₂) ::ᵣ t₂)
      (q(NF.add_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkAddProof iRM t₁ t₂
      (q(NF.add_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
    else
      let pf := mkAddProof iRM (((a₁, x₁), k₁) ::ᵣ t₁) t₂
      (q(NF.add_eq_eval₃ ($a₂, $x₂) $pf):)

/-- Given two terms `l₁`, `l₂` of type `qNF R M`, i.e. lists of `(Q($R) × Q($M)) × ℕ`s (two `Expr`s
and a natural number), construct another such term `l`, which will have the property that in the
`$R`-module `$M`, the difference of the "linear combinations" represented by `l₁` and `l₂` is the
linear combination represented by `l`.

The construction assumes, to be valid, that the lists `l₁` and `l₂` are in strictly increasing order
by `ℕ`-component, and that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with
the same `ℕ`-component `k`, then the expressions `x₁` and `x₂` are equal.

The construction is as follows: merge the first list and the negation of the second list, except
that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with the same
`ℕ`-component `k`, then contribute a term `(a₁ - a₂, x₁)` to the output list with `ℕ`-component `k`.
-/
def sub (iR : Q(Ring $R)) : qNF R M → qNF R M → qNF R M
  | [], l => l.onScalar q(Neg.neg)
  | l, [] => l
  | ((a₁, x₁), k₁) ::ᵣ t₁, ((a₂, x₂), k₂) ::ᵣ t₂ =>
    if k₁ < k₂ then
      ((a₁, x₁), k₁) ::ᵣ sub iR t₁ (((a₂, x₂), k₂) ::ᵣ t₂)
    else if k₁ = k₂ then
      ((q($a₁ - $a₂), x₁), k₁) ::ᵣ sub iR t₁ t₂
    else
      ((q(-$a₂), x₂), k₂) ::ᵣ sub iR (((a₁, x₁), k₁) ::ᵣ t₁) t₂

/-- Given two terms `l₁`, `l₂` of type `qNF R M`, i.e. lists of `(Q($R) × Q($M)) × ℕ`s (two `Expr`s
and a natural number), recursively construct a proof that in the `$R`-module `$M`, the difference
of the "linear combinations" represented by `l₁` and `l₂` is the linear combination represented by
`Module.qNF.sub iR l₁ l₁`. -/
def mkSubProof (iR : Q(Ring $R)) (iM : Q(AddCommGroup $M)) (iRM : Q(Module $R $M))
    (l₁ l₂ : qNF R M) :
    Q(NF.eval $(l₁.toNF) - NF.eval $(l₂.toNF) = NF.eval $((qNF.sub iR l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(NF.zero_sub_eq_eval $(l.toNF)):)
  | l, [] => (q(sub_zero (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) ::ᵣ t₁, ((a₂, x₂), k₂) ::ᵣ t₂ =>
    if k₁ < k₂ then
      let pf := mkSubProof iR iM iRM t₁ (((a₂, x₂), k₂) ::ᵣ t₂)
      (q(NF.sub_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkSubProof iR iM iRM t₁ t₂
      (q(NF.sub_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
    else
      let pf := mkSubProof iR iM iRM (((a₁, x₁), k₁) ::ᵣ t₁) t₂
      (q(NF.sub_eq_eval₃ ($a₂, $x₂) $pf):)

variable {iM : Q(AddCommMonoid $M)}
  {u₁ : Level} {R₁ : Q(Type u₁)} {iR₁ : Q(Semiring $R₁)} (iRM₁ : Q(@Module $R₁ $M $iR₁ $iM))
  {u₂ : Level} {R₂ : Q(Type u₂)} (iR₂ : Q(Semiring $R₂)) (iRM₂ : Q(@Module $R₂ $M $iR₂ $iM))

/-- Given an expression `M` representing a type which is an `AddCommMonoid` and a module over *two*
semirings `R₁` and `R₂`, find the "bigger" of the two semirings.  That is, we assume that it will
turn out to be the case that either (1) `R₁` is an `R₂`-algebra and the `R₂` scalar action on `M` is
induced from `R₁`'s scalar action on `M`, or (2) vice versa; we return the semiring `R₁` in the
first case and `R₂` in the second case.

Moreover, given expressions representing particular scalar multiplications of `R₁` and/or `R₂` on
`M` (a `List (R₁ × M)`, a `List (R₂ × M)`, a pair `(r, x) : R₂ × M`), bump these up to the "big"
ring by applying the algebra-map where needed. -/
def matchRings (l₁ : qNF R₁ M) (l₂ : qNF R₂ M) (r : Q($R₂)) (x : Q($M)) :
    MetaM <| Σ u : Level, Σ R : Q(Type u), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR $iM),
      (Σ l₁' : qNF R M, Q(NF.eval $(l₁'.toNF) = NF.eval $(l₁.toNF)))
      × (Σ l₂' : qNF R M, Q(NF.eval $(l₂'.toNF) = NF.eval $(l₂.toNF)))
      × (Σ r' : Q($R), Q($r' • $x = $r • $x)) := do
  if ← withReducible <| isDefEq R₁ R₂ then
  -- the case when `R₁ = R₂` is handled separately, so as not to require commutativity of that ring
    pure ⟨u₁, R₁, iR₁, iRM₁, ⟨l₁, q(rfl)⟩, ⟨l₂, (q(@rfl _ (NF.eval $(l₂.toNF))):)⟩,
      r, (q(@rfl _ ($r • $x)):)⟩
  -- otherwise the "smaller" of the two rings must be commutative
  else try
    -- first try to exhibit `R₂` as an `R₁`-algebra
    let _i₁ ← synthInstanceQ q(CommSemiring $R₁)
    let _i₃ ← synthInstanceQ q(Algebra $R₁ $R₂)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₁ $R₂ $M)
    assumeInstancesCommute
    let l₁' : qNF R₂ M := l₁.onScalar q(algebraMap $R₁ $R₂)
    pure ⟨u₂, R₂, iR₂, iRM₂, ⟨l₁', (q(NF.eval_algebraMap $R₂ $(l₁.toNF)):)⟩, ⟨l₂, q(rfl)⟩,
      r, q(rfl)⟩
  catch _ => try
    -- then if that fails, try to exhibit `R₁` as an `R₂`-algebra
    let _i₁ ← synthInstanceQ q(CommSemiring $R₂)
    let _i₃ ← synthInstanceQ q(Algebra $R₂ $R₁)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₂ $R₁ $M)
    assumeInstancesCommute
    let l₂' : qNF R₁ M := l₂.onScalar q(algebraMap $R₂ $R₁)
    let r' : Q($R₁) := q(algebraMap $R₂ $R₁ $r)
    pure ⟨u₁, R₁, iR₁, iRM₁, ⟨l₁, q(rfl)⟩, ⟨l₂', (q(NF.eval_algebraMap $R₁ $(l₂.toNF)):)⟩,
      r', (q(IsScalarTower.algebraMap_smul $R₁ $r $x):)⟩
  catch _ =>
    throwError "match_scalars failed: {R₁} is not an {R₂}-algebra and {R₂} is not an {R₁}-algebra"

end qNF

/-! ### Core of the `module` tactic -/

variable {M : Q(Type v)}

/-- The main algorithm behind the `match_scalars` and `module` tactics: partially-normalizing an
expression in an additive commutative monoid `M` into the form c1 • x1 + c2 • x2 + ... c_k • x_k,
where x1, x2, ... are distinct atoms in `M`, and c1, c2, ... are scalars. The scalar type of the
expression is not pre-determined: instead it starts as `ℕ` (when each atom is initially given a
scalar `(1:ℕ)`) and gets bumped up into bigger semirings when such semirings are encountered.

It is assumed that there is a "linear order" on all the semirings which appear in the expression:
for any two semirings `R` and `S` which occur, we have either `Algebra R S` or `Algebra S R`.

TODO: implement a variant in which a semiring `R` is provided by the user, and the assumption is
instead that for any semiring `S` which occurs, we have `Algebra S R`. The PR https://github.com/leanprover-community/mathlib4/pull/16984 provides a
proof-of-concept implementation of this variant, but it would need some polishing before joining
Mathlib.

Possible TODO, if poor performance on large problems is witnessed: switch the implementation from
`AtomM` to `CanonM`, per the discussion
https://github.com/leanprover-community/mathlib4/pull/16593/files#r1749623191 -/
partial def parse (iM : Q(AddCommMonoid $M)) (x : Q($M)) :
    AtomM (Σ u : Level, Σ R : Q(Type u), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR $iM),
      Σ l : qNF R M, Q($x = NF.eval $(l.toNF))) := do
  match x with
  /- parse an addition: `x₁ + x₂` -/
  | ~q($x₁ + $x₂) =>
    let ⟨_, _, _, iRM₁, l₁', pf₁'⟩ ← parse iM x₁
    let ⟨_, _, _, iRM₂, l₂', pf₂'⟩ ← parse iM x₂
    -- lift from the semirings of scalars parsed from `x₁`, `x₂` (say `R₁`, `R₂`) to `R₁ ⊗ R₂`
    let ⟨u, R, iR, iRM, ⟨l₁, pf₁⟩, ⟨l₂, pf₂⟩, _⟩ ← qNF.matchRings iRM₁ _ iRM₂ l₁' l₂' q(0) q(0)
    -- build the new list and proof
    let pf := qNF.mkAddProof iRM l₁ l₂
    pure ⟨u, R, iR, iRM, qNF.add iR l₁ l₂, (q(NF.add_eq_eval $pf₁' $pf₂' $pf₁ $pf₂ $pf):)⟩
  /- parse a subtraction: `x₁ - x₂` -/
  | ~q(@HSub.hSub _ _ _ (@instHSub _ $iM') $x₁ $x₂) =>
    let ⟨_, _, _, iRM₁, l₁'', pf₁''⟩ ← parse iM x₁
    let ⟨_, _, _, iRM₂, l₂'', pf₂''⟩ ← parse iM x₂
    -- lift from the semirings of scalars parsed from `x₁`, `x₂` (say `R₁`, `R₂`) to `R₁ ⊗ R₂ ⊗ ℤ`
    let iZ := q(Int.instSemiring)
    let iMZ ← synthInstanceQ q(Module ℤ $M)
    let ⟨_, _, _, iRM₁', ⟨l₁', pf₁'⟩, _, _⟩ ← qNF.matchRings iRM₁ iZ iMZ l₁'' [] q(0) q(0)
    let ⟨_, _, _, iRM₂', ⟨l₂', pf₂'⟩, _, _⟩ ← qNF.matchRings iRM₂ iZ iMZ l₂'' [] q(0) q(0)
    let ⟨u, R, iR, iRM, ⟨l₁, pf₁⟩, ⟨l₂, pf₂⟩, _⟩ ← qNF.matchRings iRM₁' _ iRM₂' l₁' l₂' q(0) q(0)
    let iR' ← synthInstanceQ q(Ring $R)
    let iM' ← synthInstanceQ q(AddCommGroup $M)
    assumeInstancesCommute
    -- build the new list and proof
    let pf := qNF.mkSubProof iR' iM' iRM l₁ l₂
    pure ⟨u, R, iR, iRM, qNF.sub iR' l₁ l₂,
      q(NF.sub_eq_eval $pf₁'' $pf₂'' $pf₁' $pf₂' $pf₁ $pf₂ $pf)⟩
  /- parse a negation: `-y` -/
  | ~q(@Neg.neg _ $iM' $y) =>
    let ⟨u₀, _, _, iRM₀, l₀, pf₀⟩ ← parse iM y
    -- lift from original semiring of scalars (say `R₀`) to `R₀ ⊗ ℤ`
    let _i ← synthInstanceQ q(AddCommGroup $M)
    let iZ := q(Int.instSemiring)
    let iMZ ← synthInstanceQ q(Module ℤ $M)
    let ⟨u, R, iR, iRM, ⟨l, pf⟩, _, _⟩ ← qNF.matchRings iRM₀ iZ iMZ l₀ [] q(0) q(0)
    let _i' ← synthInstanceQ q(Ring $R)
    assumeInstancesCommute
    -- build the new list and proof
    pure ⟨u, R, iR, iRM, l.onScalar q(Neg.neg), (q(NF.neg_eq_eval $pf $pf₀):)⟩
  /- parse a scalar multiplication: `(s₀ : S) • y` -/
  | ~q(@HSMul.hSMul _ _ _ (@instHSMul $S _ $iS) $s₀ $y) =>
    let ⟨_, _, _, iRM₀, l₀, pf₀⟩ ← parse iM y
    let i₁ ← synthInstanceQ q(Semiring $S)
    let i₂ ← synthInstanceQ q(Module $S $M)
    assumeInstancesCommute
    -- lift from original semiring of scalars (say `R₀`) to `R₀ ⊗ S`
    let ⟨u, R, iR, iRM, ⟨l, pf_l⟩, _, ⟨s, pf_r⟩⟩ ← qNF.matchRings iRM₀ i₁ i₂ l₀ [] s₀ y
    -- build the new list and proof
    pure ⟨u, R, iR, iRM, l.onScalar q(HMul.hMul $s), (q(NF.smul_eq_eval $pf₀ $pf_l $pf_r) :)⟩
  /- parse a `(0:M)` -/
  | ~q(0) =>
    pure ⟨0, q(Nat), q(Nat.instSemiring), q(AddCommMonoid.toNatModule), [], q(NF.zero_eq_eval $M)⟩
  /- anything else should be treated as an atom -/
  | _ =>
    let (k, ⟨x', _⟩) ← AtomM.addAtomQ x
    pure ⟨0, q(Nat), q(Nat.instSemiring), q(AddCommMonoid.toNatModule), [((q(1), x'), k)],
      q(NF.atom_eq_eval $x')⟩

/-- Given expressions `R` and `M` representing types such that `M`'s is a module over `R`'s, and
given two terms `l₁`, `l₂` of type `qNF R M`, i.e. lists of `(Q($R) × Q($M)) × ℕ`s (two `Expr`s
and a natural number), construct a list of new goals: that the `R`-coefficient of an `M`-atom which
appears in only one list is zero, and that the `R`-coefficients of an `M`-atom which appears in both
lists are equal.  Also construct (dependent on these new goals) a proof that the "linear
combinations" represented by `l₁` and `l₂` are equal in `M`. -/
partial def reduceCoefficientwise {R : Q(Type u)} {_ : Q(AddCommMonoid $M)} {_ : Q(Semiring $R)}
    (iRM : Q(Module $R $M)) (l₁ l₂ : qNF R M) :
    MetaM (List MVarId × Q(NF.eval $(l₁.toNF) = NF.eval $(l₂.toNF))) := do
  match l₁, l₂ with
  /- if both empty, return a `rfl` proof that `(0:M) = 0` -/
  | [], [] =>
    let pf : Q(NF.eval $(l₁.toNF) = NF.eval $(l₁.toNF)) := q(rfl)
    pure ([], pf)
  /- if one of the lists is empty and the other one is not, recurse down the nonempty one,
    forming goals that each of the listed coefficients is equal to
    zero -/
  | [], ((a, x), _) ::ᵣ L =>
    let mvar : Q((0:$R) = $a) ← mkFreshExprMVar q((0:$R) = $a)
    let (mvars, pf) ← reduceCoefficientwise iRM [] L
    pure (mvar.mvarId! :: mvars, (q(NF.eq_const_cons $x $mvar $pf):))
  | ((a, x), _) ::ᵣ L, [] =>
    let mvar : Q($a = (0:$R)) ← mkFreshExprMVar q($a = (0:$R))
    let (mvars, pf) ← reduceCoefficientwise iRM L []
    pure (mvar.mvarId! :: mvars, (q(NF.eq_cons_const $x $mvar $pf):))
  /- if both lists are nonempty, then deal with the numerically-smallest term in either list,
    forming a goal that it is equal to zero (if it appears in only one list) or that its
    coefficients in the two lists are the same (if it appears in both lists); then recurse -/
  | ((a₁, x₁), k₁) ::ᵣ L₁, ((a₂, x₂), k₂) ::ᵣ L₂ =>
    if k₁ < k₂ then
      let mvar : Q($a₁ = (0:$R)) ← mkFreshExprMVar q($a₁ = (0:$R))
      let (mvars, pf) ← reduceCoefficientwise iRM L₁ l₂
      pure (mvar.mvarId! :: mvars, (q(NF.eq_cons_const $x₁ $mvar $pf):))
    else if k₁ = k₂ then
      let mvar : Q($a₁ = $a₂) ← mkFreshExprMVar q($a₁ = $a₂)
      let (mvars, pf) ← reduceCoefficientwise iRM L₁ L₂
      pure (mvar.mvarId! :: mvars, (q(NF.eq_cons_cons $x₁ $mvar $pf):))
    else
      let mvar : Q((0:$R) = $a₂) ← mkFreshExprMVar q((0:$R) = $a₂)
      let (mvars, pf) ← reduceCoefficientwise iRM l₁ L₂
      pure (mvar.mvarId! :: mvars, (q(NF.eq_const_cons $x₂ $mvar $pf):))

/-- Given a goal which is an equality in a type `M` (with `M` an `AddCommMonoid`), parse the LHS and
RHS of the goal as linear combinations of `M`-atoms over some semiring `R`, and reduce the goal to
the respective equalities of the `R`-coefficients of each atom.

This is an auxiliary function which produces slightly awkward goals in `R`; they are later cleaned
up by the function `Mathlib.Tactic.Module.postprocess`. -/
def matchScalarsAux (g : MVarId) : AtomM (List MVarId) := do
  /- Parse the goal as an equality in a type `M` of two expressions `lhs` and `rhs`, with `M`
  carrying an `AddCommMonoid` instance. -/
  let eqData ← do
    match (← g.getType').eq? with
    | some e => pure e
    | none => throwError "goal {← g.getType} is not an equality"
  let .sort v₀ ← whnf (← inferType eqData.1) | unreachable!
  let some v := v₀.dec | unreachable!
  let ((M : Q(Type v)), (lhs : Q($M)), (rhs :Q($M))) := eqData
  let iM ← synthInstanceQ q(AddCommMonoid.{v} $M)
  /- Construct from the `lhs` expression a term `l₁` of type `qNF R₁ M` for some semiring `R₁` --
  that is, a list of `(Q($R₁) × Q($M)) × ℕ`s (two `Expr`s and a natural number) -- together with a
  proof that `lhs` is equal to the `R₁`-linear combination in `M` this represents. -/
  let e₁ ← parse iM lhs
  have u₁ : Level := e₁.fst
  have R₁ : Q(Type u₁) := e₁.snd.fst
  have _iR₁ : Q(Semiring.{u₁} $R₁) := e₁.snd.snd.fst
  let iRM₁ ← synthInstanceQ q(Module $R₁ $M)
  assumeInstancesCommute
  have l₁ : qNF R₁ M := e₁.snd.snd.snd.snd.fst
  let pf₁ : Q($lhs = NF.eval $(l₁.toNF)) := e₁.snd.snd.snd.snd.snd
  /- Do the same for the `rhs` expression, obtaining a term `l₂` of type `qNF R₂ M` for some
  semiring `R₂`. -/
  let e₂ ← parse iM rhs
  have u₂ : Level := e₂.fst
  have R₂ : Q(Type u₂) := e₂.snd.fst
  have _iR₂ : Q(Semiring.{u₂} $R₂) := e₂.snd.snd.fst
  let iRM₂ ← synthInstanceQ q(Module $R₂ $M)
  have l₂ : qNF R₂ M := e₂.snd.snd.snd.snd.fst
  let pf₂ : Q($rhs = NF.eval $(l₂.toNF)) := e₂.snd.snd.snd.snd.snd
  /- Lift everything to the same scalar ring, `R`. -/
  let ⟨_, _, _, iRM, ⟨l₁', pf₁'⟩, ⟨l₂', pf₂'⟩, _⟩ ← qNF.matchRings iRM₁ _ iRM₂ l₁ l₂ q(0) q(0)
  /- Construct a list of goals for the coefficientwise equality of these formal linear combinations,
  and resolve our original goal (modulo these new goals). -/
  let (mvars, pf) ← reduceCoefficientwise iRM l₁' l₂'
  g.assign q(NF.eq_of_eval_eq_eval $pf₁ $pf₂ $pf₁' $pf₂' $pf)
  return mvars

/-- Lemmas used to post-process the result of the `match_scalars` and `module` tactics by converting
the `algebraMap` operations which (which proliferate in the constructed scalar goals) to more
familiar forms: `ℕ`, `ℤ` and `ℚ` casts. -/
def algebraMapThms : Array Name := #[``eq_natCast, ``eq_intCast, ``eq_ratCast]

/-- Postprocessing for the scalar goals constructed in the `match_scalars` and `module` tactics.
These goals feature a proliferation of `algebraMap` operations (because the scalars start in `ℕ` and
get successively bumped up by `algebraMap`s as new semirings are encountered), so we reinterpret the
most commonly occurring `algebraMap`s (those out of `ℕ`, `ℤ` and `ℚ`) into their standard forms
(`ℕ`, `ℤ` and `ℚ` casts) and then try to disperse the casts using the various `push_cast` lemmas. -/
def postprocess (mvarId : MVarId) : MetaM MVarId := do
  -- collect the available `push_cast` lemmas
  let mut thms : SimpTheorems := ← NormCast.pushCastExt.getTheorems
  -- augment this list with the `algebraMapThms` lemmas, which handle `algebraMap` operations
  for thm in algebraMapThms do
    let ⟨levelParams, _, proof⟩ ← abstractMVars (mkConst thm)
    thms ← thms.add (.stx (← mkFreshId) Syntax.missing) levelParams proof
  -- now run `simp` with these lemmas, and (importantly) *no* simprocs
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[thms])
  let (some r, _) ← simpTarget mvarId ctx (simprocs := #[]) |
    throwError "internal error in match_scalars tactic: postprocessing should not close goals"
  return r

/-- Given a goal which is an equality in a type `M` (with `M` an `AddCommMonoid`), parse the LHS and
RHS of the goal as linear combinations of `M`-atoms over some semiring `R`, and reduce the goal to
the respective equalities of the `R`-coefficients of each atom. -/
def matchScalars (g : MVarId) : MetaM (List MVarId) := do
  let mvars ← AtomM.run .instances (matchScalarsAux g)
  mvars.mapM postprocess

/-- Given a goal parseable as a linear combination `⊢ a • x + ... + b • y = c • x + ... + d • y`,
`match_scalars` splits up the goal into equalities of the scalars for each respective atom. This
means the example goal above is replaced by goals `⊢ a = c` (from `x`), ..., `⊢ b = d` (from `y`).

The `module` tactic is equivalent to `match_scalars <;> ring1`.

`match_scalars` can parse into expressions made of the operators `+`, `-`, `•` and the numeral `0`.
Any other subexpressions (including variables) are treated as atoms.
If the goal is an equality in the type `M`, then `match_scalars` requires an `AddCommMonoid M`
instance. If the goal contains a scalar multiplication `(a : R) • (x : M)`, this requires a
`Semiring R` and `Module R M` instance. If any of the instances are missing, `match_scalars` fails.

The scalar type for the goals produced by the `match_scalars` tactic is the largest scalar type
encountered; for example, if `ℕ`, `ℚ` and a characteristic-zero field `K` all occur as scalars, then
the goals produced are equalities in `K` with the appropriate casts (from `ℕ`, `ℤ`, `ℚ`) and
`algebraMap`s (otherwise) inserted. Inserted casts are simplified by lemmas tagged `@[push_cast]`.
If the set of scalar types encountered is not totally ordered (in the sense that for all rings `R`,
`S` encountered, it holds that either `Algebra R S` or `Algebra S R`), then `match_scalars` fails.

Examples:
```
example [AddCommMonoid M] [Semiring R] [Module R M] (a b : R) (x : M) :
    a • x + b • x = (b + a) • x := by
  match_scalars
  -- one goal: `⊢ a * 1 + b * 1 = (b + a) * 1`

example [AddCommGroup M] [Ring R] [Module R M] (a b : R) (x : M) :
    a • (a • x - b • y) + (b • a • y + b • b • x) = x := by
  match_scalars
  -- two goals:
  -- `⊢ a * (a * 1) + b * (b * 1) = 1` (from the `x` atom)
  -- `⊢ a * -(b * 1) + b * (a * 1) = 0` (from the `y` atom)

example [AddCommGroup M] [Ring R] [Module R M] (a : R) (x : M) :
    -(2:R) • a • x = a • (-2:ℤ) • x := by
  match_scalars
  -- one goal: `⊢ -2 * (a * 1) = a * (-2 * 1)`
```
-/
elab "match_scalars" : tactic => Tactic.liftMetaTactic matchScalars

/-- Given a goal parseable as a linear combination `⊢ a • x + ... + b • y = c • x + ... + d • y`,
`module` proves the equalities of the scalars for each respective atom, by ring normalization.
This means the example goal above is solved if `ring` can prove `⊢ a = c` (from `x`), ..., `⊢ b = d`
(from `y`).

`module` is equivalent to `match_scalars <;> ring1`. If `ring1` fails to prove one of the
equalities, you can instead use `match_scalars` followed by specialized proofs for each scalar.

Examples:
```
example [AddCommMonoid M] [CommSemiring R] [Module R M] (a b : R) (x : M) :
    a • x + b • x = (b + a) • x := by
  module

example [AddCommMonoid M] [Field K] [CharZero K] [Module K M] (x : M) :
    (2:K)⁻¹ • x + (3:K)⁻¹ • x + (6:K)⁻¹ • x = x := by
  module

example [AddCommGroup M] [CommRing R] [Module R M] (a : R) (v w : M) :
    (1 + a ^ 2) • (v + w) - a • (a • v - w) = v + (1 + a + a ^ 2) • w := by
  module

example [AddCommGroup M] [CommRing R] [Module R M] (a b μ ν : R) (x y : M) :
    (μ - ν) • a • x = (a • μ • x + b • ν • y) - ν • (a • x + b • y) := by
  module
```
-/
elab "module" : tactic => Tactic.liftMetaFinishingTactic fun g ↦ do
  let l ← matchScalars g
  discard <| l.mapM fun mvar ↦ AtomM.run .instances (Ring.proveEq mvar)

end
end Mathlib.Tactic.Module
