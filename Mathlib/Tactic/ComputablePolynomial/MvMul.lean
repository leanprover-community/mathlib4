/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
module

public import Mathlib.Tactic.ComputablePolynomial.MvOfList

/-!
# `MvSparsePoly`: multiplication and negation

`mulFast` (balanced-merge multiplication, Johnson/Monagan–Pearce style), `mulPacked` (packed
exponent encoding for the single-variable case), the reference `mulCore`, and negation, together
with the algebraic preparation lemmas (`addCore` commutativity, zero laws) for the ring
instance.
-/

@[expose] public section

variable {nvars : ℕ}

namespace MvSparsePoly

open MvPolynomial

variable {R : Type} [CommRing R] [DecidableEq R]

/-- Fast multiplication by a **balanced merge** (mergesort tree): multiply `y` by each term of `x`
(each product `monomialMul tᵢ y` is already sorted), then merge the `#x` sorted rows pairwise in a
balanced tree. Same result as the reference `mulCore` (each polynomial has a unique sorted normal
form), but `O(#x · #y · log #x)` *time* instead of generating all `#x·#y` products and sorting
them.

Relation to Davenport's notes (Ch. 2, "What are polynomials?"): he notes the sorted approach is
`O(mn log m)`, and that "naïve construction of all the terms followed by sorting would take `O(mn)`
space ... we can do better with heapsort [Joh74]". This `balancedSum` achieves the *time* bound but
NOT the space bound — it still materialises all `#x` rows (so peak `O(#x·#y)`). A true Johnson heap
of size `#x` would stream the output in `O(#x)` working space. For multiplication the rows have
equal size `#y`, so the balanced merge is efficient (unlike the division case — see the note on
`normalForm`); the only thing a real heap would buy here is peak memory, so we keep the simpler,
verifiable merge. -/
def mulFast (x y : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  balancedSum (x.terms.map (fun t => monomialMul t.1 t.2 y))

/-- Runtime-only **packed** multiplication — the Davenport / Monagan–Pearce exponent-packing trick.

`mulFast` represents each monomial as an `Array ℕ`, so every one of the `#x·#y` partial products
allocates a fresh boxed-`Nat` array and every merge comparison walks an array. When the product's
exponents are small enough that each variable fits in a `b`-bit field with `nvars·b ≤ 64`, we
instead encode a whole monomial as a single `UInt64` (variable `0` in the most-significant field).
Then:

* the monomial order is plain `UInt64` comparison (`lexorder` is lex with var `0` most significant),
* monomial multiplication `i + j` is a single `UInt64` add (fields can't carry, since each field sum
  `≤ 2·maxDeg < 2^b`).

So the whole `#x·#y` inner loop runs on unboxed machine words; we merge/dedup in packed space and
only unpack the `≤ #product` survivors back to `MvDegrees`. When the exponents don't fit in 64 bits
(or `nvars = 0`) we fall back to `mulFast`. This is the *time*-constant-factor win Davenport's notes
point at (Ch. 2, exponent encoding); same result as `mulCore` (wired via `@[implemented_by]`), and
cross-checked against `mulFast`/`mulCore` by `#guard`. -/
def mulPacked (x y : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  if nvars = 0 then mulFast x y else
  Id.run do
    let mut maxDeg : ℕ := 0
    for t in x.terms do
      for e in t.1.degrees do
        if e > maxDeg then maxDeg := e
    for t in y.terms do
      for e in t.1.degrees do
        if e > maxDeg then maxDeg := e
    let fieldBound : ℕ := 2 * maxDeg + 1
    let b : ℕ := Nat.log2 fieldBound + 1
    if nvars * b > 64 then
      return mulFast x y
    let bb : UInt64 := b.toUInt64
    let mask : UInt64 := (1 <<< bb) - 1
    let pack : MvDegrees nvars → UInt64 := fun d => Id.run do
      let mut k : UInt64 := 0
      for e in d.degrees do
        k := (k <<< bb) ||| (e.toUInt64 &&& mask)
      return k
    let unpack : UInt64 → MvDegrees nvars := fun k =>
      let degs : Array ℕ := Array.ofFn (n := nvars) (fun j : Fin nvars =>
        ((k >>> (((nvars - 1 - j.val) * b).toUInt64)) &&& mask).toNat)
      { degrees := degs, correct := by simp [degs], totalDegree := degs.foldl (· + ·) 0,
        totalDegree_eq := rfl }
    let yk : Array (UInt64 × R) := (y.terms.map (fun t => (pack t.1, t.2))).toArray
    let mut prods : Array (UInt64 × R) := Array.mkEmpty (x.terms.length * yk.size)
    for t in x.terms do
      let xkey := pack t.1
      let xc := t.2
      for p in yk do
        prods := prods.push (xkey + p.1, xc * p.2)
    let sorted := prods.qsort (fun a c => decide (c.1 < a.1))
    let mut merged : Array (UInt64 × R) := Array.mkEmpty sorted.size
    for p in sorted do
      match merged.back? with
      | some q => if q.1 == p.1 then merged := merged.set! (merged.size - 1) (p.1, q.2 + p.2)
                  else merged := merged.push p
      | none => merged := merged.push p
    let mut out : List (MvDegrees nvars × R) := []
    for p in merged do
      if p.2 ≠ 0 then out := (unpack p.1, p.2) :: out
    return ofList out

/-- Reference multiplication: generate every product term, then sort/dedup/filter via `ofList`.
The proofs use this; compiled code uses the equivalent `mulPacked` via `@[implemented_by]`. -/
@[implemented_by mulPacked]
def mulCore (x y : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  ofList do
    let (i, a) ← x.terms
    let (j, b) ← y.terms
    return (i + j, a * b)

instance : Mul (MvSparsePoly R nvars) where
  mul := mulCore

instance : Neg (MvSparsePoly R nvars) where
  neg x := C (-1) * x

/-- Native computational negation, negating every coefficient. -/
def negCore (x : List (MvDegrees nvars × R)) : List (MvDegrees nvars × R) :=
  x.map (fun p => (p.1, -p.2))

omit [DecidableEq R] in
lemma negCore_sorted {x : List (MvDegrees nvars × R)} (h : x.Pairwise (·.1 > ·.1)) :
    (negCore x).Pairwise (·.1 > ·.1) := by
  induction x with
  | nil => exact List.Pairwise.nil
  | cons head tail ih =>
    simp only [negCore, List.map_cons, List.pairwise_cons] at h ⊢
    refine ⟨fun p hp => ?_, ih h.2⟩
    rcases List.mem_map.1 hp with ⟨p', hp', heq⟩
    subst heq
    exact h.1 p' hp'

/-- Negating non-zero elements keeps them non-zero. -/
lemma negCore_filter (x : List (MvDegrees nvars × R)) (hx : ∀ p ∈ x, p.2 ≠ 0) :
    (negCore x).filter (·.2 ≠ 0) = negCore x := by
  apply List.filter_eq_self.mpr
  intro p hp
  rcases List.mem_map.1 hp with ⟨p', hp', heq⟩
  subst heq
  have h_not_zero := hx p' hp'
  grind
/-- Adding a polynomial to its negation cancels to the empty list. -/
lemma addCore_negCore (x : List (MvDegrees nvars × R)) :
    addCore x (negCore x) = [] := by
  induction x with
  | nil => simp [addCore, negCore]
  | cons head tail ih =>
    rcases head with ⟨i, a⟩
    unfold addCore
    have h_not_lt : ¬(i < i) := lt_irrefl i
    simp only [negCore]
    have h_zero : a + -a = 0 := add_neg_cancel a
    aesop

instance : Neg (MvSparsePoly R nvars) where
  neg p := ofSortedList (negCore p.terms) (negCore_sorted p.sorted)

lemma addCore_nil_left (x : List (MvDegrees nvars × R)) : addCore [] x = x := by
  cases x <;> simp [addCore]

lemma addCore_nil_right (x : List (MvDegrees nvars × R)) : addCore x [] = x := by
  cases x <;> simp [addCore]

/-- `addCore` is commutative. -/
lemma addCore_comm : ∀ (x y : List (MvDegrees nvars × R)),
    addCore x y = addCore y x
  | [], yy => by cases yy <;> simp [addCore]
  | (i, a) :: x, [] => by simp [addCore]
  | (i, a) :: x, (j, b) :: y => by
    unfold addCore
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have h_not_ji : ¬(j < i) := fun h => lt_irrefl i (lt_trans hlt h)
      simp only [hlt, h_not_ji, ite_true, ite_false]
      rw [addCore_comm ((i, a) :: x) y]
    · subst heq
      have h_not_lt : ¬(i < i) := lt_irrefl i
      simp only [h_not_lt, ite_false, add_comm a b, addCore_comm x y]
    · have h_not_ij : ¬(i < j) := fun h => lt_irrefl j (lt_trans hgt h)
      simp only [hgt, h_not_ij, ite_true, ite_false]
      rw [addCore_comm x ((j, b) :: y)]
termination_by x y => x.length + y.length

/-- The `ofSortedList` filter does not change an already-valid polynomial. -/
lemma filter_nonzero_eq_self (p : MvSparsePoly R nvars) :
    p.terms.filter (·.2 ≠ 0) = p.terms := by
  apply List.filter_eq_self.mpr
  intro x hx
  exact decide_eq_true (p.nonzero x hx)

lemma poly_zero_add (p : MvSparsePoly R nvars) : 0 + p = p := by
  apply MvSparsePoly.ext
  change (addCore [] p.terms).filter (·.2 ≠ 0) = p.terms
  rw [addCore_nil_left]
  exact filter_nonzero_eq_self p

lemma poly_add_zero (p : MvSparsePoly R nvars) : p + 0 = p := by
  apply MvSparsePoly.ext
  change (addCore p.terms []).filter (·.2 ≠ 0) = p.terms
  rw [addCore_nil_right]
  exact filter_nonzero_eq_self p

lemma poly_add_comm (p q : MvSparsePoly R nvars) : p + q = q + p := by
  apply MvSparsePoly.ext
  change (addCore p.terms q.terms).filter (·.2 ≠ 0) =
    (addCore q.terms p.terms).filter (·.2 ≠ 0)
  rw [addCore_comm]

lemma poly_add_left_neg (p : MvSparsePoly R nvars) : -p + p = 0 := by
  apply MvSparsePoly.ext
  change (addCore ((negCore p.terms).filter (·.2 ≠ 0)) p.terms).filter (·.2 ≠ 0) = []
  rw [negCore_filter p.terms p.nonzero, addCore_comm (negCore p.terms) p.terms,
    addCore_negCore p.terms]
  rfl

/-- `ofList` of the empty list is the zero polynomial. -/
lemma ofList_nil : ofList (R := R) (nvars := nvars) [] = 0 := by
  apply MvSparsePoly.ext
  simp [ofList]
  simp [ofSortedList, dedupList]
  rfl

lemma poly_zero_mul (p : MvSparsePoly R nvars) : 0 * p = 0 := by
  change ofList [] = 0
  exact ofList_nil

lemma poly_mul_zero (p : MvSparsePoly R nvars) : p * 0 = 0 := by
  change ofList (p.terms.flatMap (fun _ => [])) = 0
  have h_bind : p.terms.flatMap
    (fun _ => ([] : List (MvDegrees nvars × R))) = [] := by
    induction p.terms with
    | nil => rfl
    | cons head tail ih => exact ih
  rw [h_bind]
  exact ofList_nil

end MvSparsePoly
