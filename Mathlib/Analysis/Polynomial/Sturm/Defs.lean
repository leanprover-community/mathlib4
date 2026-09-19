/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Data.List.SignVariations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Sturm chains and sign variations

The number of sign variations in a list is the number of adjacent opposite signs
remaining after zero entries are removed. For example, `[1, 0, -1]` has one
sign variation.

`Sturm.sturmVar` applies this count to the evaluations of a list of real
polynomials. `Sturm.IsSturmChain` records the local sign conditions used in
Sturm's theorem. The chain need not be produced by Euclidean division.

## Main definitions

* `List.signVariations`: sign variations with zero entries removed.
* `Sturm.sturmVar`: sign variations of polynomial evaluations at a real point.
* `Sturm.sturmVarPosInf` and `Sturm.sturmVarNegInf`: sign variations at infinity.
* `Sturm.IsSturmChain`: the local sign conditions for a generalized Sturm chain.
-/

public section

open Filter Topology

namespace Sturm

/-- Zero-skipping sign variations of the chain `chain` evaluated at `x`:
the sign variations of the list of evaluations `chain.map (·.eval x)`. -/
@[expose]
noncomputable def sturmVar (chain : List (Polynomial ℝ)) (x : ℝ) : ℕ :=
  List.signVariations (chain.map (Polynomial.eval x))

@[simp] theorem sturmVar_nil (x : ℝ) : sturmVar [] x = 0 := rfl

/-- A chain element that vanishes at `x` contributes no variation at `x`:
`sturmVar` ignores it. -/
theorem sturmVar_cons_zero {q : Polynomial ℝ} {x : ℝ} (h : q.eval x = 0)
    (chain : List (Polynomial ℝ)) :
    sturmVar (q :: chain) x = sturmVar chain x := by
  simp [sturmVar, h]

/-- The sign of the first nonzero entry of a real list, or `0` if every entry is zero. -/
@[expose]
noncomputable def firstSign (l : List ℝ) : SignType :=
  ((l.filter (fun v => decide (v ≠ 0))).head?.map SignType.sign).getD 0

@[simp] theorem firstSign_nil : firstSign [] = 0 := rfl

@[simp] theorem firstSign_cons_zero (l : List ℝ) : firstSign (0 :: l) = firstSign l := by
  simp [firstSign]

@[simp] theorem firstSign_cons_ne {a : ℝ} (l : List ℝ) (ha : a ≠ 0) :
    firstSign (a :: l) = SignType.sign a := by
  simp [firstSign, ha]

/-- Prepending a nonzero entry `a` adds one variation exactly when its sign is
opposite the sign of the next surviving entry. -/
theorem signVariations_cons {a : ℝ} (l : List ℝ) (ha : a ≠ 0) :
    List.signVariations (a :: l) =
      (if SignType.sign a * firstSign l = -1 then 1 else 0) + List.signVariations l := by
  induction l with
  | nil => simp [firstSign]
  | cons b l ih =>
    by_cases hb : b = 0
    · subst b
      simpa only [List.signVariations_cons_zero_cons, List.signVariations_zero_cons,
        firstSign_cons_zero] using ih
    · rw [firstSign_cons_ne l hb, List.signVariations_cons_cons_of_ne_zero l ha hb]
      have ha' : SignType.sign a ≠ 0 := by simpa using ha
      have hb' : SignType.sign b ≠ 0 := by simpa using hb
      have h : (if SignType.sign a = SignType.sign b then (0 : ℕ) else 1) =
          (if SignType.sign a * SignType.sign b = -1 then 1 else 0) := by
        revert ha' hb'
        cases SignType.sign a <;> cases SignType.sign b <;> decide
      rw [h, Nat.add_comm]

/-- Sign variations of the chain at `+∞`: the sign of each element there is the
sign of its leading coefficient, so this is the zero-skipping variation count
of the leading coefficients. The zero polynomial contributes leading
coefficient `0`, which the zero-skipping convention drops. -/
@[expose]
noncomputable def sturmVarPosInf (chain : List (Polynomial ℝ)) : ℕ :=
  List.signVariations (chain.map Polynomial.leadingCoeff)

/-- Sign variations of the chain at `−∞`: the sign of an element there is the
sign of its leading coefficient times `(-1) ^ degree`, so this is the
zero-skipping variation count of `leadingCoeff · (-1) ^ natDegree`. -/
@[expose]
noncomputable def sturmVarNegInf (chain : List (Polynomial ℝ)) : ℕ :=
  List.signVariations (chain.map (fun q => q.leadingCoeff * (-1) ^ q.natDegree))

/-- A generalized Sturm chain for a real polynomial.

At a root of the first polynomial, the product of the first two entries changes
from negative to positive. At a root of an interior entry, its neighbors have
opposite signs. The last entry has no real roots, and every entry is nonzero.

These conditions allow the one-element chain of a nonzero constant polynomial.
-/
structure IsSturmChain (p : Polynomial ℝ) (chain : List (Polynomial ℝ)) : Prop where
  /-- The head of the chain is `p`. -/
  head : chain.head? = some p
  /-- At every real root `r` of `p`, the chain has a second element `q`,
  nonzero at `r`, with `p * q` negative just left of `r` and positive just
  right of `r`. -/
  root_flank : ∀ r : ℝ, p.IsRoot r → ∃ q : Polynomial ℝ, chain[1]? = some q ∧
    q.eval r ≠ 0 ∧
    (∀ᶠ x in 𝓝[<] r, (p * q).eval x < 0) ∧
    (∀ᶠ x in 𝓝[>] r, 0 < (p * q).eval x)
  /-- No chain element is the zero polynomial. -/
  nonzero_mem : ∀ q ∈ chain, q ≠ 0
  /-- Whenever the interior element `b = chain[i+1]` vanishes at `x`, its two
  neighbours `a = chain[i]` and `c = chain[i+2]` are nonzero there and have
  opposite signs. -/
  interior_alternates : ∀ (i : ℕ) (x : ℝ) (a b c : Polynomial ℝ),
    chain[i]? = some a → chain[i + 1]? = some b → chain[i + 2]? = some c →
    b.eval x = 0 → a.eval x ≠ 0 ∧ c.eval x ≠ 0 ∧ a.eval x * c.eval x < 0
  /-- The last element of the chain has no real zero. -/
  last_no_root : ∀ q : Polynomial ℝ, chain.getLast? = some q → ∀ x : ℝ, q.eval x ≠ 0

namespace IsSturmChain

variable {p : Polynomial ℝ} {chain : List (Polynomial ℝ)}

/-- A Sturm chain is nonempty. -/
theorem nonempty (h : IsSturmChain p chain) : chain ≠ [] := by
  rintro rfl
  simpa using h.head

/-- The polynomial counted by a Sturm chain is its first entry. -/
theorem head_mem (h : IsSturmChain p chain) : p ∈ chain :=
  List.mem_of_head? h.head

/-- A polynomial admitting a Sturm chain is nonzero. -/
theorem ne_zero (h : IsSturmChain p chain) : p ≠ 0 :=
  h.nonzero_mem p h.head_mem

end IsSturmChain

end Sturm
