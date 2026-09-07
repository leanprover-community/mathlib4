/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Basic.Sign.Basic
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

* `Sturm.signVariations`: sign variations with zero entries removed.
* `Sturm.sturmVar`: sign variations of polynomial evaluations at a real point.
* `Sturm.sturmVarPosInf` and `Sturm.sturmVarNegInf`: sign variations at infinity.
* `Sturm.IsSturmChain`: the local sign conditions for a generalized Sturm chain.
-/

public section

open Filter Topology

namespace Sturm

/-- Count the sign changes of a real list: the number of adjacent pairs
whose product is negative. Callers first drop the zero entries (see
`Sturm.signVariations`), so on a zero-free list this is exactly the number
of adjacent opposite-sign pairs. -/
@[expose]
noncomputable def countSignChanges : List ℝ → ℕ
  | a :: b :: rest => (if a * b < 0 then 1 else 0) + countSignChanges (b :: rest)
  | _ => 0

@[simp] theorem countSignChanges_nil : countSignChanges [] = 0 := rfl

@[simp] theorem countSignChanges_singleton (a : ℝ) : countSignChanges [a] = 0 := rfl

theorem countSignChanges_cons_cons (a b : ℝ) (rest : List ℝ) :
    countSignChanges (a :: b :: rest) =
      (if a * b < 0 then 1 else 0) + countSignChanges (b :: rest) := rfl

/-- Zero-skipping sign variations of a real list: drop the zeros, then count
the adjacent opposite-sign pairs. This is the variation count that both the
pointwise chain evaluations and the leading-coefficient signs at `±∞` feed
into. -/
@[expose]
noncomputable def signVariations (l : List ℝ) : ℕ :=
  countSignChanges (l.filter (fun v => decide (v ≠ 0)))

@[simp] theorem signVariations_nil : signVariations [] = 0 := rfl

@[simp] theorem signVariations_singleton (a : ℝ) : signVariations [a] = 0 := by
  by_cases ha : a = 0 <;> simp [signVariations, ha]

/-- Prepending a zero entry does not change the sign variations. -/
@[simp] theorem signVariations_cons_zero (l : List ℝ) :
    signVariations (0 :: l) = signVariations l := by
  simp [signVariations]

/-- A nonzero first entry survives removal of zero entries. -/
theorem signVariations_cons_ne (a : ℝ) (l : List ℝ) (ha : a ≠ 0) :
    signVariations (a :: l) =
      countSignChanges (a :: l.filter (fun v => decide (v ≠ 0))) := by
  simp [signVariations, ha]

/-- Zero-skipping sign variations of the chain `chain` evaluated at `x`:
the sign variations of the list of evaluations `chain.map (·.eval x)`. -/
@[expose]
noncomputable def sturmVar (chain : List (Polynomial ℝ)) (x : ℝ) : ℕ :=
  signVariations (chain.map (Polynomial.eval x))

@[simp] theorem sturmVar_nil (x : ℝ) : sturmVar [] x = 0 := rfl

/-- A chain element that vanishes at `x` contributes no variation at `x`:
`sturmVar` ignores it. -/
theorem sturmVar_cons_zero {q : Polynomial ℝ} {x : ℝ} (h : q.eval x = 0)
    (chain : List (Polynomial ℝ)) :
    sturmVar (q :: chain) x = sturmVar chain x := by
  simp [sturmVar, List.map_cons, signVariations, h]

/-- Two real lists whose entries have pointwise equal signs have equal
`countSignChanges`: the sign-change count reads only the signs of the entries. -/
theorem countSignChanges_congr {l₁ l₂ : List ℝ}
    (h : List.Forall₂ (fun u v => SignType.sign u = SignType.sign v) l₁ l₂) :
    countSignChanges l₁ = countSignChanges l₂ := by
  induction h with
  | nil => rfl
  | @cons a b l₁' l₂' hab htail ih =>
    cases htail with
    | nil => rfl
    | @cons c d l₁'' l₂'' hcd _ =>
      rw [countSignChanges_cons_cons, countSignChanges_cons_cons]
      have hiff : (a * c < 0) ↔ (b * d < 0) := by
        rw [← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, sign_mul, sign_mul, hab, hcd]
      simp only [hiff, ih]

/-- Dropping the zero entries commutes with a pointwise sign-equal
correspondence: the filtered lists remain pointwise sign-equal. -/
private theorem filter_ne_zero_congr {l₁ l₂ : List ℝ}
    (h : List.Forall₂ (fun u v => SignType.sign u = SignType.sign v) l₁ l₂) :
    List.Forall₂ (fun u v => SignType.sign u = SignType.sign v)
      (l₁.filter (fun v => decide (v ≠ 0))) (l₂.filter (fun v => decide (v ≠ 0))) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b l₁' l₂' hab htail ih =>
    have hzero : (a = 0) ↔ (b = 0) := by
      rw [← sign_eq_zero_iff (a := a), ← sign_eq_zero_iff (a := b), hab]
    by_cases ha : a = 0
    · simpa [ha, hzero.mp ha] using ih
    · simpa [ha, mt hzero.mpr ha] using
        List.Forall₂.cons (R := fun u v : ℝ => SignType.sign u = SignType.sign v) hab ih

/-- `signVariations` reads only the signs of the entries: two real lists whose
entries are pointwise sign-equal have equal sign variations. -/
theorem signVariations_congr {l₁ l₂ : List ℝ}
    (h : List.Forall₂ (fun u v => SignType.sign u = SignType.sign v) l₁ l₂) :
    signVariations l₁ = signVariations l₂ :=
  countSignChanges_congr (filter_ne_zero_congr h)

/-- The sign of the first surviving (nonzero) entry of a real list, as an
`Option SignType`: `none` when every entry is zero. This is the piece of local
state that governs how prepending a nonzero entry changes `signVariations`. -/
@[expose]
noncomputable def firstSign (l : List ℝ) : Option SignType :=
  (l.filter (fun v => decide (v ≠ 0))).head?.map (fun a => SignType.sign a)

@[simp] theorem firstSign_nil : firstSign [] = none := rfl

theorem firstSign_cons_zero {a : ℝ} (l : List ℝ) (ha : a = 0) :
    firstSign (a :: l) = firstSign l := by
  unfold firstSign; rw [List.filter_cons_of_neg (by simp [ha])]

theorem firstSign_cons_ne {a : ℝ} (l : List ℝ) (ha : a ≠ 0) :
    firstSign (a :: l) = some (SignType.sign a) := by
  unfold firstSign
  rw [List.filter_cons_of_pos (by simp [ha]), List.head?_cons, Option.map_some]

private theorem sign_mul_eq_neg_one {a b : ℝ} :
    (SignType.sign a * SignType.sign b = -1) ↔ a * b < 0 := by
  rw [← sign_mul, sign_eq_neg_one_iff]

/-- Prepending a nonzero entry `a` adds one variation exactly when its sign is
opposite the sign of the next surviving entry. -/
theorem signVariations_cons {a : ℝ} (l : List ℝ) (ha : a ≠ 0) :
    signVariations (a :: l) =
      (firstSign l).elim 0
        (fun t => if SignType.sign a * t = -1 then 1 else 0) + signVariations l := by
  induction l with
  | nil => rw [signVariations_cons_ne a [] ha]; simp [firstSign]
  | cons b l' ih =>
    by_cases hb : b = 0
    · subst hb
      rw [firstSign_cons_zero l' rfl, signVariations_cons_zero l',
        signVariations_cons_ne a (0 :: l') ha, List.filter_cons_of_neg (by simp),
        ← signVariations_cons_ne a l' ha]
      exact ih
    · rw [firstSign_cons_ne l' hb, signVariations_cons_ne a (b :: l') ha,
        List.filter_cons_of_pos (by simp [hb]), countSignChanges_cons_cons,
        ← signVariations_cons_ne b l' hb]
      simp only [Option.elim_some]
      congr 1
      simp only [sign_mul_eq_neg_one]

/-- Sign variations of the chain at `+∞`: the sign of each element there is the
sign of its leading coefficient, so this is the zero-skipping variation count
of the leading coefficients. The zero polynomial contributes leading
coefficient `0`, which the zero-skipping convention drops. -/
@[expose]
noncomputable def sturmVarPosInf (chain : List (Polynomial ℝ)) : ℕ :=
  signVariations (chain.map Polynomial.leadingCoeff)

/-- Sign variations of the chain at `−∞`: the sign of an element there is the
sign of its leading coefficient times `(-1) ^ degree`, so this is the
zero-skipping variation count of `leadingCoeff · (-1) ^ natDegree`. -/
@[expose]
noncomputable def sturmVarNegInf (chain : List (Polynomial ℝ)) : ℕ :=
  signVariations (chain.map (fun q => q.leadingCoeff * (-1) ^ q.natDegree))

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
