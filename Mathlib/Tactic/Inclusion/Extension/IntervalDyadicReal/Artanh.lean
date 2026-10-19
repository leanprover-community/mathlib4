/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-!
# doc
-/

@[expose] public section

namespace Inclusion

namespace IntervalDyadicReal

-- don't use ℚ
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/LeanCert.20-.20Verified.20Computation.20.26.20Interval.20Arithmetic/near/567588580

-- TODO: use binary splitting
-- <http://numbers.computation.free.fr/Constants/Algorithms/splitting.html>
/-- TODO doc -/
def artanhSum (n : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1)

/-- TODO doc -/
def artanhError (n : ℕ) (x : ℚ) : ℚ :=
  |x| ^ (2 * n + 1) / (1 - x ^ 2)

/-- TODO doc -/
def _root_.Dyadic.artanhLower (q : Dyadic) (prec : ℕ) : Dyadic :=
  if q.toRat ≤ -1 ∨ 1 ≤ q.toRat then 0
  else (artanhSum (prec + 2) q.toRat - artanhError (prec + 2) q.toRat).toDyadic prec

/-- TODO doc -/
def _root_.Dyadic.artanhUpper (q : Dyadic) (prec : ℕ) : Dyadic :=
  if q.toRat = 0 then 0
  else if q.toRat ≤ -1 ∨ 1 ≤ q.toRat then 0
  else (artanhSum (prec + 2) q.toRat + artanhError (prec + 2) q.toRat).toDyadic prec + .step prec

end IntervalDyadicReal

-- move these three def

/-- TODO doc -/
def Interval.isEmpty {α : Type*} [LinearOrder α] (I : Interval α) : Bool :=
  match I.lb, I.ub with
  | ⊥, _ => false
  | _, ⊤ => false
  | .some l, .some u => decide (u < l)

/-- TODO doc -/
def Interval.inter? {α : Type*} [LinearOrder α] (I J : Interval α) : Option (Interval α) :=
  let K : Interval α := I.inter J
  if K.isEmpty then none else some K

/-- TODO doc -/
def Interval.insert {α : Type*} [LinearOrder α] (I : Interval α) (a : α) : Interval α where
  lb := min I.lb a
  ub := max I.ub a

/-- TODO doc -/
def Interval.artanh (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  match I.inter? ⟨(-1 : Dyadic), 1⟩ with
  | none => .singleton 0
  | some ⟨.some lb, .some ub⟩ =>
    let J : Interval Dyadic := ⟨
      if lb = -1 then (if ub = -1 then 0 else ⊥) else lb.artanhLower prec,
      if ub = 1 then (if lb = 1 then 0 else ⊤) else ub.artanhUpper prec
    ⟩
    if lb = (-1) ∨ ub = 1 then J.insert 0 else J
  | some _ => .singleton 0 -- impossible case

@[inclusion_op interval_dyadic_real]
theorem artanh_mem {x : ℝ} {I : Interval Dyadic} (prec : ℕ) (hx : x ∈ I) :
    x.artanh ∈ I.artanh prec := by
  sorry

end Inclusion

#lint
