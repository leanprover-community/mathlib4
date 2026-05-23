/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!

# The extension of adjoining all pth root to a field of characteriatic p.

-/

public section

variable (k : Type*) [Field k]

/-- Adjoining all `p`-th root to a field of characteristic `p`.
It is defined as the field itself with algebra map being the frobenius map. -/
@[nolint unusedArguments, expose]
def adjoinPthRoots (p : ℕ) [ExpChar k p] := k

variable (p : ℕ) [ExpChar k p]

instance : Field (adjoinPthRoots k p) := inferInstanceAs (Field k)

instance : Algebra k (adjoinPthRoots k p) := (frobenius k p).toAlgebra

/-- The map `adjoinPthRoots k p → k` with underlying map `RingHom.id`. -/
def adjoinPthRootsSelf : (adjoinPthRoots k p) →+* k := RingHom.id k

lemma adjoinPthRootsSelf_algebraMap (x : adjoinPthRoots k p) :
    algebraMap k (adjoinPthRoots k p) (adjoinPthRootsSelf k p x) = x ^ p := by
  rfl

instance [Fact (Nat.Prime p)] : Algebra.IsAlgebraic k (adjoinPthRoots k p) where
  isAlgebraic x := by
    use Polynomial.X ^ p - Polynomial.C (adjoinPthRootsSelf k p x)
    refine ⟨(Polynomial.monic_X_pow_sub_C _ (NeZero.ne' p).symm).ne_zero, ?_⟩
    simp [adjoinPthRootsSelf_algebraMap]

/-- The map `k → adjoinPthRoots k p` for taking `p`-th root with underlying map `RingHom.id`. -/
def adjoinPthRootsPthRoot : k →+* (adjoinPthRoots k p) := RingHom.id k

lemma adjoinPthRootsPthRoot_bijective : Function.Bijective (adjoinPthRootsPthRoot k p) :=
  (RingEquiv.refl k).bijective

lemma adjoinPthRootsPthRoot_pow (x : k) : algebraMap k (adjoinPthRoots k p) x =
    (adjoinPthRootsPthRoot k p x) ^ p := by
  rfl

lemma adjoinPthRootsSelf_pthRoot (x : k) :
    adjoinPthRootsSelf k p (adjoinPthRootsPthRoot k p x) = x := by
  rfl

lemma adjoinPthRootsPthRoot_self (x : adjoinPthRoots k p) :
    adjoinPthRootsPthRoot k p (adjoinPthRootsSelf k p x) = x := by
  rfl

instance adjoinPthRoots_purelyInseparable : IsPurelyInseparable k (adjoinPthRoots k p) := by
  rw [isPurelyInseparable_iff_pow_mem k p]
  intro x
  use 1, adjoinPthRootsSelf k p x
  rw [adjoinPthRootsPthRoot_pow, pow_one, adjoinPthRootsPthRoot_self]
