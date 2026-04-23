/-
Copyright (c) 2026 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Basis for `ExteriorAlgebra`
-/

@[expose] public section

namespace ExteriorAlgebra

open Module Set Set.powersetCard exteriorPower

variable {R M : Type*} {m n : ℕ} {I : Type*} [LinearOrder I] [CommRing R]
  [AddCommGroup M] [Module R M] (b : Module.Basis I R M)

/-- The direct sum decomposition of the exterior algebra from the graded algebra structure. -/
instance : DirectSum.Decomposition (fun n ↦ ⋀[R]^n M) :=
  GradedRing.toDecomposition (self := ExteriorAlgebra.gradedAlgebra R M)

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the exterior
algebra of `M` formed by the `n`-fold exterior products of elements of `b` for each `n`. -/
noncomputable def _root_.Module.Basis.ExteriorAlgebra : Basis (Finset I) R (ExteriorAlgebra R M) :=
  .reindex
    ((DirectSum.Decomposition.isInternal (fun n => ⋀[R]^n M)).collectedBasis b.exteriorPower)
    Set.powersetCard.prodEquiv

lemma basis_apply (s : Finset I) :
    b.ExteriorAlgebra s = ιMulti_family R s.card b (prodEquiv.symm s).2 := by
  simp [Basis.ExteriorAlgebra]

lemma basis_apply_ofCard {s : Finset I} (s_card : s.card = n) :
    b.ExteriorAlgebra s = ιMulti_family R n b (ofCard s_card) := by
  subst s_card
  simp [basis_apply]

variable (s : powersetCard I m) (t : powersetCard I n)

lemma basis_apply_powersetCard :
    b.ExteriorAlgebra s = ιMulti_family R m b s := by
  simp [basis_apply_ofCard]

lemma basis_eq_coe_basis :
    b.ExteriorAlgebra s = (b.exteriorPower m s : ExteriorAlgebra R M) := by
  rw [basis_apply_powersetCard, exteriorPower.basis_apply, ιMulti_family_apply_coe]

lemma basis_mul_of_not_disjoint (h : ¬Disjoint s.val t.val) :
    b.ExteriorAlgebra s * b.ExteriorAlgebra t = 0 := by
  simpa only [basis_apply_powersetCard] using ιMulti_family_mul_of_not_disjoint R b s t h

lemma basis_mul_of_disjoint (h : Disjoint s.val t.val) :
    b.ExteriorAlgebra s * b.ExteriorAlgebra t =
      (permOfDisjoint h).sign • b.ExteriorAlgebra (disjUnion h) := by
  simpa only [basis_apply_powersetCard] using ιMulti_family_mul_of_disjoint R b s t h

end ExteriorAlgebra
