/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Module.LinearMap.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous.IsDomain

/-!
# Characteristic polynomials of linear families of endomorphisms

Existence of a nil-regular element for a linear family of endomorphisms.
-/

open scoped Matrix

namespace LinearMap

open MvPolynomial

variable {R L M : Type*}
  [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
  (φ : L →ₗ[R] Module.End R M) [Module.Free R M]
  [Module.Finite R M] [Module.Finite R L] [Module.Free R L]

section IsDomain

variable [IsDomain R]

open Cardinal Module MvPolynomial Module.Free in
lemma exists_isNilRegular_of_finrank_le_card (h : finrank R M ≤ #R) :
    ∃ x : L, IsNilRegular φ x := by
  let b := chooseBasis R L
  let bₘ := chooseBasis R M
  let n := Fintype.card (ChooseBasisIndex R M)
  have aux :
    ((polyCharpoly φ b).coeff (nilRank φ)).IsHomogeneous (n - nilRank φ) :=
    polyCharpoly_coeff_isHomogeneous _ b (nilRank φ) (n - nilRank φ)
      (by simp [nilRank_le_card φ bₘ, finrank_eq_card_chooseBasisIndex])
  obtain ⟨x, hx⟩ : ∃ r, eval r ((polyCharpoly _ b).coeff (nilRank φ)) ≠ 0 := by
    by_contra! h₀
    apply polyCharpoly_coeff_nilRank_ne_zero φ b
    apply aux.eq_zero_of_forall_eval_eq_zero_of_le_card h₀ (le_trans _ h)
    simp only [finrank_eq_card_chooseBasisIndex, Nat.cast_le, Nat.sub_le]
  let c := Finsupp.equivFunOnFinite.symm x
  use b.repr.symm c
  rwa [isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ b, LinearEquiv.apply_symm_apply]

lemma exists_isNilRegular [Infinite R] : ∃ x : L, IsNilRegular φ x := by
  apply exists_isNilRegular_of_finrank_le_card
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

end IsDomain

end LinearMap
