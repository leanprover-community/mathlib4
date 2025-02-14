/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Data.Finsupp.MonomialOrder.DegLex

/-! # Some lemmas about the deglex monomial order on multivariate polynomials -/

namespace MvPolynomial

open MonomialOrder Finsupp

open scoped MonomialOrder

variable {σ : Type*} [LinearOrder σ] {R : Type*} [CommSemiring R] [WellFoundedGT σ]
  {f g : MvPolynomial σ R}

theorem degree_degLexDegree : (degLex.degree f).degree = f.totalDegree := by
  by_cases hf : f = 0
  · simp [hf]
  apply le_antisymm
  · apply MvPolynomial.le_totalDegree
    rw [MvPolynomial.mem_support_iff]
    change degLex.leadingCoeff f ≠ 0
    rw [leadingCoeff_ne_zero_iff]
    exact hf
  · unfold MvPolynomial.totalDegree
    apply Finset.sup_le
    intro b hb
    exact DegLex.monotone_degree (degLex.le_degree hb)

theorem degLex_totalDegree_monotone (h : degLex.degree f ≼[degLex] degLex.degree g) :
    f.totalDegree ≤ g.totalDegree := by
  simp only [← MvPolynomial.degree_degLexDegree]
  exact DegLex.monotone_degree h

end MvPolynomial
