import Mathlib.Tactic.Tendsto.Main

open Stream' Seq Filter Asymptotics

namespace TendstoTactic

namespace PreMS

theorem monomial_trimmed {basis : Basis} {n : ℕ} : (monomial basis n).isTrimmed := by
  sorry

end PreMS

def basis : Basis := [id]

theorem h_basis : MS.wellOrderedBasis basis := by
  sorry

def b1 : ℝ → ℝ := id

def ms1 : MS := MS.monomial basis 0 (by simp [basis]) h_basis

theorem tr1 : ms1.isTrimmed := PreMS.monomial_trimmed

example : Filter.Tendsto basis[0] Filter.atTop Filter.atTop := by
  have h_equiv := MS.IsEquivalent_leadingTerm ms1 h_basis tr1
  conv at h_equiv => arg 2; simp [ms1, MS.monomial]
  apply IsEquivalent.tendsto_atTop h_equiv.symm
  simp [MS.leadingTerm, PreMS.leadingTerm, ms1, MS.monomial, PreMS.monomial, basis, PreMS.one, PreMS.const]
  unfold MS.Term.toFun; simp
  sorry

end TendstoTactic
