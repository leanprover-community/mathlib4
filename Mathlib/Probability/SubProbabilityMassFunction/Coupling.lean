import Mathlib.Probability.SubProbabilityMassFunction.Constructions

noncomputable section

namespace SPMF

open scoped Classical
open BigOperators ENNReal

variable {α β : Type*}

section Coupling

noncomputable def fst (μ : SPMF (α × β)) : SPMF α :=
  ⟨λ a => ∑' b, μ (a, b), by rw [←ENNReal.tsum_prod'] ; exact μ.mass_le_one⟩

noncomputable def snd (μ : SPMF (α × β)) : SPMF β :=
  ⟨λ b => ∑' a, μ (a, b), by rw [ENNReal.tsum_comm, ←ENNReal.tsum_prod'] ; exact μ.mass_le_one⟩

theorem fst_apply (μ : SPMF (α × β)) (a : α) : μ.fst a = ∑' b, μ (a, b) := rfl

theorem snd_apply (μ : SPMF (α × β)) (b : β) : μ.snd b = ∑' a, μ (a, b) := rfl

theorem mass_eq_fst_mass (μ : SPMF (α × β)) : μ.mass = μ.fst.mass := by
  simp_rw [mass_def, fst_apply, ENNReal.tsum_prod']

theorem mass_eq_snd_mass (μ : SPMF (α × β)) : μ.mass = μ.snd.mass := by
  simp_rw [mass_def, snd_apply, ENNReal.tsum_prod', ENNReal.tsum_comm (α := α)]

theorem fst_mass_eq_snd_mass (μ : SPMF (α × β)) : μ.fst.mass = μ.snd.mass := by
  rw [← mass_eq_fst_mass, ← mass_eq_snd_mass]

def coupling (μ₁ : SPMF α) (μ₂ : SPMF β) (μ : SPMF (α × β)) := μ₁ = μ.fst ∧ μ₂ = μ.snd

theorem mass_eq_of_coupling_exists (μ₁ : SPMF α) (μ₂ : SPMF β) :
    (∃ μ : SPMF (α × β), coupling μ₁ μ₂ μ) → μ₁.mass = μ₂.mass := by
  rintro ⟨μ, rfl, rfl⟩
  exact μ.fst_mass_eq_snd_mass

end Coupling

/-

def lifting (R : Set (α × β)) (μ₁ : SPMF α) (μ₂ : SPMF β) (μ : SPMF (α × β)) : Prop :=
  coupling μ μ₁ μ₂ ∧ support μ ⊆ R

-/
end SPMF
