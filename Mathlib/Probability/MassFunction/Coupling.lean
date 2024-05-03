import Mathlib.Probability.MassFunction.Constructions

open BigOperators ENNReal

namespace SPMF

variable {α β : Type*}

section Coupling

noncomputable def fst (μ : SPMF (α × β)) : SPMF α :=
  ⟨λ a => ∑' b, μ (a, b), by rw [←ENNReal.tsum_prod'] ; exact mass_le_one⟩

noncomputable def snd (μ : SPMF (α × β)) : SPMF β :=
  ⟨λ b => ∑' a, μ (a, b), by rw [ENNReal.tsum_comm, ←ENNReal.tsum_prod'] ; exact mass_le_one⟩

theorem fst_def (μ : SPMF (α × β)) (a : α) : μ.fst a = ∑' b, μ (a, b) := rfl

theorem snd_def (μ : SPMF (α × β)) (b : β) : μ.snd b = ∑' a, μ (a, b) := rfl

theorem mass_eq_fst_mass (μ : SPMF (α × β)) : mass μ = mass μ.fst := ENNReal.tsum_prod'

theorem mass_eq_snd_mass (μ : SPMF (α × β)) : mass μ = mass μ.snd :=
  ENNReal.tsum_prod'.trans (ENNReal.tsum_comm (α := α))

theorem fst_mass_eq_snd_mass (μ : SPMF (α × β)) : mass μ.fst = mass μ.snd := by
  rw [← mass_eq_fst_mass, ← mass_eq_snd_mass]

def coupling (μ₁ : SPMF α) (μ₂ : SPMF β) (μ : SPMF (α × β)) := μ₁ = μ.fst ∧ μ₂ = μ.snd

theorem coupling_def {μ₁ : SPMF α} {μ₂ : SPMF β} {μ : SPMF (α × β)} :
  coupling μ₁ μ₂ μ ↔ μ₁ = μ.fst ∧ μ₂ = μ.snd := Iff.rfl

theorem mass_eq_of_coupling_exists (μ₁ : SPMF α) (μ₂ : SPMF β) :
    (∃ μ : SPMF (α × β), coupling μ₁ μ₂ μ) → mass μ₁ = mass μ₂ := by
  rintro ⟨μ, rfl, rfl⟩
  exact μ.fst_mass_eq_snd_mass

section flip

noncomputable def flip := bernoulli (1/2) (by norm_num)

theorem support_flip : massSupport flip = {false, true} := by
  refine' (massSupport_bernoulli _).trans _
  norm_num

@[simp]
theorem flip_apply (a : Bool) : flip a = 1/2 := (bernoulli_apply _ _).trans (by norm_num)

noncomputable def couple_flip_id : SPMF (Bool × Bool) :=
    ofFintype (fun (a, b) => if a = b then 1/2 else 0)
  (by norm_num [(ENNReal.inv_two_add_inv_two).le])

@[simp]
theorem couple_flip_id_apply (ab : (Bool × Bool)) :
  couple_flip_id ab = if ab.fst = ab.snd then 1/2 else 0 := rfl

@[simp]
theorem couple_flip_id_apply' (a : Bool) (b : Bool) :
  couple_flip_id (a, b) = if a = b then 1/2 else 0 := rfl

noncomputable def couple_flip_neg : SPMF (Bool × Bool) :=
    ofFintype (fun (a, b) => if a = !b then 1/2 else 0)
  (by norm_num [(ENNReal.inv_two_add_inv_two).le])

@[simp]
theorem couple_flip_neg_apply (ab : (Bool × Bool)) :
  couple_flip_neg ab = if ab.fst = !ab.snd then 1/2 else 0 := rfl

@[simp]
theorem couple_flip_neg_apply' (a : Bool) (b : Bool) :
  couple_flip_neg (a, b) = if a = !b then 1/2 else 0 := rfl

example : coupling flip flip couple_flip_id := by
  rw [coupling_def]
  constructor <;>
  ext b <;> cases b <;>
  simp only [flip_apply, one_div, fst_def, snd_def, couple_flip_id_apply, tsum_bool,
    ↓reduceIte, zero_add, add_zero]

example : coupling flip flip couple_flip_neg := by
  rw [coupling_def]
  constructor <;>
  ext b <;> cases b <;>
  simp only [flip_apply, one_div, fst_def, snd_def, couple_flip_neg_apply, tsum_bool,
    ↓reduceIte, zero_add, add_zero, Bool.not_false, Bool.not_true]

end flip

end Coupling

/-

def lifting (R : Set (α × β)) (μ₁ : SPMF α) (μ₂ : SPMF β) (μ : SPMF (α × β)) : Prop :=
  coupling μ μ₁ μ₂ ∧ support μ ⊆ R

-/
end SPMF
