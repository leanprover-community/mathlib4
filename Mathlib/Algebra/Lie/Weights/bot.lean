module

public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.Algebra.Lie.Weights.IsSimple
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.CategoryTheory.Category.Basic

namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
open LieAlgebra LieModule Module
variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

-- Note that after https://github.com/leanprover-community/mathlib4/issues/10068 (Cartan's criterion) is complete we can omit `[IsKilling K L]`
variable [IsKilling K L] [IsTriangularizable K H L]

open Weight in
lemma l1 (q : Submodule K (Dual K H))
    (h₀ : ∀ (i : H.root), q ∈ End.invtSubmodule ((rootSystem H).reflection i))
    (h₁ : q ≠ ⊥) : q = ⊤ := by
  let J := (invtSubmoduleToLieIdeal q h₀)
  have r_j2 : J ≠ ⊥ := by
    unfold J invtSubmoduleToLieIdeal
    simp only [ne_eq, ← LieSubmodule.toSubmodule_eq_bot, LieSubmodule.iSup_toSubmodule,
               iSup_eq_bot, not_forall]
    -- Inline exists_root_mem_q_of_ne_bot: find a root in q
    -- Step 1: Get β ∈ q with β ≠ 0
    obtain ⟨β, hβ_mem, hβ_ne⟩ := (Submodule.ne_bot_iff q).mp h₁
    -- Step 2: Find root i such that ⟨β, coroot i⟩ ≠ 0
    obtain ⟨i, hi⟩ := LieAlgebra.IsKilling.exists_coroot_pairing_ne_zero β hβ_ne
    -- Step 3: Show root i ∈ q using reflection invariance
    have h_root_in_q : ((rootSystem H).root i : Dual K H) ∈ q := by
      have h_refl : (rootSystem H).reflection i β ∈ q := h₀ i hβ_mem
      -- β - ⟨β, coroot i⟩ • root i = reflection i β (by definition)
      have h_smul_sub : β - ((rootSystem H).toLinearMap β ((rootSystem H).coroot i)) •
                        (rootSystem H).root i ∈ q := by
        convert h_refl using 1
      -- So ⟨β, coroot i⟩ • root i ∈ q
      have h_smul_in : ((rootSystem H).toLinearMap β ((rootSystem H).coroot i)) •
                       (rootSystem H).root i ∈ q := by
        simpa using q.sub_mem hβ_mem h_smul_sub
      -- Scale by inverse to get root i ∈ q
      have h_scaled := q.smul_mem ((rootSystem H).toLinearMap β ((rootSystem H).coroot i))⁻¹ h_smul_in
      simp only [smul_smul, inv_mul_cancel₀ hi, one_smul] at h_scaled
      exact h_scaled
    -- Now we have root i ∈ q, and roots are nonzero
    have hα : (i : Weight K H L).IsNonZero := by grind
    -- Provide the witness
    refine ⟨⟨i.val, h_root_in_q, hα⟩, ?_⟩
    -- Show sl2SubmoduleOfRoot ≠ ⊥ using exists_ne_zero
    intro h_eq_bot
    obtain ⟨e, he_mem, he_ne⟩ := (i : Weight K H L).exists_ne_zero
    have he_in_sl2 : e ∈ sl2SubmoduleOfRoot hα := by
      rw [sl2SubmoduleOfRoot_eq_sup]
      have h1 : genWeightSpace L (i : Weight K H L) ≤
                genWeightSpace L (i : Weight K H L) ⊔ genWeightSpace L (-(i : Weight K H L)) := le_sup_left
      have h2 : genWeightSpace L (i : Weight K H L) ⊔ genWeightSpace L (-(i : Weight K H L)) ≤
                genWeightSpace L (i : Weight K H L) ⊔ genWeightSpace L (-(i : Weight K H L)) ⊔ corootSubmodule (i : Weight K H L) := le_sup_left
      exact h2 (h1 he_mem)
    rw [Submodule.eq_bot_iff] at h_eq_bot
    exact he_ne (h_eq_bot e he_in_sl2)
  sorry


end  LieAlgebra.IsKilling
