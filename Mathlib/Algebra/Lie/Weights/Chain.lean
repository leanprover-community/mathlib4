/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Trace

/-!
# Chains of roots and weights

TODO Explain. Note also called "string" of roots / weights by some authors.

## Main definitions

TODO

-/

open Set

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [IsNoetherian R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

section IsNilpotent

variable [LieAlgebra.IsNilpotent R L] (χ₁ χ₂ : L → R) (p q : ℤ)

/-- Given two (potential) weights `χ₁` and `χ₂` together with integers `p` and `q`, it is often
useful to study the sum of weight spaces associated to the family of weights `k • χ₁ + χ₂` for
`p < k < q`. -/
def weightSpaceChain : LieSubmodule R L M :=
  ⨆ k ∈ Ioo p q, weightSpace M (k • χ₁ + χ₂)

lemma weightSpaceChain_def :
    weightSpaceChain M χ₁ χ₂ p q = ⨆ k ∈ Ioo p q, weightSpace M (k • χ₁ + χ₂) :=
  rfl

lemma weightSpaceChain_def' :
    weightSpaceChain M χ₁ χ₂ p q = ⨆ k ∈ Finset.Ioo p q, weightSpace M (k • χ₁ + χ₂) := by
  have : ∀ (k : ℤ), k ∈ Ioo p q ↔ k ∈ Finset.Ioo p q := by simp
  simp_rw [weightSpaceChain_def, this]

@[simp]
lemma weightSpaceChain_neg :
    weightSpaceChain M (-χ₁) χ₂ (-q) (-p) = weightSpaceChain M χ₁ χ₂ p q := by
  let e : ℤ ≃ ℤ := ⟨(- ·), (- ·), neg_neg, neg_neg⟩ -- TODO: surely this has a name?
  simp_rw [weightSpaceChain, ← e.biSup_comp (Ioo p q)]
  simp [-mem_Ioo, neg_mem_Ioo_iff]

end IsNilpotent

section IsCartanSubalgebra

open LieAlgebra

variable {H : LieSubalgebra R L} [H.IsCartanSubalgebra] (α χ : H → R) (p q : ℤ)

lemma lie_mem_weightSpaceChain_of_weightSpace_eq_bot_left (hq : weightSpace M (q • α + χ) = ⊥)
    {x : L} {y : M} (hx : x ∈ rootSpace H α) (hy : y ∈ weightSpaceChain M α χ p q) :
    ⁅x, y⁆ ∈ weightSpaceChain M α χ p q := by
  rw [weightSpaceChain, iSup_subtype'] at hy
  induction' hy using LieSubmodule.iSup_induction' with k z hz z₁ z₂ _ _ hz₁ hz₂
  · obtain ⟨k, hk⟩ := k
    suffices weightSpace M ((k + 1) • α + χ) ≤ weightSpaceChain M α χ p q by
      apply this
      simpa using (rootSpaceWeightSpaceProduct R L H M α (k • α + χ) ((k + 1) • α + χ)
        (by rw [add_smul]; abel) (⟨x, hx⟩ ⊗ₜ ⟨z, hz⟩)).property
    rw [weightSpaceChain]
    rcases eq_or_ne (k + 1) q with rfl | hk'; · simp only [hq, bot_le]
    replace hk' : k + 1 ∈ Ioo p q := ⟨by linarith [hk.1], lt_of_le_of_ne hk.2 hk'⟩
    exact le_biSup (fun k ↦ weightSpace M (k • α + χ)) hk'
  · simp
  · rw [lie_add]
    exact add_mem hz₁ hz₂

lemma lie_mem_weightSpaceChain_of_weightSpace_eq_bot_right (hp : weightSpace M (p • α + χ) = ⊥)
    {x : L} {y : M} (hx : x ∈ rootSpace H (-α)) (hy : y ∈ weightSpaceChain M α χ p q) :
    ⁅x, y⁆ ∈ weightSpaceChain M α χ p q := by
  replace hp : weightSpace M ((-p) • (-α) + χ) = ⊥ := by rwa [smul_neg, neg_smul, neg_neg]
  rw [← weightSpaceChain_neg] at hy ⊢
  exact lie_mem_weightSpaceChain_of_weightSpace_eq_bot_left M (-α) χ (-q) (-p) hp hx hy

lemma trace_toEndomorphism_weightSpaceChain_eq_zero
    (hp : weightSpace M (p • α + χ) = ⊥) (hq : weightSpace M (q • α + χ) = ⊥)
    {x : H} (hx : x ∈ (rootSpaceProductNegSelf α).range) :
    LinearMap.trace R _ (toEndomorphism R H (weightSpaceChain M α χ p q) x) = 0 := by
  obtain ⟨t, rfl⟩ := hx
  induction' t using TensorProduct.induction_on with y z _ _ h₁ h₂
  · simp
  · let f : Module.End R (weightSpaceChain M α χ p q) :=
      { toFun := fun ⟨m, hm⟩ ↦ ⟨⁅(y : L), m⁆,
          lie_mem_weightSpaceChain_of_weightSpace_eq_bot_left M α χ p q hq y.property hm⟩
        map_add' := fun _ _ ↦ by simp
        map_smul' := fun t m ↦ by simp }
    let g : Module.End R (weightSpaceChain M α χ p q) :=
      { toFun := fun ⟨m, hm⟩ ↦ ⟨⁅(z : L), m⁆,
          lie_mem_weightSpaceChain_of_weightSpace_eq_bot_right M α χ p q hp z.property hm⟩
        map_add' := fun _ _ ↦ by simp
        map_smul' := fun t m ↦ by simp }
    have hfg : toEndomorphism R H _ (rootSpaceProductNegSelf α (y ⊗ₜ z)) = ⁅f, g⁆ := by ext; simp
    simp [hfg]
  · rw [LieModuleHom.map_add, LieHom.map_add, map_add, h₁, h₂, zero_add]

end IsCartanSubalgebra

end LieModule
