/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Trace

/-!
# Chains of roots and weights

Given roots `α` and `β` of a Lie algebra, together with elements `x` in the `α`-root space and
`y` in the `β`-root space, it follows from the Leibniz identity that `⁅x, y⁆` is either zero or
belongs to the `α + β`-root space. Iterating this operation leads to the study of families of
roots of the form `k • α + β`. Such a family is known as the `α`-chain through `β` (or sometimes,
the `α`-string through `β`) and the study of the sum of the corresponding root spaces is an
important technique.

More generally if `α` is a root and `χ` is a weight of a representation, it is useful to study the
`α`-chain through `χ`.

We provide basic definitions and results to support `α`-chain techniques in this file.

## Main definitions / results

 * `LieModule.exists₂_weightSpace_smul_add_eq_bot`: given weights `χ₁`, `χ₂` if `χ₁ ≠ 0`, we can
   find `p < 0` and `q > 0` such that the weight spaces `p • χ₁ + χ₂` and `q • χ₁ + χ₂` are both
   trivial.
 * `LieModule.weightSpaceChain`: given weights `χ₁`, `χ₂` together with integers `p` and `q`, this
   is the sum of the weight spaces `k • χ₁ + χ₂` for `p < k < q`.
 * `LieModule.trace_toEndomorphism_weightSpaceChain_eq_zero`: given a root `α` relative to a Cartan
   subalgebra `H`, there is a natural ideal `(rootSpaceProductNegSelf α).range` in `H`. This lemma
   states that this ideal acts by trace-zero endomorphisms on the sum of root spaces of any
   `α`-chain, provided the weight spaces at the endpoints are both trivial.
 * `LieModule.exists_forall_mem_rootSpaceProductNegSelf_smul_add_eq_zero`: given a (potential) root
   `α` relative to a Cartan subalgebra `H`, if we restrict to the ideal
   `(rootSpaceProductNegSelf α).range` of `H`, we may find an integral linear combination between
   `α` and any weight `χ` of a representation.

-/

open BigOperators FiniteDimensional Function Set

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

section IsNilpotent

variable [LieAlgebra.IsNilpotent R L] (χ₁ χ₂ : L → R) (p q : ℤ)

section

variable [NoZeroSMulDivisors ℤ R] [NoZeroSMulDivisors R M] [IsNoetherian R M] (hχ₁ : χ₁ ≠ 0)

lemma eventually_weightSpace_smul_add_eq_bot :
    ∀ᶠ (k : ℕ) in Filter.atTop, weightSpace M (k • χ₁ + χ₂) = ⊥ := by
  let f : ℕ → L → R := fun k ↦ k • χ₁ + χ₂
  suffices Injective f by
    rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite, ← finite_image_iff (this.injOn _)]
    apply (finite_weightSpace_ne_bot R L M).subset
    simp [f]
  intro k l hkl
  replace hkl : (k : ℤ) • χ₁ = (l : ℤ) • χ₁ := by
    simpa only [f, add_left_inj, natCast_zsmul] using hkl
  exact Nat.cast_inj.mp <| smul_left_injective ℤ hχ₁ hkl

lemma exists_weightSpace_smul_add_eq_bot :
    ∃ k > 0, weightSpace M (k • χ₁ + χ₂) = ⊥ :=
  (Nat.eventually_pos.and <| eventually_weightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁).exists

lemma exists₂_weightSpace_smul_add_eq_bot :
    ∃ᵉ (p < (0 : ℤ)) (q > (0 : ℤ)),
      weightSpace M (p • χ₁ + χ₂) = ⊥ ∧
      weightSpace M (q • χ₁ + χ₂) = ⊥ := by
  obtain ⟨q, hq₀, hq⟩ := exists_weightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁
  obtain ⟨p, hp₀, hp⟩ := exists_weightSpace_smul_add_eq_bot M (-χ₁) χ₂ (neg_ne_zero.mpr hχ₁)
  refine ⟨-(p : ℤ), by simpa, q, by simpa, ?_, ?_⟩
  · rw [neg_smul, ← smul_neg, natCast_zsmul]
    exact hp
  · rw [natCast_zsmul]
    exact hq

end

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
  let e : ℤ ≃ ℤ := neg_involutive.toPerm
  simp_rw [weightSpaceChain, ← e.biSup_comp (Ioo p q)]
  simp [e, -mem_Ioo, neg_mem_Ioo_iff]

lemma weightSpace_le_weightSpaceChain {k : ℤ} (hk : k ∈ Ioo p q) :
    weightSpace M (k • χ₁ + χ₂) ≤ weightSpaceChain M χ₁ χ₂ p q :=
  le_biSup (fun i ↦ weightSpace M (i • χ₁ + χ₂)) hk

end IsNilpotent

section LieSubalgebra

open LieAlgebra

variable {H : LieSubalgebra R L} (α χ : H → R) (p q : ℤ)

lemma lie_mem_weightSpaceChain_of_weightSpace_eq_bot_right [LieAlgebra.IsNilpotent R H]
    (hq : weightSpace M (q • α + χ) = ⊥)
    {x : L} (hx : x ∈ rootSpace H α)
    {y : M} (hy : y ∈ weightSpaceChain M α χ p q) :
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

lemma lie_mem_weightSpaceChain_of_weightSpace_eq_bot_left [LieAlgebra.IsNilpotent R H]
    (hp : weightSpace M (p • α + χ) = ⊥)
    {x : L} (hx : x ∈ rootSpace H (-α))
    {y : M} (hy : y ∈ weightSpaceChain M α χ p q) :
    ⁅x, y⁆ ∈ weightSpaceChain M α χ p q := by
  replace hp : weightSpace M ((-p) • (-α) + χ) = ⊥ := by rwa [smul_neg, neg_smul, neg_neg]
  rw [← weightSpaceChain_neg] at hy ⊢
  exact lie_mem_weightSpaceChain_of_weightSpace_eq_bot_right M (-α) χ (-q) (-p) hp hx hy

section IsCartanSubalgebra

variable [H.IsCartanSubalgebra] [IsNoetherian R L]

lemma trace_toEndomorphism_weightSpaceChain_eq_zero
    (hp : weightSpace M (p • α + χ) = ⊥)
    (hq : weightSpace M (q • α + χ) = ⊥)
    {x : H} (hx : x ∈ (rootSpaceProductNegSelf α).range) :
    LinearMap.trace R _ (toEndomorphism R H (weightSpaceChain M α χ p q) x) = 0 := by
  obtain ⟨t, rfl⟩ := hx
  induction' t using TensorProduct.induction_on with y z _ _ h₁ h₂
  · simp
  · let f : Module.End R (weightSpaceChain M α χ p q) :=
      { toFun := fun ⟨m, hm⟩ ↦ ⟨⁅(y : L), m⁆,
          lie_mem_weightSpaceChain_of_weightSpace_eq_bot_right M α χ p q hq y.property hm⟩
        map_add' := fun _ _ ↦ by simp
        map_smul' := fun t m ↦ by simp }
    let g : Module.End R (weightSpaceChain M α χ p q) :=
      { toFun := fun ⟨m, hm⟩ ↦ ⟨⁅(z : L), m⁆,
          lie_mem_weightSpaceChain_of_weightSpace_eq_bot_left M α χ p q hp z.property hm⟩
        map_add' := fun _ _ ↦ by simp
        map_smul' := fun t m ↦ by simp }
    have hfg : toEndomorphism R H _ (rootSpaceProductNegSelf α (y ⊗ₜ z)) = ⁅f, g⁆ := by
      ext; simp [f, g]
    simp [hfg]
  · rw [LieModuleHom.map_add, LieHom.map_add, map_add, h₁, h₂, zero_add]

/-- Given a (potential) root `α` relative to a Cartan subalgebra `H`, if we restrict to the ideal
`I = (rootSpaceProductNegSelf α).range` of `H` (informally, `I = ⁅H(α), H(-α)⁆`), we may find an
integral linear combination between `α` and any weight `χ` of a representation.

This is Proposition 4.4 from [carter2005] and is a key step in the proof that the roots of a
semisimple Lie algebra form a root system. It shows that the restriction of `α` to `I` vanishes iff
the restriction of every root to `I` vanishes (which cannot happen in a semisimple Lie algebra). -/
lemma exists_forall_mem_rootSpaceProductNegSelf_smul_add_eq_zero
    [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [NoZeroSMulDivisors R M] [IsNoetherian R M]
    (hα : α ≠ 0) (hχ : weightSpace M χ ≠ ⊥) :
    ∃ a b : ℤ, 0 < b ∧ ∀ x ∈ (rootSpaceProductNegSelf α).range, (a • α + b • χ) x = 0 := by
  obtain ⟨p, hp₀, q, hq₀, hp, hq⟩ := exists₂_weightSpace_smul_add_eq_bot M α χ hα
  let a := ∑ i in Finset.Ioo p q, finrank R (weightSpace M (i • α + χ)) • i
  let b := ∑ i in Finset.Ioo p q, finrank R (weightSpace M (i • α + χ))
  have hb : 0 < b := by
    replace hχ : Nontrivial (weightSpace M χ) := by rwa [LieSubmodule.nontrivial_iff_ne_bot]
    refine Finset.sum_pos' (fun _ _ ↦ zero_le _) ⟨0, Finset.mem_Ioo.mpr ⟨hp₀, hq₀⟩, ?_⟩
    rw [zero_smul, zero_add]
    exact finrank_pos
  refine ⟨a, b, Int.ofNat_pos.mpr hb, fun x hx ↦ ?_⟩
  let N : ℤ → Submodule R M := fun k ↦ weightSpace M (k • α + χ)
  have h₁ : CompleteLattice.Independent fun (i : Finset.Ioo p q) ↦ N i := by
    rw [← LieSubmodule.independent_iff_coe_toSubmodule]
    refine (independent_weightSpace R H M).comp fun i j hij ↦ ?_
    exact SetCoe.ext <| smul_left_injective ℤ hα <| by rwa [add_left_inj] at hij
  have h₂ : ∀ i, MapsTo (toEndomorphism R H M x) ↑(N i) ↑(N i) := fun _ _ ↦ LieSubmodule.lie_mem _
  have h₃ : weightSpaceChain M α χ p q = ⨆ i ∈ Finset.Ioo p q, N i := by
    simp_rw [weightSpaceChain_def', LieSubmodule.iSup_coe_toSubmodule]
  rw [← trace_toEndomorphism_weightSpaceChain_eq_zero M α χ p q hp hq hx,
    ← LieSubmodule.toEndomorphism_restrict_eq_toEndomorphism,
    LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup _ h₁ h₂ (weightSpaceChain M α χ p q) h₃]
  simp_rw [LieSubmodule.toEndomorphism_restrict_eq_toEndomorphism,
    trace_toEndomorphism_weightSpace, Pi.add_apply, Pi.smul_apply, smul_add, ← smul_assoc,
    Finset.sum_add_distrib, ← Finset.sum_smul, natCast_zsmul]

end IsCartanSubalgebra

end LieSubalgebra

end LieModule
