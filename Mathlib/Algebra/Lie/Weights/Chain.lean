/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Lie.InvariantForm
import Mathlib.Algebra.Lie.Weights.Linear
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.PID
import LeanCopilot

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

 * `LieModule.exists₂_genWeightSpace_smul_add_eq_bot`: given weights `χ₁`, `χ₂` if `χ₁ ≠ 0`, we can
   find `p < 0` and `q > 0` such that the weight spaces `p • χ₁ + χ₂` and `q • χ₁ + χ₂` are both
   trivial.
 * `LieModule.genWeightSpaceChain`: given weights `χ₁`, `χ₂` together with integers `p` and `q`,
   this is the sum of the weight spaces `k • χ₁ + χ₂` for `p < k < q`.
 * `LieModule.trace_toEnd_genWeightSpaceChain_eq_zero`: given a root `α` relative to a Cartan
   subalgebra `H`, there is a natural ideal `corootSpace α` in `H`. This lemma
   states that this ideal acts by trace-zero endomorphisms on the sum of root spaces of any
   `α`-chain, provided the weight spaces at the endpoints are both trivial.
 * `LieModule.exists_forall_mem_corootSpace_smul_add_eq_zero`: given a (potential) root
   `α` relative to a Cartan subalgebra `H`, if we restrict to the ideal
   `corootSpace α` of `H`, we may find an integral linear combination between
   `α` and any weight `χ` of a representation.

-/

open Module Function Set

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

section IsNilpotent

variable [LieRing.IsNilpotent L] (χ₁ χ₂ : L → R) (p q : ℤ)

section

variable [NoZeroSMulDivisors ℤ R] [NoZeroSMulDivisors R M] [IsNoetherian R M] (hχ₁ : χ₁ ≠ 0)
include hχ₁

lemma eventually_genWeightSpace_smul_add_eq_bot :
    ∀ᶠ (k : ℕ) in Filter.atTop, genWeightSpace M (k • χ₁ + χ₂) = ⊥ := by
  let f : ℕ → L → R := fun k ↦ k • χ₁ + χ₂
  suffices Injective f by
    rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite, ← finite_image_iff this.injOn]
    apply (finite_genWeightSpace_ne_bot R L M).subset
    simp [f]
  intro k l hkl
  replace hkl : (k : ℤ) • χ₁ = (l : ℤ) • χ₁ := by
    simpa only [f, add_left_inj, natCast_zsmul] using hkl
  exact Nat.cast_inj.mp <| smul_left_injective ℤ hχ₁ hkl

lemma exists_genWeightSpace_smul_add_eq_bot :
    ∃ k > 0, genWeightSpace M (k • χ₁ + χ₂) = ⊥ :=
  (Nat.eventually_pos.and <| eventually_genWeightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁).exists

lemma exists₂_genWeightSpace_smul_add_eq_bot :
    ∃ᵉ (p < (0 : ℤ)) (q > (0 : ℤ)),
      genWeightSpace M (p • χ₁ + χ₂) = ⊥ ∧
      genWeightSpace M (q • χ₁ + χ₂) = ⊥ := by
  obtain ⟨q, hq₀, hq⟩ := exists_genWeightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁
  obtain ⟨p, hp₀, hp⟩ := exists_genWeightSpace_smul_add_eq_bot M (-χ₁) χ₂ (neg_ne_zero.mpr hχ₁)
  refine ⟨-(p : ℤ), by simpa, q, by simpa, ?_, ?_⟩
  · rw [neg_smul, ← smul_neg, natCast_zsmul]
    exact hp
  · rw [natCast_zsmul]
    exact hq

end

/-- Given two (potential) weights `χ₁` and `χ₂` together with integers `p` and `q`, it is often
useful to study the sum of weight spaces associated to the family of weights `k • χ₁ + χ₂` for
`p < k < q`. -/
def genWeightSpaceChain : LieSubmodule R L M :=
  ⨆ k ∈ Ioo p q, genWeightSpace M (k • χ₁ + χ₂)

lemma genWeightSpaceChain_def :
    genWeightSpaceChain M χ₁ χ₂ p q = ⨆ k ∈ Ioo p q, genWeightSpace M (k • χ₁ + χ₂) :=
  rfl

lemma genWeightSpaceChain_def' :
    genWeightSpaceChain M χ₁ χ₂ p q = ⨆ k ∈ Finset.Ioo p q, genWeightSpace M (k • χ₁ + χ₂) := by
  have : ∀ (k : ℤ), k ∈ Ioo p q ↔ k ∈ Finset.Ioo p q := by simp
  simp_rw [genWeightSpaceChain_def, this]

@[simp]
lemma genWeightSpaceChain_neg :
    genWeightSpaceChain M (-χ₁) χ₂ (-q) (-p) = genWeightSpaceChain M χ₁ χ₂ p q := by
  let e : ℤ ≃ ℤ := neg_involutive.toPerm
  simp_rw [genWeightSpaceChain, ← e.biSup_comp (Ioo p q)]
  simp [e, -mem_Ioo, neg_mem_Ioo_iff]

lemma genWeightSpace_le_genWeightSpaceChain {k : ℤ} (hk : k ∈ Ioo p q) :
    genWeightSpace M (k • χ₁ + χ₂) ≤ genWeightSpaceChain M χ₁ χ₂ p q :=
  le_biSup (fun i ↦ genWeightSpace M (i • χ₁ + χ₂)) hk

end IsNilpotent

section LieSubalgebra

open LieAlgebra

variable {H : LieSubalgebra R L} (α χ : H → R) (p q : ℤ)

lemma lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right [LieRing.IsNilpotent H]
    (hq : genWeightSpace M (q • α + χ) = ⊥)
    {x : L} (hx : x ∈ rootSpace H α)
    {y : M} (hy : y ∈ genWeightSpaceChain M α χ p q) :
    ⁅x, y⁆ ∈ genWeightSpaceChain M α χ p q := by
  rw [genWeightSpaceChain, iSup_subtype'] at hy
  induction hy using LieSubmodule.iSup_induction' with
  | hN k z hz =>
    obtain ⟨k, hk⟩ := k
    suffices genWeightSpace M ((k + 1) • α + χ) ≤ genWeightSpaceChain M α χ p q by
      apply this
      -- was `simpa using [...]` and very slow
      -- (https://github.com/leanprover-community/mathlib4/issues/19751)
      simpa only [zsmul_eq_mul, Int.cast_add, Pi.intCast_def, Int.cast_one] using
        (rootSpaceWeightSpaceProduct R L H M α (k • α + χ) ((k + 1) • α + χ)
            (by rw [add_smul]; abel) (⟨x, hx⟩ ⊗ₜ ⟨z, hz⟩)).property
    rw [genWeightSpaceChain]
    rcases eq_or_ne (k + 1) q with rfl | hk'; · simp only [hq, bot_le]
    replace hk' : k + 1 ∈ Ioo p q := ⟨by linarith [hk.1], lt_of_le_of_ne hk.2 hk'⟩
    exact le_biSup (fun k ↦ genWeightSpace M (k • α + χ)) hk'
  | h0 => simp
  | hadd _ _ _ _ hz₁ hz₂ => rw [lie_add]; exact add_mem hz₁ hz₂

lemma lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left [LieRing.IsNilpotent H]
    (hp : genWeightSpace M (p • α + χ) = ⊥)
    {x : L} (hx : x ∈ rootSpace H (-α))
    {y : M} (hy : y ∈ genWeightSpaceChain M α χ p q) :
    ⁅x, y⁆ ∈ genWeightSpaceChain M α χ p q := by
  replace hp : genWeightSpace M ((-p) • (-α) + χ) = ⊥ := by rwa [smul_neg, neg_smul, neg_neg]
  rw [← genWeightSpaceChain_neg] at hy ⊢
  exact lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right M (-α) χ (-q) (-p) hp hx hy

section IsCartanSubalgebra

variable [H.IsCartanSubalgebra] [IsNoetherian R L]

lemma trace_toEnd_genWeightSpaceChain_eq_zero
    (hp : genWeightSpace M (p • α + χ) = ⊥)
    (hq : genWeightSpace M (q • α + χ) = ⊥)
    {x : H} (hx : x ∈ corootSpace α) :
    LinearMap.trace R _ (toEnd R H (genWeightSpaceChain M α χ p q) x) = 0 := by
  rw [LieAlgebra.mem_corootSpace'] at hx
  induction hx using Submodule.span_induction
  · next u hu =>
    obtain ⟨y, hy, z, hz, hyz⟩ := hu
    let f : Module.End R (genWeightSpaceChain M α χ p q) :=
      { toFun := fun ⟨m, hm⟩ ↦ ⟨⁅(y : L), m⁆,
          lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right M α χ p q hq hy hm⟩
        map_add' := fun _ _ ↦ by simp
        map_smul' := fun t m ↦ by simp }
    let g : Module.End R (genWeightSpaceChain M α χ p q) :=
      { toFun := fun ⟨m, hm⟩ ↦ ⟨⁅(z : L), m⁆,
          lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left M α χ p q hp hz hm⟩
        map_add' := fun _ _ ↦ by simp
        map_smul' := fun t m ↦ by simp }
    have hfg : toEnd R H _ u = ⁅f, g⁆ := by
      ext
      rw [toEnd_apply_apply, LieSubmodule.coe_bracket, LieSubalgebra.coe_bracket_of_module, ← hyz]
      simp only [lie_lie, LieHom.lie_apply, LinearMap.coe_mk, AddHom.coe_mk, Module.End.lie_apply,
      AddSubgroupClass.coe_sub, f, g]
    simp [hfg]
  · simp
  · simp_all
  · simp_all

/-- Given a (potential) root `α` relative to a Cartan subalgebra `H`, if we restrict to the ideal
`I = corootSpace α` of `H` (informally, `I = ⁅H(α), H(-α)⁆`), we may find an
integral linear combination between `α` and any weight `χ` of a representation.

This is Proposition 4.4 from [carter2005] and is a key step in the proof that the roots of a
semisimple Lie algebra form a root system. It shows that the restriction of `α` to `I` vanishes iff
the restriction of every root to `I` vanishes (which cannot happen in a semisimple Lie algebra). -/
lemma exists_forall_mem_corootSpace_smul_add_eq_zero
    [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [NoZeroSMulDivisors R M] [IsNoetherian R M]
    (hα : α ≠ 0) (hχ : genWeightSpace M χ ≠ ⊥) :
    ∃ a b : ℤ, 0 < b ∧ ∀ x ∈ corootSpace α, (a • α + b • χ) x = 0 := by
  obtain ⟨p, hp₀, q, hq₀, hp, hq⟩ := exists₂_genWeightSpace_smul_add_eq_bot M α χ hα
  let a := ∑ i ∈ Finset.Ioo p q, finrank R (genWeightSpace M (i • α + χ)) • i
  let b := ∑ i ∈ Finset.Ioo p q, finrank R (genWeightSpace M (i • α + χ))
  have hb : 0 < b := by
    replace hχ : Nontrivial (genWeightSpace M χ) := by rwa [LieSubmodule.nontrivial_iff_ne_bot]
    refine Finset.sum_pos' (fun _ _ ↦ zero_le _) ⟨0, Finset.mem_Ioo.mpr ⟨hp₀, hq₀⟩, ?_⟩
    rw [zero_smul, zero_add]
    exact finrank_pos
  refine ⟨a, b, Int.ofNat_pos.mpr hb, fun x hx ↦ ?_⟩
  let N : ℤ → Submodule R M := fun k ↦ genWeightSpace M (k • α + χ)
  have h₁ : iSupIndep fun (i : Finset.Ioo p q) ↦ N i := by
    rw [← LieSubmodule.iSupIndep_iff_toSubmodule]
    refine (iSupIndep_genWeightSpace R H M).comp fun i j hij ↦ ?_
    exact SetCoe.ext <| smul_left_injective ℤ hα <| by rwa [add_left_inj] at hij
  have h₂ : ∀ i, MapsTo (toEnd R H M x) ↑(N i) ↑(N i) := fun _ _ ↦ LieSubmodule.lie_mem _
  have h₃ : genWeightSpaceChain M α χ p q = ⨆ i ∈ Finset.Ioo p q, N i := by
    simp_rw [N, genWeightSpaceChain_def', LieSubmodule.iSup_toSubmodule]
  rw [← trace_toEnd_genWeightSpaceChain_eq_zero M α χ p q hp hq hx,
    ← LieSubmodule.toEnd_restrict_eq_toEnd]
  -- The lines below illustrate the cost of treating `LieSubmodule` as both a
  -- `Submodule` and a `LieSubmodule` simultaneously.
  erw [LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup _ h₁ h₂ (genWeightSpaceChain M α χ p q) h₃]
  simp_rw [N, LieSubmodule.toEnd_restrict_eq_toEnd]
  dsimp [N]
  convert_to _ =
    ∑ k ∈ Finset.Ioo p q, (LinearMap.trace R { x // x ∈ (genWeightSpace M (k • α + χ)) })
      ((toEnd R { x // x ∈ H } { x // x ∈ genWeightSpace M (k • α + χ) }) x)
  simp_rw [a, b, trace_toEnd_genWeightSpace, Pi.add_apply, Pi.smul_apply, smul_add,
    ← smul_assoc, Finset.sum_add_distrib, ← Finset.sum_smul, natCast_zsmul]

end IsCartanSubalgebra

end LieSubalgebra

section

variable {M}
variable [LieRing.IsNilpotent L]
variable [NoZeroSMulDivisors ℤ R] [NoZeroSMulDivisors R M] [IsNoetherian R M]
variable (α : L → R) (β : Weight R L M)

/-- This is the largest `n : ℕ` such that `i • α + β` is a weight for all `0 ≤ i ≤ n`. -/
noncomputable
def chainTopCoeff : ℕ :=
  letI := Classical.propDecidable
  if hα : α = 0 then 0 else
  Nat.pred <| Nat.find (show ∃ n, genWeightSpace M (n • α + β : L → R) = ⊥ from
    (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists)

/-- This is the largest `n : ℕ` such that `-i • α + β` is a weight for all `0 ≤ i ≤ n`. -/
noncomputable
def chainBotCoeff : ℕ := chainTopCoeff (-α) β

@[simp] lemma chainTopCoeff_neg : chainTopCoeff (-α) β = chainBotCoeff α β := rfl
@[simp] lemma chainBotCoeff_neg : chainBotCoeff (-α) β = chainTopCoeff α β := by
  rw [← chainTopCoeff_neg, neg_neg]

@[simp] lemma chainTopCoeff_zero : chainTopCoeff 0 β = 0 := dif_pos rfl
@[simp] lemma chainBotCoeff_zero : chainBotCoeff 0 β = 0 := dif_pos neg_zero

section
variable (hα : α ≠ 0)
include hα

lemma chainTopCoeff_add_one :
    letI := Classical.propDecidable
    chainTopCoeff α β + 1 =
      Nat.find (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists := by
  classical
  rw [chainTopCoeff, dif_neg hα]
  apply Nat.succ_pred_eq_of_pos
  rw [zero_lt_iff]
  intro e
  have : genWeightSpace M (0 • α + β : L → R) = ⊥ := by
    rw [← e]
    exact Nat.find_spec (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists
  exact β.genWeightSpace_ne_bot _ (by simpa only [zero_smul, zero_add] using this)

lemma genWeightSpace_chainTopCoeff_add_one_nsmul_add :
    genWeightSpace M ((chainTopCoeff α β + 1) • α + β : L → R) = ⊥ := by
  classical
  rw [chainTopCoeff_add_one _ _ hα]
  exact Nat.find_spec (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists

lemma genWeightSpace_chainTopCoeff_add_one_zsmul_add :
    genWeightSpace M ((chainTopCoeff α β + 1 : ℤ) • α + β : L → R) = ⊥ := by
  rw [← genWeightSpace_chainTopCoeff_add_one_nsmul_add α β hα, ← Nat.cast_smul_eq_nsmul ℤ,
    Nat.cast_add, Nat.cast_one]

lemma genWeightSpace_chainBotCoeff_sub_one_zsmul_sub :
    genWeightSpace M ((-chainBotCoeff α β - 1 : ℤ) • α + β : L → R) = ⊥ := by
  rw [sub_eq_add_neg, ← neg_add, neg_smul, ← smul_neg, chainBotCoeff,
    genWeightSpace_chainTopCoeff_add_one_zsmul_add _ _ (by simpa using hα)]

end

lemma genWeightSpace_nsmul_add_ne_bot_of_le {n} (hn : n ≤ chainTopCoeff α β) :
    genWeightSpace M (n • α + β : L → R) ≠ ⊥ := by
  by_cases hα : α = 0
  · rw [hα, smul_zero, zero_add]; exact β.genWeightSpace_ne_bot
  classical
  rw [← Nat.lt_succ, Nat.succ_eq_add_one, chainTopCoeff_add_one _ _ hα] at hn
  exact Nat.find_min (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists hn

lemma genWeightSpace_zsmul_add_ne_bot {n : ℤ}
    (hn : -chainBotCoeff α β ≤ n) (hn' : n ≤ chainTopCoeff α β) :
      genWeightSpace M (n • α + β : L → R) ≠ ⊥ := by
  rcases n with (n | n)
  · simp only [Int.ofNat_eq_coe, Nat.cast_le, Nat.cast_smul_eq_nsmul] at hn' ⊢
    exact genWeightSpace_nsmul_add_ne_bot_of_le α β hn'
  · simp only [Int.negSucc_eq, ← Nat.cast_succ, neg_le_neg_iff, Nat.cast_le] at hn ⊢
    rw [neg_smul, ← smul_neg, Nat.cast_smul_eq_nsmul]
    exact genWeightSpace_nsmul_add_ne_bot_of_le (-α) β hn

lemma genWeightSpace_neg_zsmul_add_ne_bot {n : ℕ} (hn : n ≤ chainBotCoeff α β) :
    genWeightSpace M ((-n : ℤ) • α + β : L → R) ≠ ⊥ := by
  apply genWeightSpace_zsmul_add_ne_bot α β <;> omega

/-- The last weight in an `α`-chain through `β`. -/
noncomputable
def chainTop (α : L → R) (β : Weight R L M) : Weight R L M :=
  ⟨chainTopCoeff α β • α + β, genWeightSpace_nsmul_add_ne_bot_of_le α β le_rfl⟩

/-- The first weight in an `α`-chain through `β`. -/
noncomputable
def chainBot (α : L → R) (β : Weight R L M) : Weight R L M :=
  ⟨(- chainBotCoeff α β : ℤ) • α + β, genWeightSpace_neg_zsmul_add_ne_bot α β le_rfl⟩

lemma coe_chainTop' : (chainTop α β : L → R) = chainTopCoeff α β • α + β := rfl

@[simp] lemma coe_chainTop : (chainTop α β : L → R) = (chainTopCoeff α β : ℤ) • α + β := by
  rw [Nat.cast_smul_eq_nsmul ℤ]; rfl
@[simp] lemma coe_chainBot : (chainBot α β : L → R) = (-chainBotCoeff α β : ℤ) • α + β := rfl

@[simp] lemma chainTop_neg : chainTop (-α) β = chainBot α β := by ext; simp
@[simp] lemma chainBot_neg : chainBot (-α) β = chainTop α β := by ext; simp

@[simp] lemma chainTop_zero : chainTop 0 β = β := by ext; simp
@[simp] lemma chainBot_zero : chainBot 0 β = β := by ext; simp

section
variable (hα : α ≠ 0)
include hα

lemma genWeightSpace_add_chainTop :
    genWeightSpace M (α + chainTop α β : L → R) = ⊥ := by
  rw [coe_chainTop', ← add_assoc, ← succ_nsmul',
    genWeightSpace_chainTopCoeff_add_one_nsmul_add _ _ hα]

lemma genWeightSpace_neg_add_chainBot :
    genWeightSpace M (-α + chainBot α β : L → R) = ⊥ := by
  rw [← chainTop_neg, genWeightSpace_add_chainTop _ _ (by simpa using hα)]

lemma chainTop_isNonZero' (hα' : genWeightSpace M α ≠ ⊥) :
    (chainTop α β).IsNonZero := by
  by_contra e
  apply hα'
  rw [← add_zero (α : L → R), ← e, genWeightSpace_add_chainTop _ _ hα]

end

lemma chainTop_isNonZero (α β : Weight R L M) (hα : α.IsNonZero) :
    (chainTop α β).IsNonZero :=
  chainTop_isNonZero' α β hα α.2

end

section

open LieAlgebra
set_option maxHeartbeats 400000

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  (H : LieSubalgebra K L) [LieRing.IsNilpotent H]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [IsTriangularizable K H M] [FiniteDimensional K M]

lemma root_space_ad_is_nilpotent
    {x : L} {χ : H → K} (hχ : χ ≠ 0) (hx : x ∈ rootSpace H χ) :
    _root_.IsNilpotent (toEnd K L M x) := by
  have partition := iSup_genWeightSpace_eq_top' K H M
  -- set s := ⋃ χ ∈ Weight K H M, (genWeightSpace M χ).carrier
  --set s := ⋃ χ ∈ Weight K H M, χ
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (LieSubmodule.iSupIndep_iff_toSubmodule.mp <| iSupIndep_genWeightSpace' K H M)
    (LieSubmodule.iSup_eq_top_iff_toSubmodule.mp <| iSup_genWeightSpace_eq_top' K H M)

  set s : Set (Weight K H M) := by
    exact univ
  have Mm : Finite s := by
    exact Subtype.finite

  have helpMe : ∀ ε ∈ s, ∃ n : ℕ, ∀ (v : genWeightSpace M ε), ∀ m ≥ n, ((toEnd K L M x) ^ m) v = 0 := by
    intro ε he
    have hoho := exists_genWeightSpace_smul_add_eq_bot (R := K) (L := H) (M := M) χ ε hχ
    obtain ⟨k, ⟨hk1, hk2⟩⟩ := hoho
    use k
    intro v m hm
    suffices ((toEnd K L M x) ^ k) v = 0 by
      exact LinearMap.pow_map_zero_of_le hm this
    --  (hm : m ∈ genWeightSpace M χ₂)
    simp_all
    have s0 := v.mem
    have s1 := toEnd_pow_apply_mem hx s0 k
    simp_all
    --rw [hk2] at s1



  have exists_global_n0 : ∃ n0 : ℕ, ∀ ε ∈ s, ∀ (v : genWeightSpace M ε), ((toEnd K L M x) ^ n0) v = 0 := by
    let fs := Finite.toFinset Mm
    choose n hn using helpMe
    simp_all
    let nn1 : (ε : Weight K H M) → ℕ := by
      intro ε
      have ttt : ε ∈ s := by
        simp_all only [ne_eq, gt_iff_lt, nsmul_eq_mul, Pi.natCast_def, mem_univ, ge_iff_le, Subtype.forall, forall_const,
        iSup_pos, iUnion_true, LieSubmodule.top_toSubmodule, top_le_iff, s]
      apply n ε ttt
    let n0 := fs.sup nn1
    use n0
    intro ε hε v
    specialize hn ε hε v
    intro ropi
    have ropi2 := hn ropi
    have ropi3 : n ε hε ≤ nn1 ε := by
      simp_all
      simp_all only [le_refl, s, nn1]
    have ropi4 : nn1 ε ≤ n0 := by
      simp_all
      dsimp [n0]
      have ttt : ε ∈ s := by
        simp_all only [ne_eq, gt_iff_lt, nsmul_eq_mul, Pi.natCast_def, mem_univ, ge_iff_le, Subtype.forall, forall_const,
        iSup_pos, iUnion_true, LieSubmodule.top_toSubmodule, top_le_iff, s]
      have tttt : ε ∈ fs := by
        simp_all only [le_refl, mem_univ, Finite.toFinset_setOf, Finset.filter_True, Finset.mem_univ, s, nn1, n0, fs]
      exact Finset.le_sup tttt
    have hellp : n ε hε ≤ n0 := by
      linarith [ropi3, ropi4]
    have ropi5 := ropi2 n0 hellp
    exact ropi5

  obtain ⟨n0, hn0⟩ := exists_global_n0
  let A := (toEnd K L M x) ^ n0
  have r : ⨆ χ ∈ s, genWeightSpace M χ = ⊤ := by
    simp_all only [ne_eq, gt_iff_lt, nsmul_eq_mul, Pi.natCast_def, mem_univ,
    iUnion_true, iSup_pos, s]

  have rrr : ∀ χ1 ∈ s, genWeightSpace M χ1 ≤ Submodule.span K (⋃ χ ∈ s, (genWeightSpace M χ).carrier) := by
    intro χ1
    intro a
    intro m hm
    have nam : Submodule.span K (genWeightSpace M χ1).carrier ≤ Submodule.span K (⋃ χ ∈ s, (genWeightSpace M χ).carrier) := by
      apply Submodule.span_mono
      simp_all
      intro x hx
      apply Set.mem_biUnion a
      simp_all only [mem_univ, iSup_pos, AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, LieSubmodule.mem_toSubmodule, s]
    have tq : genWeightSpace M χ1 ≤ Submodule.span K (genWeightSpace M χ1).carrier := by
      intro m hm
      simp_all
      dsimp [Submodule.span]
      intro p hp
      simp_all
      obtain ⟨pr, hr⟩ := hp
      obtain ⟨aa, aaa⟩ := hr
      simp_all
      intro xx
      have ttttt := xx hm
      simp_all
    have := nam (tq hm)
    simp_all only [ne_eq, gt_iff_lt, nsmul_eq_mul, Pi.natCast_def, mem_univ, iSup_pos, LieSubmodule.mem_toSubmodule,
      iUnion_true, s]


  have rrr : ⨆ χ ∈ s, genWeightSpace M χ ≤ Submodule.span K (⋃ χ ∈ s, (genWeightSpace M χ).carrier) := by
    apply sSup_le
    intro x hf
    simp_all only [ne_eq, gt_iff_lt, nsmul_eq_mul, Pi.natCast_def, mem_univ, iSup_pos, iUnion_true, forall_const,
      mem_range, exists_exists_eq_and, mem_setOf_eq, s]
    obtain ⟨w_1, h_1⟩ := hf
    subst h_1
    simp_all only [s]


  have rr : Submodule.span K (⋃ χ ∈ s, (genWeightSpace M χ).carrier) = ⊤ := by
    simp_all only [ne_eq, gt_iff_lt, nsmul_eq_mul, Pi.natCast_def, mem_univ, iSup_pos, iUnion_true, forall_const,
      LieSubmodule.top_toSubmodule, top_le_iff, s]

  have ttt1 (ε : Weight K H M) (n : M) (n : genWeightSpace M ε) : A n = 0 := by
    have ttt : ε ∈ s := by
      simp_all only [ne_eq, gt_iff_lt, nsmul_eq_mul, Pi.natCast_def, mem_univ, ge_iff_le, Subtype.forall, forall_const,
        iSup_pos, iUnion_true, LieSubmodule.top_toSubmodule, top_le_iff, s]
    have zzz := (hn0 ε) (ttt) n
    exact zzz

  have ttt2 : A = 0 := by
    haveI := [Module K M]
    have call := Submodule.linearMap_eq_zero_iff_of_span_eq_top (A : M →ₗ[K] M) rr
    apply call.2
    intro s1
    obtain ⟨a, ⟨b, ⟨c, d⟩⟩⟩ := s1
    simp_all
    obtain ⟨e, ⟨f, g⟩⟩ := c
    simp_all
    obtain ⟨d1, d2⟩ := d
    exact ttt1 e a d2
  use n0

lemma root_space_ad_is_nilpotent2 [IsTriangularizable K H L] [FiniteDimensional K L]
    {x : L} {χ : H → K} (hχ : χ ≠ 0) (hx : x ∈ rootSpace H χ) :
    _root_.IsNilpotent (ad K L x) :=
  root_space_ad_is_nilpotent (M := L) H hχ hx

end

end LieModule

namespace LieAlgebra

open LieModule

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  (H : LieSubalgebra K L) [LieRing.IsNilpotent H]

lemma root_space_ad_is_nilpotent [IsTriangularizable K H L] [FiniteDimensional K L]
    {x : L} {χ : H → K} (hχ : χ ≠ 0) (hx : x ∈ rootSpace H χ) :
    _root_.IsNilpotent (ad K L x) :=
  LieModule.root_space_ad_is_nilpotent (M := L) H hχ hx

end LieAlgebra
