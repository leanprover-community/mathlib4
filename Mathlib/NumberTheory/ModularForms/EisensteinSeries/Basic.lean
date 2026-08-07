/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.MDifferentiable
public import Mathlib.NumberTheory.LSeries.ZMod

/-!
# Eisenstein series are Modular Forms

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are Modular Forms.

## TODO

Add q-expansions and prove that they are not all identically zero.
-/

@[expose] public section

noncomputable section

namespace ModularForm

open EisensteinSeries CongruenceSubgroup MatrixGroups

/-- This defines Eisenstein series as modular forms of weight `k`, level `Γ(N)` and congruence
condition given by `a : Fin 2 → ZMod N`. -/
def eisensteinSeriesMF {k : ℤ} {N : ℕ} [NeZero N] (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    ModularForm Γ(N) k where
  toFun := eisensteinSeriesSIF a k
  slash_action_eq' := (eisensteinSeriesSIF a k).slash_action_eq'
  holo' := eisensteinSeriesSIF_mdifferentiable hk a
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ hγ ↦ isBoundedAtImInfty_eisensteinSeriesSIF a hk γ

lemma eisensteinSeriesMF_apply {k : ℤ} {N : ℕ} [NeZero N] (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
  eisensteinSeriesMF hk a = eisensteinSeries a k := rfl

@[deprecated (since := "2026-02-10")] noncomputable alias eisensteinSeries_MF := eisensteinSeriesMF

/-- Normalised Eisenstein series of level 1 and weight `k`,
here they have been scaled by `1/2` since we sum over coprime pairs. -/
def E {k : ℕ} (hk : 3 ≤ k) : ModularForm 𝒮ℒ k :=
  ((1 / 2 : ℂ) • eisensteinSeriesMF (mod_cast hk) 0).copy _ rfl Gamma_one_coe_eq_SL.symm

/-- The normalised level 1 Eisenstein series of weight 4. -/
abbrev E₄ : ModularForm 𝒮ℒ 4 := E (by norm_num : 3 ≤ 4)

/-- The normalised level 1 Eisenstein series of weight 6. -/
abbrev E₆ : ModularForm 𝒮ℒ 6 := E (by norm_num : 3 ≤ 6)

end ModularForm

section G_eq_sum_E

open UpperHalfPlane EisensteinSeries

variable {N : ℕ} {r : ℕ} (a : Fin 2 → ZMod N)

/-- The modified zeta function `ζ₊ⁿ(k)`, i.e. the sum of `m ^ (-k)` over the positive integers
`m ≡ n (mod N)`, is the value at `k` of the `L`-function of the indicator function of the
residue class `n`. -/
lemma tsum_zpow_eq_LFunction [NeZero N] (n : (ZMod N)ˣ) {k : ℤ} (hk : 1 < k) :
    ∑' m : {m : ℕ // 0 < m ∧ (m : ZMod N) = n}, (m : ℂ) ^ (-k) =
      ZMod.LFunction (Pi.single n.val 1) k := by
  rw [ZMod.LFunction_eq_LSeries _ (mod_cast hk)]
  calc
    _ = ∑' m : {m : ℕ // 0 < m ∧ (m : ZMod N) = n},
        LSeries.term (fun j : ℕ ↦ (Pi.single n.val 1 : ZMod N → ℂ) (j : ZMod N)) k m.1 := by
      refine tsum_congr fun m ↦ ?_
      simp [LSeries.term_of_ne_zero m.2.1.ne', m.2.2]
    _ = LSeries (fun j : ℕ ↦ (Pi.single n.val 1 : ZMod N → ℂ) (j : ZMod N)) k := by
      refine Function.Injective.tsum_eq (fun _ _ h ↦ Subtype.ext h) fun b hb ↦ ?_
      rcases Nat.eq_zero_or_pos b with rfl | hb0
      · simp at hb
      · by_contra hbn
        have hbn' : (b : ZMod N) ≠ (n : ZMod N) := fun hc ↦ hbn ⟨⟨b, hb0, hc⟩, rfl⟩
        exact hb (by simp [LSeries.term_of_ne_zero hb0.ne', Pi.single_eq_of_ne hbn'])

/-- The sum of `eisSummand` over `gammaSet N r a` for `r` coprime to `N` is `r ^ (-k)` times
an Eisenstein series with congruence condition `r⁻¹ • a`. -/
lemma tsum_gammaSet_eisSummand_of_coprime {k : ℤ} (hk : k ≠ 0) (z : ℍ) (h : r.Coprime N) :
    ∑' v : gammaSet N r a, eisSummand k v z =
      (r : ℂ) ^ (-k) * eisensteinSeries ((ZMod.unitOfCoprime r h)⁻¹ • a) k z := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hN : N = 1 := N.coprime_zero_left.mp h
    subst hN
    have h0 : gammaSet 1 0 a = {0} := by
      ext
      simp [gammaSet_one_eq, Int.gcd_eq_zero_iff, funext_iff]
    rw [h0, tsum_singleton 0 (eisSummand k · z)]
    simp [eisSummand, _root_.zero_zpow _ (neg_ne_zero.mpr hk)]
  · have : NeZero r := ⟨hr.ne'⟩
    calc
      _ = ∑' v : gammaSet N r a, (r : ℂ) ^ (-k) * eisSummand k (divIntMap r v) z := by
        congr! 2 with v
        conv_lhs => rw [gammaSet_eq_gcd_mul_divIntMap ((gammaSet_one_mem_iff r _).mpr v.2.2),
          ← natCast_zsmul, eisSummand_smul]
        norm_cast
      _ = (r : ℂ) ^ (-k) * eisensteinSeries ((ZMod.unitOfCoprime r h)⁻¹ • a) k z := by
        rw [tsum_mul_left]
        congr! 1
        exact ((bijOn_divIntMap_gammaSet _ _ a h).equiv _).tsum_eq (eisSummand k · z)

/-- Mapping a positive natural number `m` congruent to `n`
mod `N` to the corresponding element of the fiber of `coprimeUnitMap` over `n`. -/
def toCoprimeUnitFiber (n : (ZMod N)ˣ)
    (m : {m : ℕ // 0 < m ∧ (m : ZMod N) = n}) : ZMod.coprimeUnitMap ⁻¹' {n} :=
  ⟨⟨m.1, (ZMod.isUnit_iff_coprime m.1 N).mp (by simp [m.2.2])⟩,
    Units.ext (by simp [ZMod.coprimeUnitMap, m.2.2])⟩

/-- The Eisenstein series `G` with congruence condition `a`
mod `N` is the sum over `n ∈ (ZMod N)ˣ` of `ζ₊ⁿ(k) * E (n⁻¹ • a)`, where `ζ₊ⁿ(k)` is the
`L`-function of the indicator function of the residue class `n` and `E` is `eisensteinSeries`. -/
theorem G_eq_sum_E [NeZero N] {k : ℤ} (hk : 3 ≤ k) (z : ℍ) :
    eisensteinSeriesG a k z = ∑ n : (ZMod N)ˣ,
      ZMod.LFunction (Pi.single n.val 1) k * eisensteinSeries (n⁻¹ • a) k z := by
  have hk0 : k ≠ 0 := by omega
  have hσ := summable_coprime_eisSummand a hk z
  have h1 : eisensteinSeriesG a k z =
      ∑' p : Σ r : {r : ℕ // r.Coprime N}, gammaSet N r.1 a, eisSummand k p.2 z :=
    ((gammaSetCoprimeSigmaEquiv a).symm.tsum_eq (eisSummand k · z)).symm
  rw [h1, hσ.tsum_sigma, ← (hσ.sigma.hasSum.tsum_fiberwise ZMod.coprimeUnitMap).tsum_eq,
    tsum_fintype]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have h3 : ∀ p : ZMod.coprimeUnitMap ⁻¹' {n}, ∑' v : gammaSet N p.1 a, eisSummand k v z =
      p.1 ^ (-k) * eisensteinSeries (n⁻¹ • a) k z := by
    intro ⟨r, hr⟩
    rw [tsum_gammaSet_eisSummand_of_coprime a hk0 z r.2]
    congr
  rw [tsum_congr h3, tsum_mul_right, ← tsum_zpow_eq_LFunction n (by omega)]
  congr! 1
  refine (Function.Injective.tsum_eq (g := toCoprimeUnitFiber n)
    (fun _ _ hm ↦ Subtype.ext (congrArg (fun x ↦ x.1.1) hm)) fun x hx ↦ ?_).symm
  have hx0 : x.1.1 ≠ 0 := fun h0 ↦ hx (by simp [h0, _root_.zero_zpow _ hk0])
  simp only [Set.mem_range, Subtype.exists]
  use x.1.1, ⟨Nat.pos_of_ne_zero hx0, (ZMod.coe_unitOfCoprime _ _).symm.trans
    (congrArg Units.val x.2)⟩
  rfl

end G_eq_sum_E

namespace ModularForm

open UpperHalfPlane EisensteinSeries CongruenceSubgroup

/-- The Eisenstein series `G` of weight `k`, level `Γ(N)` and congruence condition
`a : Fin 2 → ZMod N` as a modular form. -/
def eisensteinSeriesGMF {k : ℤ} {N : ℕ} [NeZero N] (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    ModularForm Γ(N) k :=
  ∑ n : (ZMod N)ˣ, ZMod.LFunction (Pi.single n.val 1) k • eisensteinSeriesMF hk (n⁻¹ • a)

lemma eisensteinSeriesGMF_apply {k : ℤ} {N : ℕ} [NeZero N] (hk : 3 ≤ k) (a : Fin 2 → ZMod N)
    (z : ℍ) : eisensteinSeriesGMF hk a z = eisensteinSeriesG a k z := by
  rw [G_eq_sum_E a hk z]
  have := congr_fun (map_sum coeHom (fun n : (ZMod N)ˣ ↦
    ZMod.LFunction (Pi.single n.val 1) k • eisensteinSeriesMF hk (n⁻¹ • a)) Finset.univ) z
  rwa [coeHom_apply, Finset.sum_apply] at this

end ModularForm
