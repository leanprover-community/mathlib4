/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Equivalent power-multiplicative norms

In this file, we prove [BGR, Proposition 3.1.5/1][bosch-guntzer-remmert]: if `R` is a normed
commutative ring and `f₁` and `f₂` are two power-multiplicative `R`-algebra norms on `S`, then if
`f₁` and `f₂` are equivalent on every subring `R[y]` for `y : S`, it follows that `f₁ = f₂`.

## Main Results
* `eq_of_powMul_faithful` : the proof of [BGR, Proposition 3.1.5/1][bosch-guntzer-remmert].

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

norm, equivalent, power-multiplicative
-/

public section

open Filter Real Algebra
open scoped Topology

/-- If `f : α →+* β` is bounded with respect to a ring seminorm `nα` on `α` and a
  power-multiplicative function `nβ : β → ℝ`, then `∀ x : α, nβ (f x) ≤ nα x`. -/
theorem contraction_of_isPowMul_of_boundedWrt {F : Type*} {α : outParam (Type*)} [Ring α]
    [FunLike F α ℝ] [RingSeminormClass F α ℝ] {β : Type*} [Ring β] (nα : F) {nβ : β → ℝ}
    (hβ : IsPowMul nβ) {f : α →+* β} (hf : f.IsBoundedWrt nα nβ) (x : α) : nβ (f x) ≤ nα x := by
  obtain ⟨C, hC0, hC⟩ := hf
  have hlim : Tendsto (fun n : ℕ => C ^ (1 / (n : ℝ)) * nα x) atTop (𝓝 (nα x)) := by
    nth_rewrite 2 [← one_mul (nα x)]
    exact ((rpow_zero C ▸ ContinuousAt.tendsto (continuousAt_const_rpow (ne_of_gt hC0))).comp
      (tendsto_const_div_atTop_nhds_zero_nat 1)).mul tendsto_const_nhds
  apply ge_of_tendsto hlim
  simp only [eventually_atTop]
  use 1
  intro n hn
  have h : (C ^ (1 / n : ℝ)) ^ n = C := by
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
    rw [← rpow_natCast, ← rpow_mul hC0.le, one_div, inv_mul_cancel₀ hn0, rpow_one]
  apply le_of_pow_le_pow_left₀ (ne_of_gt hn) (by positivity)
  · rw [mul_pow, h, ← hβ _ hn, ← map_pow]
    apply le_trans (hC (x ^ n))
    rw [mul_le_mul_iff_right₀ hC0]
    exact map_pow_le_pow _ _ (Nat.one_le_iff_ne_zero.mp hn)

/-- Given a bounded `f : α →+* β` between seminormed rings, is the seminorm on `β` is
  power-multiplicative, then `f` is a contraction. -/
theorem contraction_of_isPowMul {α β : Type*} [SeminormedRing α] [SeminormedRing β]
    (hβ : IsPowMul (norm : β → ℝ)) {f : α →+* β} (hf : f.IsBounded) (x : α) : norm (f x) ≤ norm x :=
  contraction_of_isPowMul_of_boundedWrt (SeminormedRing.toRingSeminorm α) hβ hf x

/-- Given two power-multiplicative ring seminorms `f, g` on `α`, if `f` is bounded by a positive
  multiple of `g` and vice versa, then `f = g`. -/
theorem eq_seminorms {F : Type*} {α : outParam (Type*)} [Ring α] [FunLike F α ℝ]
    [RingSeminormClass F α ℝ] {f g : F} (hfpm : IsPowMul f) (hgpm : IsPowMul g)
    (hfg : ∃ (r : ℝ) (_ : 0 < r), ∀ a : α, f a ≤ r * g a)
    (hgf : ∃ (r : ℝ) (_ : 0 < r), ∀ a : α, g a ≤ r * f a) : f = g := by
  obtain ⟨r, hr0, hr⟩ := hfg
  obtain ⟨s, hs0, hs⟩ := hgf
  have hle : RingHom.IsBoundedWrt f g (RingHom.id _) := ⟨s, hs0, hs⟩
  have hge : RingHom.IsBoundedWrt g f (RingHom.id _) := ⟨r, hr0, hr⟩
  rw [← Function.Injective.eq_iff DFunLike.coe_injective]
  ext x
  exact le_antisymm (contraction_of_isPowMul_of_boundedWrt g hfpm hge x)
    (contraction_of_isPowMul_of_boundedWrt f hgpm hle x)

variable {R S : Type*} [NormedCommRing R] [CommRing S] [Algebra R S]

/-- If `R` is a normed commutative ring and `f₁` and `f₂` are two power-multiplicative `R`-algebra
  norms on `S`, then if `f₁` and `f₂` are equivalent on every subring `R[y]` for `y : S`, it
  follows that `f₁ = f₂` [BGR, Proposition 3.1.5/1][bosch-guntzer-remmert]. -/
theorem eq_of_powMul_faithful (f₁ : AlgebraNorm R S) (hf₁_pm : IsPowMul f₁) (f₂ : AlgebraNorm R S)
    (hf₂_pm : IsPowMul f₂)
    (h_eq : ∀ y : S, ∃ (C₁ C₂ : ℝ) (_ : 0 < C₁) (_ : 0 < C₂),
      ∀ x : R[y], f₁ x.val ≤ C₁ * f₂ x.val ∧ f₂ x.val ≤ C₂ * f₁ x.val) :
    f₁ = f₂ := by
  ext x
  set g₁ : AlgebraNorm R R[(x : S)] := AlgebraNorm.restriction _ f₁
  set g₂ : AlgebraNorm R R[(x : S)] := AlgebraNorm.restriction _ f₂
  have hg₁_pm : IsPowMul g₁ := IsPowMul.restriction _ hf₁_pm
  have hg₂_pm : IsPowMul g₂ := IsPowMul.restriction _ hf₂_pm
  let y : R[(x : S)] := ⟨x, self_mem_adjoin_singleton R x⟩
  have hy : x = y.val := rfl
  have h1 : f₁ y.val = g₁ y := rfl
  have h2 : f₂ y.val = g₂ y := rfl
  obtain ⟨C₁, C₂, hC₁_pos, hC₂_pos, hC⟩ := h_eq x
  obtain ⟨hC₁, hC₂⟩ := forall_and.mp hC
  rw [hy, h1, h2, eq_seminorms hg₁_pm hg₂_pm ⟨C₁, hC₁_pos, hC₁⟩ ⟨C₂, hC₂_pos, hC₂⟩]

open IntermediateField

variable {K L : Type*} [NontriviallyNormedField K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Type synonym of `K⟮x⟯`. -/
private def AlgebraNorm.copy (_f : AlgebraNorm K L) (x : L) : Type _ := K⟮x⟯
deriving Field, Algebra K

private instance (f : AlgebraNorm K L) (x : L) : FiniteDimensional K (f.copy x) :=
  adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)

private instance (f : AlgebraNorm K L) (x : L) : Algebra (f.copy x) L :=
  inferInstanceAs (Algebra K⟮x⟯ L)

/-- The ring norm defined by a spectral norm. -/
private def AlgebraNorm.ringNorm (f : AlgebraNorm K L) (x : L) : RingNorm (f.copy x) where
  toFun y := f ((algebraMap (f.copy x) L) y)
  map_zero' := map_zero _
  add_le' a b := map_add_le_add _ _ _
  neg' y := by simp
  mul_le' a b := map_mul_le_mul _ _ _
  eq_zero_of_map_eq_zero' a ha := by rwa [map_eq_zero_iff_eq_zero, map_eq_zero] at ha

private instance (f : AlgebraNorm K L) (x : L) : NormedRing (f.copy x) :=
  (f.ringNorm x).toNormedRing

private instance (f : AlgebraNorm K L) (x : L) : NormedAlgebra K (f.copy x) where
  norm_smul_le c y := (map_smul_eq_mul f c (algebraMap (f.copy x) L y)).le

theorem IsPowMul.unique [CompleteSpace K] {f g : AlgebraNorm K L}
    (hf_pm : IsPowMul f) (hg_pm : IsPowMul g) : f = g := by
  apply eq_of_powMul_faithful f hf_pm g hg_pm
  intro x
  let T₀ : g.copy x ≃ₗ[K] f.copy x := LinearEquiv.refl K K⟮x⟯
  let T : g.copy x ≃L[K] f.copy x := T₀.toContinuousLinearEquiv
  obtain ⟨C1, hC1_pos, hC1⟩ := T.symm.toContinuousLinearMap.isBoundedLinearMap.bound
  obtain ⟨C2, hC2_pos, hC2⟩ := T.toContinuousLinearMap.isBoundedLinearMap.bound
  exact ⟨ C2, C1, hC2_pos, hC1_pos,
    forall_and.mpr ⟨fun y ↦ hC2 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩,
      fun y ↦ hC1 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩⟩⟩
