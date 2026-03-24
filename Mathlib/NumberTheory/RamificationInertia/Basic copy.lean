/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.GroupWithZero.Torsion
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Ramification index

-/

@[expose] public section

section temp

open TensorProduct

theorem Submodule.baseChange_mono {R M : Type*} (A : Type*) [CommSemiring R]
    [Semiring A] [Algebra R A] [AddCommMonoid M] [Module R M]
    {N N' : Submodule R M} (h : N ≤ N') :
    N.baseChange A ≤ N'.baseChange A := by
  rw [Submodule.baseChange, LinearMap.baseChange, ← Submodule.subtype_comp_inclusion N N' h,
    ← LinearMap.id_comp LinearMap.id, TensorProduct.AlgebraTensorModule.map_comp]
  apply LinearMap.range_comp_le_range

@[simp]
theorem Submodule.baseChange_le_iff {R M A : Type*} [CommRing R]
    [Ring A] [Algebra R A] [Module.FaithfullyFlat R A] [AddCommGroup M] [Module R M]
    {N N' : Submodule R M} :
    N.baseChange A ≤ N'.baseChange A ↔ N ≤ N' := by
  refine ⟨fun h ↦ ?_, Submodule.baseChange_mono A⟩
  rwa [← N'.ker_mkQ, LinearMap.le_ker_iff_comp_subtype_eq_zero,
    Module.FaithfullyFlat.zero_iff_lTensor_zero R A (N'.mkQ.comp N.subtype),
    LinearMap.lTensor_comp, ← LinearMap.range_le_ker_iff, lTensor_mkQ, ← restrictScalars_le R]

theorem Submodule.baseChange_inj {R M A : Type*} [CommRing R]
    [Ring A] [Algebra R A] [Module.FaithfullyFlat R A] [AddCommGroup M] [Module R M]
    {N N' : Submodule R M} :
    N.baseChange A = N'.baseChange A ↔ N = N' := by
  simp [le_antisymm_iff]

theorem Submodule.baseChange_injective {R M A : Type*} [CommRing R]
    [Ring A] [Algebra R A] [Module.FaithfullyFlat R A] [AddCommGroup M] [Module R M]
    {N N' : Submodule R M} (h : N.baseChange A = N'.baseChange A) :
    N = N' :=
  Submodule.baseChange_inj.mp h

variable (R M S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
  [AddCommGroup M] [Module R M]

/-- `Submodule.baseChange` as an order embedding. -/
def Submodule.baseChangeOrderEmbedding [Module.FaithfullyFlat R S] :
    Submodule R M ↪o Submodule S (S ⊗[R] M) where
  toFun := Submodule.baseChange S
  inj' _ _ := Submodule.baseChange_injective
  map_rel_iff' := Submodule.baseChange_le_iff

variable {R M S}

theorem IsNoetherian.ofFaithfullyFlat (h : IsNoetherian S (S ⊗[R] M)) : IsNoetherian R M := by
  rw [isNoetherian_iff'] at h ⊢
  exact OrderEmbedding.wellFoundedGT (Submodule.baseChangeOrderEmbedding R M S)

theorem IsArtinian.ofFaithfullyFlat (h : IsArtinian S (S ⊗[R] M)) : IsArtinian R M := by
  rw [isArtinian_iff] at h ⊢
  exact OrderEmbedding.wellFounded (Submodule.baseChangeOrderEmbedding R M S) h

theorem IsFiniteLength.ofFaithfullyFlat (h : IsFiniteLength S (S ⊗[R] M)) : IsFiniteLength R M := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
  exact h.imp IsNoetherian.ofFaithfullyFlat IsArtinian.ofFaithfullyFlat

end temp

namespace Ideal

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (p : Ideal R) (q : Ideal S) [q.IsPrime] (r : Ideal T) [r.IsPrime]

noncomputable def ramificationIdx : ℕ :=
  letI Sq := Localization.AtPrime q
  (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat

#check CompositionSeries

theorem ramificationIdx_tower [r.LiesOver q] [q.LiesOver p]
    [Module.Flat (Localization.AtPrime q) (Localization.AtPrime r)] :
    p.ramificationIdx r = p.ramificationIdx q * q.ramificationIdx r := by
  have : r.LiesOver p := LiesOver.trans r q p -- this line might not be necessary
  let Sq := Localization.AtPrime q
  let Tr := Localization.AtPrime r
  have : Module.FaithfullyFlat Sq Tr := Module.FaithfullyFlat.of_flat_of_isLocalHom
  by_cases h : IsFiniteLength Sq (Sq ⧸ p.map (algebraMap R Sq))
  · rw [isFiniteLength_iff_exists_compositionSeries] at h
    obtain ⟨s, hs_bot, hs_top⟩ := h
    rw [RelSeries.head] at hs_bot
    rw [RelSeries.last] at hs_top
    nth_rewrite 2 [ramificationIdx]
    rw [← Module.length_compositionSeries s hs_bot hs_top, ENat.toNat_coe]
    rw [ramificationIdx, ramificationIdx]
    let ψ : TensorProduct Sq Tr (Sq ⧸ map (algebraMap R Sq) p) ≃ₐ[Tr] Tr ⧸ map (algebraMap R Tr) p := by
      sorry
    let φ₀ : Submodule Sq (Sq ⧸ map (algebraMap R Sq) p) →
        Submodule Tr (TensorProduct Sq Tr (Sq ⧸ map (algebraMap R Sq) p)) :=
      Submodule.baseChange Tr
    have hφ₀_bot : φ₀ ⊥ = ⊥ := by simp [φ₀]
    have hφ₀_top : φ₀ ⊤ = ⊤ := by simp [φ₀]
    let φ : Submodule Sq (Sq ⧸ map (algebraMap R Sq) p) →
        Submodule Tr (Tr ⧸ map (algebraMap R Tr) p) := by
      intro N
      have key := N.baseChange Tr
      sorry
    have hφ_bot : φ ⊥ = ⊥ := by
      sorry
    have hφ_top : φ ⊤ = ⊤ := by
      sorry
    have key : ∀ k : Fin s.length.succ, (Order.height (φ (s k))).toNat =
      k * (Module.length Tr (Tr ⧸ map (algebraMap S Tr) q)).toNat := by
      intro k
      induction k using Fin.induction
      case zero =>

        rw [Fin.val_zero, zero_mul, hs_bot, hφ_bot, Order.height_bot, ENat.toNat_zero]
      case succ i hi =>
        have : (i.succ : ℕ) = (i.castSucc : ℕ).succ := by
          rfl
        rw [this, Nat.succ_mul, ← hi, ← Module.length_submodule, ← Module.length_submodule]
        sorry
    specialize key (Fin.last s.length)
    rw [hs_top, hφ_top, Fin.val_last] at key
    rwa [Module.length_eq_height]
  · suffices ¬ IsFiniteLength Tr (Tr ⧸ p.map (algebraMap R Tr)) by
      rw [← Module.length_ne_top_iff, not_ne_iff] at h this
      rw [ramificationIdx, ramificationIdx, ramificationIdx, h, this, ENat.toNat_top, zero_mul]
    contrapose! h
    let f := (Ideal.quotientEquivAlgOfEq Tr (by rw [map_map, ← IsScalarTower.algebraMap_eq])).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Tr (p.map (algebraMap R Sq)))
    exact (f.toLinearEquiv.isFiniteLength h).ofFaithfullyFlat

end Ideal
