/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Krull dimension of polynomial ring

This file proves the basic properties of the krull dimension of the polynomial ring over a
commutative ring

## Main results

* `Polynomial.ringKrullDim_le`: the krull dimension of the polynomial ring over a commutative ring
  `R` is less than `2 * (ringKrullDim R) + 1`.
-/

lemma Order.krullDim_le_of_krullDim_preimage_le {α β : Type*} [Preorder α] [Preorder β] (f : α →o β)
    {m : ℕ} (h : ∀ (x : β), Order.krullDim (f ⁻¹' {x}) ≤ m) :
    Order.krullDim α ≤ (m + 1) * Order.krullDim β + m := by
  classical
  rw [Order.krullDim, Order.krullDim]
  apply iSup_le fun p ↦ ?_
  suffices h : ∃ (q : LTSeries β), p.length ≤ (m + 1) * q.length + m by
    obtain ⟨q, hq⟩ := h
    apply le_trans (Nat.mono_cast hq)
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    apply add_le_add_right
    sorry
  let q : List β := List.dedup (List.map f p.toList)
  have hq_lt : List.Chain' (· < ·) q := sorry
  have hq_ne_nil : q ≠ [] := by simp [q, RelSeries.toList_ne_nil p]
  let q' : LTSeries β := RelSeries.Equiv.symm ⟨q, ⟨hq_ne_nil, hq_lt⟩⟩
  have : q'.toList = q := congr($((RelSeries.Equiv.right_inv ⟨q, ⟨hq_ne_nil, hq_lt⟩⟩)))
  have h_length : p.length ≤ (m + 1) * q'.length + m := by
    rw [← Nat.succ_le_succ_iff, Nat.succ_eq_add_one, Nat.succ_eq_add_one, add_assoc]
    nth_rw 2 [← mul_one (m + 1)]
    rw [← mul_add, ← RelSeries.length_toList, ← RelSeries.length_toList, this, ← List.length_map f,
      ← List.sum_map_count_dedup_eq_length, mul_comm]
    convert List.sum_le_card_nsmul _ (m + 1) ?_
    · exact Eq.symm (List.length_map fun x ↦ List.count x (List.map f (RelSeries.toList p)))
    · simp only [List.count_eq_countP, List.countP_eq_length_filter, List.filter_map,
      List.length_map, List.mem_map, List.mem_dedup, RelSeries.mem_toList, exists_exists_and_eq_and,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, q]
      intro a ha
      let p' : List (f ⁻¹' {f a}) := List.map (fun x ↦ ⟨x.val, sorry⟩)
        (List.filter ((fun x ↦ x == f a) ∘ ⇑f) (RelSeries.toList p)).attach

      sorry
  exact ⟨q', h_length⟩

/-- Another version when the `OrderHom` is unbundled -/
lemma Order.krullDim_le_of_krullDim_preimage_le' {α β : Type*} [Preorder α] [Preorder β] (f : α → β)
    (h_mono : Monotone f) {m : ℕ} (h : ∀ (x : β), Order.krullDim (f ⁻¹' {x}) ≤ m) :
    Order.krullDim α ≤ (m + 1) * Order.krullDim β + m :=
  Order.krullDim_le_of_krullDim_preimage_le ⟨f, h_mono⟩ h

def PrimeSpectrum.preimageOrderIsoTensorResidueField (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    (algebraMap R S).specComap ⁻¹' {p} ≃o
      PrimeSpectrum (TensorProduct R p.asIdeal.ResidueField S) := sorry

theorem Polynomial.ringKrullDim_eq_one_of_field (k : Type*) [Field k] :
    ringKrullDim (Polynomial k) = 1 := sorry

theorem Polynomial.ringKrullDim_le {R : Type*} [CommRing R] :
    ringKrullDim (Polynomial R) ≤ 2 * (ringKrullDim R) + 1 := by
  rw [ringKrullDim, ringKrullDim]
  apply Order.krullDim_le_of_krullDim_preimage_le' C.specComap ?_ (fun p ↦ ?_)
  · exact fun {a b} h ↦ Ideal.comap_mono h
  · rw [show C = (algebraMap R (Polynomial R)) from rfl, Order.krullDim_eq_of_orderIso
      (PrimeSpectrum.preimageOrderIsoTensorResidueField R (Polynomial R) p), ← ringKrullDim,
      ← ringKrullDim_eq_of_ringEquiv (polyEquivTensor R (p.asIdeal.ResidueField)).toRingEquiv,
      Polynomial.ringKrullDim_eq_one_of_field, Nat.cast_one]
