/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Adjoin.Polynomial
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Ideals in polynomial rings
-/

@[expose] public section

noncomputable section

open Polynomial

open Finset

universe u v w

namespace Polynomial

variable {R : Type*} [CommRing R] {a : R}

theorem mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero {b : R[X]} {P : R[X][X]} :
    P ∈ Ideal.span {C (X - C a), X - C b} ↔ (P.eval b).eval a = 0 := by
  rw [Ideal.mem_span_pair]
  constructor <;> intro h
  · rcases h with ⟨_, _, rfl⟩
    simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, add_zero, mul_zero, sub_self]
  · rcases dvd_iff_isRoot.mpr h with ⟨p, hp⟩
    rcases @X_sub_C_dvd_sub_C_eval _ b _ P with ⟨q, hq⟩
    exact ⟨C p, q, by rw [mul_comm, mul_comm q, eq_add_of_sub_eq' hq, hp, C_mul]⟩

theorem ker_evalRingHom (x : R) : RingHom.ker (evalRingHom x) = Ideal.span {X - C x} := by
  ext y
  simp [Ideal.mem_span_singleton, dvd_iff_isRoot, RingHom.mem_ker]

@[simp]
theorem ker_modByMonicHom {q : R[X]} (hq : q.Monic) :
    LinearMap.ker (Polynomial.modByMonicHom q) = (Ideal.span {q}).restrictScalars R :=
  Submodule.ext fun _ => (mem_ker_modByMonic hq).trans Ideal.mem_span_singleton.symm

@[simp]
lemma ker_constantCoeff : RingHom.ker constantCoeff = .span {(X : R[X])} := by
  refine le_antisymm (fun p hp ↦ ?_) (by simp [Ideal.span_le])
  simp only [RingHom.mem_ker, constantCoeff_apply, ← Polynomial.X_dvd_iff] at hp
  rwa [Ideal.mem_span_singleton]

end Polynomial

namespace Algebra

variable {R S : Type*}

lemma mem_ideal_map_adjoin [CommSemiring R] [Semiring S] [Algebra R S] (x : S) (I : Ideal R)
    {y : adjoin R {x}} :
    y ∈ I.map (algebraMap R (adjoin R {x})) ↔
      ∃ p : R[X], (∀ i, p.coeff i ∈ I) ∧ Polynomial.aeval x p = y := by
  constructor
  · intro H
    induction H using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      exact ⟨C a, fun i ↦ by rw [coeff_C]; aesop, aeval_C _ _⟩
    | zero => exact ⟨0, by simp, aeval_zero _⟩
    | add a b ha hb ha' hb' =>
      obtain ⟨a, ha, ha'⟩ := ha'
      obtain ⟨b, hb, hb'⟩ := hb'
      exact ⟨a + b, fun i ↦ by simpa using add_mem (ha i) (hb i), by simp [ha', hb']⟩
    | smul a b hb hb' =>
      obtain ⟨b', hb, hb'⟩ := hb'
      have ⟨p, hp⟩ := adjoin_eq_exists_aeval R x a
      refine ⟨p * b', fun i ↦ ?_, by simp [hp, hb']⟩
      rw [coeff_mul]
      exact sum_mem fun i hi ↦ Ideal.mul_mem_left _ _ (hb _)
  · rintro ⟨p, hp, hp'⟩
    have : y = ∑ i ∈ p.support, p.coeff i • ⟨_, (X ^ i).aeval_mem_adjoin_singleton _ x⟩ := by
      trans ∑ i ∈ p.support, ⟨_, (C (p.coeff i) * X ^ i).aeval_mem_adjoin_singleton _ x⟩
      · ext1
        simp only [AddSubmonoidClass.coe_finset_sum, ← map_sum, ← hp', ← as_sum_support_C_mul_X_pow]
      · congr with i
        simp [Algebra.smul_def]
    simp_rw [this, Algebra.smul_def]
    exact sum_mem fun i _ ↦ Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hp i))

lemma exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top [CommRing R] [CommRing S]
    [Algebra R S] (x : S) (I : Ideal R) (hI : I ≠ ⊤) [Invertible x]
    (h : I.map (algebraMap R (adjoin R {x})) ⊔ .span {⟨x, subset_adjoin rfl⟩} = ⊤) :
    ∃ p : R[X], p.leadingCoeff - 1 ∈ I ∧ p.aeval ⅟x = 0 := by
  rw [← Ideal.one_eq_top, ← Ideal.add_eq_sup, Ideal.add_eq_one_iff] at h
  have ⟨y, hy, z, hz, eq⟩ := h
  have ⟨p, hp⟩ := (mem_ideal_map_adjoin ..).mp hy
  have ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hz
  have ⟨q, hq⟩ := adjoin_eq_exists_aeval R x w
  use (1 - p - X * q).reverse
  have : (1 - p - X * q).coeff 0 - 1 ∈ I := by simpa using hp.1 0
  apply_fun (·.1) at eq hw
  dsimp at eq
  rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero]
  · exact ⟨this, (eval₂_reverse_eq_zero_iff ..).mpr <| by simp [← aeval_def, hp.2, hq, ← eq, hw]⟩
  · exact fun h ↦ hI <| by simpa [h, Ideal.eq_top_iff_one]

end Algebra
