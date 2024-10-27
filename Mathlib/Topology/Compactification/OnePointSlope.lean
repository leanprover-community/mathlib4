/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Compactification.OnePoint
import Mathlib.Algebra.Quaternion

/-!
# An alternative equivalence between OnePoint K and Projectivization

An alternative to `OnePointEquiv` which has other generalizations.

## Main results

* `field_slope_equiv`: The desired equivalence.

## Tags

one-point compactification
-/

open scoped LinearAlgebra.Projectivization OnePoint
open Projectivization

open Classical

noncomputable def OnePoint_div {K : Type} [DivisionRing K] (a : K) (r : K): OnePoint K
  := ite (r ≠ 0) (a / r) ∞

infix:50 " ÷ " => OnePoint_div




lemma div_slope_well_defined {K : Type} [Field K]
  (a b : { v : Fin 2 → K // v ≠ 0 })
  (h : ∃ c : Kˣ, (fun m : Kˣ ↦ m • b.1) c = a.1) :
  (fun u ↦ u.1 0 ÷ u.1 1) a = (fun u ↦ u.1 0 ÷ u.1 1) b := by
        obtain ⟨c,hc⟩ := h
        simp_all only
        rw [← hc]; unfold OnePoint_div; simp only [ne_eq, Fin.isValue, Pi.smul_apply, ite_not]
        split_ifs with hbc hb hb
        · rfl
        · simp_all
          apply hb;exact (Units.mul_right_eq_zero c).mp hbc
        · rw [hb] at hbc;simp at hbc
        · apply congrArg some
          field_simp
          show c * b.1 0 * b.1 1 = b.1 0 * (c * b.1 1)
          ring

noncomputable def field_div_slope {K : Type} [Field K] (p : ℙ K (Fin 2 → K)) : OnePoint K :=
  Quotient.lift (fun u : { v : Fin 2 → K // v ≠ 0} ↦ OnePoint_div (u.1 0) (u.1 1))
  div_slope_well_defined p


lemma not_both_zero {K : Type} [Field K]
  (a : { v : Fin 2 → K // v ≠ 0}) (h : a.1 1 = 0) : a.1 0 ≠ 0 := by
  intro hc; apply a.2; ext s
  cases (Nat.le_one_iff_eq_zero_or_eq_one.mp (Fin.is_le s)) with
  |inl hl =>
    have : s = 0 := by apply Fin.eq_of_val_eq;tauto
    subst this;simp_all
  |inr hr =>
    have : s = 1 := by apply Fin.eq_of_val_eq;tauto
    subst this;simp_all


instance mys {K : Type} [Field K]:
  Setoid ({v : Fin 2 → K // v ≠ 0}) :=
  projectivizationSetoid K (Fin 2 → K)

lemma field_div_slope_inj_lifted {K : Type} [Field K]
  (a b : { v : Fin 2 → K // v ≠ 0 }) :
    field_div_slope ⟦a⟧ = field_div_slope ⟦b⟧ →
    (⟦a⟧ : Quotient (projectivizationSetoid K (Fin 2 → K))) = ⟦b⟧ := by
      unfold field_div_slope
      intro h
      repeat rw [Quotient.lift_mk] at h
      apply Quotient.sound
      unfold OnePoint_div at h
      split_ifs at h with g₀ g₁ g₂
      · use Units.mk ((a.1 1) / (b.1 1)) ((b.1 1) / (a.1 1)) (by field_simp) (by field_simp)
        ext s
        cases (Nat.le_one_iff_eq_zero_or_eq_one.mp (Fin.is_le s)) with
        |inl hl =>
          have : s = 0 := Fin.eq_of_val_eq hl
          subst this; simp_all;field_simp
          have h' : (a.1 0 / a.1 1) = (b.1 0 / b.1 1) := by
            apply Option.some_injective; tauto
          field_simp at h';rw [h',mul_comm]
        |inr hr =>
          have : s = 1 := Fin.eq_of_val_eq hr
          subst this; simp_all
      · simp at h
      · simp at h
      · simp_all
        have h₀ : a.1 0 ≠ 0 := by apply not_both_zero;tauto
        have h₁ : b.1 0 ≠ 0 := by apply not_both_zero;tauto
        use Units.mk ((a.1 0) / (b.1 0)) ((b.1 0) / (a.1 0)) (by field_simp) (by field_simp)
        simp; apply List.ofFn_inj.mp; simp; rw [g₀,g₂]; field_simp

lemma field_div_slope_injective {K : Type} [Field K]  :
  Function.Injective (@field_div_slope K _) :=
  Quotient.ind (fun a ↦ Quotient.ind (field_div_slope_inj_lifted a))

def slope_inv {K : Type} [Field K] (p : OnePoint K) : ℙ K (Fin 2 → K) := match p with
|some t => mk' K ⟨![t, 1], by simp⟩
|∞      => mk' K ⟨![1, 0], by simp⟩

noncomputable def field_f {K : Type} [Field K] :=
  (fun u : {v : Fin 2 → K // v ≠ 0} ↦
    if u.1 1 ≠ 0 then some (u.1 0 / u.1 1) else ∞)

lemma field_div_slope_inv {K : Type} [Field K] :
  Function.LeftInverse (@field_div_slope K _) (@slope_inv K _) := by
    intro a
    have g₀ : field_f ⟨![(1:K), 0], by simp⟩ = ∞ := by unfold field_f;simp;
    have g₁ (t:K) : field_f ⟨![t, 1], by simp⟩ = some t := by unfold field_f;simp
    cases a with
    |none => exact g₀
    |some t => exact g₁ t

lemma field_div_slope_surjective {K : Type} [Field K]:
  Function.Surjective (@field_div_slope K _) :=
  fun r ↦ ⟨slope_inv r, field_div_slope_inv r⟩

noncomputable instance field_slope_equiv {K : Type} [Field K] :
  OnePoint K ≃ ℙ K (Fin 2 → K) where
  toFun     := slope_inv
  invFun    := field_div_slope
  left_inv  := field_div_slope_inv
  right_inv := Function.rightInverse_of_injective_of_leftInverse
    field_div_slope_injective field_div_slope_inv
