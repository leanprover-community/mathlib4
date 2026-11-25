/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johnathon Kyle Armstrong
-/
module

public import Mathlib.GroupTheory.Coxeter.ReflectionSystem
public import Mathlib.Logic.Relation

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finiteness Reduction for Connected Reflection Systems

This file proves that if a connected `ReflectionSystem ι K` over a linearly ordered field `K`
generates a finite group `S.group`, then its bilinear form `S.B` is definite (either positive
definite or negative definite). As an immediate corollary, any connected mixed-sign reflection
system (having both a positive and a negative diagonal entry) generates an infinite group.

## Main definitions
* `ReflectionSystem.quadForm`: The quadratic form `v ↦ ∑ i j, v i * B i j * v j`.
* `ReflectionSystem.IsPosDef` / `ReflectionSystem.IsNegDef`: Definiteness predicates.
* `ReflectionSystem.IsConnected`: Connectedness of the support graph of `S.B`.

## Main results
* `ReflectionSystem.finite_connected_isDefinite`: Connected + finite `S.group` implies
  `S.IsPosDef ∨ S.IsNegDef`.
* `ReflectionSystem.mixed_sign_infinite_of_isConnected`: Connected + positive node + negative
  node implies `¬ Finite S.group`.
-/

open Matrix

@[expose] public section

namespace ReflectionSystem

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- Quadratic form `v ↦ vᵀ B v` associated to a matrix `B`. -/
def quadForm (B : Matrix ι ι K) (v : ι → K) : K :=
  ∑ i : ι, ∑ j : ι, v i * B i j * v j

/-- A `ReflectionSystem` is positive definite if `vᵀ B v > 0` for all `v ≠ 0`. -/
def IsPosDef [LinearOrder K] (S : ReflectionSystem ι K) : Prop :=
  ∀ v : ι → K, v ≠ 0 → 0 < quadForm S.B v

/-- A `ReflectionSystem` is negative definite if `vᵀ B v < 0` for all `v ≠ 0`. -/
def IsNegDef [LinearOrder K] (S : ReflectionSystem ι K) : Prop :=
  ∀ v : ι → K, v ≠ 0 → quadForm S.B v < 0

/-- A `ReflectionSystem` is connected if every pair of indices is linked by a chain of
nonzero entries of `S.B`. -/
def IsConnected (S : ReflectionSystem ι K) : Prop :=
  ∀ i j : ι, Relation.ReflTransGen (fun u v => S.B u v ≠ 0) i j

private def avgForm (S : ReflectionSystem ι K) [Fintype S.group] : Matrix ι ι K :=
  ∑ w : S.group, w.valᵀ * w.val

private lemma avgForm_symm (S : ReflectionSystem ι K) [Fintype S.group] :
    (avgForm S).IsSymm := by
  unfold Matrix.IsSymm avgForm
  rw [transpose_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

private lemma avgForm_invariant (S : ReflectionSystem ι K) [Fintype S.group] (i : ι) :
    (reflectionMatrix S.B i)ᵀ * avgForm S * reflectionMatrix S.B i = avgForm S := by
  let si : S.group := ⟨reflectionMatrix S.B i, Submonoid.subset_closure ⟨i, rfl⟩⟩
  let e : S.group ≃ S.group :=
    { toFun := fun w => w * si
      invFun := fun w => w * si
      left_inv := fun w => by
        ext1
        change (w.val * reflectionMatrix S.B i) * reflectionMatrix S.B i = w.val
        rw [mul_assoc, S.reflectionMatrix_mul_self i, mul_one]
      right_inv := fun w => by
        ext1
        change (w.val * reflectionMatrix S.B i) * reflectionMatrix S.B i = w.val
        rw [mul_assoc, S.reflectionMatrix_mul_self i, mul_one] }
  unfold avgForm
  rw [Finset.mul_sum, Finset.sum_mul]
  calc ∑ w : S.group, (reflectionMatrix S.B i)ᵀ * (w.valᵀ * w.val) * reflectionMatrix S.B i
      = ∑ w : S.group, (w * si).valᵀ * (w * si).val := by
          refine Finset.sum_congr rfl fun w _ => ?_
          change (reflectionMatrix S.B i)ᵀ * (w.valᵀ * w.val) * reflectionMatrix S.B i =
            (w.val * reflectionMatrix S.B i)ᵀ * (w.val * reflectionMatrix S.B i)
          rw [Matrix.transpose_mul]
          simp only [mul_assoc]
    _ = ∑ w : S.group, w.valᵀ * w.val :=
          Equiv.sum_comp e (fun w : S.group => w.valᵀ * w.val)

private lemma quadForm_avgForm_pos [LinearOrder K] [IsStrictOrderedRing K]
    (S : ReflectionSystem ι K) [Fintype S.group] {v : ι → K} (hv : v ≠ 0) :
    0 < quadForm (avgForm S) v := by
  have hterm : ∀ w : S.group,
      ∑ i : ι, ∑ j : ι, v i * (w.valᵀ * w.val) i j * v j =
        ∑ r : ι, (∑ i : ι, w.val r i * v i) ^ 2 := by
    intro w
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    calc ∑ i : ι, ∑ j : ι, v i * (∑ r : ι, w.val r i * w.val r j) * v j
        = ∑ i : ι, ∑ j : ι, ∑ r : ι, (w.val r i * v i) * (w.val r j * v j) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun r _ => by ring
      _ = ∑ r : ι, ∑ i : ι, ∑ j : ι, (w.val r i * v i) * (w.val r j * v j) := by
            have hsw : (∑ i : ι, ∑ j : ι, ∑ r : ι, (w.val r i * v i) * (w.val r j * v j)) =
                ∑ i : ι, ∑ r : ι, ∑ j : ι, (w.val r i * v i) * (w.val r j * v j) :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
            rw [hsw, Finset.sum_comm]
      _ = ∑ r : ι, (∑ i : ι, w.val r i * v i) ^ 2 := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [sq, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  have hquad : quadForm (avgForm S) v =
      ∑ w : S.group, ∑ r : ι, (∑ i : ι, w.val r i * v i) ^ 2 := by
    unfold quadForm avgForm
    simp only [Matrix.sum_apply]
    have h1 : (∑ i : ι, ∑ j : ι,
          v i * (∑ w : S.group, (w.valᵀ * w.val) i j) * v j) =
        ∑ i : ι, ∑ w : S.group, ∑ j : ι, v i * (w.valᵀ * w.val) i j * v j := by
      refine Finset.sum_congr rfl fun i _ => ?_
      calc ∑ j : ι, v i * (∑ w : S.group, (w.valᵀ * w.val) i j) * v j
          = ∑ j : ι, ∑ w : S.group, v i * (w.valᵀ * w.val) i j * v j := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum, Finset.sum_mul]
        _ = ∑ w : S.group, ∑ j : ι, v i * (w.valᵀ * w.val) i j * v j := Finset.sum_comm
    rw [h1, Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => hterm w
  rw [hquad]
  obtain ⟨r₀, hr₀⟩ := Function.ne_iff.mp hv
  have h1_term : 0 < ∑ r : ι, (∑ i : ι, (1 : S.group).val r i * v i) ^ 2 := by
    have hsimp : ∑ r : ι, (∑ i : ι, (1 : S.group).val r i * v i) ^ 2 =
        ∑ r : ι, v r ^ 2 := by
      refine Finset.sum_congr rfl fun r _ => ?_
      have hrow : ∑ i : ι, (1 : Matrix ι ι K) r i * v i = v r := by
        simp [Matrix.one_apply]
      change (∑ i : ι, (1 : Matrix ι ι K) r i * v i) ^ 2 = v r ^ 2
      rw [hrow]
    rw [hsimp]
    have hpos : 0 < v r₀ ^ 2 := sq_pos_of_ne_zero hr₀
    have hle : v r₀ ^ 2 ≤ ∑ r : ι, v r ^ 2 :=
      Finset.single_le_sum (fun r _ => sq_nonneg (v r)) (Finset.mem_univ r₀)
    linarith
  have hle_sum :
      (∑ r : ι, (∑ i : ι, (1 : S.group).val r i * v i) ^ 2) ≤
        ∑ w : S.group, ∑ r : ι, (∑ i : ι, w.val r i * v i) ^ 2 :=
    Finset.single_le_sum
      (f := fun w : S.group => ∑ r : ι, (∑ i : ι, w.val r i * v i) ^ 2)
      (fun w _ => Finset.sum_nonneg fun r _ => sq_nonneg _)
      (Finset.mem_univ (1 : S.group))
  linarith

private lemma avgForm_diag_pos [LinearOrder K] [IsStrictOrderedRing K]
    (S : ReflectionSystem ι K) [Fintype S.group] (i : ι) :
    0 < avgForm S i i := by
  let e : ι → K := fun r => if r = i then 1 else 0
  have he : e ≠ 0 := by
    intro h
    have := congrFun h i
    simp [e] at this
  have hpos := quadForm_avgForm_pos S he
  have hquad : quadForm (avgForm S) e = avgForm S i i := by
    unfold quadForm
    simp [e]
  linarith

private lemma avgForm_entry_ratio [LinearOrder K] [IsStrictOrderedRing K]
    (S : ReflectionSystem ι K) [Fintype S.group] (i j : ι) :
    avgForm S i j = (avgForm S i i / S.B i i) * S.B i j := by
  have hinv := congrFun (congrFun (avgForm_invariant S i) i) j
  have hBii : S.B i i ≠ 0 := S.B_diag_ne_zero i
  have hcol_i : ∀ r : ι, reflectionMatrix S.B i r i = if r = i then -1 else 0 := by
    intro r
    rw [reflectionMatrix_apply]
    by_cases hri : r = i
    · subst hri; simp [hBii]; field_simp; ring
    · simp [hri]
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at hinv
  have hleft :
      (∑ x : ι,
        (∑ r : ι, reflectionMatrix S.B i r i * avgForm S r x) *
          reflectionMatrix S.B i x j) =
      -(avgForm S i j) + (2 * S.B i j / S.B i i) * avgForm S i i := by
    have h1 : ∀ x : ι,
        (∑ r : ι, reflectionMatrix S.B i r i * avgForm S r x) = -avgForm S i x := by
      intro x
      simp_rw [hcol_i]
      simp
    simp_rw [h1, reflectionMatrix_apply]
    calc ∑ x : ι, -avgForm S i x *
          ((if x = j then 1 else 0) - if x = i then 2 * S.B i j / S.B i i else 0)
        = (∑ x : ι, (if x = j then -avgForm S i x else 0)) -
            ∑ x : ι, (if x = i then -avgForm S i x * (2 * S.B i j / S.B i i) else 0) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun x _ => ?_
            split_ifs <;> ring
      _ = -(avgForm S i j) + (2 * S.B i j / S.B i i) * avgForm S i i := by
            simp [Finset.sum_ite_eq', Finset.mem_univ]; ring
  rw [hleft] at hinv
  have h2 : 2 * avgForm S i j = 2 * ((S.B i j / S.B i i) * avgForm S i i) := by
    have h2' : 2 * avgForm S i j = (2 * S.B i j / S.B i i) * avgForm S i i := by linarith
    rw [h2']; ring
  have h3 : avgForm S i j = (S.B i j / S.B i i) * avgForm S i i := by linarith
  rw [h3]
  field_simp

/-- If a connected `ReflectionSystem` over a nonempty index type `ι` generates a finite group
`S.group`, then its bilinear form `S.B` is definite (`S.IsPosDef ∨ S.IsNegDef`). -/
theorem finite_connected_isDefinite [LinearOrder K] [IsStrictOrderedRing K]
    (S : ReflectionSystem ι K) [Nonempty ι] (hconn : S.IsConnected) (hfin : Finite S.group) :
    S.IsPosDef ∨ S.IsNegDef := by
  classical
  let _ : Fintype S.group := Fintype.ofFinite S.group
  let c : ι → K := fun i => avgForm S i i / S.B i i
  have hadj : ∀ u v : ι, S.B u v ≠ 0 → c u = c v := by
    intro u v huv
    have h1 := avgForm_entry_ratio S u v
    have h2 := avgForm_entry_ratio S v u
    have hG : avgForm S u v = avgForm S v u := by
      have hs := congrFun (congrFun (avgForm_symm S) v) u
      simpa using hs
    have hB : S.B u v = S.B v u := by
      have hs := congrFun (congrFun S.B_symm v) u
      simpa using hs
    have hmul : c u * S.B u v = c v * S.B u v := by
      calc c u * S.B u v = avgForm S u v := h1.symm
        _ = avgForm S v u := hG
        _ = c v * S.B v u := h2
        _ = c v * S.B u v := by rw [hB]
    exact mul_right_cancel₀ huv hmul
  have hconst : ∀ i j : ι, c i = c j := by
    intro i j
    induction hconn i j with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans (hadj _ _ hbc)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hG_eq : ∀ i j : ι, avgForm S i j = c i₀ * S.B i j := by
    intro i j
    rw [avgForm_entry_ratio S i j]
    change c i * S.B i j = c i₀ * S.B i j
    rw [hconst i i₀]
  have hquad_eq : ∀ v : ι → K, quadForm (avgForm S) v = c i₀ * quadForm S.B v := by
    intro v
    unfold quadForm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hG_eq i j]
    ring
  have hc0 : c i₀ ≠ 0 := div_ne_zero (ne_of_gt (avgForm_diag_pos S i₀)) (S.B_diag_ne_zero i₀)
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · right
    intro v hv
    have hGpos := quadForm_avgForm_pos S hv
    rw [hquad_eq v] at hGpos
    nlinarith
  · left
    intro v hv
    have hGpos := quadForm_avgForm_pos S hv
    rw [hquad_eq v] at hGpos
    nlinarith

/-- Every connected `ReflectionSystem` having both a positive node (`S.B i i > 0`) and a
negative node (`S.B j j < 0`) generates an infinite group (`¬ Finite S.group`). -/
theorem mixed_sign_infinite_of_isConnected [LinearOrder K] [IsStrictOrderedRing K]
    (S : ReflectionSystem ι K) (hconn : S.IsConnected) (i j : ι)
    (hi : 0 < S.B i i) (hj : S.B j j < 0) :
    ¬ Finite S.group := by
  intro hfin
  have hne : Nonempty ι := ⟨i⟩
  rcases S.finite_connected_isDefinite hconn hfin with hpos | hneg
  · let ej : ι → K := fun r => if r = j then 1 else 0
    have hej : ej ≠ 0 := by intro h; have := congrFun h j; simp [ej] at this
    have hq := hpos ej hej
    have hval : quadForm S.B ej = S.B j j := by unfold quadForm; simp [ej]
    linarith
  · let ei : ι → K := fun r => if r = i then 1 else 0
    have hei : ei ≠ 0 := by intro h; have := congrFun h i; simp [ei] at this
    have hq := hneg ei hei
    have hval : quadForm S.B ei = S.B i i := by unfold quadForm; simp [ei]
    linarith

end ReflectionSystem
