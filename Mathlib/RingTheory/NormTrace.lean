/-
Copyright (c) 2023 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs

/-!
# Relation between norms and traces
-/

public section

open Module

lemma Algebra.norm_one_add_smul {A B} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (a : A) (x : B) :
    ∃ r : A, Algebra.norm A (1 + a • x) = 1 + Algebra.trace A B x * a + r * a ^ 2 := by
  classical
  let ι := Module.Free.ChooseBasisIndex A B
  let b : Basis ι A B := Module.Free.chooseBasis _ _
  have : Fintype ι := inferInstance
  clear_value ι b
  simp_rw [Algebra.norm_eq_matrix_det b, Algebra.trace_eq_matrix_trace b]
  simp only [map_add, map_one, map_smul, Matrix.det_one_add_smul a]
  exact ⟨_, rfl⟩

/-- Let `B` be a finite free `ℤ`-algebra. If `1 + a • x` is a unit, where `a : ℤ` does not
divide `2`, then its norm is `1`. -/
lemma Algebra.norm_one_add_smul_eq_one_of_isUnit {B : Type*} [CommRing B] [Module.Free ℤ B]
    [Module.Finite ℤ B] {a : ℤ} (ha : ¬ a ∣ 2) {x : B} (hx : IsUnit (1 + a • x)) :
    Algebra.norm ℤ (1 + a • x) = 1 := by
  obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul a x
  exact (Int.isUnit_iff.mp (hx.map (Algebra.norm ℤ))).resolve_right fun h ↦
    ha ⟨-Algebra.trace ℤ B x - r * a, by grind⟩
