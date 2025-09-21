/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Data.Set.Lattice

/-!
# Big operators on a finset in groups with zero

This file contains the results concerning the interaction of finset big operators with groups with
zero.
-/

open Function

variable {ι κ G₀ M₀ : Type*}

namespace Finset
variable [CommMonoidWithZero M₀] {p : ι → Prop} [DecidablePred p] {f : ι → M₀} {s : Finset ι}
  {i : ι}

lemma prod_eq_zero (hi : i ∈ s) (h : f i = 0) : ∏ j ∈ s, f j = 0 := by
  classical rw [← prod_erase_mul _ _ hi, h, mul_zero]

lemma prod_ite_zero :
    (∏ i ∈ s, if p i then f i else 0) = if ∀ i ∈ s, p i then ∏ i ∈ s, f i else 0 := by
  split_ifs with h
  · exact prod_congr rfl fun i hi => by simp [h i hi]
  · push_neg at h
    rcases h with ⟨i, hi, hq⟩
    exact prod_eq_zero hi (by simp [hq])

lemma prod_boole : ∏ i ∈ s, (ite (p i) 1 0 : M₀) = ite (∀ i ∈ s, p i) 1 0 := by
  rw [prod_ite_zero, prod_const_one]

lemma support_prod_subset (s : Finset ι) (f : ι → κ → M₀) :
    support (fun x ↦ ∏ i ∈ s, f i x) ⊆ ⋂ i ∈ s, support (f i) :=
  fun _ hx ↦ Set.mem_iInter₂.2 fun _ hi H ↦ hx <| prod_eq_zero hi H

variable [Nontrivial M₀] [NoZeroDivisors M₀]

lemma prod_eq_zero_iff : ∏ x ∈ s, f x = 0 ↔ ∃ a ∈ s, f a = 0 := by
  classical
    induction s using Finset.induction_on with
    | empty => exact ⟨Not.elim one_ne_zero, fun ⟨_, H, _⟩ => by simp at H⟩
    | insert _ _ ha ih => rw [prod_insert ha, mul_eq_zero, exists_mem_insert, ih]

lemma prod_ne_zero_iff : ∏ x ∈ s, f x ≠ 0 ↔ ∀ a ∈ s, f a ≠ 0 := by
  rw [Ne, prod_eq_zero_iff]
  push_neg; rfl

lemma support_prod (s : Finset ι) (f : ι → κ → M₀) :
    support (fun j ↦ ∏ i ∈ s, f i j) = ⋂ i ∈ s, support (f i) :=
  Set.ext fun x ↦ by simp [support, prod_eq_zero_iff]

end Finset

namespace Fintype
variable [Fintype ι] [CommMonoidWithZero M₀] {p : ι → Prop} [DecidablePred p] {f : ι → M₀}

lemma prod_ite_zero : (∏ i, if p i then f i else 0) = if ∀ i, p i then ∏ i, f i else 0 := by
  simp [Finset.prod_ite_zero]

lemma prod_boole : ∏ i, (ite (p i) 1 0 : M₀) = ite (∀ i, p i) 1 0 := by simp [Finset.prod_boole]

end Fintype

lemma Units.mk0_prod [CommGroupWithZero G₀] (s : Finset ι) (f : ι → G₀) (h) :
    Units.mk0 (∏ i ∈ s, f i) h =
      ∏ i ∈ s.attach, Units.mk0 (f i) fun hh ↦ h (Finset.prod_eq_zero i.2 hh) := by
  classical induction s using Finset.induction_on <;> simp [*]
