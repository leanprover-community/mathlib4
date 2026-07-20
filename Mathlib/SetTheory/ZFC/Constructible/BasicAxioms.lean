/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Model

/-!
# The elementary set axioms in the constructible universe

This file records the axioms which follow immediately from transitivity and
the basic closure properties of `L`.  They are stated on `Model.LCarrier`, so
they connect directly to the sentences in the membership language.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

/-- Extensionality for the membership structure induced on `L`. -/
theorem lCarrier_extensionality {x y : LCarrier.{u}}
    (h : ∀ z : LCarrier.{u}, z.1 ∈ x.1 ↔ z.1 ∈ y.1) :
    x = y := by
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  constructor
  · intro hzx
    exact (h ⟨z, mem_L_of_mem hzx x.2⟩).mp hzx
  · intro hzy
    exact (h ⟨z, mem_L_of_mem hzy y.2⟩).mpr hzy

/-- The empty-set witness in `L`. -/
def emptyLCarrier : LCarrier.{u} :=
  ⟨∅, empty_mem_L⟩

@[simp]
theorem not_mem_emptyLCarrier (x : LCarrier.{u}) :
    x.1 ∉ emptyLCarrier.1 :=
  ZFSet.notMem_empty x.1

/-- The unordered-pair witness in `L`. -/
def pairLCarrier (x y : LCarrier.{u}) : LCarrier.{u} :=
  ⟨({x.1, y.1} : ZFSet.{u}), pair_mem_L x.2 y.2⟩

@[simp]
theorem mem_pairLCarrier_iff (x y z : LCarrier.{u}) :
    z.1 ∈ (pairLCarrier x y).1 ↔ z = x ∨ z = y := by
  rw [pairLCarrier, ZFSet.mem_pair]
  simp only [Subtype.ext_iff]

/-- The union-set witness in `L`. -/
def sUnionLCarrier (x : LCarrier.{u}) : LCarrier.{u} :=
  ⟨ZFSet.sUnion x.1, sUnion_mem_L x.2⟩

@[simp]
theorem mem_sUnionLCarrier_iff (x z : LCarrier.{u}) :
    z.1 ∈ (sUnionLCarrier x).1 ↔
      ∃ y : LCarrier.{u}, y.1 ∈ x.1 ∧ z.1 ∈ y.1 := by
  rw [sUnionLCarrier, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hyx, hzy⟩
    exact ⟨⟨y, mem_L_of_mem hyx x.2⟩, hyx, hzy⟩
  · rintro ⟨y, hyx, hzy⟩
    exact ⟨y.1, hyx, hzy⟩

/--
Foundation for the membership structure induced on `L`.

The premise is the internal assertion that `x` is nonempty.  Ambient
regularity supplies a member disjoint from `x`, and transitivity of `L` puts
that member back in the carrier.
-/
theorem lCarrier_foundation (x : LCarrier.{u})
    (hx : ∃ y : LCarrier.{u}, y.1 ∈ x.1) :
    ∃ y : LCarrier.{u}, y.1 ∈ x.1 ∧
      ∀ z : LCarrier.{u}, z.1 ∈ x.1 → z.1 ∉ y.1 := by
  have hxne : x.1 ≠ ∅ := by
    intro hxe
    rcases hx with ⟨y, hy⟩
    rw [hxe] at hy
    exact ZFSet.notMem_empty y.1 hy
  rcases ZFSet.regularity x.1 hxne with ⟨y, hyx, hxy⟩
  refine ⟨⟨y, mem_L_of_mem hyx x.2⟩, hyx, ?_⟩
  intro z hzx hzy
  have hzxy : z.1 ∈ x.1 ∩ y := ZFSet.mem_inter.mpr ⟨hzx, hzy⟩
  rw [hxy] at hzxy
  exact ZFSet.notMem_empty z.1 hzxy

end Constructible.Model
