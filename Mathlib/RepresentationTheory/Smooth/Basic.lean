/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Smooth representations

This file defines smoothness for representations of a topological group, and proves basic closure
properties.

A representation is called smooth if the stabilizer of any vector is open. We prove that
subrepresentations, quotient representations, direct sums, and tensor products of smooth
representations are smooth. We define `smoothHom` and `contragredient` by cutting out the
smooth vectors from the naive `linHom` and `dual`.

## Main definitions

* `Representation.Smooth.IsSmoothVector`
* `Representation.Smooth.IsSmooth`
* `Representation.Smooth.smoothVectors`
* `Representation.Smooth.smoothHom`
* `Representation.Smooth.contragredient`

## Main theorems

* `isSmooth_smoothVectors`

-/

@[expose] public section

open Representation

namespace Representation.Smooth

section basic

variable {G : Type*} [TopologicalSpace G] [Group G]
variable {k : Type*} [Semiring k]
variable {V : Type*} [AddCommMonoid V] [Module k V]

/-- A vector is called smooth if its stabilizer is open. -/
def IsSmoothVector (ρ : Representation k G V) (v : V) : Prop :=
  IsOpen ((stabilizer ρ v) : Set G)

lemma isSmoothVector_iff {ρ : Representation k G V} {v : V} :
    IsSmoothVector ρ v ↔ IsOpen {g : G | ρ g v = v} := by
  rfl

/-- A representation is called smooth if every vector is smooth. -/
class IsSmooth (ρ : Representation k G V) : Prop where
  smooth : ∀ v : V, IsSmoothVector ρ v

lemma isSmooth_iff {ρ : Representation k G V} :
    IsSmooth ρ ↔ ∀ v : V, IsOpen {g : G | ρ g v = v} :=
  ⟨fun h v => isSmoothVector_iff.mp (h.smooth v),
    fun h => {smooth v := isSmoothVector_iff.mpr (h v)}⟩

/-- Any trivial representation is smooth. -/
lemma isSmooth_trivial : IsSmooth (trivial k G V) := by
  simp [isSmooth_iff]

/-- Any subrepresentation of a smooth representation is smooth. -/
lemma isSmooth_subrepresentation {ρ : Representation k G V} (φ : Subrepresentation ρ)
    [h : IsSmooth ρ] : IsSmooth φ.toRepresentation := by
  simpa [isSmooth_iff, isSmoothVector_iff] using fun v _ => h.smooth v

/-- An arbitrary direct sum of smooth representations is smooth. -/
lemma isSmooth_directSum {I : Type*} {V : I → Type*} [(i : I) → AddCommMonoid (V i)]
    [(i : I) → Module k (V i)] (ρ : (i : I) → Representation k G (V i)) (h : ∀ i, IsSmooth (ρ i)) :
    IsSmooth (Representation.directSum ρ) := by
  classical
  simp only [isSmooth_iff, directSum_apply, DirectSum.ext_iff, DirectSum.lmap_apply]
  intro v
  have heq : {g | ∀ i, ρ i g (v i) = v i} = ⋂ i ∈ DFinsupp.support v, {g | ρ i g (v i) = v i} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · exact fun h_stab i _ => h_stab i
    · intro h_stab i
      by_cases h_supp : i ∈ DFinsupp.support v
      · exact h_stab i h_supp
      · rw [DFinsupp.notMem_support_iff] at h_supp
        rw [h_supp, map_zero]
  rw [heq]
  exact isOpen_biInter_finset fun i _ => (h i).smooth (v i)

end basic

section quotient

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
variable {k : Type*} [Ring k]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- Any quotient representation of a smooth representation is smooth. -/
lemma isSmooth_quotient {ρ : Representation k G V} {φ : Subrepresentation ρ} [h : IsSmooth ρ] :
    IsSmooth φ.quotient := by
  refine ⟨fun w => Quotient.inductionOn' w fun v => ?_⟩
  have h_sub : stabilizer ρ v ≤ stabilizer φ.quotient ⟦v⟧ := by
    simp +contextual [SetLike.le_def, Subrepresentation.quotient_apply_mk]
  exact Subgroup.isOpen_mono h_sub (h.smooth v)

end quotient

section smoothVectors

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
variable {k : Type*} [Semiring k]
variable {V : Type*} [AddCommMonoid V] [Module k V]
variable {V' : Type*} [AddCommMonoid V'] [Module k V']

omit [IsTopologicalGroup G] in
lemma isSmoothVector_zero (ρ : Representation k G V) : IsSmoothVector ρ 0 := by
  simp [isSmoothVector_iff]

lemma isSmoothVector_add {ρ : Representation k G V} {v1 v2 : V}
    (hv1 : IsSmoothVector ρ v1) (hv2 : IsSmoothVector ρ v2) :
    IsSmoothVector ρ (v1 + v2) :=
  Subgroup.isOpen_mono (le_stabilizer_add ρ v1 v2) (hv1.inter hv2)

lemma isSmoothVector_sum {n : ℕ} {ρ : Representation k G V} {v : Fin n → V}
    (h : ∀ i : Fin n, IsSmoothVector ρ (v i)) : IsSmoothVector ρ (∑ i, v i) :=
  Subgroup.isOpen_mono (le_stabilizer_sum ρ v) (by simpa using isOpen_iInter_of_finite h)

lemma isSmoothVector_smul {ρ : Representation k G V} {v : V} (c : k)
    (h : IsSmoothVector ρ v) : IsSmoothVector ρ (c • v) :=
  Subgroup.isOpen_mono (le_stabilizer_smul ρ c v) h

open scoped Pointwise

lemma isSmoothVector_apply {ρ : Representation k G V} {v : V} (g : G) (hv : IsSmoothVector ρ v) :
    IsSmoothVector ρ (ρ g v) := by
  rw [IsSmoothVector, stabilizer_conj]
  convert isOpenMap_mul_right g⁻¹ (g • ρ.stabilizer v) (isOpenMap_mul_left g (ρ.stabilizer v) hv)
  ext x
  rw [Set.mem_image]
  simp [Set.mem_smul_set]

/-- `IntertwiningMap` sends smooth vectors to smooth vectors. -/
lemma IntertwiningMap.isSmoothVector {ρ : Representation k G V} {ρ' : Representation k G V'}
    {v : V} (f : ρ.IntertwiningMap ρ') (h : IsSmoothVector ρ v) : IsSmoothVector ρ' (f v) :=
  Subgroup.isOpen_mono (IntertwiningMap.stabilizer_le f v) h

/-- The submodule of smooth vectors of a representation. -/
def smoothSubmodule (ρ : Representation k G V) : Submodule k V where
  carrier := {v : V | IsSmoothVector ρ v}
  add_mem' h1 h2 := isSmoothVector_add h1 h2
  zero_mem' := isSmoothVector_zero ρ
  smul_mem' c _ h := isSmoothVector_smul c h

/-- Smooth vectors of a representation form a `Subrepresentation`. -/
def smoothVectors (ρ : Representation k G V) : Subrepresentation ρ where
  toSubmodule := smoothSubmodule ρ
  apply_mem_toSubmodule g _ h := isSmoothVector_apply g h

@[simp]
lemma mem_smoothSubmodule {ρ : Representation k G V} {v : V} :
    v ∈ (smoothVectors ρ).toSubmodule ↔ IsSmoothVector ρ v := by
  rfl

/-- Taking smooth vectors gives a smooth representation. -/
theorem isSmooth_smoothVectors {ρ : Representation k G V} :
    IsSmooth (smoothVectors ρ).toRepresentation := by
  simp [isSmooth_iff, isSmoothVector_iff]

/-- `IntertwiningMap` descends to maximal smooth subrepresentations. -/
def IntertwiningMap.smoothVectors {ρ : Representation k G V} {ρ' : Representation k G V'}
    (f : ρ.IntertwiningMap ρ') :
    ((smoothVectors ρ).toRepresentation).IntertwiningMap (smoothVectors ρ').toRepresentation where
  toFun v := ⟨f v.1, IntertwiningMap.isSmoothVector f v.2⟩
  map_add' := by simp [Subtype.ext_iff]
  map_smul' := by simp [Subtype.ext_iff]
  isIntertwining' g := by ext; apply IntertwiningMap.isIntertwining

end smoothVectors

section tensorHomContragredient

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
variable {k : Type*} [CommSemiring k]
variable {V : Type*} [AddCommMonoid V] [Module k V]
variable {V' : Type*} [AddCommMonoid V'] [Module k V']

lemma isSmoothVector_tmul {ρ : Representation k G V} {ρ' : Representation k G V'} {v : V} {v' : V'}
    (h : IsSmoothVector ρ v) (h' : IsSmoothVector ρ' v') :
    IsSmoothVector (ρ.tprod ρ') (v ⊗ₜ[k] v') := by
  have h_sub : ρ.stabilizer v ⊓ ρ'.stabilizer v' ≤ (ρ.tprod ρ').stabilizer (v ⊗ₜ[k] v') := by
    simp +contextual [SetLike.le_def]
  exact Subgroup.isOpen_mono h_sub (h.inter h')

/-- The tensor product of two smooth representations is smooth. -/
lemma isSmooth_tprod {ρ : Representation k G V} {ρ' : Representation k G V'}
    [h : IsSmooth ρ] [h' : IsSmooth ρ'] : IsSmooth (tprod ρ ρ') := by
  refine ⟨fun v => ?_⟩
  induction v with
  | zero => exact isSmoothVector_zero _
  | tmul v v' => exact isSmoothVector_tmul (h.smooth v) (h'.smooth v')
  | add _ _ h1 h2 => exact isSmoothVector_add h1 h2

/-- The maximal smooth subrepresentation of the `linHom` representation. -/
def smoothHom (ρ : Representation k G V) (ρ' : Representation k G V') :
    Representation k G (smoothVectors (linHom ρ ρ')).toSubmodule :=
  (smoothVectors (linHom ρ ρ')).toRepresentation

lemma isSmooth_smoothHom {ρ : Representation k G V} {ρ' : Representation k G V'} :
    IsSmooth (smoothHom ρ ρ') :=
  isSmooth_smoothVectors

/-- The maximal smooth subrepresentation of the dual representation. -/
def contragredient (ρ : Representation k G V) :
    Representation k G (smoothVectors ρ.dual).toSubmodule :=
  (smoothVectors ρ.dual).toRepresentation

lemma isSmooth_contragredient {ρ : Representation k G V} :
    IsSmooth (contragredient ρ) :=
  isSmooth_smoothVectors

end tensorHomContragredient

end Representation.Smooth
