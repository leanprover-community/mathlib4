/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Smooth representations

This file defines smoothness for representations of a topological group, and proves basic closure
properties.

A representation is called smooth if the stabilizer of any vector is open. We prove that
subrepresentations, quotient representations, direct sums, and tensor products of smooth
representations are smooth. We construct `smoothHom`, resp. `contragredient` by cutting out the
smooth vectors from the naive `linHom`, resp. `dual`.

## Main definitions

* `Representation.Smooth.IsSmooth`
* `Representation.Smooth.smoothHom`
* `Representation.Smooth.smoothDual`

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
    (IsSmoothVector ρ v) ↔ IsOpen {g : G | ρ g v = v} := by
  rfl

/-- A representation is called smooth if every vector is smooth. -/
class IsSmooth (ρ : Representation k G V) : Prop where
  smooth : ∀ (v : V), IsSmoothVector ρ v

lemma isSmooth_iff {ρ : Representation k G V} :
    (IsSmooth ρ) ↔ ∀ (v : V), IsOpen {g : G | ρ g v = v} :=
  ⟨fun h v => isSmoothVector_iff.mp (h.smooth v),
  fun h => {smooth := fun v => isSmoothVector_iff.mpr (h v)}⟩

/-- Any trivial representation is smooth. -/
lemma isSmooth_trivial : IsSmooth (trivial k G V) := by
  simp [isSmooth_iff]

/-- Any subrepresentation of a smooth representation is smooth. -/
lemma isSmooth_subrepresentation (ρ : Representation k G V) (φ : Subrepresentation ρ)
    [h : IsSmooth ρ] : IsSmooth φ.toRepresentation := by
  simpa [isSmooth_iff, isSmoothVector_iff] using fun v hv => h.smooth v

/-- An arbitrary direct sum of smooth representations is smooth. -/
lemma isSmooth_directSum {I : Type*} {V : I → Type*} [(i : I) → AddCommMonoid (V i)]
    [(i : I) → Module k (V i)] (ρ : (i : I) → Representation k G (V i)) (h : ∀ i, IsSmooth (ρ i)) :
    IsSmooth (Representation.directSum ρ) := by
  simp only [isSmooth_iff, directSum_apply, DirectSum.ext_iff, DirectSum.lmap_apply]
  classical
  simp only [isSmooth_iff] at h
  intro v
  have hset : {g : G | ∀ i : I, ((ρ i) g) (v i) = v i}
      = ⋂ i ∈ DFinsupp.support v, {g : G | ((ρ i) g) (v i) = v i} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · exact fun h_stab i _ => h_stab i
    · intro h_stab i
      by_cases h_supp : i ∈ DFinsupp.support v
      · exact h_stab i h_supp
      · rw [DFinsupp.notMem_support_iff] at h_supp
        rw [h_supp, map_zero]
  rw [hset]
  exact isOpen_biInter_finset fun i _ => h i (v i)

end basic

section Quotient

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
variable {k : Type*} [Ring k]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- Any quotient representation of a smooth representation is smooth. -/
lemma isSmooth_quotient {ρ : Representation k G V} {φ : Subrepresentation ρ} [IsSmooth ρ]
    : IsSmooth (φ.quotient) := by
  refine ⟨fun w => Quotient.inductionOn' w fun v => ?_⟩
  have h_sub : stabilizer ρ v ≤ stabilizer (φ.quotient) ⟦v⟧ := by
    simp +contextual [Subrepresentation.quotient_apply_mk, SetLike.le_def]
  exact Subgroup.isOpen_mono h_sub (IsSmooth.smooth v)

end Quotient

section smoothVectors

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
variable {k : Type*} [Semiring k]
variable {V : Type*} [AddCommMonoid V] [Module k V]
variable {V' : Type*} [AddCommMonoid V'] [Module k V']

omit [IsTopologicalGroup G] in
lemma isSmoothVector_zero (ρ : Representation k G V) : IsSmoothVector ρ 0 := by
  simp [isSmoothVector_iff]

lemma isSmoothVector_add {ρ : Representation k G V} {v1 v2 : V}
    (hv1 : IsSmoothVector ρ v1) (hv2 : IsSmoothVector ρ v2)
    : IsSmoothVector ρ (v1 + v2) :=
  Subgroup.isOpen_mono (le_stabilizer_add ρ v1 v2) (hv1.inter hv2)

lemma isSmoothVector_sum {n : ℕ} {ρ : Representation k G V} {v : Fin n → V}
    (h_smooth : ∀ (i : Fin n), IsSmoothVector ρ (v i))
    : IsSmoothVector ρ (∑ i, v i) :=
  Subgroup.isOpen_mono (le_stabilizer_sum ρ v)
  (by simpa [Subgroup.coe_iInf] using isOpen_iInter_of_finite h_smooth)

lemma isSmoothVector_smul {ρ : Representation k G V} {v : V} (c : k)
    (h_smooth : IsSmoothVector ρ v)
    : IsSmoothVector ρ (c • v) :=
  Subgroup.isOpen_mono (le_stabilizer_smul ρ c v) h_smooth

lemma isSmoothVector_apply {ρ : Representation k G V} {v : V} (g : G)
    (h_smooth : IsSmoothVector ρ v)
    : IsSmoothVector ρ (ρ g v) := by
  let gS := (fun x => g * x) '' (stabilizer ρ v)
  let S_conj := (fun x => x * g⁻¹) '' gS
  have h_open_gS : IsOpen gS := isOpenMap_mul_left g (stabilizer ρ v) h_smooth
  have h_open_S_conj : IsOpen S_conj := isOpenMap_mul_right g⁻¹ gS h_open_gS
  have heq : S_conj = {y | ∃ x ∈ ρ.stabilizer v, g * x * g⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨gx, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨g * x, ⟨x, hx, rfl⟩, rfl⟩
  simpa [heq, isSmoothVector_iff, ← mem_stabilizer, stabilizer_conj] using h_open_S_conj

/-- Intertwining maps send smooth vectors to smooth vectors. -/
lemma IntertwiningMap.isSmoothVector {ρ : Representation k G V} {ρ' : Representation k G V'}
    {v : V} (f : ρ.IntertwiningMap ρ') (h_smooth : IsSmoothVector ρ v)
    : IsSmoothVector ρ' (f v) := Subgroup.isOpen_mono (IntertwiningMap.stabilizer_le f v) h_smooth

/-- The submodule of smooth vectors of a representation. -/
def smoothSubmodule (ρ : Representation k G V) : Submodule k V where
  carrier := {v : V | IsSmoothVector ρ v}
  add_mem' := fun h1 h2 => isSmoothVector_add h1 h2
  zero_mem' := isSmoothVector_zero ρ
  smul_mem' := fun c _ h => isSmoothVector_smul c h

/-- Smooth vectors of a representation form a subrepresentation. -/
def smoothVectors (ρ : Representation k G V) : Subrepresentation ρ where
  toSubmodule := smoothSubmodule ρ
  apply_mem_toSubmodule := fun g _ h_smooth => isSmoothVector_apply g h_smooth

@[simp]
lemma mem_smoothVectors {ρ : Representation k G V} {v : V} :
    v ∈ (smoothVectors ρ).toSubmodule ↔ IsSmoothVector ρ v := by
  rfl

/-- Taking smooth vectors gives a smooth representation. -/
theorem isSmooth_smoothVectors {ρ : Representation k G V} :
    IsSmooth ((smoothVectors ρ).toRepresentation) := by
  simp [isSmooth_iff, isSmoothVector_iff]

def IntertwiningMap.smoothVectors {ρ : Representation k G V} {ρ' : Representation k G V'}
    (f : ρ.IntertwiningMap ρ')
    : ((smoothVectors ρ).toRepresentation).IntertwiningMap (smoothVectors ρ').toRepresentation where
  toFun := fun ⟨v, hv⟩ ↦ ⟨f v, IntertwiningMap.isSmoothVector f hv⟩
  map_add' := by simp [Subtype.ext_iff]
  map_smul' := by simp [Subtype.ext_iff]
  isIntertwining' g := by ext x; apply IntertwiningMap.isIntertwining

end smoothVectors

section TensorHomContragredient

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
variable {k : Type*} [CommSemiring k]
variable {V : Type*} [AddCommMonoid V] [Module k V]
variable {V' : Type*} [AddCommMonoid V'] [Module k V']

/-- The tensor product of two smooth representations is smooth. -/
lemma isSmooth_tprod {ρ : Representation k G V} {ρ' : Representation k G V'}
    [h : IsSmooth ρ] [h' : IsSmooth ρ'] : IsSmooth (tprod ρ ρ') := by
  constructor
  intro m
  rcases TensorProduct.exists_sum_tmul_eq m with ⟨n, v, v', rfl⟩
  apply isSmoothVector_sum
  intro i
  let S := (stabilizer ρ (v i)) ⊓ (stabilizer ρ' (v' i))
  have h_open: IsOpen (S : Set G) := by
    apply TopologicalSpace.isOpen_inter
    · obtain h_s := h.smooth
      specialize h_s (v i)
      rw [isSmoothVector_iff] at h_s
      exact h_s
    · obtain h'_s := h'.smooth
      specialize h'_s (v' i)
      rw [isSmoothVector_iff] at h'_s
      exact h'_s
  have h_sub : S ≤ ((ρ.tprod ρ').stabilizer (v i ⊗ₜ[k] v' i)) := by
    intro s hs
    rw [mem_stabilizer, Representation.tprod_apply, TensorProduct.map_tmul]
    simp only [Subgroup.mem_inf, mem_stabilizer, S] at hs
    simp [hs]
  exact S.isOpen_mono h_sub h_open

/-- The smooth vectors in the internal Hom representation. -/
def smoothHom (ρ : Representation k G V) (ρ' : Representation k G V') :
    Representation k G (smoothVectors (linHom ρ ρ')).toSubmodule :=
  (smoothVectors (linHom ρ ρ')).toRepresentation

lemma isSmooth_smoothHom {ρ : Representation k G V} {ρ' : Representation k G V'}
    : IsSmooth (smoothHom ρ ρ') := by
  apply isSmooth_smoothVectors

/-- The smooth vectors in the dual representation. -/
def contragredient (ρ : Representation k G V) :
    Representation k G (smoothVectors ρ.dual).toSubmodule :=
  (smoothVectors ρ.dual).toRepresentation

lemma isSmooth_contragredient {ρ : Representation k G V}
    : IsSmooth (contragredient ρ) := by
  apply isSmooth_smoothVectors

end TensorHomContragredient

end Representation.Smooth
