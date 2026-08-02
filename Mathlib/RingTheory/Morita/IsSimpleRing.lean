/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.Matrix.Module
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Simple modules over simple rings

## Main results

* `linearEquiv_of_isSimpleModule_over_simple_ring`: any two simple modules over an Artinian
  simple ring are isomorphic.
* `directSum_simple_module_over_simple_ring`: any module over an Artinian simple ring is
  isomorphic to a direct sum of copies of a simple module.
* `linearEquiv_iff_length_eq_over_simple_ring`: two finite modules over a simple algebra `A` over a
  commutative Artinian ring `k` are isomorphic as `A`-modules if and only if they have the same
  length over `k`.
* `linearEquiv_iff_finrank_eq_over_simple_ring`: two finite modules over a finite simple algebra
  `A` over a field `k` are isomorphic as `A`-modules if and only if they have the same dimension
  over `k`.

-/

@[expose] public section

universe w u v

section simple

namespace IsSimpleRing

variable (k : Type u) (A : Type v) [CommRing k] [Ring A] [Algebra k A]
    [IsSimpleRing A] [Module.Finite k A]

@[stacks 074E "(1)"]
lemma nonempty_linearEquiv_of_isSimpleModule_of_isSimpleRing [IsArtinianRing A] (M N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N] [IsSimpleModule A M]
    [IsSimpleModule A N] : Nonempty (M ≃ₗ[A] N) := by
  let eM := LinearEquiv.ofInjective (LinearMap.inl A M N) LinearMap.inl_injective
  let eN := LinearEquiv.ofInjective (LinearMap.inr A M N) LinearMap.inr_injective
  have : IsSimpleModule A (LinearMap.range (LinearMap.inl A M N)) := .congr eM.symm
  have : IsSimpleModule A (LinearMap.range (LinearMap.inr A M N)) := .congr eN.symm
  obtain ⟨e⟩ := IsSimpleRing.isIsotypic A (M × N) (LinearMap.range (LinearMap.inl A M N))
    (LinearMap.range (LinearMap.inr A M N))
  exact ⟨eM.trans (e.symm.trans eN.symm)⟩

lemma isIsotypicOfType_of_isSimpleRing [IsArtinianRing A] (M : Type w) [AddCommGroup M]
    [Module A M] (S : Type w) [AddCommGroup S] [Module A S] [IsSimpleModule A S] :
    IsIsotypicOfType A M S := fun m _ ↦ nonempty_linearEquiv_of_isSimpleModule_of_isSimpleRing A m S

@[stacks 074E "(2)"]
lemma directSum_simple_module_of_isSimpleRing [IsArtinianRing A] (M : Type v) [AddCommGroup M]
    [Module A M] : ∃ (S : Type v) (_ : AddCommGroup S) (_ : Module A S) (_ : IsSimpleModule A S)
    (ι : Type v), Nonempty (M ≃ₗ[A] (ι →₀ S)) := by
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule A A)
  rw [← isSimpleModule_iff_isAtom] at hS
  obtain ⟨ι, he⟩ := (isIsotypicOfType_of_isSimpleRing A M S).linearEquiv_finsupp
  exact ⟨S, inferInstance, inferInstance, hS, ι, he⟩

lemma directSum_simple_module_of_isSimpleRing' (A : Type u) [Ring A] [IsArtinianRing A]
    [IsSimpleRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (S : Type v) [AddCommGroup S] [Module A S] [IsSimpleModule A S] :
    ∃ (ι : Type v), Nonempty (M ≃ₗ[A] (ι →₀ S)) :=
  (isIsotypicOfType_of_isSimpleRing A M S).linearEquiv_finsupp

@[stacks 074E "(2)"]
lemma directSum_simple_module_of_simple_algebra [IsArtinianRing k] (M : Type v) [AddCommGroup M]
    [Module A M] : ∃ (S : Type v) (_ : AddCommGroup S) (_ : Module k S)
    (_ : Module A S) (_ : IsScalarTower k A S) (_ : IsSimpleModule A S) (ι : Type v),
    Nonempty (M ≃ₗ[A] (ι →₀ S)) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨S, _, _, _, ι, ⟨iso⟩⟩ := directSum_simple_module_of_isSimpleRing A M
  let : Module k S := Module.compHom S (algebraMap k A)
  have : IsScalarTower k A S := .of_algebraMap_smul fun _ _ ↦ rfl
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ι, ⟨iso⟩⟩

/-- Two finite modules over an artinian simple ring `A` have an `A`-linear
equivalence if and only if their `A`-length is the same. -/
lemma nonempty_linearEquiv_iff_length_eq_of_isSimpleRing [IsArtinianRing A]
    (M N : Type v) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N] :
    Nonempty (M ≃ₗ[A] N) ↔ Module.length A M = Module.length A N := by
  refine ⟨fun ⟨e⟩ ↦ e.length_eq, fun h ↦ ?_⟩
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule A A)
  rw [← isSimpleModule_iff_isAtom] at hS
  obtain ⟨m, ⟨eM⟩⟩ := (isIsotypicOfType_of_isSimpleRing A M S).linearEquiv_fun
  obtain ⟨n, ⟨eN⟩⟩ := (isIsotypicOfType_of_isSimpleRing A N S).linearEquiv_fun
  obtain rfl : m = n := by simpa [eM.length_eq, eN.length_eq] using h
  exact ⟨eM.trans eN.symm⟩

/-- Two finite modules over a simple `k`-algebra `A` have an `A`-linear equivalence if and only if
their `k`-length is the same. -/
@[stacks 074E "(3)"]
lemma nonempty_linearEquiv_iff_length_eq_of_simple_algebra [IsArtinianRing k]
    (M N : Type v) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k A N]
    [Module.Finite A M] [Module.Finite A N] :
    Nonempty (M ≃ₗ[A] N) ↔ Module.length k M = Module.length k N := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  refine ⟨fun ⟨e⟩ ↦ (e.restrictScalars k).length_eq, fun h ↦ ?_⟩
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule A A)
  rw [← isSimpleModule_iff_isAtom] at hS
  obtain ⟨m, ⟨eM⟩⟩ := (isIsotypicOfType_of_isSimpleRing A M S).linearEquiv_fun
  obtain ⟨n, ⟨eN⟩⟩ := (isIsotypicOfType_of_isSimpleRing A N S).linearEquiv_fun
  have : Nontrivial S := IsSimpleModule.nontrivial A S
  obtain rfl : m = n := by
    apply_fun ENat.toNat at h
    simpa [(eM.restrictScalars k).length_eq, (eN.restrictScalars k).length_eq,
      (Module.length_pos (R := k) (M := S)).ne', Module.length_ne_top] using h
  exact ⟨eM.trans eN.symm⟩

/-- Two finite modules over a finite simple algebra `A` over a field `k` have an `A`-linear
equivalence if and only if their `k`-dimension is the same. -/
@[stacks 074E "(3)"]
lemma linearEquiv_iff_finrank_eq_over_simple_algebra (k : Type u) (A : Type v) [Field k] [Ring A]
    [Algebra k A] [IsSimpleRing A] [Module.Finite k A]
    (M N : Type v) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k A N]
    [Module.Finite A M] [Module.Finite A N] :
    Nonempty (M ≃ₗ[A] N) ↔ Module.finrank k M = Module.finrank k N := by
  have : Module.Finite k M := .trans A M
  have : Module.Finite k N := .trans A N
  rw [nonempty_linearEquiv_iff_length_eq_of_simple_algebra k A M N, Module.length_eq_finrank,
    Module.length_eq_finrank, Nat.cast_inj]

open Matrix.Module

/-- Along a Wedderburn–Artin isomorphism `A ≃ₐ[k] Mₙ(D)`, the induced `A`-action on `Fin n → D`
is compatible with the `k`-action. -/
scoped instance isScalarTower_compHom_pi {n : ℕ} (D : Type w) [DivisionRing D] [Algebra k D]
    (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    letI := Module.compHom (Fin n → D) wdb.toRingEquiv.toRingHom
    IsScalarTower k A (Fin n → D) :=
  let := Module.compHom (Fin n → D) wdb.toRingEquiv.toRingHom
  ⟨fun a b x ↦ show wdb (a • b) • x = _ by
    rw [map_smul, Algebra.smul_def, mul_smul, algebraMap_smul]; rfl⟩

scoped instance smulCommClass_compHom_pi {n : ℕ} (D : Type w) [DivisionRing D] [Algebra k D]
    (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    letI := Module.compHom (Fin n → D) wdb.toRingEquiv.toRingHom
    SMulCommClass A k (Fin n → D) :=
  let := Module.compHom (Fin n → D) wdb.toRingEquiv.toRingHom
  ⟨fun a b x ↦ show wdb a • b • x = b • wdb a • x by ext; simp [Finset.smul_sum]⟩

end IsSimpleRing

end simple
