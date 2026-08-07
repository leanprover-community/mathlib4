/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.HeckeModule
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Smooth.Basic


/-!
# Induction

This file introduces admissible representations over a field and prove basic properties on them.
We also prove **Schur's Lemma** for irreducible admissible smooth representations over an
algeraically closed field.

## Main definitions


## Implementation notes

-/

@[expose] public section

variable {G : Type*} [Group G]
variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
variable {W : Type*} [AddCommGroup W] [Module k W] (σ : Representation k G W)

namespace Representation

lemma finiteDimensional_intertwiningMap.le_subgroup {H1 H2 : Subgroup G} (h : H1 ≤ H2)
    [FiniteDimensional k ((ind H1.subtype (trivial k H1 k)).IntertwiningMap ρ)] :
    FiniteDimensional k ((ind H2.subtype (trivial k H2 k)).IntertwiningMap ρ) := by
  let f := bimoduleHecke₁.canonicalIntertwiningMap k H1 H2 h
  have h_sur : Function.Surjective f := by
    apply IntertwiningMap.surjective_cosetVector₁_one
    use cosetVector₁ k H1 1
    simp [f]
  have : Function.Injective ((IntertwiningMap.llcomp
      (ind H1.subtype (trivial k H1 k)) (ind H2.subtype (trivial k H2 k)) ρ).flip f) := by
    intro _ _ h_eq
    apply IntertwiningMap.ext
    apply Function.Surjective.injective_linearMapComp_right h_sur
    exact LinearMap.ext fun v => congrArg (fun f ↦ f v) h_eq
  exact FiniteDimensional.of_injective _ this

namespace Smooth

variable [TopologicalSpace G]

section admissible

/-- A representation `(ρ, V)` of `G` is called admissible if for any open subgroup `K` of `G`, its
`K`-invariants is finite dimensional. -/
@[mk_iff] class IsAdmissible : Prop where
  finiteDimensional_intertwiningMap : ∀ (H : OpenSubgroup G),
      FiniteDimensional k (moduleHecke₁ H ρ)

variable {ρ σ}

lemma isAdmissible_injective [h : IsAdmissible ρ] {f : IntertwiningMap σ ρ}
    (h_inj : Function.Injective f) : IsAdmissible σ := by
  rw [isAdmissible_iff]
  intro H
  have : FiniteDimensional k (moduleHecke₁ H ρ) :=
    h.finiteDimensional_intertwiningMap H
  have : Function.Injective (IntertwiningMap.llcomp (ind H.subtype (trivial k H k)) σ ρ f) := by
    intro _ _ h_eq
    apply IntertwiningMap.ext
    apply Function.Injective.injective_linearMapComp_left h_inj
    exact LinearMap.ext fun v => congrArg (fun f ↦ f v) h_eq
  exact FiniteDimensional.of_injective _ this

lemma isAdmissible_subrepresentation [h : IsAdmissible ρ] (φ : Subrepresentation ρ) :
    IsAdmissible φ.toRepresentation := by
  have : Function.Injective (⟨φ.1.subtype, fun _ ↦ rfl⟩ : IntertwiningMap φ.toRepresentation ρ) :=
    Submodule.subtype_injective φ.1
  exact isAdmissible_injective this

end admissible

section Schur

variable [h_irred : IsIrreducible ρ] [h_smooth : IsSmooth ρ]

open MonoidAlgebra

lemma IsAdmissible.finiteDimensional_intertwiningMap_self [h : IsAdmissible ρ] :
    FiniteDimensional k (IntertwiningMap ρ ρ) := by
  have : Nontrivial V := IsSimpleModule.nontrivial k[G] ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let H := ρ.stabilizer v
  have : FiniteDimensional k (moduleHecke₁ H ρ) :=
    h.finiteDimensional_intertwiningMap ⟨H, h_smooth.smooth v⟩
  let f := moduleHecke₁.invariantMk H v (ρ := ρ) (fun h ↦ by simp [mem_stabilizer.mp h.2])
  have hf : f ≠ 0 := by
    have hfeq : f (cosetVector₁ k H 1) = v := by
      simp [f]
    by_contra
    have : v = 0 := by
      rw [← hfeq, this, IntertwiningMap.coe_zero, Pi.zero_apply]
    contradiction
  have h_inj : Function.Injective ((IntertwiningMap.llcomp _ ρ ρ).flip f) := by
    intro _ _ h
    ext x
    obtain ⟨w, hw⟩ := (IsIrreducible.surjective_or_eq_zero f).resolve_right hf x
    rw [← hw, IntertwiningMap.coe_toLinearMap, IntertwiningMap.coe_toLinearMap]
    exact congrArg (fun f ↦ f w) h
  exact FiniteDimensional.of_injective ((IntertwiningMap.llcomp _ ρ ρ).flip f) h_inj

theorem IsAdmissible.finrank_intertwiningMap_self_eq_one [IsAlgClosed k] [h : IsAdmissible ρ] :
    Module.finrank k (IntertwiningMap ρ ρ) = 1 := by
  have : FiniteDimensional k (IntertwiningMap ρ ρ) :=
    IsAdmissible.finiteDimensional_intertwiningMap_self ρ
  exact IsIrreducible.finrank_intertwiningMap_self ρ

theorem IsAdmissible.algebraMap_intertwiningMap_self_bijective [IsAlgClosed k]
    [h : IsAdmissible ρ] : Function.Bijective (algebraMap k (IntertwiningMap ρ ρ)) := by
  have : FiniteDimensional k (IntertwiningMap ρ ρ) :=
    IsAdmissible.finiteDimensional_intertwiningMap_self ρ
  exact IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed

end Schur

end Representation.Smooth
