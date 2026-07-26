/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Smooth.Basic
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Induction

This file introduces admissible representations over a field and prove basic properties on them.
We also prove the **Schur's Lemma** for irreducible admissible smooth representations over an
algeraically closed field.

## Main definitions


## Implementation notes

-/

@[expose] public section

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
variable {W : Type*} [AddCommGroup W] [Module k W] (σ : Representation k G W)

namespace Representation.Smooth

section admissible

/-- A representation `(ρ, V)` of `G` is called admissible if for any open subgroup `K` of `G`, its
`K`-invariants is finite dimensional. -/
class IsAdmissible : Prop where
  finiteDimensional_intertwiningMap : ∀ (H : OpenSubgroup G),
      FiniteDimensional k ((ind H.subtype (trivial k H k)).IntertwiningMap ρ)

end admissible

section Schur

variable [h_irred : IsIrreducible ρ] [h_smooth : IsSmooth ρ]

open MonoidAlgebra

lemma IsAdmissible.finiteDimensional_intertwiningMap_self [h : IsAdmissible ρ] :
    FiniteDimensional k (IntertwiningMap ρ ρ) := by
  have : Nontrivial V := IsSimpleModule.nontrivial k[G] ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let H := ρ.stabilizer v
  let f' : k →ₗ[k] V := LinearMap.toSpanSingleton k V v
  have hstab (h : H) : ρ h⁻¹ v = v := by simp [(mem_stabilizer (ρ := ρ) (g := h⁻¹) (v := v)).mp]
  let fToLinearMap : IndV H.subtype (trivial k H k) →ₗ[k] V :=
    Representation.Coinvariants.lift _
      (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h => ρ h⁻¹ ∘ₗ f') ∘ₗ
        (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
      fun h ↦ by
        ext g
        simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
        simp [ofMulAction_single, mul_inv_rev, f', hstab]
  let f : IntertwiningMap (ind H.subtype (trivial k H k)) ρ
    := ⟨fToLinearMap, fun g ↦ by unfold fToLinearMap; ext; simp⟩
  have : FiniteDimensional k (IntertwiningMap (ind H.subtype (trivial k H k)) ρ) :=
    h.finiteDimensional_intertwiningMap ⟨H, h_smooth.smooth v⟩
  have hf : f ≠ 0 := by
    have hfeq : f (IndV.mk H.subtype (trivial k H k) 1 1) = v := by
      change fToLinearMap (IndV.mk H.subtype (trivial k H k) 1 1) = v
      simp only [fToLinearMap, Coinvariants.lift_mk, LinearMap.coe_comp, Function.comp_apply,
        TensorProduct.mk_apply, TensorProduct.lift.tmul]
      simp [f', coeffLinearEquiv_apply, coeff_single, Finsupp.lift_apply, Finsupp.sum_single_index,
         LinearMap.toSpanSingleton_apply]
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
