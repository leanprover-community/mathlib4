/-
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

public import Mathlib
public import Mathlib.RepresentationTheory.Intertwining

/-public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RingTheory.SimpleModule.Basic-/

/-!
# Irreducible representations

This file defines irreducible monoid representations.

-/

namespace Representation

@[expose] public section

open scoped MonoidAlgebra

universe u

variable {G k V W : Type u} [Group G] [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W] (ρ : Representation k G V) (σ : Representation k G W)

/-- A representation `ρ` is irreducible if it has no proper non-trivial subrepresentations.
-/
@[mk_iff] class IsIrreducible extends
  IsSimpleOrder (Subrepresentation ρ)

theorem irreducible_iff_is_simple_module_as_module :
    IsIrreducible ρ ↔ IsSimpleModule k[G] ρ.asModule := by
  rw [isSimpleModule_iff, isIrreducible_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.subrepresentationSubmoduleOrderIso

theorem is_simple_module_iff_irreducible_of_module (M : Type u) [AddCommGroup M] [Module k[G] M] :
    IsSimpleModule k[G] M ↔ IsIrreducible (ofModule (k := k) (G := G) M) := by
  rw [isSimpleModule_iff, isIrreducible_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.submoduleSubrepresentationOrderIso

theorem bijective_or_eq_zero [IsIrreducible ρ] [IsIrreducible σ] (f : IntertwiningMap ρ σ) :
    Function.Bijective f ∨ f = 0 := by
  letI : IsSimpleModule k[G] ρ.asModule :=
    (irreducible_iff_is_simple_module_as_module ρ).mp (by assumption)
  letI : IsSimpleModule k[G] σ.asModule :=
    (irreducible_iff_is_simple_module_as_module σ).mp (by assumption)
  have h := @LinearMap.bijective_or_eq_zero k[G] _ ρ.asModule _ _ σ.asModule _ _ _ _ (asLinearMap f)
  rcases h with h | h
  · exact Or.inl h
  · right
    apply to_fun_injective
    ext x
    change asLinearMap f x = 0
    rw [h]
    rfl

theorem scalar_intertwining_map_of_irreducible_alg_closed [IsIrreducible ρ] [FiniteDimensional k V]
    [IsAlgClosed k] (f : IntertwiningMap ρ ρ) : ∃ a : k, ∀ v : V, f v = a • v := by
  by_cases h : Nontrivial V
  · obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f.toLinearMap)
    set g := f + (-c) • (IntertwiningMap.id ρ)
    have schur := bijective_or_eq_zero ρ ρ g
    suffices ¬Function.Bijective g by
      have hg := Or.resolve_left schur this
      use c
      intro v
      have h : g v = 0 := by simp [hg]
      simp only [coe_add, coe_smul, neg_smul, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
        IntertwiningMap.id_apply, g] at h
      exact eq_of_add_neg_eq_zero h
    intro ⟨inj, _⟩
    rw [Module.End.HasEigenvalue, Module.End.HasUnifEigenvalue] at hc
    apply Submodule.exists_mem_ne_zero_of_ne_bot at hc
    obtain ⟨b, hb, b_nz⟩ := hc
    rw [Module.End.mem_genEigenspace_one] at hb
    specialize @inj b 0
    apply b_nz
    apply inj
    simp only [coe_add, coe_smul, neg_smul, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
      IntertwiningMap.id_apply, smul_zero, neg_zero, add_zero, g]
    rw [intertwiningMap_toLinearMap, intertwiningMap_toLinearMap, f.toLinearMap.map_zero, hb,
      add_neg_cancel]
  · rw [not_nontrivial_iff_subsingleton] at h
    use 0
    intro v
    exact h.allEq (f v) (0 • v)

theorem one_dimensional_of_irreducible_of_abelian [IsIrreducible ρ] [FiniteDimensional k V]
    [Nontrivial V] [IsAlgClosed k] [IsMulCommutative G] : Module.finrank k V = 1 := by
  obtain ⟨v, v_nz⟩ := exists_ne (0 : V)
  set U : Subrepresentation ρ := {
    toSubmodule := Submodule.span k {v}
    apply_mem_toSubmodule g w hw := by
      have g_cent : g ∈ Submonoid.center G := by
        rw [Submonoid.mem_center_iff]
        intro g'
        exact CommMonoid.mul_comm g' g
      set f := IntertwiningMap.CentralMul ρ g g_cent
      obtain ⟨a, ha⟩ := scalar_intertwining_map_of_irreducible_alg_closed ρ f
      specialize ha w
      dsimp [f] at ha
      change (ρ g) w = a • w at ha
      rw [ha]
      exact Submodule.smul_of_tower_mem (k ∙ v) a hw
  }
  obtain hU | hU := (show ρ.IsIrreducible by infer_instance).eq_bot_or_eq_top U
  · exfalso
    have hv : v ∈ U := by exact Submodule.mem_span_singleton_self v
    rw [hU] at hv
    exact v_nz hv
  · have hU' : U.toSubmodule = ⊤ := by rw [hU]; rfl
    dsimp [U] at hU'
    exact (finrank_eq_one_iff_of_nonzero v v_nz).mpr hU'
end

end Representation
