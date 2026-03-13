/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# P-Primary Components of modules

Let `A` be a commutative ring and `P`, a nonzero prime ideal of `A`.
Given an `A`-Module `M` it's `P`-primary component is defined as
  $$M(P) := \bigcup_{i : \mathbb{N}} \text{torsionBySet A  M }  P ^ i.$$

The main result of this file (TODO) is that
  $$M = \bigoplus_{P} M(P).$$

## Main definitions

* `Module.primaryComponent` : The `P`-primary component of an `A`-module `M`.

-/

@[expose] public section

variable {A M M₁ M₂ : Type*} [CommRing A] (P : IsDedekindDomain.HeightOneSpectrum A)

namespace Module

section CommRing

section AddCommMonoid

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module A M] [Module A M₁]
    [Module A M₂]

open Set Function Submodule Module

variable (M)
/--
The `P`-primaryComponent component of a module `M`. -/
def primaryComponent := (⨆ i : ℕ, torsionBySet A M ↑(P.asIdeal ^ i))

@[simp]
theorem primaryComponent_mem (x : M) :
    x ∈ primaryComponent M P ↔ ∃ n, x ∈ torsionBySet A M ↑(P.asIdeal ^ n) := by
  simp only [primaryComponent, mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall]
  constructor
  · intro a
    rw [Submodule.mem_iSup_of_directed] at a
    · simpa using a
    · intro x y
      use max x y
      aesop (add safe torsionBySet_le_torsionBySet_pow)
  · aesop (add norm Submodule.mem_iSup)

theorem primaryComponent_map_mem (φ : M₁ →ₗ[A] M₂) (c : primaryComponent M₁ P) :
    φ c ∈ primaryComponent M₂ P := by
  obtain ⟨c, hc⟩ := c
  simp only [primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall,
    ← map_smul] at ⊢ hc
  obtain ⟨n, hn⟩ := hc
  use n
  grind

/-- Given an A-linear map between M₁ and M₂, `primaryComponent.map` is the
restriction to the P-primaryComponent components of M₁ and M₂. -/
def primaryComponent.map (φ : M₁ →ₗ[A] M₂) :
    primaryComponent M₁ P →ₗ[A] primaryComponent M₂ P :=
  (φ.domRestrict (primaryComponent M₁ P)).codRestrict (primaryComponent M₂ P) (fun c ↦
    by simpa only [LinearMap.domRestrict_apply] using primaryComponent_map_mem P φ c)

theorem primaryComponent.map_ker_eq (φ : M₁ →ₗ[A] M₂) :
    (primaryComponent.map P φ).ker.map (primaryComponent M₁ P).subtype =
      (primaryComponent φ.ker P).map φ.ker.subtype := by
  aesop (add norm [map, Subtype.ext_iff])

theorem primaryComponent_of_torsion_eq_inf (I : Ideal A) :
    (primaryComponent (torsionBySet A M ↑I) P).map (Submodule.subtype _) =
    (primaryComponent M P) ⊓ (torsionBySet A M ↑I) := by
  ext x
  simp_all only [mem_map, primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe,
    Subtype.forall, subtype_apply, Subtype.exists, SetLike.mk_smul_mk, mk_eq_zero, exists_and_left,
    exists_prop, exists_eq_right_right, mem_inf]

theorem primaryComponent_torsion_of_coprime (I : Ideal A)
    (hD : P.asIdeal ⊔ I = ⊤) : primaryComponent (torsionBySet A M ↑I) P = ⊥ := by
  have (n : ℕ) : Disjoint (torsionBySet A M ↑(P.asIdeal ^ n)) (torsionBySet A M ↑I) :=
    Submodule.disjoint_torsionBySet_ideal (M := M) (Ideal.pow_sup_eq_top hD)
  apply Submodule.map_injective_of_injective (Submodule.subtype_injective (torsionBySet A M ↑I))
  ext x
  simp only [primaryComponent_of_torsion_eq_inf, mem_inf, primaryComponent_mem,
    mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall, Submodule.map_bot, mem_bot]
  constructor
  · rintro ⟨⟨n, hn⟩, h₂⟩
    specialize this n
    simp_all only [disjoint_def, mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall,
      smul_zero, implies_true]
  · simp_all

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [Module A M]

open Submodule in
theorem primaryComponent_sup (N₁ N₂ : Submodule A M) (hD : Disjoint N₁ N₂) :
    (primaryComponent ↥(N₁ ⊔ N₂) P).map (N₁ ⊔ N₂).subtype =
    ((primaryComponent N₁ P).map N₁.subtype) ⊔ (primaryComponent N₂ P).map N₂.subtype := by
  ext x
  simp_all only [mem_map, primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe,
    Subtype.forall, subtype_apply, Subtype.exists, SetLike.mk_smul_mk, mk_eq_zero, exists_and_left,
    exists_prop, exists_eq_right_right, Submodule.mem_sup]
  constructor
  · rintro ⟨⟨w, h⟩, ⟨y, hy, z, hz, rfl⟩⟩
    refine ⟨y, ⟨⟨w, fun a ha ↦ ?_⟩, by simp [hy]⟩, z, ⟨⟨w, fun a ha ↦ ?_⟩, by simp [hz]⟩, rfl⟩
    · exact ((Submodule.disjoint_iff_add_eq_zero.mp hD) (Submodule.smul_mem N₁ a hy)
        (Submodule.smul_mem N₂ a hz) (h a ha ▸ (smul_add a y z).symm)).1
    · exact ((Submodule.disjoint_iff_add_eq_zero.mp hD) (Submodule.smul_mem N₁ a hy)
        (Submodule.smul_mem N₂ a hz) (h a ha ▸ (smul_add a y z).symm)).2
  · rintro ⟨y, ⟨⟨n₁, hy⟩, hymem⟩, z, ⟨⟨n₂, hz⟩, hzmem⟩, rfl⟩
    constructor
    · use (max n₁ n₂)
      intro a ha
      specialize hy a (Ideal.pow_le_pow_right (by simp : n₁ ≤ max n₁ n₂) ha)
      specialize hz a (Ideal.pow_le_pow_right (by simp : n₂ ≤ max n₁ n₂) ha)
      aesop
    · use y, hymem, z, hzmem

end AddCommGroup

end CommRing

end Module
