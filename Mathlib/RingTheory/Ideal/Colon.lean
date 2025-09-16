/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Ring.Action.Pointwise.Set
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Ideal.Maps

/-!
# The colon ideal

This file defines `Submodule.colon N P` as the ideal of all elements `r : R` such that `r • P ⊆ N`.
The normal notation for this would be `N : P` which has already been taken by type theory.

-/

namespace Submodule

open Pointwise

variable {R M : Type*}

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable {N N₁ N₂ P P₁ P₂ : Submodule R M}

/-- `N.colon P` is the ideal of all elements `r : R` such that `r • P ⊆ N`. -/
def colon (N P : Submodule R M) : Ideal R where
  carrier := {r : R | (r • P : Set M) ⊆ N}
  add_mem' ha hb :=
    (Set.add_smul_subset _ _ _).trans ((Set.add_subset_add ha hb).trans_eq (by simp))
  zero_mem' := by simp [Set.zero_smul_set P.nonempty]
  smul_mem' r := by
    simp only [Set.mem_setOf_eq, smul_eq_mul, mul_smul, Set.smul_set_subset_iff]
    intro x hx y hy
    exact N.smul_mem _ (hx hy)

theorem mem_colon {r} : r ∈ N.colon P ↔ ∀ p ∈ P, r • p ∈ N := Set.smul_set_subset_iff

instance (priority := low) : (N.colon P).IsTwoSided where
  mul_mem_of_left {r} s hr p hp := by
    obtain ⟨p, hp, rfl⟩ := hp
    exact hr ⟨_, P.smul_mem _ hp, (mul_smul ..).symm⟩

@[simp]
theorem colon_top {I : Ideal R} [I.IsTwoSided] : I.colon ⊤ = I := by
  simp_rw [SetLike.ext_iff, mem_colon, smul_eq_mul]
  exact fun x ↦ ⟨fun h ↦ mul_one x ▸ h 1 trivial, fun h _ _ ↦ I.mul_mem_right _ h⟩

@[simp]
theorem colon_bot : colon ⊥ N = N.annihilator := by
  simp_rw [SetLike.ext_iff, mem_colon, mem_annihilator, mem_bot, forall_const]

theorem colon_mono (hn : N₁ ≤ N₂) (hp : P₁ ≤ P₂) : N₁.colon P₂ ≤ N₂.colon P₁ := fun _ hrnp =>
  mem_colon.2 fun p₁ hp₁ => hn <| mem_colon.1 hrnp p₁ <| hp hp₁

theorem _root_.Ideal.le_colon {I J : Ideal R} [I.IsTwoSided] : I ≤ I.colon J := by
  calc I = I.colon ⊤ := colon_top.symm
       _ ≤ I.colon J := colon_mono (le_refl I) le_top

end Semiring

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {N P : Submodule R M}

theorem mem_colon' {r} : r ∈ N.colon P ↔ P ≤ comap (r • (LinearMap.id : M →ₗ[R] M)) N :=
  mem_colon

theorem iInf_colon_iSup (ι₁ : Sort*) (f : ι₁ → Submodule R M) (ι₂ : Sort*)
    (g : ι₂ → Submodule R M) : (⨅ i, f i).colon (⨆ j, g j) = ⨅ (i) (j), (f i).colon (g j) :=
  le_antisymm (le_iInf fun _ => le_iInf fun _ => colon_mono (iInf_le _ _) (le_iSup _ _)) fun _ H =>
    mem_colon'.2 <|
      iSup_le fun j =>
        map_le_iff_le_comap.1 <|
          le_iInf fun i =>
            map_le_iff_le_comap.2 <|
              mem_colon'.1 <|
                have := (mem_iInf _).1 H i
                have := (mem_iInf _).1 this j
                this

@[simp]
theorem mem_colon_singleton {x : M} {r : R} : r ∈ N.colon (Submodule.span R {x}) ↔ r • x ∈ N :=
  calc
    r ∈ N.colon (Submodule.span R {x}) ↔ ∀ a : R, r • a • x ∈ N := by
      simp [Submodule.mem_colon, Submodule.mem_span_singleton]
    _ ↔ r • x ∈ N := by simp_rw [fun (a : R) ↦ smul_comm r a x]; exact SetLike.forall_smul_mem_iff

@[simp]
theorem _root_.Ideal.mem_colon_singleton {I : Ideal R} {x r : R} :
    r ∈ I.colon (Ideal.span {x}) ↔ r * x ∈ I := by
  simp only [← Ideal.submodule_span_eq, Submodule.mem_colon_singleton, smul_eq_mul]

end CommSemiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M]
variable {N P : Submodule R M}

@[simp]
lemma annihilator_map_mkQ_eq_colon : annihilator (P.map N.mkQ) = N.colon P := by
  ext
  rw [mem_annihilator, mem_colon]
  exact ⟨fun H p hp ↦ (Quotient.mk_eq_zero N).1 (H (Quotient.mk p) (mem_map_of_mem hp)),
    fun H _ ⟨p, hp, hpm⟩ ↦ hpm ▸ ((Quotient.mk_eq_zero N).2 <| H p hp)⟩

theorem annihilator_quotient : Module.annihilator R (M ⧸ N) = N.colon ⊤ := by
  simp_rw [SetLike.ext_iff, Module.mem_annihilator, ← annihilator_map_mkQ_eq_colon, mem_annihilator,
    map_top, LinearMap.range_eq_top.mpr (mkQ_surjective N), mem_top, forall_true_left,
    forall_const]

theorem _root_.Ideal.annihilator_quotient {I : Ideal R} [I.IsTwoSided] :
    Module.annihilator R (R ⧸ I) = I := by
  rw [Submodule.annihilator_quotient, colon_top]

end Ring

end Submodule
