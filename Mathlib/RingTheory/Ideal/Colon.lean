/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.LinearAlgebra.Quotient
import Mathlib.RingTheory.Ideal.Operations

/-!
# The colon ideal

This file defines `Submodule.colon N P` as the ideal of all elements `r : R` such that `r • P ⊆ N`.
The normal notation for this would be `N : P` which has already been taken by type theory.

-/

namespace Submodule

open Pointwise

variable {R M M' F G : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {N N₁ N₂ P P₁ P₂ : Submodule R M}

/-- `N.colon P` is the ideal of all elements `r : R` such that `r • P ⊆ N`. -/
def colon (N P : Submodule R M) : Ideal R :=
  annihilator (P.map N.mkQ)
#align submodule.colon Submodule.colon

theorem mem_colon {r} : r ∈ N.colon P ↔ ∀ p ∈ P, r • p ∈ N :=
  mem_annihilator.trans
     ⟨fun H p hp => (Quotient.mk_eq_zero N).1 (H (Quotient.mk p) (mem_map_of_mem hp)),
       fun H _ ⟨p, hp, hpm⟩ => hpm ▸ ((Quotient.mk_eq_zero N).2 <| H p hp)⟩
#align submodule.mem_colon Submodule.mem_colon

theorem mem_colon' {r} : r ∈ N.colon P ↔ P ≤ comap (r • (LinearMap.id : M →ₗ[R] M)) N :=
  mem_colon
#align submodule.mem_colon' Submodule.mem_colon'

@[simp]
theorem colon_top {I : Ideal R} : I.colon ⊤ = I := by
  simp_rw [SetLike.ext_iff, mem_colon, smul_eq_mul]
  exact fun x ↦ ⟨fun h ↦ mul_one x ▸ h 1 trivial, fun h _ _ ↦ I.mul_mem_right _ h⟩

@[simp]
theorem colon_bot : colon ⊥ N = N.annihilator := by
  simp_rw [SetLike.ext_iff, mem_colon, mem_annihilator, mem_bot, forall_const]

theorem colon_mono (hn : N₁ ≤ N₂) (hp : P₁ ≤ P₂) : N₁.colon P₂ ≤ N₂.colon P₁ := fun _ hrnp =>
  mem_colon.2 fun p₁ hp₁ => hn <| mem_colon.1 hrnp p₁ <| hp hp₁
#align submodule.colon_mono Submodule.colon_mono

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
#align submodule.infi_colon_supr Submodule.iInf_colon_iSup

@[simp]
theorem mem_colon_singleton {N : Submodule R M} {x : M} {r : R} :
    r ∈ N.colon (Submodule.span R {x}) ↔ r • x ∈ N :=
  calc
    r ∈ N.colon (Submodule.span R {x}) ↔ ∀ a : R, r • a • x ∈ N := by
      simp [Submodule.mem_colon, Submodule.mem_span_singleton]
    _ ↔ r • x ∈ N := by simp_rw [fun (a : R) ↦ smul_comm r a x]; exact SetLike.forall_smul_mem_iff
#align submodule.mem_colon_singleton Submodule.mem_colon_singleton

@[simp]
theorem _root_.Ideal.mem_colon_singleton {I : Ideal R} {x r : R} :
    r ∈ I.colon (Ideal.span {x}) ↔ r * x ∈ I := by
  simp only [← Ideal.submodule_span_eq, Submodule.mem_colon_singleton, smul_eq_mul]
#align ideal.mem_colon_singleton Ideal.mem_colon_singleton

theorem annihilator_quotient {N : Submodule R M} :
    Module.annihilator R (M ⧸ N) = N.colon ⊤ := by
  simp_rw [SetLike.ext_iff, Module.mem_annihilator, colon, mem_annihilator, map_top,
    LinearMap.range_eq_top.mpr (mkQ_surjective N), mem_top, forall_true_left, forall_const]

theorem _root_.Ideal.annihilator_quotient {I : Ideal R} : Module.annihilator R (R ⧸ I) = I := by
  rw [Submodule.annihilator_quotient, colon_top]

end Submodule
