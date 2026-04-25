/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.RingTheory.Ideal.Maps

/-!

# Some basic lemmas for manipulating Ext over ModuleCat

-/

@[expose] public section

universe v u

open LinearMap CategoryTheory Limits

variable {R : Type u} [CommRing R]

variable {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

lemma LinearMap.lsmul_eq_smul_id (M : ModuleCat.{v} R) (r : R) :
    ModuleCat.ofHom (LinearMap.lsmul R M r) = r • 𝟙 M := rfl

namespace CategoryTheory.Abelian

variable [Small.{v} R] {M N : ModuleCat.{v} R}

set_option backward.isDefEq.respectTransparency false in
lemma Ext.smul_id_postcomp_eq_zero_of_mem_annihilator {r : R} (mem_ann : r ∈ Module.annihilator R N)
    (n : ℕ) : AddCommGrpCat.ofHom ((Ext.mk₀ (r • (𝟙 M))).postcomp N (add_zero n)) = 0 := by
  ext h
  have : r • (𝟙 N) = 0 := by
    simp [← lsmul_eq_smul_id, mem_annihilator_iff_lsmul_eq_zero.mp mem_ann, ModuleCat.ofHom_zero]
  have smul_eq : r • h = (Ext.mk₀ (r • (𝟙 N))).comp h (zero_add n) := by simp [Ext.mk₀_smul]
  simp [Ext.mk₀_smul, this, smul_eq]

set_option backward.isDefEq.respectTransparency false in
lemma Ext.smul_id_postcomp_mono_iff (r : R) (i : ℕ) :
    Mono (AddCommGrpCat.ofHom ((Ext.mk₀ (r • 𝟙 M)).postcomp N (add_zero i))) ↔
    IsSMulRegular (Ext N M i) r := by
  simp only [IsSMulRegular, AddCommGrpCat.mono_iff_injective]
  congr!
  ext
  simp [Ext.mk₀_smul]

end CategoryTheory.Abelian
