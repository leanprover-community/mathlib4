/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Baer
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The Global Dimension of a Ring

In this file, we define the projective dimension of an module and global dimension of ring
and their basic properties.

# Main definition and results

* `projectiveDimension` : Given `X : C` where `C` is abelian,
  return its projective dimension as `WithBot ℕ∞`

* `globalDimension` : The global (homological) dimension of a (commutative) ring defined as
  the supremum of projective dimension over all modules.

-/

@[expose] public section

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory

section GlobalDimension

variable (R : Type u) [CommRing R]

open Abelian

local instance small_of_quotient [Small.{v} R] (I : Ideal R) : Small.{v} (R ⧸ I) :=
  small_of_surjective Ideal.Quotient.mk_surjective

/-- The global (homological) dimension of a (commutative) ring defined as
the supremum of projective dimension over all modules. -/
noncomputable def globalDimension : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{v} R), projectiveDimension.{v} M

lemma globalDimension_eq_bot_iff [Small.{v} R] : globalDimension.{v} R = ⊥ ↔ Subsingleton R := by
  simp only [globalDimension, iSup_eq_bot, projectiveDimension_eq_bot_iff,
    ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun h ↦ ?_, fun h M ↦ Module.subsingleton R M⟩
  let _ := h (ModuleCat.of R (Shrink.{v} R))
  exact (equivShrink.{v} R).subsingleton

lemma globalDimension_le_iff (n : ℕ) : globalDimension.{v} R ≤ n ↔
    ∀ M : ModuleCat.{v} R, HasProjectiveDimensionLE M n := by
  simp [globalDimension, projectiveDimension_le_iff]

lemma globalDimension_le_tfae [Small.{v} R] (n : ℕ) :
    letI := CategoryTheory.HasExt.standard (ModuleCat.{v} R)
    [globalDimension.{v} R ≤ n,
    ∀ M : ModuleCat.{v} R, Module.Finite R M → HasProjectiveDimensionLE M n,
    ∀ m ≥ n + 1, ∀ (N M : ModuleCat.{v} R), Subsingleton (Ext N M m)].TFAE := by
  tfae_have 1 → 2 := by
    simpa only [globalDimension, iSup_le_iff, projectiveDimension_le_iff]
      using fun h M _ ↦ h M
  tfae_have 2 → 3 := by
    intro h m ge N M
    let _ := CategoryTheory.HasExt.standard (ModuleCat.{v} R)
    have (I : Ideal R) : Subsingleton (Ext (ModuleCat.of R (Shrink.{v, u} (R ⧸ I))) M m) :=
      (h (ModuleCat.of R (Shrink.{v, u} (R ⧸ I)))
        (Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm)).1 m ge (Y := M)
    exact ext_subsingleton_of_quotients.{u, v, max u (v + 1)} M m this N
  tfae_have 3 → 1 := by
    intro h
    simp only [globalDimension, iSup_le_iff, projectiveDimension_le_iff]
    intro M
    exact ⟨fun m hm {N} ↦ h m hm M N⟩
  tfae_finish

lemma globalDimension_eq_sup_projectiveDimension_finite [Small.{v, u} R] : globalDimension.{v} R =
    ⨆ (M : ModuleCat.{v} R), ⨆ (_ : Module.Finite R M), projectiveDimension.{v} M := by
  have aux (n : ℕ): globalDimension.{v} R ≤ n ↔
    ⨆ (M : ModuleCat.{v} R), ⨆ (_ : Module.Finite R M), projectiveDimension.{v} M ≤ n := by
    simpa only [iSup_le_iff, projectiveDimension_le_iff] using (globalDimension_le_tfae R n).out 0 1
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  by_cases eqbot : N = ⊥
  · simp only [eqbot, le_bot_iff, globalDimension_eq_bot_iff, iSup_eq_bot,
      projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun h M _ ↦ Module.subsingleton R M, fun h ↦ ?_⟩
    let _ := h (ModuleCat.of R (Shrink.{v} R)) (Module.Finite.equiv (Shrink.linearEquiv R R).symm)
    exact (equivShrink.{v} R).subsingleton
  · by_cases eqtop : N.unbot eqbot = ⊤
    · have : N = ⊤ := (WithBot.coe_unbot _ eqbot).symm.trans (WithBot.coe_inj.mpr eqtop)
      simp [this]
    · let n := (N.unbot eqbot).toNat
      have : N = n := (WithBot.coe_unbot _ eqbot).symm.trans
        (WithBot.coe_inj.mpr (ENat.coe_toNat eqtop).symm)
      simpa only [this] using aux n

end GlobalDimension
