/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.LinearAlgebra.Transvection.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.GroupTheory.GroupAction.Iwasawa

/-!
# The special linear group is simple (modulo its center)
-/

@[expose] public section

namespace SpecialLinearGroup

open MulAction Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def iwasawaT (D : Projectivization K V) :
    Subgroup (SpecialLinearGroup K V) where
  carrier := {e | ∃ (f : Dual K V) (h : f (D.rep) = 0), e = transvection h }
  mul_mem' {x y} hx hy := by
    obtain ⟨f, hfx, ⟨hx, rfl⟩⟩ := hx
    obtain ⟨g, hgy, ⟨hy, rfl⟩⟩ := hy
    simp only [Set.mem_setOf_eq]
    refine ⟨f + g, by simp [hfx, hgy], ?_⟩
    simp [← Subtype.coe_inj, ← LinearEquiv.toLinearMap_inj,
      End.mul_eq_comp, LinearMap.transvection.comp_of_right_eq hfx]
  one_mem' := ⟨0, by simp, by aesop⟩
  inv_mem' {g} hg := by
    obtain ⟨f, hf, ⟨hg, rfl⟩⟩ := hg
    refine ⟨(-f : Dual K V), by aesop, by
      simp only [← Subtype.coe_inj, coe_inv, transvection.coe_toLinearEquiv]
      exact LinearEquiv.transvection.symm_eq' hf ?_⟩

open Pointwise

def iwasawa [Module.Finite K V] :
    IwasawaStructure (SpecialLinearGroup K V) (Projectivization K V) where
  T := iwasawaT
  is_comm D := {
    is_comm := {
      comm x y := by
        obtain ⟨f, hfx, hx⟩ := x.prop
        obtain ⟨g, hgy, hy⟩ := y.prop
        simp [← Subtype.coe_inj, hx, hy, ← LinearEquiv.toLinearMap_inj,
          End.mul_eq_comp, LinearMap.transvection.comp_of_right_eq hgy,
          LinearMap.transvection.comp_of_right_eq hfx, add_comm] } }
  is_conj g D := by
    suffices ∀ g D, MulAut.conj g • iwasawaT D ≤ iwasawaT (g • D) by
      apply le_antisymm _ (this g D)
      intro x hx
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      rw [show D = g⁻¹ • g • D from by simp]
      apply this g⁻¹ (g • D)
      rw [← Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa
    intro g D x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    obtain ⟨f, hfx, hx⟩ := hx
    rw [inv_smul_eq_iff] at hx
    have : ∃ a : Kˣ, a • g • D.rep = (g • D).rep := by
      rw [← Projectivization.mk_eq_mk_iff K (g • D).rep (g • D.rep)
        (g • D).rep_nonzero ((smul_ne_zero_iff_ne g).mpr D.rep_nonzero)]
      simp [Projectivization.mk_rep, ← eq_inv_smul_iff]
    obtain ⟨a, ha⟩ := this
    use a⁻¹ • f ∘ₗ g⁻¹.toLinearEquiv
    refine ⟨by simp [← ha, ← hfx, SpecialLinearGroup.smul_def], ?_⟩
    -- the rest of the proof is ugly,
    -- one needs a better congr lemma for transvections
    rw [hx]
    simp only [MulAut.smul_def, MulAut.conj_apply, coe_toLinearEquiv, coe_inv, ← Subtype.coe_inj,
      coe_mul, transvection.coe_toLinearEquiv, ← LinearEquiv.toLinearMap_inj,
      LinearEquiv.coe_toLinearMap_mul, LinearEquiv.transvection.coe_toLinearMap]
    have := LinearEquiv.transvection.congr hfx g.toLinearEquiv
    simp only [coe_toLinearEquiv, ← LinearEquiv.mul_eq_trans, ← LinearEquiv.toLinearMap_inj,
      LinearEquiv.coe_toLinearMap_mul, LinearEquiv.transvection.coe_toLinearMap] at this
    erw [this]
    ext v
    simp only [LinearMap.transvection.apply, ← ha, add_right_inj]
    simp only [SpecialLinearGroup.smul_def, Units.smul_def,
      LinearEquiv.smul_def, coe_toLinearEquiv]
    match_scalars
    simp [mul_comm a.val⁻¹]
  is_generator := by
    rw [eq_top_iff, ← SpecialLinearGroup.subgroup_closure_transvections_eq_top, Subgroup.closure_le]
    rintro _ ⟨f, v, hfv, rfl⟩
    by_cases hv : v = 0
    · suffices transvection hfv = 1 by simp [this]
      simp [← Subtype.coe_inj, hv, ← LinearEquiv.toLinearMap_inj]
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
    apply Subgroup.mem_iSup_of_mem (Projectivization.mk K v hv)
    refine ⟨a⁻¹ • f, ?_, ?_⟩
    · simp [LinearMap.smul_apply, Units.smul_def, ← ha, hfv]
    -- this is slightly less ugly, but not so much
    ext x
    rw [← smul_left_cancel_iff a]
    suffices a • f x • v = f x • a • v by
      simpa [LinearMap.transvection.apply, ← ha]
    simp [Units.smul_def, smul_comm (f x)]

example [Module.Finite K V]
    (hV : finrank K V ≠ 2 ∨ Nat.card K ≠ 2 ∧ Nat.card K ≠ 3)
    {N : Subgroup (SpecialLinearGroup K V)} [N.Normal]
    (hN : ¬ N ≤ Subgroup.center (SpecialLinearGroup K V)) :
    N = ⊤ := by
  rw [eq_top_iff, ← SpecialLinearGroup.commutator_eq_top hV]
  apply iwasawa.commutator_le
  contrapose hN
  intro n hn
  sorry

end SpecialLinearGroup

end
