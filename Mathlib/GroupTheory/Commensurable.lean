/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Pointwise
import Mathlib.GroupTheory.GroupAction.ConjAct

#align_import group_theory.commensurable from "leanprover-community/mathlib"@"48085f140e684306f9e7da907cd5932056d1aded"

/-!
# Commensurability for subgroups

This file defines commensurability for subgroups of a group `G`. It then goes on to prove that
commensurability defines an equivalence relation and finally defines the commensurator of a subgroup
of `G`.

## Main definitions

* `Commensurable`: defines commensurability for two subgroups `H`, `K` of `G`
* `commensurator`: defines the commensurator of a subgroup `H` of `G`.

## Implementation details

We define the commensurator of a subgroup `H` of `G` by first defining it as a subgroup of
`(conjAct G)`, which we call commensurator' and then taking the pre-image under
the map `G → (conjAct G)` to obtain our commensurator as a subgroup of `G`.
-/


variable {G : Type*} [Group G]

/-- Two subgroups `H K` of `G` are commensurable if `H ⊓ K` has finite index in both `H` and `K` -/
def Commensurable (H K : Subgroup G) : Prop :=
  H.relindex K ≠ 0 ∧ K.relindex H ≠ 0
#align commensurable Commensurable

namespace Commensurable

open Pointwise

@[refl]
protected theorem refl (H : Subgroup G) : Commensurable H H := by simp [Commensurable]
                                                                  -- 🎉 no goals
#align commensurable.refl Commensurable.refl

theorem comm {H K : Subgroup G} : Commensurable H K ↔ Commensurable K H := and_comm
#align commensurable.comm Commensurable.comm

@[symm]
theorem symm {H K : Subgroup G} : Commensurable H K → Commensurable K H := And.symm
#align commensurable.symm Commensurable.symm

@[trans]
theorem trans {H K L : Subgroup G} (hhk : Commensurable H K) (hkl : Commensurable K L) :
    Commensurable H L :=
  ⟨Subgroup.relindex_ne_zero_trans hhk.1 hkl.1, Subgroup.relindex_ne_zero_trans hkl.2 hhk.2⟩
#align commensurable.trans Commensurable.trans

theorem equivalence : Equivalence (@Commensurable G _) :=
  ⟨Commensurable.refl, fun h => Commensurable.symm h, fun h₁ h₂ => Commensurable.trans h₁ h₂⟩
#align commensurable.equivalence Commensurable.equivalence

/-- Equivalence of `K/H ⊓ K` with `gKg⁻¹/gHg⁻¹ ⊓ gKg⁻¹`-/
def quotConjEquiv (H K : Subgroup G) (g : ConjAct G) :
    K ⧸ H.subgroupOf K ≃ (g • K).1 ⧸ (g • H).subgroupOf (g • K) :=
  Quotient.congr (K.equivSMul g).toEquiv fun a b => by
    dsimp
    -- ⊢ Setoid.r a b ↔ Setoid.r (↑(Subgroup.equivSMul g K) a) (↑(Subgroup.equivSMul  …
    rw [← Quotient.eq'', ← Quotient.eq'', QuotientGroup.eq', QuotientGroup.eq',
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ← MulEquiv.map_inv, ← MulEquiv.map_mul,
      Subgroup.equivSMul_apply_coe]
    exact Subgroup.smul_mem_pointwise_smul_iff.symm
    -- 🎉 no goals
#align commensurable.quot_conj_equiv Commensurable.quotConjEquiv

theorem commensurable_conj {H K : Subgroup G} (g : ConjAct G) :
    Commensurable H K ↔ Commensurable (g • H) (g • K) :=
  and_congr (not_iff_not.mpr (Eq.congr_left (Cardinal.toNat_congr (quotConjEquiv H K g))))
    (not_iff_not.mpr (Eq.congr_left (Cardinal.toNat_congr (quotConjEquiv K H g))))
#align commensurable.commensurable_conj Commensurable.commensurable_conj

theorem commensurable_inv (H : Subgroup G) (g : ConjAct G) :
    Commensurable (g • H) H ↔ Commensurable H (g⁻¹ • H) := by rw [commensurable_conj, inv_smul_smul]
                                                              -- 🎉 no goals
#align commensurable.commensurable_inv Commensurable.commensurable_inv

/-- For `H` a subgroup of `G`, this is the subgroup of all elements `g : conjAut G`
such that `Commensurable (g • H) H` -/
def commensurator' (H : Subgroup G) : Subgroup (ConjAct G) where
  carrier := { g : ConjAct G | Commensurable (g • H) H }
  one_mem' := by rw [Set.mem_setOf_eq, one_smul]
                 -- 🎉 no goals
  mul_mem' ha hb := by
    -- ⊢ Commensurable (a✝ • b✝ • H) H
    rw [Set.mem_setOf_eq, mul_smul]
    -- 🎉 no goals
    exact trans ((commensurable_conj _).mp hb) ha
  inv_mem' _ := by rwa [Set.mem_setOf_eq, comm, ← commensurable_inv]
                   -- 🎉 no goals
#align commensurable.commensurator' Commensurable.commensurator'

/-- For `H` a subgroup of `G`, this is the subgroup of all elements `g : G`
such that `Commensurable (g H g⁻¹) H` -/
def commensurator (H : Subgroup G) : Subgroup G :=
  (commensurator' H).comap ConjAct.toConjAct.toMonoidHom
#align commensurable.commensurator Commensurable.commensurator

@[simp]
theorem commensurator'_mem_iff (H : Subgroup G) (g : ConjAct G) :
    g ∈ commensurator' H ↔ Commensurable (g • H) H := Iff.rfl
#align commensurable.commensurator'_mem_iff Commensurable.commensurator'_mem_iff

@[simp]
theorem commensurator_mem_iff (H : Subgroup G) (g : G) :
    g ∈ commensurator H ↔ Commensurable (ConjAct.toConjAct g • H) H := Iff.rfl
#align commensurable.commensurator_mem_iff Commensurable.commensurator_mem_iff

theorem eq {H K : Subgroup G} (hk : Commensurable H K) : commensurator H = commensurator K :=
  Subgroup.ext fun x =>
    let hx := (commensurable_conj x).1 hk
    ⟨fun h => hx.symm.trans (h.trans hk), fun h => hx.trans (h.trans hk.symm)⟩
#align commensurable.eq Commensurable.eq

end Commensurable
