/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.HeckeRing.Defs
public import Mathlib.GroupTheory.Index

/-!
# Hecke rings: the double coset API

Basic API for the double cosets `HeckeCoset` indexing a Hecke coset module, following
[Shimura][shimura1971], Chapter 3. This file provides representatives of double cosets, the
characterisation of when two elements give the same double coset, and the quotient
`Γ₁ ⧸ (Γ₁ ∩ gΓ₂g⁻¹)` indexing the left cosets inside a double coset `Γ₁gΓ₂`, which is used to
define the Hecke product in later files and is finite for a Hecke triple.

## Main definitions

* `HeckeCoset.toSet`: the underlying set `H₁gH₂` of a double coset.
* `HeckeCoset.rep`: a chosen representative in `Δ`.
* `DoubleCoset.DecompQuotient`: the quotient `Γ₁ ⧸ (Γ₁ ∩ gΓ₂g⁻¹)` indexing the left cosets
  in `Γ₁gΓ₂`; finite for a Hecke triple.

## Main results

* `HeckeCoset.eq_iff`: `mk H₁ H₂ g = mk H₁ H₂ h ↔ H₁gH₂ = H₁hH₂`.
* `HeckeCoset.toSet_injective`: a double coset is determined by its underlying set.
-/

@[expose] public section

open DoubleCoset Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

namespace HeckeCoset

variable {Δ : Submonoid G} {H₁ H₂ : Subgroup G}

/-- The underlying set `H₁gH₂` of a double coset, well-defined on the quotient. -/
def toSet (D : HeckeCoset Δ H₁ H₂) : Set G :=
  Quotient.lift (fun g : Δ ↦ doubleCoset (g : G) H₁ H₂) (fun _ _ h ↦ h) D

/-- A representative `g : Δ` of a double coset (via `Quotient.out`). -/
noncomputable def rep (D : HeckeCoset Δ H₁ H₂) : Δ := Quotient.out D

@[simp] lemma mk_rep (D : HeckeCoset Δ H₁ H₂) : mk H₁ H₂ D.rep = D := Quotient.out_eq' D

lemma eq_iff {g h : Δ} : mk H₁ H₂ g = mk H₁ H₂ h ↔
    doubleCoset (g : G) H₁ H₂ = doubleCoset (h : G) H₁ H₂ := Quotient.eq''

@[simp] lemma toSet_mk (g : Δ) : toSet (mk H₁ H₂ g) = doubleCoset (g : G) H₁ H₂ := rfl

lemma toSet_eq_doubleCoset_rep (D : HeckeCoset Δ H₁ H₂) :
    D.toSet = doubleCoset (D.rep : G) H₁ H₂ := by rw [← toSet_mk, mk_rep]

lemma toSet_injective : Function.Injective (toSet : HeckeCoset Δ H₁ H₂ → Set G) := fun D₁ D₂ ↦
  Quotient.inductionOn₂' D₁ D₂ fun _ _ h ↦ Quotient.sound' h

lemma rep_mem (D : HeckeCoset Δ H₁ H₂) : (D.rep : G) ∈ D.toSet :=
  D.toSet_eq_doubleCoset_rep ▸ mem_doubleCoset_self H₁ H₂ _

/-- `mk H₁ H₂ g₁ = mk H₁ H₂ g₂` when `g₁` lies in the double coset of `g₂`. -/
lemma mk_eq_mk_of_mem {g₁ g₂ : Δ} (h : (g₁ : G) ∈ doubleCoset (g₂ : G) H₁ H₂) :
    mk H₁ H₂ g₁ = mk H₁ H₂ g₂ :=
  eq_iff.mpr (doubleCoset_eq_of_mem h)

/-- Induction: to prove something for all double cosets, prove it for `mk H₁ H₂ g`. -/
protected lemma ind {motive : HeckeCoset Δ H₁ H₂ → Prop} (h : ∀ g : Δ, motive (mk H₁ H₂ g)) :
    ∀ D, motive D :=
  Quotient.ind' h

/-- Two-argument induction for double cosets. -/
protected lemma ind₂ {motive : HeckeCoset Δ H₁ H₂ → HeckeCoset Δ H₁ H₂ → Prop}
    (h : ∀ g₁ g₂ : Δ, motive (mk H₁ H₂ g₁) (mk H₁ H₂ g₂)) : ∀ D₁ D₂, motive D₁ D₂ := fun D₁ D₂ ↦
  Quotient.inductionOn₂' D₁ D₂ h

variable {H : Subgroup G}

@[simp] lemma toSet_one : toSet (1 : HeckeCoset Δ H H) = (H : Set G) := by
  change (H : Set G) * {(1 : G)} * H = (H : Set G)
  rw [Subgroup.subgroup_mul_singleton H.one_mem, coe_mul_coe]

lemma rep_one_mem : (rep (1 : HeckeCoset Δ H H) : G) ∈ H := by
  simpa using rep_mem (1 : HeckeCoset Δ H H)

end HeckeCoset

namespace DoubleCoset

/-- The decomposition quotient `Γ₁ ⧸ (Γ₁ ∩ gΓ₂g⁻¹)`, indexing the left cosets of `Γ₂` inside
the double coset `Γ₁gΓ₂`; see `DoubleCoset.doubleCoset_eq_iUnion_leftCosets`. -/
abbrev DecompQuotient (Γ₁ Γ₂ : Subgroup G) (g : G) :=
  Γ₁ ⧸ (ConjAct.toConjAct g • Γ₂).subgroupOf Γ₁

instance (Γ₁ Γ₂ : Subgroup G) (g : G) : Nonempty (DecompQuotient Γ₁ Γ₂ g) :=
  ⟨QuotientGroup.mk 1⟩

end DoubleCoset

namespace IsHeckeTriple

/-- For a Hecke triple, the decomposition quotient of any `g : Δ` is finite: `Δ`
commensurates `H₂`, which is commensurable with `H₁`. -/
noncomputable instance {Δ : Submonoid G} {H₁ H₂ : Subgroup G} [IsHeckeTriple Δ H₁ H₂]
    (g : Δ) : Fintype (DecompQuotient H₁ H₂ (g : G)) :=
  Subgroup.fintypeOfIndexNeZero (IsHeckeTriple.commensurable_conjAct_right g).1

end IsHeckeTriple
