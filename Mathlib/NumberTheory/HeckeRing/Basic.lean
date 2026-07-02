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

Basic API for the double cosets `HeckeCoset` indexing an abstract Hecke ring, following
[Shimura][shimura1971], Chapter 3. This file provides representatives of double cosets, the
characterisation of when two elements give the same double coset, and the quotient
`Γ₁ ⧸ (Γ₁ ∩ gΓ₂g⁻¹)` indexing the left cosets inside a double coset `Γ₁gΓ₂`, which is used to
define the Hecke product in later files and is finite in the Hecke pair setting.

## Main definitions

* `HeckeCoset.toSet`: the underlying set `HgH` of a double coset.
* `HeckeCoset.rep`: a chosen representative in `Δ`.
* `DoubleCoset.DecompQuotient`: the quotient `Γ₁ ⧸ (Γ₁ ∩ gΓ₂g⁻¹)` indexing the left cosets
  in `Γ₁gΓ₂`; finite for a Hecke pair.

## Main results

* `HeckeCoset.eq_iff`: `⟦g⟧ = ⟦h⟧ ↔ HgH = HhH`.
* `HeckeCoset.toSet_injective`: a double coset is determined by its underlying set.

## Implementation notes

`HeckePair.doubleCosetSetoid` is a `def`, not a global instance; this file opts in to it with
`attribute [local instance]` so that the quotient notation `⟦·⟧` is available for `HeckeCoset`.
-/

@[expose] public section

open DoubleCoset Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

attribute [local instance] HeckePair.doubleCosetSetoid

namespace HeckeCoset

variable {P : HeckePair G}

/-- The underlying set `HgH` of a double coset, well-defined on the quotient. -/
def toSet (D : HeckeCoset P) : Set G :=
  Quotient.lift (fun g : P.Δ ↦ doubleCoset (g : G) P.H P.H) (fun _ _ h ↦ h) D

/-- A representative `g : Δ` of a double coset (via `Quotient.out`). -/
noncomputable def rep (D : HeckeCoset P) : P.Δ := Quotient.out D

@[simp] lemma mk_rep (D : HeckeCoset P) : (⟦D.rep⟧ : HeckeCoset P) = D := Quotient.out_eq D

lemma eq_iff {g h : P.Δ} : (⟦g⟧ : HeckeCoset P) = ⟦h⟧ ↔
    doubleCoset (g : G) P.H P.H = doubleCoset (h : G) P.H P.H := Quotient.eq

@[simp] lemma toSet_mk (g : P.Δ) :
    toSet (⟦g⟧ : HeckeCoset P) = doubleCoset (g : G) P.H P.H := rfl

lemma toSet_eq_doubleCoset_rep (D : HeckeCoset P) :
    D.toSet = doubleCoset (D.rep : G) P.H P.H := by rw [← toSet_mk, mk_rep]

lemma toSet_injective : Function.Injective (toSet : HeckeCoset P → Set G) := fun D₁ D₂ ↦
  Quotient.inductionOn₂ D₁ D₂ fun _ _ h ↦ Quotient.sound h

lemma rep_mem (D : HeckeCoset P) : (D.rep : G) ∈ D.toSet :=
  D.toSet_eq_doubleCoset_rep ▸ mem_doubleCoset_self P.H P.H _

/-- `⟦g₁⟧ = ⟦g₂⟧` when `g₁` lies in the double coset of `g₂`. -/
lemma mk_eq_mk_of_mem {g₁ g₂ : P.Δ} (h : (g₁ : G) ∈ doubleCoset (g₂ : G) P.H P.H) :
    (⟦g₁⟧ : HeckeCoset P) = ⟦g₂⟧ :=
  eq_iff.mpr (doubleCoset_eq_of_mem h)

/-- Induction: to prove something for all double cosets, prove it for `⟦g⟧`. -/
protected lemma ind {motive : HeckeCoset P → Prop} (h : ∀ g : P.Δ, motive ⟦g⟧) : ∀ D, motive D :=
  Quotient.ind h

/-- Two-argument induction for double cosets. -/
protected lemma ind₂ {motive : HeckeCoset P → HeckeCoset P → Prop}
    (h : ∀ g₁ g₂ : P.Δ, motive ⟦g₁⟧ ⟦g₂⟧) : ∀ D₁ D₂, motive D₁ D₂ :=
  Quotient.ind₂ h

@[simp] lemma toSet_one : toSet (1 : HeckeCoset P) = (P.H : Set G) := by
  change (P.H : Set G) * {(1 : G)} * P.H = (P.H : Set G)
  rw [Subgroup.subgroup_mul_singleton P.H.one_mem, coe_mul_coe]

lemma rep_one_mem : (rep (1 : HeckeCoset P) : G) ∈ P.H := by
  simpa using rep_mem (1 : HeckeCoset P)

end HeckeCoset

namespace DoubleCoset

/-- The decomposition quotient `Γ₁ ⧸ (Γ₁ ∩ gΓ₂g⁻¹)`, indexing the left cosets of `Γ₂` inside
the double coset `Γ₁gΓ₂`; see `DoubleCoset.doubleCoset_eq_iUnion_leftCosets`. -/
abbrev DecompQuotient (Γ₁ Γ₂ : Subgroup G) (g : G) :=
  Γ₁ ⧸ (ConjAct.toConjAct g • Γ₂).subgroupOf Γ₁

instance (Γ₁ Γ₂ : Subgroup G) (g : G) : Nonempty (DecompQuotient Γ₁ Γ₂ g) :=
  ⟨QuotientGroup.mk 1⟩

end DoubleCoset

namespace HeckePair

/-- For a Hecke pair, the decomposition quotient of any `g : Δ` is finite, because `Δ` lies in
the commensurator of `H`. -/
noncomputable instance (P : HeckePair G) (g : P.Δ) :
    Fintype (DecompQuotient P.H P.H (g : G)) :=
  Subgroup.fintypeOfIndexNeZero (P.le_commensurator g.2).1

end HeckePair
