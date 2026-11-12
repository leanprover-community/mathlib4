/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Commensurability for subgroups

Two subgroups `H` and `K` of a group `G` are commensurable if `H ∩ K` has finite index in both `H`
and `K`.

This file defines commensurability for subgroups of a group `G`. It goes on to prove that
commensurability defines an equivalence relation on subgroups of `G` and finally defines the
commensurator of a subgroup `H` of `G`, which is the elements `g` of `G` such that `gHg⁻¹` is
commensurable with `H`.

## Main definitions

* `Commensurable H K`: the statement that the subgroups `H` and `K` of `G` are commensurable.
* `commensurator H`: the commensurator of a subgroup `H` of `G`.

## Implementation details

We define the commensurator of a subgroup `H` of `G` by first defining it as a subgroup of
`(conjAct G)`, which we call `commensurator'` and then taking the pre-image under
the map `G → (conjAct G)` to obtain our commensurator as a subgroup of `G`.

We define `Commensurable` both for additive and multiplicative groups (in the `AddSubgroup` and
`Subgroup` namespaces respectively); but `Commensurator` is not additivized, since it is not an
interesting concept for abelian groups, and it would be unusual to write a non-abelian group
additively.
-/

@[expose] public section

open scoped Pointwise

variable {G G' : Type*} [Group G] [Group G'] {H K L : Subgroup G}

/-- Equivalence of `K / (H ⊓ K)` with `gKg⁻¹/ (gHg⁻¹ ⊓ gKg⁻¹)` -/
@[deprecated "This technical lemma is no longer necessary for the proof of `commensurable_conj`."
(since := "2026-06-25")]
def Subgroup.quotConjEquiv (H K : Subgroup G) (g : ConjAct G) :
    K ⧸ H.subgroupOf K ≃ (g • K : Subgroup G) ⧸ (g • H).subgroupOf (g • K) :=
  Quotient.congr (K.equivSMul g).toEquiv fun a b ↦ by
    dsimp
    rw [← Quotient.eq'', ← Quotient.eq'', QuotientGroup.eq, QuotientGroup.eq,
      mem_subgroupOf, mem_subgroupOf, ← map_inv, ← map_mul, equivSMul_apply_coe]
    exact smul_mem_pointwise_smul_iff.symm

/-- Two subgroups `H K` of `G` are commensurable if `H ⊓ K` has finite index in both `H` and `K`. -/
@[to_additive /-- Two subgroups `H K` of `G` are commensurable if `H ⊓ K` has finite index in both
`H` and `K`. -/]
def Subgroup.Commensurable (H K : Subgroup G) : Prop :=
  H.IsFiniteRelIndex K ∧ K.IsFiniteRelIndex H

namespace Subgroup.Commensurable

@[to_additive (attr := refl)]
protected theorem refl (H : Subgroup G) : Commensurable H H := by simp [Commensurable]

@[to_additive]
theorem comm : Commensurable H K ↔ Commensurable K H := and_comm

@[to_additive (attr := symm)]
theorem symm : Commensurable H K → Commensurable K H := And.symm

@[to_additive (attr := trans)]
theorem trans (hhk : Commensurable H K) (hkl : Commensurable K L) :
    Commensurable H L :=
  ⟨hhk.1.trans hkl.1, hkl.2.trans hhk.2⟩

@[to_additive]
theorem equivalence : Equivalence (@Commensurable G _) :=
  ⟨Commensurable.refl, fun h => Commensurable.symm h, fun h₁ h₂ => Commensurable.trans h₁ h₂⟩

@[to_additive (attr := simp)]
theorem top_left_iff : Commensurable ⊤ H ↔ H.FiniteIndex := by
  simp [Commensurable, isFiniteRelIndex_iff_relIndex_ne_zero, finiteIndex_iff]

@[to_additive (attr := simp)]
theorem top_right_iff : Commensurable H ⊤ ↔ H.FiniteIndex := by
  simp [Commensurable, isFiniteRelIndex_iff_relIndex_ne_zero, finiteIndex_iff]

@[to_additive (attr := simp)]
theorem bot_left_iff : Commensurable ⊥ H ↔ Finite H := by
  simp [Commensurable, isFiniteRelIndex_iff_relIndex_ne_zero, Nat.card_ne_zero, One.instNonempty]

@[to_additive (attr := simp)]
theorem bot_right_iff : Commensurable H ⊥ ↔ Finite H := by
  simp [Commensurable, isFiniteRelIndex_iff_relIndex_ne_zero, Nat.card_ne_zero, One.instNonempty]

theorem inf_left (hHL : Commensurable H L) (hKL : Commensurable K L) :
    Commensurable (H ⊓ K) L :=
  ⟨hHL.1.inf hKL.1, have := hHL.2; isFiniteRelIndex_of_le_right L inf_le_left⟩

theorem inf_right (hHK : Commensurable H K) (hHL : Commensurable H L) :
    Commensurable H (K ⊓ L) :=
  ⟨have := hHL.1; isFiniteRelIndex_of_le_right H inf_le_right, hHK.2.inf hHL.2⟩

protected theorem map (f : G →* G') (h : H.Commensurable K) :
    Commensurable (H.map f) (K.map f) :=
  h.imp (.map f) (.map f)

protected theorem comap (f : G' →* G) (h : H.Commensurable K) :
    Commensurable (H.comap f) (K.comap f) :=
  h.imp (.comap f) (.comap f)

theorem map_injective_iff {f : G →* G'} (hf : Function.Injective f) :
    Commensurable (H.map f) (K.map f) ↔ Commensurable H K :=
  ⟨fun h ↦ by simpa [comap_map_eq_self_of_injective hf] using h.comap f, .map f⟩

theorem comap_surjective_iff {f : G' →* G} (hf : Function.Surjective f) :
    Commensurable (H.comap f) (K.comap f) ↔ Commensurable H K :=
  ⟨fun h ↦ by simpa [map_comap_eq_self_of_surjective hf] using h.map f, .comap f⟩

protected theorem smul {Φ : Type*} [Group Φ] [MulDistribMulAction Φ G] (φ : Φ)
    (h : H.Commensurable K) : Commensurable (φ • H) (φ • K) :=
  h.map _

@[deprecated (since := "2026-06-25")] alias conj := Subgroup.Commensurable.smul

theorem smul_iff {Φ : Type*} [Group Φ] [MulDistribMulAction Φ G] {φ : Φ} :
    Commensurable (φ • H) (φ • K) ↔ Commensurable H K :=
  ⟨fun h ↦ by simpa using h.smul φ⁻¹, .smul φ⟩

@[deprecated (since := "2026-06-25")] alias commensurable_conj := Subgroup.Commensurable.smul_iff

theorem inv_smul_iff {Φ : Type*} [Group Φ] [MulDistribMulAction Φ G] {φ : Φ} :
    Commensurable (φ⁻¹ • H) K ↔ Commensurable H (φ • K) := by
  simpa using smul_iff (H := H) (K := φ • K) (φ := φ⁻¹)

@[deprecated (since := "2026-06-25")] alias commensurable_inv := inv_smul_iff

/-- For `H` a subgroup of `G`, this is the subgroup of all elements `g : G`
such that `Commensurable (g H g⁻¹) H` -/
def commensurator (H : Subgroup G) : Subgroup G where
  carrier := {g : G | Commensurable (MulAut.conj g • H) H}
  one_mem' := by simpa using .refl H
  mul_mem' {g h} hg hh := by simpa [mul_smul] using (hh.smul (MulAut.conj g)).trans hg
  inv_mem' h := by simpa [inv_smul_iff] using h.symm

/-- For `H` a subgroup of `G`, this is the subgroup of all elements `g : conjAut G`
such that `Commensurable (g • H) H` -/
@[deprecated "Use `Subgroup.Commensurable.commensurator` instead." (since := "2026-06-25")]
def commensurator' (H : Subgroup G) : Subgroup (ConjAct G) :=
  (commensurator H).map ConjAct.toConjAct.toMonoidHom

@[simp]
theorem commensurator_mem_iff (H : Subgroup G) (g : G) :
    g ∈ commensurator H ↔ Commensurable (MulAut.conj g • H) H := Iff.rfl

@[deprecated "Use `commensurator_mem_iff` instead." (since := "2026-06-25")]
theorem commensurator'_mem_iff (H : Subgroup G) (g : ConjAct G) :
    g ∈ commensurator' H ↔ Commensurable (g • H) H := by
  rw [commensurator', map_equiv_eq_comap_symm']
  rfl

theorem eq (hk : Commensurable H K) : commensurator H = commensurator K :=
  Subgroup.ext fun x =>
    let hx := hk.smul (MulAut.conj x)
    ⟨fun h => hx.symm.trans (h.trans hk), fun h => hx.trans (h.trans hk.symm)⟩

end Subgroup.Commensurable
