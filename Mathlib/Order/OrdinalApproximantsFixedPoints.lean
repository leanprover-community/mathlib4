/-
Copyright (c) 2023 Ira Fesefeldt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ira Fesefeldt
-/
import Mathlib.Order.FixedPoints
import Mathlib.Logic.Function.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic


/-!
# Ordinal Approximants for the Fixed points on complete lattices

This file sets up the ordinal approximation theory of fixed points
of a monotone function in a complete lattice.

## Main definitions

* `OrdinalApprox.lfp_approx`: The ordinal approximation of
  the least fixed point of a bundled monotone function.
* `OrdinalApprox.gfp_approx`: The ordinal approximation of
  the greatest fixed point of a bundled monotone function.

## Main theorems
* `OrdinalApprox.lfp_is_lfp_approx`: The approximation of
  the least fixed point eventually reaches the least fixed point
* `OrdinalApprox.gfp_is_gfp_approx`: The approximation of
  the greatest fixed point eventually reaches the greatest fixed point

## Tags

fixed point, complete lattice, monotone function, ordinals, approximation
-/

namespace Cardinal

universe u
variable {α : Type u}
variable (g: Ordinal → α)

open Cardinal Ordinal SuccOrder Function

def limitation : { i : Ordinal // i < (ord $ succ #α)} → α := λ i => g i

theorem limitation_def : ∀ i, limitation g i = g i := by
  intro h; unfold limitation; exact rfl

lemma mk_initialSeg_Subtype (ℵ : Cardinal ): #{ i : Ordinal // i < (ord  ℵ)} = lift.{u+1, u} ℵ := by
  simpa using mk_initialSeg (ord ℵ)

theorem limitation_not_injective: ¬ Injective (limitation g) := by
  intro h_inj
  have h₁ := by apply lift_mk_le_lift_mk_of_injective h_inj;
  rw[mk_initialSeg_Subtype (succ #α), Cardinal.lift_lift, Cardinal.lift_le] at h₁
  have h₂ := not_le_of_lt (Cardinal.succ_lt #α)
  exact h₂ h₁

end Cardinal



namespace Monotone


universe u v
variable {α : Type u}
variable {β : Type v}
variable [Preorder α] [PartialOrder β] (f: α → β)

theorem monotone_stabilizing {a₁ a₂ : α} (h_mon : Monotone f) (h_fa : f a₁ = f a₂):
    ∀ i, a₂ ≥ i → i ≥ a₁ → f i = f a₁ := by
  intro i h₂ h₁
  apply le_antisymm
  · rw[h_fa]; exact h_mon h₂
  · exact h_mon h₁

theorem antitone_stabilizing {a₁ a₂ : α} (h_anti : Antitone f) (h_fa : f a₁ = f a₂):
    ∀ i, a₂ ≥ i → i ≥ a₁ → f i = f a₁ := by
  intro i h₂ h₁
  apply le_antisymm
  · exact h_anti h₁
  · rw[h_fa]; exact h_anti h₂

end Monotone

/-We loosly follow the proof from Frederico Enchenique in A Short and Constructive Proof of
  Tarski's fixed-point theorem published in the International Journal of Game Theory Volume 33(2),
  June 2005, pages 215-218. -/

namespace OrdinalApprox

universe u
variable {α : Type u}
variable [CompleteLattice α] (f : α →o α)

open Function fixedPoints Cardinal Order OrderHom

/- Ordinal approximants of the least fixed points -/
set_option linter.unusedVariables false in
def lfp_approx (a : Ordinal.{u}) : α :=
  sSup { f (lfp_approx b) | (b : Ordinal) (h : b < a) }
termination_by lfp_approx a => a
decreasing_by exact h

theorem lfp_approx_monotone : Monotone (lfp_approx f) := by
  unfold Monotone; intros a b h; unfold lfp_approx
  refine sSup_le_sSup ?h; simp
  intros a' h'
  use a'; apply And.intro; exact lt_of_lt_of_le h' h
  exact rfl

def lfp_approx_hom : Ordinal.{u} →o α where
  toFun i := lfp_approx f i
  monotone' a b h := by simp; apply lfp_approx_monotone f h

theorem lfp_approx_addition (a : Ordinal.{u}) : f (lfp_approx f a) = lfp_approx f (a+1) := by
  apply le_antisymm
  · conv => right; unfold lfp_approx
    apply le_sSup; simp
    use a
  · conv => left; unfold lfp_approx
    apply sSup_le; simp
    intros a' h
    apply f.2; apply lfp_approx_monotone; exact h


theorem lfp_approx_stabilizing_at_fp (a : Ordinal.{u}) (h: lfp_approx f a ∈ (fixedPoints f)):
    ∀ b > a, lfp_approx f b = lfp_approx f a := by
  intro b hab; rw[mem_fixedPoints_iff] at h;
  induction b using Ordinal.induction with | h b IH =>
  apply le_antisymm
  · conv => left; unfold lfp_approx
    apply sSup_le; simp
    intro a' ha'b
    by_cases haa : a' < a
    · rw[lfp_approx_addition]
      apply lfp_approx_monotone
      simp; exact haa
    · simp at haa
      cases (le_iff_lt_or_eq.mp haa) with
      | inl haa => specialize IH a' ha'b haa; rw[IH, h];
      | inr haa => rw[←haa, h];
  · conv => right; unfold lfp_approx
    apply le_sSup; simp
    use a

theorem lfp_approx_eq_fp (a : Ordinal.{u}) (h: lfp_approx f a ∈ (fixedPoints f)):
    ∀ b > a, lfp_approx f b ∈ (fixedPoints f)  := by
  intro b h_ab;
  rw[mem_fixedPoints_iff]
  have h_stab := lfp_approx_stabilizing_at_fp f a h b h_ab
  rw[h_stab]
  exact mem_fixedPoints_iff.mp h


theorem lfp_approx_has_cycle : ∃ i < ord $ succ #α, ∃ j < ord $ succ #α,
    i ≠ j ∧ lfp_approx f i = lfp_approx f j := by
  have h_ninj := Function.Injective.not_exists_equal (limitation_not_injective $ lfp_approx f)
  let ⟨a, b, h_nab, h_fab⟩ := h_ninj
  rw[limitation_def, limitation_def] at h_fab
  use a.val; apply And.intro a.prop;
  use b.val; apply And.intro b.prop;
  apply And.intro
  · intro h_eq; rw[Subtype.coe_inj] at h_eq; exact h_nab h_eq
  · exact h_fab

lemma lfp_approx_one_fixedPoint (a b : Ordinal.{u}) (h : a < b)
    (h_fab : lfp_approx f a = lfp_approx f b):
    lfp_approx f a ∈ (fixedPoints f) := by
  rw[mem_fixedPoints_iff,lfp_approx_addition]
  apply Monotone.monotone_stabilizing (lfp_approx f) (lfp_approx_monotone f)
    h_fab (a+1) (SuccOrder.succ_le_of_lt h) (SuccOrder.le_succ a)

lemma lfp_approx_many_fixedPoints (a b : Ordinal.{u}) (h : a < b)
    (h_fab : lfp_approx f a = lfp_approx f b):
    ∀ i ≥ a, lfp_approx f i ∈ (fixedPoints f) := by
  intro i h_i;
  by_cases h_ia : i = a
  · rw[h_ia]; exact lfp_approx_one_fixedPoint f a b h h_fab
  · apply lfp_approx_eq_fp f a
    · exact lfp_approx_one_fixedPoint f a b h h_fab
    · exact Ne.lt_of_le' h_ia h_i

lemma lfp_approx_has_fixedPoint_cardinal : lfp_approx f (ord $ succ #α) ∈ (fixedPoints f) := by
  let ⟨a, h_a, b, h_b, h_nab, h_fab⟩ := lfp_approx_has_cycle f
  cases (le_total a b) with
  | inl h_ab =>
    exact lfp_approx_many_fixedPoints f a b (Ne.lt_of_le h_nab h_ab) h_fab
      (ord $ succ #α) (le_of_lt h_a)
  | inr h_ba =>
    exact lfp_approx_many_fixedPoints f b a (Ne.lt_of_le (id (Ne.symm h_nab)) h_ba)
      (h_fab.symm) (ord $ succ #α) (le_of_lt h_b)

lemma lfp_approx_le_fixedPoint : ∀ a : (fixedPoints f), ∀ i : Ordinal, lfp_approx f i ≤ a := by
  intro ⟨a, h_a⟩ i
  induction i using Ordinal.induction with
  | h i IH =>
    unfold lfp_approx
    apply sSup_le; simp
    intro j h_j
    rw[←h_a]
    apply f.monotone'
    exact IH j h_j

theorem lfp_is_lfp_approx_cardinal : lfp_approx f (ord $ succ #α) = lfp f := by
  apply le_antisymm
  · have h_lfp : ∃ x : fixedPoints f, lfp f = x := by use ⊥; exact rfl
    let ⟨x, h_x⟩ := h_lfp; rw[h_x]
    exact lfp_approx_le_fixedPoint f x (ord $ succ #α)
  · have h_fix : ∃ x: fixedPoints f, lfp_approx f (ord $ succ #α) = x := by
      simpa using lfp_approx_has_fixedPoint_cardinal f
    let ⟨x, h_x⟩ := h_fix; rw[h_x]
    exact lfp_le_fixed f x.prop

/-- **Constructive Knaster-Tarski Theorem**: Some ordinal approximation of the least fixed point
  is the least fixed point. Also known as ordinal approximation of the least fixed point.-/
theorem lfp_is_lfp_approx : ∃ a : Ordinal, lfp_approx f a = OrderHom.lfp f := by
  use (ord $ succ #α)
  exact lfp_is_lfp_approx_cardinal f


/- Ordinal approximants of the least fixed points -/
set_option linter.unusedVariables false in
def gfp_approx (a : Ordinal.{u}) : α :=
  sInf { f (gfp_approx b) | (b : Ordinal) (h : b < a) }
termination_by gfp_approx a => a
decreasing_by exact h

theorem gfp_approx_antitone : Antitone (gfp_approx f) := by
  unfold Antitone; intros a b h; unfold gfp_approx
  refine sInf_le_sInf ?h; simp
  intros a' h'
  use a'; apply And.intro; exact lt_of_lt_of_le h' h
  exact rfl

theorem gfp_approx_addition (a : Ordinal.{u}) : f (gfp_approx f a) = gfp_approx f (a+1) := by
  apply le_antisymm
  · conv => right; unfold gfp_approx
    apply le_sInf; simp
    intros a' h
    apply f.2; apply gfp_approx_antitone; exact h
  · conv => left; unfold gfp_approx
    apply sInf_le; simp
    use a


theorem gfp_approx_stabilizing_at_fp (a : Ordinal.{u}) (h: gfp_approx f a ∈ (fixedPoints f)):
    ∀ b > a, gfp_approx f b = gfp_approx f a := by
  intro b hab; rw[mem_fixedPoints_iff] at h;
  induction b using Ordinal.induction with | h b IH =>
  apply le_antisymm
  · conv => left; unfold gfp_approx
    apply sInf_le
    use a
  · conv => right; unfold gfp_approx
    apply le_sInf; simp
    intro a' ha'b
    by_cases haa : a' < a
    · rw[gfp_approx_addition]
      apply gfp_approx_antitone
      simp; exact haa
    · simp at haa
      cases (le_iff_lt_or_eq.mp haa) with
      | inl haa => specialize IH a' ha'b haa; rw[IH, h];
      | inr haa => rw[←haa, h];

theorem gfp_approx_eq_fp (a : Ordinal.{u}) (h: gfp_approx f a ∈ (fixedPoints f)):
    ∀ b > a, gfp_approx f b ∈ (fixedPoints f)  := by
  intro b h_ab;
  rw[mem_fixedPoints_iff]
  have h_stab := gfp_approx_stabilizing_at_fp f a h b h_ab
  rw[h_stab]
  exact mem_fixedPoints_iff.mp h


theorem gfp_approx_has_cycle : ∃ i < ord $ succ #α, ∃ j < ord $ succ #α,
    i ≠ j ∧ gfp_approx f i = gfp_approx f j := by
  have h_ninj := Function.Injective.not_exists_equal (limitation_not_injective $ gfp_approx f)
  let ⟨a, b, h_nab, h_fab⟩ := h_ninj
  rw[limitation_def, limitation_def] at h_fab
  use a.val; apply And.intro a.prop;
  use b.val; apply And.intro b.prop;
  apply And.intro
  · intro h_eq; rw[Subtype.coe_inj] at h_eq; exact h_nab h_eq
  · exact h_fab

lemma gfp_approx_one_fixedPoint (a b : Ordinal.{u}) (h : a < b)
    (h_fab : gfp_approx f a = gfp_approx f b):
    gfp_approx f a ∈ (fixedPoints f) := by
  rw[mem_fixedPoints_iff,gfp_approx_addition]
  apply Monotone.antitone_stabilizing (gfp_approx f) (gfp_approx_antitone f)
    h_fab (a+1) (SuccOrder.succ_le_of_lt h) (SuccOrder.le_succ a)

lemma gfp_approx_many_fixedPoints (a b : Ordinal.{u}) (h : a < b)
    (h_fab : gfp_approx f a = gfp_approx f b):
    ∀ i ≥ a, gfp_approx f i ∈ (fixedPoints f) := by
  intro i h_i;
  by_cases h_ia : i = a
  · rw[h_ia]; exact gfp_approx_one_fixedPoint f a b h h_fab
  · apply gfp_approx_eq_fp f a
    · exact gfp_approx_one_fixedPoint f a b h h_fab
    · exact Ne.lt_of_le' h_ia h_i

lemma gfp_approx_has_fixedPoint_cardinal : gfp_approx f (ord $ succ #α) ∈ (fixedPoints f) := by
  let ⟨a, h_a, b, h_b, h_nab, h_fab⟩ := gfp_approx_has_cycle f
  cases (le_total a b) with
  | inl h_ab =>
    exact gfp_approx_many_fixedPoints f a b (Ne.lt_of_le h_nab h_ab)
      h_fab (ord $ succ #α) (le_of_lt h_a)
  | inr h_ba =>
    exact gfp_approx_many_fixedPoints f b a (Ne.lt_of_le (id (Ne.symm h_nab)) h_ba)
      (h_fab.symm) (ord $ succ #α) (le_of_lt h_b)

lemma gfp_approx_ge_fixedPoint : ∀ a : (fixedPoints f), ∀ i : Ordinal, gfp_approx f i ≥ a := by
  intro ⟨a, h_a⟩ i
  induction i using Ordinal.induction with
  | h i IH =>
    unfold gfp_approx
    apply le_sInf; simp
    intro j h_j
    rw[←h_a]
    apply f.monotone'
    exact IH j h_j


theorem gfp_is_gfp_approx_cardinal : gfp_approx f (ord $ succ #α) = gfp f := by
  apply le_antisymm
  · have h_fix : ∃ x: fixedPoints f, gfp_approx f (ord $ succ #α) = x := by
      simpa using gfp_approx_has_fixedPoint_cardinal f
    let ⟨x, h_x⟩ := h_fix; rw[h_x]
    exact fixed_le_gfp f x.prop
  · have h_lfp : ∃ x : fixedPoints f, gfp f = x := by use ⊤; exact rfl
    let ⟨x, h_x⟩ := h_lfp; rw[h_x]
    exact gfp_approx_ge_fixedPoint f x (ord $ succ #α)


/-- **Dual Constructive Knaster-Tarski Theorem**: Some ordinal approximation of
  the greatest fixed point is the greatest fixed point. Also known as ordinal approximation of
  the greatest fixed point.-/
theorem gfp_is_gfp_approx : ∃ a : Ordinal, gfp_approx f a = gfp f := by
  use (ord $ succ #α)
  exact gfp_is_gfp_approx_cardinal f

end OrdinalApprox
