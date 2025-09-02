/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Group.Action
import Mathlib.Order.Filter.EventuallyConst

/-!
# A.e. stabilizer of a set

In this file we define the a.e. stabilizer of a set under a measure preserving group action.

The a.e. stabilizer `MulAction.aestabilizer G μ s` of a set `s`
is the set of the elements `g : G` such that `s` is a.e.-invariant under `(g • ·)`.

For a measure preserving group action, this set is a subgroup of `G`.
If the set is null or conull, then this subgroup is the whole group.
The converse is true for an ergodic action and a null-measurable set.

## Implementation notes

We define the a.e. stabilizer as a bundled `Subgroup`,
thus we do not deal with monoid actions.

Also, many lemmas in this file are true for a *quasi-measure-preserving* action,
but we don't have the corresponding typeclass.
-/

open Filter Set MeasureTheory
open scoped Pointwise

variable (G : Type*) {α : Type*} [Group G] [MulAction G α]
  {_ : MeasurableSpace α} (μ : Measure α) [SMulInvariantMeasure G α μ]

namespace MulAction

/-- A.e. stabilizer of a set under a group action. -/
@[to_additive (attr := simps) /-- A.e. stabilizer of a set under an additive group action. -/]
def aestabilizer (s : Set α) : Subgroup G where
  carrier := {g | g • s =ᵐ[μ] s}
  one_mem' := by simp
  -- TODO: `calc` would be more readable but fails because of defeq abuse
  mul_mem' {g₁ g₂} h₁ h₂ := by simpa only [smul_smul] using ((smul_set_ae_eq g₁).2 h₂).trans h₁
  inv_mem' {g} h := by simpa using (smul_set_ae_eq g⁻¹).2 h.out.symm

variable {G μ}
variable {g : G} {s t : Set α}

@[to_additive (attr := simp)]
lemma mem_aestabilizer : g ∈ aestabilizer G μ s ↔ g • s =ᵐ[μ] s := .rfl

@[to_additive]
lemma stabilizer_le_aestabilizer (s : Set α) : stabilizer G s ≤ aestabilizer G μ s := by
  intro g hg
  simp_all

@[to_additive (attr := simp)]
lemma aestabilizer_empty : aestabilizer G μ ∅ = ⊤ := top_unique fun _ _ ↦ by simp

@[to_additive (attr := simp)]
lemma aestabilizer_univ : aestabilizer G μ univ = ⊤ := top_unique fun _ _ ↦ by simp

@[to_additive]
lemma aestabilizer_congr (h : s =ᵐ[μ] t) : aestabilizer G μ s = aestabilizer G μ t := by
  ext g
  rw [mem_aestabilizer, mem_aestabilizer, h.congr_right, ((smul_set_ae_eq g).2 h).congr_left]

lemma aestabilizer_of_aeconst (hs : EventuallyConst s (ae μ)) : aestabilizer G μ s = ⊤ := by
  refine top_unique fun g _ ↦ ?_
  cases eventuallyConst_set'.mp hs with
  | inl h => simp [aestabilizer_congr h]
  | inr h => simp [aestabilizer_congr h]

end MulAction

variable {G μ}
variable {x y : G} {s : Set α}

namespace MeasureTheory

@[to_additive]
theorem smul_ae_eq_self_of_mem_zpowers (hs : (x • s : Set α) =ᵐ[μ] s)
    (hy : y ∈ Subgroup.zpowers x) : (y • s : Set α) =ᵐ[μ] s := by
  rw [← MulAction.mem_aestabilizer, ← Subgroup.zpowers_le] at hs
  exact hs hy

@[to_additive]
theorem inv_smul_ae_eq_self (hs : (x • s : Set α) =ᵐ[μ] s) : (x⁻¹ • s : Set α) =ᵐ[μ] s :=
  inv_mem (s := MulAction.aestabilizer G μ s) hs

end MeasureTheory
