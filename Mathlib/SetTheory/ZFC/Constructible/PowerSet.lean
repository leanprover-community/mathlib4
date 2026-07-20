/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Bounding
public import Mathlib.SetTheory.ZFC.Constructible.Model

/-!
# The internal powerset axiom for the constructible universe

The ambient powerset of a constructible set need not itself be constructible.
The powerset computed by `L` contains exactly those ambient subsets which are
constructible.  We first bound all such subsets in one level and then define
the required collection over that level.
-/

@[expose] public section

open Set

universe u

namespace Constructible

section ZFC

/-- The ambient set collecting the constructible subsets of `a`. -/
def constructibleSubsetsZF (a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => x ∈ L) a.powerset

@[simp]
theorem mem_constructibleSubsetsZF_iff {a x : ZFSet.{u}} :
    x ∈ constructibleSubsetsZF a ↔ x ∈ L ∧ x ⊆ a := by
  simp [constructibleSubsetsZF, and_comm]

/--
Over a transitive carrier, the collection of its members which are subsets of
the parameter `a` is first-order definable over that carrier.
-/
theorem subsetSeparation_mem_DefZF {U a : ZFSet.{u}}
    (hU : U.IsTransitive) (ha : a ∈ U) :
    ZFSet.sep (fun x => x ⊆ a) U ∈ DefZF U := by
  rw [mem_DefZF_iff_exists_satisfies]
  let sa : ZFCarrier U := ⟨a, ha⟩
  let params : Tuple (ZFCarrier U) 1 := ![sa]
  let phi : FOFormula 2 :=
    .neg (.ex (.conj
      (.mem (2 : Fin 3) (1 : Fin 3))
      (.neg (.mem (2 : Fin 3) (0 : Fin 3)))))
  refine ⟨ZFSet.sep_subset, 1, params, phi, ?_⟩
  intro x
  simp only [ZFSet.mem_sep, phi, FOFormula.Satisfies]
  change (x.1 ∈ U ∧ x.1 ⊆ a) ↔
    ¬ ∃ z : ZFCarrier U, z.1 ∈ x.1 ∧ z.1 ∉ a
  rw [and_iff_right x.2]
  constructor
  · intro hxa ⟨z, hzx, hza⟩
    exact hza (hxa hzx)
  · intro hno z hzx
    by_contra hza
    exact hno ⟨⟨z, hU.mem_trans hzx x.2⟩, hzx, hza⟩

/--
The powerset axiom in its precise inner-model form.  The witness contains
exactly the constructible subsets of `a`.
-/
theorem exists_internalPowerset {a : ZFSet.{u}} (ha : a ∈ L) :
    ∃ b : ZFSet.{u}, b ∈ L ∧
      ∀ x : ZFSet.{u}, x ∈ b ↔ x ∈ L ∧ x ⊆ a := by
  have hconstructible :
      ∀ x ∈ constructibleSubsetsZF a, x ∈ L := by
    intro x hx
    exact (mem_constructibleSubsetsZF_iff.mp hx).1
  rcases exists_LStage_for_members hconstructible with ⟨alpha, halpha⟩
  let b : ZFSet.{u} :=
    ZFSet.sep (fun x => x ⊆ a) (LStageZF alpha)
  have haSubsets : a ∈ constructibleSubsetsZF a :=
    mem_constructibleSubsetsZF_iff.mpr ⟨ha, Set.Subset.rfl⟩
  have haStage : a ∈ LStageZF alpha := halpha a haSubsets
  have hbDef : b ∈ DefZF (LStageZF alpha) := by
    simpa only [b] using
      subsetSeparation_mem_DefZF (LStageZF_isTransitive alpha) haStage
  have hbL : b ∈ L := by
    refine ⟨Order.succ alpha, ?_⟩
    rw [LStageZF_succ]
    exact hbDef
  refine ⟨b, hbL, ?_⟩
  intro x
  constructor
  · intro hxb
    have hxStage : x ∈ LStageZF alpha := (ZFSet.mem_sep.mp hxb).1
    exact ⟨LStageZF_subset_constructibleUniverse alpha hxStage,
      (ZFSet.mem_sep.mp hxb).2⟩
  · rintro ⟨hxL, hxa⟩
    have hxSubsets : x ∈ constructibleSubsetsZF a :=
      mem_constructibleSubsetsZF_iff.mpr ⟨hxL, hxa⟩
    exact ZFSet.mem_sep.mpr ⟨halpha x hxSubsets, hxa⟩

/-- The powerset witness, packaged as an element of `Model.LCarrier`. -/
theorem Model.exists_powerSetLCarrier (a : Model.LCarrier.{u}) :
    ∃ b : Model.LCarrier.{u},
      ∀ x : Model.LCarrier.{u}, x.1 ∈ b.1 ↔ x.1 ⊆ a.1 := by
  rcases exists_internalPowerset a.2 with ⟨b, hbL, hb⟩
  refine ⟨⟨b, hbL⟩, ?_⟩
  intro x
  simpa only [x.2, true_and] using hb x.1

end ZFC

end Constructible
