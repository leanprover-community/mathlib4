/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic

/-!
# Inner fibrations

Inner fibrations of simplicial sets are the morphisms in `SSet` which have the right lifting
property with respect to all inner horn inclusions.

Basic consequences of inner fibrations with respect to the definition of quasi-categories are
formalized.

-/


@[expose] public section

open CategoryTheory MorphismProperty Simplicial

universe u

namespace SSet

/-- The family of morphisms in `SSet` which consists of inner horn inclusions
`Λ[n, i].ι : Λ[n, i] ⟶ Δ[n]` (for `0 < i < n`). -/
inductive innerHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 3)) (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    innerHornInclusions Λ[n + 2, i].ι

lemma horn_ι_mem_innerHornInclusions {n : ℕ} {i : Fin (n + 1)}
    (h0 : 0 < i) (hn : i < Fin.last n) : innerHornInclusions (horn.{u} n i).ι := by
  obtain _ | _ | k := n
  · grind
  · grind
  · exact ⟨i, h0, hn⟩

lemma innerHornInclusions_eq_iSup :
    innerHornInclusions.{u} =
    ⨆ n, .ofHoms (fun p : {p : Fin (n + 3) // 0 < p ∧ p < Fin.last (n + 2)} ↦ Λ[n + 2, p].ι) := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain @⟨n, i, h0, hn⟩ := h
    simp only [iSup_iff, ofHoms_iff, Subtype.exists, exists_prop]
    use n, i
  · simp only [iSup_iff, ofHoms_iff] at h
    obtain ⟨n, ⟨⟨i, h0, hn⟩, _, _⟩⟩ := h
    exact horn_ι_mem_innerHornInclusions h0 hn

lemma innerHornInclusions_le_J : innerHornInclusions.{u} ≤ modelCategoryQuillen.J :=
  fun _ _ _ ⟨_, _, _⟩ ↦ modelCategoryQuillen.horn_ι_mem_J ..

lemma innerHornInclusions_le_monomorphisms :
    innerHornInclusions.{u} ≤ monomorphisms SSet :=
  innerHornInclusions_le_J.trans modelCategoryQuillen.J_le_monomorphisms

/-- The inner fibrations are the morphisms which have the right lifting property
with respect to inner horn inclusions. -/
def innerFibrations : MorphismProperty SSet.{u} := innerHornInclusions.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange,
  IsStableUnderRetracts

/-- A morphism `q` satisfies `[InnerFibration q]` if it belongs to `innerFibrations`. -/
@[mk_iff]
class InnerFibration {X Y : SSet} (q : X ⟶ Y) : Prop where
  mem : innerFibrations q

lemma mem_innerFibrations {X Y : SSet} (q : X ⟶ Y) [InnerFibration q] : innerFibrations q :=
  InnerFibration.mem

lemma quasicategory_of_from_innerFibrations (S : SSet) {X : SSet} (t : Limits.IsTerminal X)
    (h : innerFibrations (t.from S)) : Quasicategory S :=
  quasicategory_of_hasLiftingProperty S t (fun h0 hn ↦ h _ (horn_ι_mem_innerHornInclusions h0 hn))

lemma Quasicategory.from_innerFibrations (S : SSet) [Quasicategory S]
    {X : SSet} (t : Limits.IsTerminal X) : innerFibrations (t.from S) :=
  fun _ _ _ ⟨_, h0, hn⟩ ↦ hasLiftingProperty S t h0 hn

@[kerodon 01BB]
lemma quasicategory_iff_from_innerFibration (S : SSet) {X : SSet} (t : Limits.IsTerminal X) :
    Quasicategory S ↔ InnerFibration (t.from S) :=
  ⟨fun _ ↦ ⟨Quasicategory.from_innerFibrations S t⟩,
    fun ⟨h⟩ ↦ quasicategory_of_from_innerFibrations S t h⟩

@[kerodon 01BJ]
lemma quasicategory_of_innerFibration_quasicategory {X Y : SSet} {q : X ⟶ Y} [Quasicategory Y]
    [InnerFibration q] : Quasicategory X := by
  rw [quasicategory_iff_from_innerFibration]
  constructor
  rw [Limits.terminalIsTerminal.hom_ext (Limits.terminalIsTerminal.from X)
    (q ≫ Limits.terminalIsTerminal.from Y)]
  exact comp_mem _ _ _ (mem_innerFibrations q) (Quasicategory.from_innerFibrations Y _)

end SSet
