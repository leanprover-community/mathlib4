/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.AlgebraicTopology.Quasicategory.Basic

@[expose] public section

open CategoryTheory MorphismProperty Simplicial

universe u

namespace SSet

/-- The family of morphisms in `SSet` which consists of inner horn inclusions
`Λ[n, i].ι : Λ[n, i] ⟶ Δ[n]` (for `0 < i < n`). -/
def innerHornInclusions : MorphismProperty SSet.{u} :=
  .ofHoms (fun p : {p : (n : ℕ) × Fin (n + 3) // 0 < p.2 ∧ p.2 < Fin.last (p.1 + 2)} ↦
    Λ[p.1.1 + 2, p.1.2].ι)

lemma horn_ι_mem_innerHornInclusions {n : ℕ} {i : Fin (n + 3)}
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) : innerHornInclusions (horn.{u} (n + 2) i).ι :=
  .mk (⟨⟨n, i⟩, ⟨h0, hn⟩⟩ : {p : (n : ℕ) × Fin (n + 3) // 0 < p.2 ∧ p.2 < Fin.last (p.1 + 2)})

lemma innerHornInclusions_le_J : innerHornInclusions.{u} ≤ modelCategoryQuillen.J := by
  rintro _ _ _ ⟨⟩
  apply modelCategoryQuillen.horn_ι_mem_J

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
  fun _ _ _ ⟨⟨⟨n, i⟩, ⟨h0, hn⟩⟩⟩ ↦ Quasicategory.hasLiftingProperty S t h0 hn

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
