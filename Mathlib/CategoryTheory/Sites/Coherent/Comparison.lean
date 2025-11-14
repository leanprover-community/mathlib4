/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.EffectiveEpi.Extensive
/-!

# Connections between the regular, extensive and coherent topologies

This file compares the regular, extensive and coherent topologies.

## Main results

* `instance : Precoherent C` given `Preregular C` and `FinitaryPreExtensive C`.

* `extensive_union_regular_generates_coherent`: the union of the regular and extensive coverages
  generates the coherent topology on `C` if `C` is precoherent, preextensive and preregular.
-/

namespace CategoryTheory

open Limits GrothendieckTopology Sieve

variable (C : Type*) [Category C]

instance [Precoherent C] [HasFiniteCoproducts C] : Preregular C where
  exists_fac {X Y Z} f g _ := by
    have hp := Precoherent.pullback f PUnit (fun () ↦ Z) (fun () ↦ g)
    simp only [exists_const] at hp
    rw [← effectiveEpi_iff_effectiveEpiFamily g] at hp
    obtain ⟨β, _, X₂, π₂, h, ι, hι⟩ := hp inferInstance
    refine ⟨∐ X₂, Sigma.desc π₂, inferInstance, Sigma.desc ι, ?_⟩
    ext b
    simpa using hι b

instance [FinitaryPreExtensive C] [Preregular C] : Precoherent C where
  pullback {B₁ B₂} f α _ X₁ π₁ h := by
    refine ⟨α, inferInstance, ?_⟩
    obtain ⟨Y, g, _, g', hg⟩ := Preregular.exists_fac f (Sigma.desc π₁)
    let X₂ := fun a ↦ pullback g' (Sigma.ι X₁ a)
    let π₂ := fun a ↦ pullback.fst g' (Sigma.ι X₁ a) ≫ g
    let π' := fun a ↦ pullback.fst g' (Sigma.ι X₁ a)
    have _ := FinitaryPreExtensive.isIso_sigmaDesc_fst (fun a ↦ Sigma.ι X₁ a) g' inferInstance
    refine ⟨X₂, π₂, ?_, ?_⟩
    · have : (Sigma.desc π' ≫ g) = Sigma.desc π₂ := by ext; simp [π₂, π']
      rw [← effectiveEpi_desc_iff_effectiveEpiFamily, ← this]
      infer_instance
    · refine ⟨id, fun b ↦ pullback.snd _ _, fun b ↦ ?_⟩
      simp only [X₂, π₂, id_eq, Category.assoc, ← hg]
      rw [← Category.assoc, pullback.condition]
      simp

/-- The union of the extensive and regular coverages generates the coherent topology on `C`. -/
theorem extensive_regular_generate_coherent [Preregular C] [FinitaryPreExtensive C] :
    ((extensiveCoverage C) ⊔ (regularCoverage C)).toGrothendieck =
    (coherentTopology C) := by
  ext B S
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · induction h with
    | of Y T hT =>
      apply Coverage.Saturate.of
      simp only [Coverage.sup_covering, Set.mem_union] at hT
      exact Or.elim hT
        (fun ⟨α, x, X, π, ⟨h, _⟩⟩ ↦ ⟨α, x, X, π, ⟨h, inferInstance⟩⟩)
        (fun ⟨Z, f, ⟨h, _⟩⟩ ↦ ⟨Unit, inferInstance, fun _ ↦ Z, fun _ ↦ f, ⟨h, inferInstance⟩⟩)
    | top => apply Coverage.Saturate.top
    | transitive Y T => apply Coverage.Saturate.transitive Y T<;> [assumption; assumption]
  · induction h with
    | of Y T hT =>
      obtain ⟨I, _, X, f, rfl, hT⟩ := hT
      apply Coverage.Saturate.transitive Y (generate (Presieve.ofArrows
        (fun (_ : Unit) ↦ (∐ fun (i : I) => X i)) (fun (_ : Unit) ↦ Sigma.desc f)))
      · apply Coverage.Saturate.of
        simp only [Coverage.sup_covering, extensiveCoverage, regularCoverage, Set.mem_union,
          Set.mem_setOf_eq]
        exact Or.inr ⟨_, Sigma.desc f, ⟨rfl, inferInstance⟩⟩
      · rintro R g ⟨W, ψ, σ, ⟨⟩, rfl⟩
        change _ ∈ ((extensiveCoverage C) ⊔ (regularCoverage C)).toGrothendieck R
        rw [Sieve.pullback_comp]
        apply pullback_stable
        have : generate (Presieve.ofArrows X fun (i : I) ↦ Sigma.ι X i) ≤
            (generate (Presieve.ofArrows X f)).pullback (Sigma.desc f) := by
          rintro Q q ⟨E, e, r, ⟨hq, rfl⟩⟩
          exact ⟨E, e, r ≫ (Sigma.desc f), by cases hq; simpa using Presieve.ofArrows.mk _, by simp⟩
        apply Coverage.saturate_of_superset _ this
        apply Coverage.Saturate.of
        refine Or.inl ⟨I, inferInstance, _, _, ⟨rfl, ?_⟩⟩
        convert IsIso.id _
        aesop
    | top => apply Coverage.Saturate.top
    | transitive Y T => apply Coverage.Saturate.transitive Y T<;> [assumption; assumption]

end CategoryTheory
