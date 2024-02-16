/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.Basic
/-!

# Connections between the regular, extensive and coherent topologies

This file compares the regular, extensive and coherent topologies.

## Main results

* `instance : Precoherent C` given `Preregular C` and `FinitaryPreExtensive C`.

* `extensive_union_regular_generates_coherent`: the union of the regular and extensive coverages
  generates the coherent topology on `C` if `C` is precoherent, preextensive and preregular.
-/

namespace CategoryTheory

open Limits

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

theorem effectiveEpi_desc_iff_effectiveEpiFamily [FinitaryPreExtensive C] {α : Type} [Finite α]
    {B : C} (X : α → C) (π : (a : α) → X a ⟶ B) :
    EffectiveEpi (Sigma.desc π) ↔ EffectiveEpiFamily X π := by
  exact ⟨fun h ↦ ⟨⟨@effectiveEpiFamilyStructOfEffectiveEpiDesc _ _ _ _ X π _ h _ _ (fun g ↦
    (FinitaryPreExtensive.sigma_desc_iso (fun a ↦ Sigma.ι X a) g inferInstance).epi_of_iso)⟩⟩,
    fun _ ↦ inferInstance⟩

instance [FinitaryPreExtensive C] [Preregular C] : Precoherent C where
  pullback {B₁ B₂} f α _ X₁ π₁ h := by
    refine ⟨α, inferInstance, ?_⟩
    obtain ⟨Y, g, _, g', hg⟩ := Preregular.exists_fac f (Sigma.desc π₁)
    let X₂ := fun a ↦ pullback g' (Sigma.ι X₁ a)
    let π₂ := fun a ↦ pullback.fst (f := g') (g := Sigma.ι X₁ a) ≫ g
    let π' := fun a ↦ pullback.fst (f := g') (g := Sigma.ι X₁ a)
    have _ := FinitaryPreExtensive.sigma_desc_iso (fun a ↦ Sigma.ι X₁ a) g' inferInstance
    refine ⟨X₂, π₂, ?_, ?_⟩
    · have : (Sigma.desc π' ≫ g) = Sigma.desc π₂ := by ext; simp
      rw [← effectiveEpi_desc_iff_effectiveEpiFamily, ← this]
      infer_instance
    · refine ⟨id, fun b ↦ pullback.snd, fun b ↦ ?_⟩
      simp only [id_eq, Category.assoc, ← hg]
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
      apply Coverage.saturate.of
      simp only [Coverage.sup_covering, Set.mem_union] at hT
      refine Or.elim hT
        (fun ⟨α, x, X, π, h, ⟨hc⟩⟩ ↦ ⟨α, x, X, π, h, ?_⟩)
        (fun ⟨Z, f, ⟨h, _⟩⟩ ↦ ⟨Unit, inferInstance, fun _ ↦ Z, fun _ ↦ f, ⟨h, inferInstance⟩⟩)
      have : IsIso (Sigma.desc π) := Cofan.isIsoSigmaDesc_of_isCoproduct _ hc
      infer_instance
    | top => apply Coverage.saturate.top
    | transitive Y T => apply Coverage.saturate.transitive Y T<;> [assumption; assumption]
  · induction h with
    | of Y T hT =>
      obtain ⟨I, hI, X, f, ⟨h, hT⟩⟩ := hT
      let φ := fun (i : I) ↦ Sigma.ι X i
      let F := Sigma.desc f
      let Z := Sieve.generate T
      let Xs := (∐ fun (i : I) => X i)
      let Zf := Sieve.generate (Presieve.ofArrows (fun (_ : Unit) ↦ Xs) (fun (_ : Unit) ↦ F))
      apply Coverage.saturate.transitive Y Zf
      · apply Coverage.saturate.of
        simp only [Coverage.sup_covering, extensiveCoverage, regularCoverage, Set.mem_union,
          Set.mem_setOf_eq]
        exact Or.inr ⟨Xs, F, ⟨rfl, inferInstance⟩⟩
      · intro R g hZfg
        dsimp at hZfg
        rw [Presieve.ofArrows_pUnit] at hZfg
        obtain ⟨W, ψ, σ, ⟨hW, hW'⟩⟩ := hZfg
        induction hW
        rw [← hW', Sieve.pullback_comp Z]
        suffices Sieve.pullback ψ ((Sieve.pullback F) Z) ∈ GrothendieckTopology.sieves
          ((extensiveCoverage C) ⊔ (regularCoverage C)).toGrothendieck R by assumption
        apply GrothendieckTopology.pullback_stable'
        suffices Coverage.saturate ((extensiveCoverage C) ⊔ (regularCoverage C)) Xs
          (Z.pullback F) by assumption
        suffices : Sieve.generate (Presieve.ofArrows X φ) ≤ Z.pullback F
        · apply Coverage.saturate_of_superset _ this
          apply Coverage.saturate.of
          simp only [Coverage.sup_covering, extensiveCoverage, regularCoverage, Set.mem_union,
            Set.mem_setOf_eq]
          refine Or.inl ⟨I, hI, X, φ, rfl, ⟨coproductIsCoproduct _⟩⟩
        intro Q q hq
        simp only [Sieve.pullback_apply, Sieve.generate_apply]
        simp only [Sieve.generate_apply] at hq
        obtain ⟨E, e, r, hq⟩ := hq
        refine' ⟨E, e, r ≫ F, ⟨_, _⟩⟩
        · rw [h]
          induction hq.1
          simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
          exact Presieve.ofArrows.mk _
        · rw [← hq.2]
          simp only [Category.assoc]
    | top => apply Coverage.saturate.top
    | transitive Y T => apply Coverage.saturate.transitive Y T<;> [assumption; assumption]
