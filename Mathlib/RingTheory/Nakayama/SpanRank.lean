/-
Copyright (c) 2025 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Mathlib.RingTheory.Nakayama.Basic
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Nakayama's lemma and `Submodule.spanRank`

This file states some versions of Nakayama's lemma in terms of `Submodule.spanRank`.
-/

@[expose] public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Submodule

theorem spanRank_eq_spanRank_map_mkQ_of_le_jacobson_bot
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG) (hIjac : I ≤ Ideal.jacobson ⊥) :
    N.spanRank = (map (I • N).mkQ N).spanRank := by
  have smul_sup_eq : I • N ⊔ N = N := by rw [sup_eq_right]; exact smul_le_right
  apply le_antisymm
  · rcases exists_span_set_card_eq_spanRank (map (I • N).mkQ N) with ⟨s, ⟨hscard, hsspan⟩⟩
    have hs_subset : s ⊆ map (I • N).mkQ N := by rw [← hsspan]; exact subset_span
    -- pull back `s` from N / I to N to get a spanning set of N
    let pbv := fun (y : M ⧸ I • N) ↦ Classical.choose <|
      Set.Nonempty.preimage (Set.singleton_nonempty y) (mkQ_surjective (I • N))
    let pbp := fun (y : M ⧸ I • N) ↦ Classical.choose_spec <|
      Set.Nonempty.preimage (Set.singleton_nonempty y) (mkQ_surjective (I • N))
    have mkQ_comp_pbv_cancel : (I • N).mkQ  ∘ pbv = id := by funext y; exact pbp y
    -- show the inequality via the pulled back set
    rw [FG.spanRank_le_iff_exists_span_set_card_le]
    use pbv '' s
    constructor
    · rw [← hscard]
      apply Cardinal.mk_image_le
    · apply le_antisymm
      · rw [span_le]; grw [hs_subset]
        have := comap_map_mkQ (I • N) N; rw [smul_sup_eq] at this
        -- obtain a set version of `Submodule.comap_map_mkQ`
        apply_fun fun x ↦ (x : Set M) at this
        rw [comap_coe, map_coe] at this
        -- return to the goal
        rw [← this, ← Set.image_subset_iff, ← Set.image_comp, mkQ_comp_pbv_cancel]
        simp
      · apply le_span_of_map_mkQ_le_map_mkQ_span_of_le_jacobson_bot hN hIjac
        rw [map_span, ← Set.image_comp, mkQ_comp_pbv_cancel]
        simp [hsspan]
  · exact spanRank_le_spanRank_of_map_eq (mkQ (I • N)) (by dsimp)

theorem spanRank_eq_spanRank_quotientIdealSubmodule
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG) (hIjac : I ≤ Ideal.jacobson ⊥) :
    N.spanRank = (⊤ : Submodule R (N ⧸ (I • ⊤ : Submodule R N))).spanRank := by
  rw [spanRank_eq_spanRank_map_mkQ_of_le_jacobson_bot hN hIjac]
  apply spanRank_eq_spanRank_of_equiv
  symm
  exact LinearEquiv.trans
    (Submodule.topEquiv : _ ≃ₗ[R] (N ⧸ (I • ⊤ : Submodule R N)))
    (quotientIdealSubmoduleEquivMap N I)

theorem spanRank_eq_spanRank_quotient_ideal_quotientIdealSubmodule
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG) (hIjac : I ≤ Ideal.jacobson ⊥) :
    N.spanRank = (⊤ : Submodule (R ⧸ I) (N ⧸ (I • ⊤ : Submodule R N))).spanRank := by
  rw [spanRank_eq_spanRank_quotientIdealSubmodule hN hIjac]
  exact spanRank_eq_spanRank_of_addEquiv (Ideal.Quotient.mk I)
    (LinearEquiv.toAddEquiv (LinearEquiv.refl R _)) (by intros; rfl)

end Submodule
