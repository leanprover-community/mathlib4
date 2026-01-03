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

/--
The span rank of an `R`-submodule `N` of `M` is equal to
the span rank of the `R`-submodule `N / (I • N)` of `M / (I • N)`,
provided that `N` is finitely generated and `I` is contained in the Jacobson radical of `R`.

Here `N / (I • N)` is the image of `N` under the `R`-module quotient map `M → M / (I • N)`.
-/
theorem spanRank_eq_spanRank_map_mkQ_of_le_jacobson_bot
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG) (hIjac : I ≤ Ideal.jacobson ⊥) :
    N.spanRank = (map (I • N).mkQ N).spanRank := by
  apply le_antisymm
  · rcases exists_span_set_card_eq_spanRank (map (I • N).mkQ N) with ⟨s, ⟨hscard, hsspan⟩⟩
    rcases exists_set_equiv_eq_mkQ_span_of_span_eq_map_mkQ_of_le_jacobson_bot
      s hN hIjac hsspan with ⟨t, e, heq, htspan⟩
    rw [FG.spanRank_le_iff_exists_span_set_card_le]
    use t, (by rw [← hscard, Equiv.cardinal_eq]; exact e), htspan
  · exact spanRank_le_spanRank_of_map_eq (mkQ (I • N)) (by dsimp)

/--
The span rank of an `R`-submodule `N` of `M` is equal to
the span rank of the `R`-module `N / (I • N)`,
provided that `N` is finitely generated and `I` is contained in the Jacobson radical of `R`.

Here `N / (I • N)` is obtained by directly taking the quotient of `N` by the its submodule `I • ⊤`.
-/
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

/--
The span rank of an `R`-submodule `N` of `M` is equal to
the span rank of the `R / I`-module `N / (I • N)`,
provided that `N` is finitely generated and `I` is contained in the Jacobson radical of `R`.

Here `N / (I • N)` is obtained by directly taking the quotient of `N` by the its submodule `I • ⊤`.
-/
theorem spanRank_eq_spanRank_quotient_ideal_quotientIdealSubmodule
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG) (hIjac : I ≤ Ideal.jacobson ⊥) :
    N.spanRank = (⊤ : Submodule (R ⧸ I) (N ⧸ (I • ⊤ : Submodule R N))).spanRank := by
  rw [spanRank_eq_spanRank_quotientIdealSubmodule hN hIjac]
  exact spanRank_eq_spanRank_of_addEquiv (Ideal.Quotient.mk I)
    (LinearEquiv.toAddEquiv (LinearEquiv.refl R _)) (by intros; rfl)

end Submodule
