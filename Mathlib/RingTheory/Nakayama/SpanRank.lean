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
The span rank of the `R`-submodule `N / (I • N)` of `M / (I • N)`
is equal to the span rank of an `R`-submodule `N` of `M`,
provided that `N` is finitely generated and `I` is contained in the Jacobson radical of `R`.

Here `N / (I • N)` is the image of `N` under the `R`-module quotient map `M → M / (I • N)`.
-/
theorem spanRank_map_mkQ_of_le_jacobson_bot_eq
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG) (hIjac : I ≤ Ideal.jacobson ⊥) :
    (map (I • N).mkQ N).spanRank = N.spanRank := by
  apply le_antisymm
  · apply spanRank_map_le
  · obtain ⟨s, hscard, hsspan⟩ := exists_span_set_card_eq_spanRank (map (I • N).mkQ N)
    obtain ⟨t, hinj, heq, htspan⟩ :=
      exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot s hN hIjac hsspan
    rw [FG.spanRank_le_iff_exists_span_set_card_le]
    refine ⟨t, ?_, htspan⟩
    rw [← hscard, ← heq]
    exact (Cardinal.mk_image_eq_of_injOn _ _ hinj).ge

/--
The span rank of the `R`-module `N / (I • N)`
is equal to the span rank of an `R`-submodule `N` of `M`,
provided that `N` is finitely generated and `I` is contained in the Jacobson radical of `R`.

Here `N / (I • N)` is obtained by directly taking the quotient of `N` by the its submodule `I • ⊤`.
-/
theorem spanRank_quotientIdealSubmodule_eq
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG) (hIjac : I ≤ Ideal.jacobson ⊥) :
    (⊤ : Submodule R (N ⧸ (I • ⊤ : Submodule R N))).spanRank = N.spanRank := by
  rw [← spanRank_map_mkQ_of_le_jacobson_bot_eq hN hIjac,
    spanRank_eq_of_equiv <| quotientIdealSubmoduleEquivMap N I, spanRank_top]

/--
The span rank of the `R / I`-module `N / (I • N)`
is equal to the span rank of an `R`-submodule `N` of `M`,
provided that `N` is finitely generated and `I` is contained in the Jacobson radical of `R`.

Here `N / (I • N)` is obtained by directly taking the quotient of `N` by the its submodule `I • ⊤`.
-/
theorem spanRank_quotient_ideal_quotientIdealSubmodule_eq
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG) (hIjac : I ≤ Ideal.jacobson ⊥) :
    (⊤ : Submodule (R ⧸ I) (N ⧸ (I • ⊤ : Submodule R N))).spanRank = N.spanRank := by
  rw [← spanRank_quotientIdealSubmodule_eq hN hIjac]
  refine (spanRank_restrictScalars_eq ?_ ⊤).symm
  exact Ideal.Quotient.mk_surjective

end Submodule
