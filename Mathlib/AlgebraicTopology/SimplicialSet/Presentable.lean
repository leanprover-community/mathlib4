/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import Mathlib.AlgebraicTopology.SimplicialSet.RegularEpi
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Presentable.Presheaf

/-!
# Finite simplicial sets are presentable

In this file, we show that finite simplicial sets are finitely presentable,
which will allow the use of the small object argument in `SSet`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial Limits Opposite

namespace SSet

namespace Finite

instance (n : SimplexCategory) :
    IsFinitelyPresentable.{u} (stdSimplex.{u}.obj n) :=
  inferInstanceAs (IsFinitelyPresentable.{u} (uliftYoneda.obj n))

lemma exists_epi_from_isCardinalPresentable (X : SSet.{u}) [X.Finite] :
    ∃ (Y : SSet.{u}) (_ : Y.Finite) (_ : IsFinitelyPresentable.{u} Y)
      (p : Y ⟶ X), Epi p := by
  refine ⟨∐ (fun (s : X.N) ↦ Δ[s.dim]), inferInstance, ?_,
    Sigma.desc (fun s ↦ yonedaEquiv.symm s.simplex), ?_⟩
  · apply +allowSynthFailures isCardinalPresentable_of_isColimit' _ (coproductIsCoproduct _)
    · exact hasCardinalLT_of_finite _ _ (by rfl)
    · rintro s
      dsimp
      infer_instance
  · simp only [← Subcomplex.range_eq_top_iff, range_eq_iSup_sigma_ι,
        colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, ← N.iSup_subcomplex_eq_top,
        Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]

instance (X : SSet.{u}) [X.Finite] : IsFinitelyPresentable.{u} X := by
  obtain ⟨Y, _, _, p, _⟩ := exists_epi_from_isCardinalPresentable X
  obtain ⟨Z, _, _, q, _⟩ := exists_epi_from_isCardinalPresentable (pullback p p)
  have := Cardinal.fact_isRegular_aleph0.{u}
  have := IsRegularEpiCategory.regularEpiOfEpi p
  apply +allowSynthFailures isCardinalPresentable_of_isColimit' _
      (isCoequalizerEpiComp ((EffectiveEpi.getStruct p).isColimitCoforkOfIsPullback
        (IsPullback.of_hasPullback p p)) q) _
  · exact hasCardinalLT_of_finite _ _ (by rfl)
  · rintro (_ | _) <;> dsimp <;> infer_instance

end Finite

end SSet
