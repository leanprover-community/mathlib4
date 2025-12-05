/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import Mathlib.CategoryTheory.EffectiveEpi.Coequalizer
public import Mathlib.CategoryTheory.EffectiveEpi.FunctorToTypes
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Presentable.Limits

/-!
# Finite simplicial sets are presentable

In this file, we show that finite simplicial sets are `ℵ₀`-presentable,
which will allow the use of the small object argument in `SSet`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial Limits Opposite

namespace CategoryTheory

end CategoryTheory

namespace SSet

attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace Finite

instance (n : SimplexCategory) :
    IsCardinalPresentable (stdSimplex.{u}.obj n) Cardinal.aleph0.{u} where
  preservesColimitOfShape J _ _ := by
    let e : coyoneda.obj (op (stdSimplex.{u}.obj n)) ≅ (evaluation _ _).obj (op n) :=
      NatIso.ofComponents (fun X ↦ yonedaEquiv.toIso)
    apply preservesColimitsOfShape_of_natIso e.symm

lemma exists_epi_from_isCardinalPresentable (X : SSet.{u}) [X.Finite] :
    ∃ (Y : SSet.{u}) (_ : Y.Finite ) (_ : IsCardinalPresentable Y Cardinal.aleph0.{u})
      (p : Y ⟶ X), Epi p := by
  refine ⟨∐ (fun (s : X.N) ↦ Δ[s.dim]), inferInstance, ?_,
    Sigma.desc (fun s ↦ yonedaEquiv.symm s.simplex), ?_⟩
  · apply (config := { allowSynthFailures := true })
      isCardinalPresentable_of_isColimit' _ (coproductIsCoproduct _)
    · exact hasCardinalLT_of_finite _ _ (by rfl)
    · rintro s
      dsimp
      infer_instance
  · simp only [← Subcomplex.range_eq_top_iff, range_eq_iSup_sigma_ι,
        colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, ← N.iSup_subcomplex_eq_top,
        Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]

instance (X : SSet.{u}) [X.Finite] : IsCardinalPresentable X (Cardinal.aleph0.{u}) := by
  obtain ⟨Y, _, _, p, _⟩ := exists_epi_from_isCardinalPresentable X
  obtain ⟨Z, _, _, q, _⟩ := exists_epi_from_isCardinalPresentable (pullback p p)
  have := FunctorToTypes.effectiveEpi_of_epi p
  apply (config := { allowSynthFailures := true })
    isCardinalPresentable_of_isColimit' _
      ((EffectiveEpi.getStruct p).isColimitCoforkOfEpiOfIsPullback
    (IsPullback.of_hasPullback p p) q) _
  · exact hasCardinalLT_of_finite _ _ (by rfl)
  · rintro (_ | _) <;> dsimp <;> infer_instance

end Finite

end SSet
