/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
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

-- to be moved
/-- Let `p : Y ⟶ X` be an effective epimorphism, `p₁ : Z ⟶ Y` and `p₂ : Z ⟶ Y` two
morphisms which make `Z` the pullback of two copies of `Y` over `X`, let `q : W ⟶ Z` be an
epimorphism. Then, `X` is the coequalizer of `q ≫ p₁` and `q ≫ p₂`. -/
noncomputable def isCoequalizerOfEpiOfIsPullback {C : Type*} [Category C]
    {X Y Z : C} {p : Y ⟶ X} {p₁ p₂ : Z ⟶ Y} [EffectiveEpi p]
    (sq : IsPullback p₁ p₂ p p) {W : C} (q : W ⟶ Z) [Epi q] :
    IsColimit (Cofork.ofπ (f := q ≫ p₁) (g := q ≫ p₂) p (by simp only [Category.assoc, sq.w])) :=
  Cofork.IsColimit.mk _ (fun s ↦ (EffectiveEpi.getStruct p).desc s.π (fun {T} g₁ g₂ h ↦ by
      obtain ⟨l, rfl, rfl⟩ : ∃ l, l ≫ p₁ = g₁ ∧ l ≫ p₂ = g₂ :=
        ⟨sq.lift g₁ g₂ h, by simp, by simp⟩
      have := s.condition
      simp only [Category.assoc, cancel_epi] at this
      simp [this]))
    (fun s ↦ EffectiveEpiStruct.fac _ _ _)
    (fun s m hm ↦ by
      dsimp at hm
      rw [← cancel_epi p, hm, EffectiveEpiStruct.fac])

-- to be moved
namespace FunctorToTypes

variable {J : Type*} [Category J] {Y X : J ⥤ Type u} (p : Y ⟶ X) [Epi p]

namespace effectiveEpiStructOfEpi

variable {T : J ⥤ Type u} (f : Y ⟶ T)
  (hf : ∀ {Z : J ⥤ Type u} (g₁ g₂ : Z ⟶ Y),
    g₁ ≫ p = g₂ ≫ p → g₁ ≫ f = g₂ ≫ f)

lemma surjective_app {j : J} :
    Function.Surjective (p.app j) := by
  rw [← epi_iff_surjective]
  infer_instance

variable {p}

include hf in
lemma exists_image {j : J} (x : X.obj j) :
    ∃ (t : T.obj j), ∀ (y : Y.obj j), p.app _ y = x → f.app _ y = t := by
  obtain ⟨y₀, rfl⟩ := surjective_app p x
  refine ⟨f.app _ y₀, fun y hy ↦ ?_⟩
  obtain ⟨z, rfl, rfl⟩ := Types.exists_of_isPullback
    ((IsPullback.of_hasPullback p p).map ((evaluation _ _).obj j)) y y₀ hy
  exact congr_fun (congr_app (hf _ _ pullback.condition) j) z

/-- Auxiliary definition for `FunctorToTypes.effectiveEpiStructOfEpi`. -/
noncomputable def descApp (j : J) : X.obj j ⟶ T.obj j :=
  fun x ↦ (exists_image f hf x).choose

lemma descApp_eq {j : J} (y : Y.obj j) :
    descApp f hf j (p.app _ y) = f.app _ y :=
  ((exists_image f hf (p.app _ y)).choose_spec _ rfl).symm

/-- Auxiliary definition for `FunctorToTypes.effectiveEpiStructOfEpi`. -/
@[simps]
noncomputable def desc : X ⟶ T where
  app := descApp f hf
  naturality j₁ j₂ φ := by
    ext x
    obtain ⟨y, rfl⟩ := surjective_app p x
    dsimp
    rw [descApp_eq, ← FunctorToTypes.naturality, descApp_eq,
      FunctorToTypes.naturality]

end effectiveEpiStructOfEpi

open effectiveEpiStructOfEpi in
/-- In a category of functors to types, epimorphisms are effective. -/
noncomputable def effectiveEpiStructOfEpi : EffectiveEpiStruct p where
  desc f hf := desc f hf
  fac f hf := by
    ext j y
    exact descApp_eq f hf y
  uniq f hf l hl := by
    ext j x
    dsimp
    obtain ⟨y, rfl⟩ := surjective_app p x
    rw [descApp_eq, ← hl]
    rfl

lemma effectiveEpi_of_epi : EffectiveEpi p where
  effectiveEpi := ⟨effectiveEpiStructOfEpi p⟩

end FunctorToTypes

end CategoryTheory

namespace SSet

attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace Finite

-- to be moved
instance (X : Type*) [Finite X] : Finite (Arrow (Discrete X)) :=
  Finite.of_equiv _ (Arrow.discreteEquiv X).symm

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
  · apply (config := { allowSynthFailures := true})
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
  have ip := isCoequalizerOfEpiOfIsPullback (IsPullback.of_hasPullback p p) q
  apply (config := { allowSynthFailures := true})
    isCardinalPresentable_of_isColimit' _
      (isCoequalizerOfEpiOfIsPullback (IsPullback.of_hasPullback p p) q) _
  · exact hasCardinalLT_of_finite _ _ (by rfl)
  · rintro (_ | _) <;> dsimp <;> infer_instance

end Finite

end SSet
