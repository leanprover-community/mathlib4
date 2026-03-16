/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
--public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono


/-!
# Torsion Theory

A **torsion theory** on an abelian category `C` is a pair of classes `T` and `F` of objects from `C`
such that
(i) For all `X : T` and `Y : F`, `Hom(X,Y) = 0`.
(ii) For all `X : C`, if for all `Y : F`, `Hom(X,Y) = 0`, then `X : T`.
(iii) For all `Y : C`, if for all `X : T`, `Hom(X,Y0 = 0`, then `X : F`.
We call `T` the *torsion class* and its objects *torsion objects*.  We call `F` the
*torsion-free class* and its objects *torsion-free objects*

## Main definitions

* `TorsionTheory C`: The type of a torsion theory on `C`.

## References

* [Bo Stenström, *Rings and Modules of Quotients*][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category theory, preradical, torsion theory
-/

@[expose] public section

universe v u u' v'

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A Torsion Theory in an abelian category consists of two classes, `T` and `F`, of
torsion and torsion-free objects, respectively, such that `T` is the left orthogonal
of `F` and `F` is the right orthogonal of `T`. -/
class TorsionTheory (T F : ObjectProperty C) : Prop where
  T_leftOrthogonal : T ≤ F.leftOrthogonal
  F_rightOrthogonal : F ≤ T.rightOrthogonal
  le_leftOrthogonal : F.leftOrthogonal ≤ T
  le_rightOrthogonal : T.rightOrthogonal ≤ F

namespace TorsionTheory

lemma torsion_eq_leftOrthogonal (T F : ObjectProperty C) [TorsionTheory T F] :
    T = F.leftOrthogonal :=
  le_antisymm T_leftOrthogonal le_leftOrthogonal

lemma free_eq_rightOrthogonal (T F : ObjectProperty C) [TorsionTheory T F] :
    F = T.rightOrthogonal :=
  le_antisymm F_rightOrthogonal le_rightOrthogonal

lemma mem_torsion_iff {X : C} (T F : ObjectProperty C) [TorsionTheory T F] :
    T X ↔ F.leftOrthogonal X := by
  simp [torsion_eq_leftOrthogonal T F]

lemma mem_free_iff {X : C} (T F : ObjectProperty C) [TorsionTheory T F] :
    F X ↔ T.rightOrthogonal X := by
  simp [free_eq_rightOrthogonal (T := T) (F := F)]

example (T F : ObjectProperty C) [TorsionTheory T F] (X : C) :
    T X ↔ (∀ {Y : C}, ∀ f : X ⟶ Y, F Y → f = 0) := by
  simpa [torsion_eq_leftOrthogonal T F] using ObjectProperty.leftOrthogonal_iff F X

example (T F : ObjectProperty C) [TorsionTheory T F] (Y : C) :
    F Y ↔  (∀ {X : C}, ∀ f : X ⟶ Y, T X → f = 0) := by
  simpa [free_eq_rightOrthogonal T F] using ObjectProperty.rightOrthogonal_iff T Y

lemma torsion_of_epi (T F : ObjectProperty C) [TorsionTheory T F]
    {X Y : C} (hX : T X)
    (f : X ⟶ Y) [Epi f] : T Y := by
  apply (mem_torsion_iff T F).mpr
  intro Z g hZ
  have hfg : f ≫ g = 0 := ((mem_torsion_iff T F).mp hX (f ≫ g) hZ)
  exact Limits.zero_of_epi_comp f hfg

/- /-- Given a class, `P`, of objects in `C`, define its free closure to be the the right orthogonal
to `P`. -/
abbrev freeClosure (P : ObjectProperty C) : ObjectProperty C := P.rightOrthogonal

/-- Given a class, `P`, of objects in `C`, define its torsion closure to be the left orthogonal of
the free closure. -/
def torsionClosure (P : ObjectProperty C) : ObjectProperty C := (freeClosure P).leftOrthogonal -/

instance instTorsionTheoryGeneratedBy (P : ObjectProperty C) :
    TorsionTheory P.rightOrthogonal.leftOrthogonal P.rightOrthogonal where
  T_leftOrthogonal :=
    le_refl P.rightOrthogonal.leftOrthogonal
  F_rightOrthogonal := by
    intro F hF
    exact
      (ObjectProperty.rightOrthogonal_iff P.rightOrthogonal.leftOrthogonal F).mpr
        fun X f a ↦ a f hF
  le_leftOrthogonal := by
    intro T hT
    exact (ObjectProperty.leftOrthogonal_iff P.rightOrthogonal T).mpr hT
  le_rightOrthogonal := by
    intro F hF
    apply (P.rightOrthogonal_iff F).mpr
    intro X f hX
    apply ((P.rightOrthogonal.leftOrthogonal).rightOrthogonal_iff F).mp hF f
    exact (ObjectProperty.leftOrthogonal_iff P.rightOrthogonal X).mpr fun Y f a ↦ a f hX

instance instTorsionTheoryCogeneratedBy (P : ObjectProperty C) :
    TorsionTheory P.leftOrthogonal P.leftOrthogonal.rightOrthogonal where
      T_leftOrthogonal := by
        intro T hT
        apply ((P.leftOrthogonal.rightOrthogonal).leftOrthogonal_iff T).mpr
        intro Y f hY
        exact hY f hT
      F_rightOrthogonal :=
        le_refl P.leftOrthogonal.rightOrthogonal
      le_leftOrthogonal := by
        intro F hF
        apply (P.leftOrthogonal_iff F).mpr
        intro Y f hY
        apply ((P.leftOrthogonal.rightOrthogonal).leftOrthogonal_iff F).mp hF f
        exact (ObjectProperty.rightOrthogonal_iff P.leftOrthogonal Y).mpr fun X f a ↦ a f hY
      le_rightOrthogonal := by
        exact ObjectProperty.le_def.mpr fun X a ↦ a

theorem isTorsionClass_iff {T : ObjectProperty C} : (∃ F : ObjectProperty C, TorsionTheory T F) ↔
    (T.IsClosedUnderQuotients ∧ T.IsClosedUnderExtensions ∧
    ∀ {J : Type u}, T.IsClosedUnderColimitsOfShape (Discrete J)) := by
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨?quotients, ?extensions, ?coproducts⟩
    · refine { prop_of_epi := ?_ }
      intro X Y f hEpif hTX
      exact torsion_of_epi T F hTX f
    · refine { prop_X₂_of_shortExact := ?_ }
      intro S hs hX₁ hX₃
      apply (mem_torsion_iff T F).mpr
      intro Z k hZ
      let t : Limits.CokernelCofork S.f :=
        Limits.CokernelCofork.ofπ k  ((mem_torsion_iff T F).mp hX₁ (S.f ≫ k) hZ)
      let l : S.X₃ ⟶ Z := hs.gIsCokernel.desc t
      have hl: l = 0 := (mem_free_iff T F).mp hZ l hX₃
      have hfac : S.g ≫ l = k :=
        hs.gIsCokernel.fac t Limits.WalkingParallelPair.one
      simp [← hfac, hl]
    · intro J
      refine { colimitsOfShape_le := ?_}
      intro X ⟨hX⟩
      apply (mem_torsion_iff T F).mpr
      intro Y f hY
      apply hX.isColimit.hom_ext
      intro j
      simpa [Limits.comp_zero] using
        (mem_torsion_iff T F).mp (hX.prop_diag_obj j) (hX.ι.app j ≫ f) hY
  · rintro ⟨hquot, hext, hcoprod⟩
    refine ⟨T.leftOrthogonal.rightOrthogonal, ?_⟩
    refine
      { T_leftOrthogonal := ?_, F_rightOrthogonal := ?_, le_leftOrthogonal := ?_,
        le_rightOrthogonal := ?_ }
    · intro X hX Y f hY

      sorry
    · sorry
    · sorry
    · sorry

end TorsionTheory

end CategoryTheory.Abelian
#lint
