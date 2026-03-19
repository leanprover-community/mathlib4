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
such that `T` is the left orthogonal of `F` and `F` is the right orthogonal of `T`. We call `T`
the *torsion class* and its objects *torsion objects*.  We call `F` the *torsion-free class*
and its objects *torsion-free objects*.

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
structure TorsionTheory (T F : ObjectProperty C) : Prop where
  torsion_eq_leftOrthogonal : T = F.leftOrthogonal
  free_eq_rightOrthogonal : F = T.rightOrthogonal
  /- T_leftOrthogonal : T ≤ F.leftOrthogonal
  F_rightOrthogonal : F ≤ T.rightOrthogonal
  le_leftOrthogonal : F.leftOrthogonal ≤ T
  le_rightOrthogonal : T.rightOrthogonal ≤ F
 -/
namespace TorsionTheory

lemma mem_torsion_iff {X : C} {T F : ObjectProperty C} (hTF : TorsionTheory T F) :
    T X ↔ F.leftOrthogonal X := by
  simp [hTF.torsion_eq_leftOrthogonal]

lemma mem_free_iff {X : C} (T F : ObjectProperty C) (hTF : TorsionTheory T F) :
    F X ↔ T.rightOrthogonal X := by
  simp [hTF.free_eq_rightOrthogonal]

example (T F : ObjectProperty C) (hTF : TorsionTheory T F) (X : C) :
    T X ↔ (∀ {Y : C}, ∀ f : X ⟶ Y, F Y → f = 0) := by
  simpa [hTF.torsion_eq_leftOrthogonal] using ObjectProperty.leftOrthogonal_iff F X

example (T F : ObjectProperty C) (hTF : TorsionTheory T F) (Y : C) :
    F Y ↔  (∀ {X : C}, ∀ f : X ⟶ Y, T X → f = 0) := by
  simpa [hTF.free_eq_rightOrthogonal] using ObjectProperty.rightOrthogonal_iff T Y

lemma torsion_of_epi {T F : ObjectProperty C} (hTF : TorsionTheory T F)
    {X Y : C} (hX : T X)
    (f : X ⟶ Y) [Epi f] : T Y := by
  apply hTF.mem_torsion_iff.mpr
  intro Z g hZ
  have hfg : f ≫ g = 0 := (hTF.mem_torsion_iff.mp hX (f ≫ g) hZ)
  exact Limits.zero_of_epi_comp f hfg

/- /-- Given a class, `P`, of objects in `C`, define its free closure to be the the right orthogonal
to `P`. -/
abbrev freeClosure (P : ObjectProperty C) : ObjectProperty C := P.rightOrthogonal

/-- Given a class, `P`, of objects in `C`, define its torsion closure to be the left orthogonal of
the free closure. -/
def torsionClosure (P : ObjectProperty C) : ObjectProperty C := (freeClosure P).leftOrthogonal -/

instance instTorsionTheoryGeneratedBy (P : ObjectProperty C) :
    TorsionTheory P.rightOrthogonal.leftOrthogonal P.rightOrthogonal where
      torsion_eq_leftOrthogonal := by
        refine le_antisymm (le_refl P.rightOrthogonal.leftOrthogonal) ?_
        intro F hF
        exact (ObjectProperty.leftOrthogonal_iff P.rightOrthogonal F).mpr hF
      free_eq_rightOrthogonal := by
        refine le_antisymm ?_ ?_
        · intro F hF
          exact
            (ObjectProperty.rightOrthogonal_iff P.rightOrthogonal.leftOrthogonal F).mpr
              fun X f a ↦ a f hF
        · intro F hF
          apply (P.rightOrthogonal_iff F).mpr
          intro X f hX
          apply ((P.rightOrthogonal.leftOrthogonal).rightOrthogonal_iff F).mp hF f
          exact (ObjectProperty.leftOrthogonal_iff P.rightOrthogonal X).mpr fun Y f a ↦ a f hX

instance instTorsionTheoryCogeneratedBy (P : ObjectProperty C) :
    TorsionTheory P.leftOrthogonal P.leftOrthogonal.rightOrthogonal where
      torsion_eq_leftOrthogonal := by
        refine le_antisymm ?_ ?_
        · intro T hT
          apply ((P.leftOrthogonal.rightOrthogonal).leftOrthogonal_iff T).mpr
          intro Y f hY
          exact hY f hT
        · intro F hF
          apply (P.leftOrthogonal_iff F).mpr
          intro Y f hY
          apply ((P.leftOrthogonal.rightOrthogonal).leftOrthogonal_iff F).mp hF f
          exact (ObjectProperty.rightOrthogonal_iff P.leftOrthogonal Y).mpr fun X f a ↦ a f hY
      free_eq_rightOrthogonal := by
        refine le_antisymm (le_refl P.leftOrthogonal.rightOrthogonal) ?_
        intro F hF
        exact (ObjectProperty.rightOrthogonal_iff P.leftOrthogonal F).mpr hF

theorem isTorsionClass_iff {P : ObjectProperty C} : (∃ F : ObjectProperty C, TorsionTheory P F) ↔
    (P.IsClosedUnderQuotients ∧ P.IsClosedUnderExtensions ∧
    ∀ {J : Type u}, P.IsClosedUnderColimitsOfShape (Discrete J)) := by
  constructor
  · rintro ⟨F, hPF⟩
    refine ⟨?quotients, ?extensions, ?coproducts⟩
    · refine { prop_of_epi := ?_ }
      intro X Y f hEpif hPX
      exact hPF.torsion_of_epi hPX f
    · refine { prop_X₂_of_shortExact := ?_ }
      intro S hs hX₁ hX₃
      apply hPF.mem_torsion_iff.mpr
      intro Z k hZ
      let t : Limits.CokernelCofork S.f :=
        Limits.CokernelCofork.ofπ k  (hPF.mem_torsion_iff.mp hX₁ (S.f ≫ k) hZ)
      let l : S.X₃ ⟶ Z := hs.gIsCokernel.desc t
      have hl: l = 0 := hPF.mem_free_iff.mp hZ l hX₃
      have hfac : S.g ≫ l = k :=
        hs.gIsCokernel.fac t Limits.WalkingParallelPair.one
      simp [← hfac, hl]
    · intro J
      refine { colimitsOfShape_le := ?_}
      intro X ⟨hX⟩
      apply hPF.mem_torsion_iff.mpr
      intro Y f hY
      apply hX.isColimit.hom_ext
      intro j
      simpa [Limits.comp_zero] using
        hPF.mem_torsion_iff.mp (hX.prop_diag_obj j) (hX.ι.app j ≫ f) hY
  · rintro ⟨hquot, hext, hcoprod⟩
    refine ⟨P.leftOrthogonal.rightOrthogonal, ?_⟩
    refine { torsion_eq_leftOrthogonal := ?_, free_eq_rightOrthogonal := ?_ }
    · sorry
    · sorry

end TorsionTheory

end CategoryTheory.Abelian
