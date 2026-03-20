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
public import Mathlib.CategoryTheory.Subobject.WellPowered
public import Mathlib.CategoryTheory.Subobject.Lattice
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

universe w v u

namespace CategoryTheory.Abelian

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C] -- [HasCoproducts C]

lemma gc_rightOrthogonal_leftOrthogonal :
    GaloisConnection (OrderDual.toDual (α := ObjectProperty C) ∘ ObjectProperty.rightOrthogonal)
  (ObjectProperty.leftOrthogonal ∘ OrderDual.ofDual) :=
  fun _ _ ↦ ⟨fun h _ hX _ _ hY ↦ h _ hY _ hX, fun h _ hX _ _ hY ↦ h _ hY _ hX⟩

@[simp]
lemma leftOrthogonal_rightOrthogonal_leftOrthogonal_eq_leftOrthogonal (P : ObjectProperty C) :
    P.leftOrthogonal.rightOrthogonal.leftOrthogonal = P.leftOrthogonal := by
  simpa [Function.comp] using
    gc_rightOrthogonal_leftOrthogonal.u_l_u_eq_u (OrderDual.toDual P)

@[simp]
lemma leftOrthogonal_rightOrthogonal_leftOrthogonal_eq_rightOrthogonal (P : ObjectProperty C) :
    P.rightOrthogonal.leftOrthogonal.rightOrthogonal = P.rightOrthogonal := by
  simpa [Function.comp] using
    gc_rightOrthogonal_leftOrthogonal.l_u_l_eq_l (OrderDual.toDual P)

lemma le_rightOrthogonal_leftOrthogonal (P : ObjectProperty C) :
    P ≤ P.rightOrthogonal.leftOrthogonal := by
  simpa [Function.comp] using gc_rightOrthogonal_leftOrthogonal.le_u_l P

lemma le_leftOrthogonal_rightOrthogonal (P : ObjectProperty C) :
    P ≤ P.leftOrthogonal.rightOrthogonal := by
  simpa [Function.comp] using gc_rightOrthogonal_leftOrthogonal.l_u_le (OrderDual.toDual P)

/-
def PretorsionClass (Φ : Preradical C) : ObjectProperty C :=
  fun X ↦ IsIso (Φ.ι.app X)

def PretorsionFreeClass (Φ : Preradical C) : ObjectProperty C :=
  fun X ↦ CategoryTheory.Limits.IsZero (Φ.r.obj X)

example (X : C) (P : ObjectProperty C) : C := by
  haveI : Limits.HasCoproducts C := by infer_instance
  let f := fun Y : {Y : Subobject X // P Y} ↦ (Y.1 : C)
  #check ∐ f
  sorry
-/

/-- A Torsion Theory in an abelian category consists of two classes, `T` and `F`, of
torsion and torsion-free objects, respectively, such that `T` is the left orthogonal
of `F` and `F` is the right orthogonal of `T`. -/
structure TorsionTheory (T F : ObjectProperty C) : Prop where
  torsion_eq_leftOrthogonal : T = F.leftOrthogonal
  free_eq_rightOrthogonal : F = T.rightOrthogonal

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

lemma torsionTheoryGeneratedBy (P : ObjectProperty C) :
    TorsionTheory P.rightOrthogonal.leftOrthogonal P.rightOrthogonal where
      torsion_eq_leftOrthogonal := rfl
      free_eq_rightOrthogonal := by simp

lemma torsionTheoryCogeneratedBy (P : ObjectProperty C) :
    TorsionTheory P.leftOrthogonal P.leftOrthogonal.rightOrthogonal where
      torsion_eq_leftOrthogonal := by simp
      free_eq_rightOrthogonal := rfl

lemma isClosedUnderQuotients_of_torsionTheory {T F : ObjectProperty C} (hTF : TorsionTheory T F) :
    T.IsClosedUnderQuotients where
      prop_of_epi := fun f _ hPX ↦ hTF.torsion_of_epi hPX f

lemma isClosedUnderExtensions_of_torsionTheory {T F : ObjectProperty C} (hTF : TorsionTheory T F) :
    T.IsClosedUnderExtensions where
      prop_X₂_of_shortExact := by
        intro S hs hX₁ hX₃
        apply hTF.mem_torsion_iff.mpr
        intro Z k hZ
        let t : Limits.CokernelCofork S.f :=
          Limits.CokernelCofork.ofπ k  (hTF.mem_torsion_iff.mp hX₁ (S.f ≫ k) hZ)
        let l : S.X₃ ⟶ Z := hs.gIsCokernel.desc t
        have hl: l = 0 := hTF.mem_free_iff.mp hZ l hX₃
        have hfac : S.g ≫ l = k :=
          hs.gIsCokernel.fac t Limits.WalkingParallelPair.one
        simp [← hfac, hl]

lemma isClosedUnderCoproducts_of_torsionTheory {T F : ObjectProperty C} (hTF : TorsionTheory T F) :
    ∀ {J : Type w}, T.IsClosedUnderColimitsOfShape (Discrete J) := by
  intro J
  refine { colimitsOfShape_le := ?_}
  intro X ⟨hX⟩
  apply hTF.mem_torsion_iff.mpr
  intro Y f hY
  apply hX.isColimit.hom_ext
  intro j
  simpa [comp_zero] using hTF.mem_torsion_iff.mp (hX.prop_diag_obj j) (hX.ι.app j ≫ f) hY

theorem isTorsionClass_iff {P : ObjectProperty C} [LocallySmall.{w} C] [WellPowered.{w} C]
    [HasCoproducts.{w} C] : (∃ F : ObjectProperty C, TorsionTheory P F) ↔
    (P.IsClosedUnderQuotients ∧ P.IsClosedUnderExtensions ∧
    ∀ {J : Type w}, P.IsClosedUnderColimitsOfShape (Discrete J)) := by
  refine ⟨fun ⟨F, hPF⟩ ↦ ⟨isClosedUnderQuotients_of_torsionTheory hPF,
      isClosedUnderExtensions_of_torsionTheory hPF,
      isClosedUnderCoproducts_of_torsionTheory hPF⟩, ?_⟩
  rintro ⟨hquot, hext, hcoprod⟩
  refine ⟨P.rightOrthogonal, ?_⟩
  refine { torsion_eq_leftOrthogonal := ?_, free_eq_rightOrthogonal := rfl }
  · refine le_antisymm (le_rightOrthogonal_leftOrthogonal P) ?_
    · intro X hPX
      let Y := CategoryTheory.Subobject.sSup {A : Subobject X | P (A : C)}
      /- TODO: Prove that X/Y has property P. -/
      sorry



end TorsionTheory

end CategoryTheory.Abelian
