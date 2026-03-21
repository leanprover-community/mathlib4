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

universe w v v' u u'

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

/-- A Torsion Theory in an abelian category consists of two classes, `T` and `F`, of
torsion and torsion-free objects, respectively, such that `T` is the left orthogonal
of `F` and `F` is the right orthogonal of `T`. -/
structure TorsionTheory (T F : ObjectProperty C) : Prop where
  torsion_eq_leftOrthogonal : T = F.leftOrthogonal
  free_eq_rightOrthogonal : F = T.rightOrthogonal

namespace TorsionTheory

/- lemma mem_torsion_iff {X : C} {T F : ObjectProperty C} (hTF : TorsionTheory T F) :
    T X ↔ F.leftOrthogonal X := by
  simp [hTF.torsion_eq_leftOrthogonal]

lemma mem_free_iff {X : C} (T F : ObjectProperty C) (hTF : TorsionTheory T F) :
    F X ↔ T.rightOrthogonal X := by
  simp [hTF.free_eq_rightOrthogonal] -/

example (T F : ObjectProperty C) (hTF : TorsionTheory T F) (X : C) :
    T X ↔ (∀ {Y : C}, ∀ f : X ⟶ Y, F Y → f = 0) := by
  simpa [hTF.torsion_eq_leftOrthogonal] using ObjectProperty.leftOrthogonal_iff F X

example (T F : ObjectProperty C) (hTF : TorsionTheory T F) (Y : C) :
    F Y ↔  (∀ {X : C}, ∀ f : X ⟶ Y, T X → f = 0) := by
  simpa [hTF.free_eq_rightOrthogonal] using ObjectProperty.rightOrthogonal_iff T Y

lemma torsionTheoryGeneratedBy (P : ObjectProperty C) :
    TorsionTheory P.rightOrthogonal.leftOrthogonal P.rightOrthogonal where
      torsion_eq_leftOrthogonal := rfl
      free_eq_rightOrthogonal := by simp

lemma torsionTheoryCogeneratedBy (P : ObjectProperty C) :
    TorsionTheory P.leftOrthogonal P.leftOrthogonal.rightOrthogonal where
      torsion_eq_leftOrthogonal := by simp
      free_eq_rightOrthogonal := rfl

lemma leftOrthogonal_of_epi (P : ObjectProperty C)
    {X Y : C} (hX : P.leftOrthogonal X) (f : X ⟶ Y) [Epi f] : P.leftOrthogonal Y := by
  intro Z g hZ
  have hfg : f ≫ g = 0 := hX (f ≫ g) hZ
  exact Limits.zero_of_epi_comp f hfg

instance (P : ObjectProperty C) : (P.leftOrthogonal).IsClosedUnderQuotients where
  prop_of_epi := fun f _ hX ↦ leftOrthogonal_of_epi P hX f

instance (P : ObjectProperty C) : (P.leftOrthogonal).IsClosedUnderExtensions where
  prop_X₂_of_shortExact := by
    intro s hs hX₁ hX₃ Z k hZ
    let t : Limits.CokernelCofork s.f :=
      Limits.CokernelCofork.ofπ k (hX₁ (s.f ≫ k) hZ)
    let l : s.X₃ ⟶ Z := hs.gIsCokernel.desc t
    have hl : l = 0 := hX₃ l hZ
    have hfac : s.g ≫ l = k :=
      hs.gIsCokernel.fac t Limits.WalkingParallelPair.one
    simp [← hfac, hl]

instance (P : ObjectProperty C) {J : Type u'} [Category.{v'} J] :
    ObjectProperty.IsClosedUnderColimitsOfShape (P.leftOrthogonal) J where
  colimitsOfShape_le := by
    intro X ⟨hX⟩ Y f hY
    apply hX.isColimit.hom_ext
    intro j
    simpa [comp_zero] using (hX.prop_diag_obj j) (hX.ι.app j ≫ f) hY

-- I think these will likely get removed once things are cleand up.
lemma isClosedUnderQuotients_of_torsionTheory {T F : ObjectProperty C} (hTF : TorsionTheory T F) :
    T.IsClosedUnderQuotients := by
  rw [hTF.torsion_eq_leftOrthogonal]
  infer_instance

lemma isClosedUnderExtensions_of_torsionTheory {T F : ObjectProperty C} (hTF : TorsionTheory T F) :
    T.IsClosedUnderExtensions := by
  rw [hTF.torsion_eq_leftOrthogonal]
  infer_instance

lemma isClosedUnderCoproducts_of_torsionTheory {T F : ObjectProperty C} (hTF : TorsionTheory T F) :
    ∀ {J : Type w}, T.IsClosedUnderColimitsOfShape (Discrete J) := by
  intro J
  rw [hTF.torsion_eq_leftOrthogonal]
  infer_instance

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
    · intro X hX
      /-
        Started off trying to ape the construction from Stenström, which goes roughly like this:
        Assume `X : C` and `hX : P.rightOrthogonal.leftOrthogonal X`. Form the maximal `P`-subobject
        of `X`, `Y`. Prove that `X/Y` lies in `P.rightOrthogonal` as follows. If `T : C` and
        `P T`, then any morphism `α : T ⟶ X/Y` has image with property `P` because
        `P.isClosedUnderQuotients`. But then the image of `α` corresponds to a subobject of `X` that
        contains `Y` and has property `P`. Hence the corresponding subobject of `X` is `Y`, the
        image of `α` is zero. This implies `α` is zero and thus `X/Y` lies in `P.rightOrthogonal`.
        Now projection `X ⟶ X/Y` is zero by `hX`. Therefore `Y = X`.

        Somewhere along the way, things went off the rails. Starting to think I'm using the wrong
        components. Will revisit.
      -/
      let subobjs : Set (Subobject X) := {A : Subobject X | P (Subobject.underlying.obj A)}
      let Y := CategoryTheory.Subobject.sSup subobjs
      let I := equivShrink (Subobject X) '' subobjs
      let f := Subobject.smallCoproductDesc subobjs -- Morphism coproduct over `subobjs` to `X`
      let D : Discrete I ⥤ C := Discrete.functor fun j => ((equivShrink (Subobject X)).symm j : C)
      have hPcoprod : P (colimit D) := by
        haveI := hcoprod (J := I)
        have hD : ∀ j, P (D.obj j) := by
          intro j
          rcases j with ⟨j⟩
          change P (((equivShrink (Subobject X)).symm j : Subobject X) : C)
          rcases j.2 with ⟨A, hA, hj⟩
          have : ((equivShrink (Subobject X)).symm j : Subobject X) = A := by
            simpa using (congrArg (Equiv.symm (equivShrink (Subobject X))) hj).symm
          rw [this]
          exact hA
        simpa [D] using P.prop_colimit D hD
      have hPimage : P (image f) := by
        exact hquot.prop_of_epi (factorThruImage f) hPcoprod
      have hPY : P (Subobject.underlying.obj Y) := by
        dsimp [Y,f]
        rw [Subobject.sSup]
        let e : Subobject.underlying.obj
            (Subobject.mk (Limits.image.ι (Subobject.smallCoproductDesc subobjs))) ≅
            Limits.image (Subobject.smallCoproductDesc subobjs) :=
        Subobject.underlyingIso (Limits.image.ι (Subobject.smallCoproductDesc subobjs))
        exact P.prop_of_iso e.symm hPimage
      let ses := ShortComplex.mk Y.arrow (cokernel.π Y.arrow) (cokernel.condition Y.arrow)
      have hs : ses.ShortExact := {
        exact := by
          exact ShortComplex.exact_of_g_is_cokernel ses
            (cokernelIsCokernel ses.f)
        mono_f := by infer_instance
        epi_g := by infer_instance
      }
      have hcok : P.rightOrthogonal (cokernel Y.arrow) := by
        sorry
      sorry

end TorsionTheory

end CategoryTheory.Abelian
