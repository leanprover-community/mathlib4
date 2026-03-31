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

example (P : ObjectProperty C) [P.IsClosedUnderQuotients] {X Y : C} (hX : P X) (f : X ⟶ Y) :
    P (image f) :=
  ObjectProperty.IsClosedUnderQuotients.prop_of_epi (factorThruImage f) hX

lemma prop_sSup_subobjectOf (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C]
    (X : C) : P (Subobject.sSup {A : Subobject X | P (A : C)}) := by
  let subobjs := {A : Subobject X | P (A : C)}
  let I := equivShrink (Subobject X) '' subobjs
  let D : Discrete I ⥤ C := Discrete.functor fun j => ((equivShrink (Subobject X)).symm j : C)
  have hPDi (i : Discrete I) : P (D.obj i) := by
    obtain ⟨⟨_, A, hA, rfl⟩⟩ := i
    simpa [D] using hA
  have hPcolimD : P (colimit D) := by
    simpa using P.prop_colimit D hPDi
  let f := Subobject.smallCoproductDesc subobjs
  have hPimage : P (image f) :=
    P.prop_of_epi (factorThruImage f) hPcolimD
  let e : ((Subobject.mk (Limits.image.ι (Subobject.smallCoproductDesc subobjs))) : C) ≅
      Limits.image (Subobject.smallCoproductDesc subobjs) :=
    Subobject.underlyingIso (Limits.image.ι (Subobject.smallCoproductDesc subobjs))
  simpa [Subobject.sSup] using P.prop_of_iso e.symm hPimage

/-
These should be all the ingredients for the converse of `isTorsion_iff`, but currently in an
awful state. Some notes on the badness:

Attack is basically the same as Stenström's, just adapted to the available tools in mathlib.
Form the maximal `P`-subobject, `Y`, of `X` via `Subobject.sSup` and show `P Y` (above).
Show `P.rightOrothogonal (cokernel Y.arrow)` and conclude that `Y.arrow` is `Epi`, hence `P X`.
The bulk of the ugliness lies in showing `P.rightOrthogonal (cokernel Y.arrow)`.
(Part of the problem might be in misunderstanding/misuing the API for `Subobject`?)

Most of the work is in showing for `P Z` and `f : Z ⟶ cokernel Y.arrow`, `B := image f` is 0.
The necessary component is lifting `B` to a subobject of `X` that contains `Y` and has property `P`.
Initially attempted to use `Subobject.pullback`, but couldn't seem to find a way to prove that
`Subobject.pullbackπ` (i.e. the morphism from the subobject of `X` to `B`) is `Epi`. This is mostly
why I'm concerned about my usage of the `Subobject` API; `Subobject.pullbackπ` is supposed to be the
projection corresponding to `cokernel.π Y.arrow`, so I would expect to be able to prove
`Subobject.pullbackπ` easily when `Epi` is stable under pullback in `C`. I assume I've missed
something.

Decided instead to use `A := pullback (cokernel.π Y.arrow) (image.ι f)` directly, with `i := fst`
and `p := snd`. From there,
  * Use `pullback.lift Y.arrow 0` to construct `g : Y ⟶ A`,
  * Show the `ShortComplex` with left leg `g` and right leg `p` is `ShortExact`,
  * Prove that the subobject of `X` corresponding to `image.ι i` is contained in `Y`, which factors
    `image.ι i` through `Y.arrow`,
  * Use `p = 0` and `Epi p` to force `B = 0`.

TODO: Need to sort out the correct level of generality to state, prove, and home the above.
 -/
example (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
    [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C] :
    P = P.rightOrthogonal.leftOrthogonal := by
  refine le_antisymm (le_rightOrthogonal_leftOrthogonal P) ?_
  intro X hX
  let Y := CategoryTheory.Subobject.sSup {A : Subobject X | P (A : C)}
  have hPY : P (Y : C) := prop_sSup_subobjectOf P X
  let ses := ShortComplex.mk Y.arrow (cokernel.π Y.arrow) (cokernel.condition Y.arrow)
  have hses : ses.ShortExact := {
    exact := by
      exact ShortComplex.exact_of_g_is_cokernel ses
        (cokernelIsCokernel ses.f)
    mono_f := by infer_instance
    epi_g := by infer_instance
  }
  have hcok : P.rightOrthogonal (cokernel Y.arrow) := by
    rw [ObjectProperty.rightOrthogonal_iff]
    intro Z f hPZ
    let A := pullback (cokernel.π Y.arrow) (Abelian.image.ι f)
    let B := Abelian.image f
    let p : A ⟶ B := pullback.snd (cokernel.π Y.arrow) (Abelian.image.ι f)
    let i : A ⟶ X := pullback.fst (cokernel.π Y.arrow) (Abelian.image.ι f)
    have hPimf : P (Abelian.image f) :=
      ObjectProperty.IsClosedUnderQuotients.prop_of_epi (Abelian.factorThruImage f) hPZ
    have w₁ : Y.arrow ≫ cokernel.π Y.arrow = 0 ≫ Abelian.image.ι f := by
      simp
    let g := pullback.lift Y.arrow 0 w₁
    haveI : Mono g := by
      apply (mono_comp_iff_of_mono g i).mp
      rw [pullback.lift_fst Y.arrow 0 w₁]
      infer_instance
    let shortComplex : ShortComplex C :=
      ShortComplex.mk g p (pullback.lift_snd Y.arrow 0 w₁)
    have hshortComplex : shortComplex.ShortExact := {
      exact := by
        refine ShortComplex.exact_of_f_is_kernel shortComplex ?_
        refine KernelFork.IsLimit.ofι' g (pullback.lift_snd Y.arrow 0 w₁) ?_
        intro A k hk
        have : i ≫ cokernel.π Y.arrow = p ≫ Abelian.image.ι f := by
          simpa [i, p] using pullback.condition
        have : (k ≫ i) ≫ cokernel.π Y.arrow = 0 := calc
          _ = k ≫ i ≫ cokernel.π Y.arrow := by rw [← Category.assoc]
          _ = k ≫ p ≫ Abelian.image.ι f := by
            rw [this]
          _ = (k ≫ p) ≫ Abelian.image.ι f := by
            rw [Category.assoc]
          _ = 0 := by simp [p, hk]
        let kernelFork : KernelFork (cokernel.π Y.arrow) := (KernelFork.ofι (k ≫ i) this)
        let l : A ⟶ Y := hses.fIsKernel.lift kernelFork
        have hfac : l ≫ Y.arrow = k ≫ i :=
          hses.fIsKernel.fac kernelFork WalkingParallelPair.zero
        refine ⟨l ,?_⟩
        apply (cancel_mono i).mp
        calc
          _ = l ≫ g ≫ i := by rw [Category.assoc]
          _ = l ≫ Y.arrow := by rw [pullback.lift_fst Y.arrow 0 w₁]
          _ =  k ≫ i := hfac
      mono_f := by infer_instance
      epi_g := by infer_instance
    }
    have hPA: P A :=
      ObjectProperty.prop_X₂_of_shortExact P hshortComplex hPY hPimf
    have hPimagefst : P (Abelian.image i) :=
      P.prop_of_epi (Abelian.factorThruImage i) hPA
    have himg_mem : Subobject.mk (Abelian.image.ι i) ∈ {A : Subobject X | P (A : C)} := by
      change P (((Subobject.mk (Abelian.image.ι i) : Subobject X) : C))
      exact P.prop_of_iso (Subobject.underlyingIso (Abelian.image.ι i)).symm hPimagefst
    have himg_le_Y : Subobject.mk (Abelian.image.ι i) ≤ Y := by
      simpa [Y] using (le_sSup himg_mem)
    have : (Subobject.mk (Abelian.image.ι i) : C) ⟶ (Y : C) :=
      (Subobject.mk (Abelian.image.ι i)).ofLE Y himg_le_Y
    let g' : Abelian.image i ⟶ (Y : C) := Subobject.ofMkLE (Abelian.image.ι i) Y himg_le_Y
    have : g' ≫ Y.arrow = image.ι i := by exact Subobject.ofMkLE_arrow himg_le_Y
    have : p = 0 := by
      rw [← cancel_mono (Abelian.image.ι f), zero_comp]
      calc
        _ = i ≫ cokernel.π Y.arrow := pullback.condition.symm
        _ = Abelian.factorThruImage i ≫ image.ι i ≫ cokernel.π Y.arrow :=
          Eq.symm (kernel.lift_ι_assoc (cokernel.π i) i (cokernel.condition i) (cokernel.π Y.arrow))
        _ = Abelian.factorThruImage i ≫ (g' ≫ Y.arrow) ≫ cokernel.π Y.arrow := by
          exact
            Eq.symm
              (Abelian.factorThruImage i ≫=
                congrFun (congrArg CategoryStruct.comp this) (cokernel.π Y.arrow))
        _ = 0 := by simp
    have : IsZero (Abelian.image f) :=
      IsZero.of_epi_eq_zero p this
    have : Abelian.image.ι f = 0 := IsZero.eq_zero_of_src this (Abelian.image.ι f)
    rw [← image.fac f, this, comp_zero]
  have : cokernel.π Y.arrow = 0 := by
    exact
      eq_of_comp_right_eq fun {Z} h ↦
        congrArg (CategoryStruct.comp h) (hX (cokernel.π Y.arrow) hcok)
  haveI : Epi Y.arrow := by exact Preadditive.epi_of_cokernel_zero (hX (cokernel.π Y.arrow) hcok)
  exact ObjectProperty.prop_of_epi P Y.arrow hPY

/- theorem isTorsionClass_iff {P : ObjectProperty C} [LocallySmall.{w} C] [WellPowered.{w} C]
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
      let subobjs : Set (Subobject X) := {A : Subobject X | P (A : C)}
      let Y := CategoryTheory.Subobject.sSup subobjs
      have hPY : P Y := prop_sSup_subobjectOf P X
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
      sorry -/

end TorsionTheory

end CategoryTheory.Abelian
